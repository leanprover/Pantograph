/- A scrolling refactor algorithm: The algorithm ingests Lean compilation units
on one end and outputs compilation units on the other. -/
import Pantograph.Frontend.Basic
import Pantograph.Frontend.Elab
import Pantograph.Delate

open Lean

namespace Pantograph.Frontend

namespace Refactor

/-- A command in the input file, frozen in context -/
structure Command where
  dependencies : NameSet := .empty
  stx : Syntax
  trees : List Elab.InfoTree
  hasError : Bool := false
  isSearchTarget : Bool := false
  constants : NameSet := .empty
  state : Elab.Command.State

inductive CommandCategory where
  -- Definition of data
  | data
  -- Definition fo theorems
  | declaration
  -- section, variable, universe
  | flow
  -- Things which can be discarded.
  | auxiliary
  -- No refactor units may cross an `.unknown` boundary.
  | unknown

protected def Command.category (command : Command) : CommandCategory :=
  match command.stx.getKind with
  | `Lean.Parser.Command.declaration =>
    match command.stx.getArg 2 |>.getKind with
    | `Lean.Parser.Command.structure
    | `Lean.Parser.Command.inductive
      => .data
    | `Lean.Parser.Command.theorem
    | `Lean.Parser.Command.definition
      => .data
    | _ => .unknown
  | `Lean.Parser.Command.section
  | `Lean.Parser.Command.namespace
  | `Lean.Parser.Command.variable
  | `Lean.Parser.Command.end
    => .flow
  | `Lean.Parser.Command.set_option
    => .auxiliary
  | _ => .unknown
protected def Command.comments (command : Command) : Syntax :=
  let modifiers := command.stx.getArg 0
  let comments := modifiers.getArg 0
  comments[0]

structure Context where
  inContext : Parser.InputContext
  deriving Inhabited

structure State where
  outContext : Parser.InputContext
  outState : Elab.Frontend.State

  -- Collected top-level units, scrolling
  commands : List Command := []

/-- Two monads rolled into one -/
abbrev RefactorM := ReaderT Context $ StateRefT State IO

def fail { α } (s : String) : IO α :=
  throw <| .userError s

/-- Add one command to the refactored file -/
def pushNewCommand (command : Format) : RefactorM Unit := do
  modify λ state =>
    let src := state.outContext.input ++ "\n" ++ command.pretty
    let positions := state.outContext.fileMap.positions.push src.endPos
    {
      state with outContext := {
        state.outContext with
        input := src,
        fileMap := {
          source := src,
          positions,
        }
      }
    }
  -- After modification, run the parser ahead by one position
  let { outContext := inputCtx, outState, .. } ← get
  let (_end, outState) ← Elab.Frontend.processCommand.run { inputCtx } |>.run outState
  modify ({ · with outState })

/-- Run `FrontendM` at the tail of the out file -/
def liftFrontend { α } (x : FrontendM α) : RefactorM α := do
  let { outContext := inputCtx, outState, .. } ← get
  x.run {} |>.run { inputCtx } |>.run' outState
def runCoreM { α } (x : CoreM α) : RefactorM α := do
  liftFrontend $ runCommandElabM $ Elab.Command.liftCoreM x

def pushNewCommand' (command : Syntax.Command) : RefactorM Unit := do
  let f ← runCoreM $ PrettyPrinter.formatCommand command
  pushNewCommand f

/-- runs a "frozen" `CommandElabM` that can't modify anything. -/
@[inline] protected
def Command.runCommandElabM (command : Command) (x : Elab.Command.CommandElabM α) : RefactorM α := do
  let inputCtx := (← read).inContext
  let cmdCtx : Elab.Command.Context := {
    fileName     := inputCtx.fileName
    fileMap      := inputCtx.fileMap
    snap?        := none,
    cancelTk?    := .none,
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run command.state) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, _sNew) => return a

@[inline] protected
def Command.runCoreM { α } (command : Command) (c : CoreM α) : RefactorM α :=
  command.runCommandElabM $ Elab.Command.liftCoreM c

def constantDependencies (env : Environment) (name : Name) : NameSet :=
  let const := env.find? name |>.get!
  let s := const.type.getUsedConstantsAsSet
  let s := match const.value? with
    | .some v => s.union v.getUsedConstantsAsSet
    | .none => s
  s

def hasSorry (step : CompilationStep) : Bool :=
  step.trees.any λ tree =>
    let nodes := tree.filter λ
      | .ofTermInfo { expr, .. } => expr.isSorry
      | .ofTacticInfo { stx, .. } => stx.isOfKind `Lean.Parser.Tactic.tacticSorry
      | _ => false
    !nodes.isEmpty

/-- Scroll to the end of the file, reading all compilation units in the process  -/
def preprocessRefactor : FrontendM (List Command) := mapCompilationSteps λ step => do
  let constants ← collectNewDefinedConstants step
  let dependencies := constants.fold (init := NameSet.empty) λ acc c =>
    acc.union $ constantDependencies step.after c
  let commandState := (← getThe Elab.Frontend.State).commandState
  let unit := if step.msgs.any (·.severity == .error) then
      {
        hasError := true,
        stx := step.stx,
        trees := step.trees,
        state := commandState,
      }
    else
      {
        stx := step.stx,
        trees := step.trees,
        dependencies,
        isSearchTarget := hasSorry step,
        constants,
        state := commandState,
      }
  return unit

private def mkProdElem (combine : Name := ``And.intro) : List Expr → MetaM Expr
  | .nil => return .const `Unit []
  | [a] => return a
  | x :: xs => do
    let r ← mkProdElem combine xs
    Meta.mkAppM combine #[x, r]

private def mkDocComment (s : String) :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom s!"{s} -/"]

/-- Fold `sorry`s into one definition -/
def foldTheoremsFlat (head : Command) (tail : List Command) : RefactorM Format := do
  let (headName, witness) ← head.runCommandElabM do
    Elab.Command.liftCoreM do
      let env := head.state.env
      let name := head.constants.toList.head!
      let info := env.find? name |>.get!
      return (name, ← normalize info.type)
  let companions ← tail.mapM λ command => command.runCommandElabM do
    Elab.Command.liftTermElabM do
      let env := command.state.env
      let name := command.constants.toList.head!
      let info := env.find? name |>.get!
      let type ← normalize info.type
      let c ← mkConstWithLevelParams headName
      Meta.kabstract type c
  -- Concatenate all comments
  let allDocs := "\n".intercalate $ (head :: tail).filterMap λ command =>
    let `(docComment|$comment) := command.comments
    let s := comment.getDocString
    if s.isEmpty then .none else s
  let .str _ binderName := headName | panic! s!"head name must be .str but it is {headName}"
  -- Under the environment of `head`, construct the companion type
  liftFrontend <| runCommandElabM do
    let target ← Elab.Command.liftTermElabM do
      -- Construct the companion
      let companion ← Meta.withLocalDeclD (Name.mkSimple binderName) witness λ binder => do
        let companion ← mkProdElem ``And.intro <| companions.map (·.instantiate1 binder)
        Meta.mkLambdaFVars #[binder] companion
      let target ← Meta.mkAppOptM ``Subtype #[witness, companion]
      Meta.check target
      -- Delaborate this back into syntax
      withOptions (λ opt => pp.funBinderTypes.set (pp.proofs.set opt true) true) do
        PrettyPrinter.delab target
    let theoremIdent := mkIdent $ Name.mkSimple s!"{binderName}_composite"
    let comment? := if allDocs.isEmpty then .none else .some $ mkDocComment allDocs
    let command ← `(command|$[$comment?:docComment]? def $theoremIdent : $target := sorry)
    Elab.Command.liftCoreM do
      PrettyPrinter.formatCommand command
  where
  normalize (e : Expr) : CoreM Expr := do
    unfoldAuxLemmas $ ← unfoldMatchers e

structure DependencyTracker where
  -- Constants generated during the next batch of commands to be processed
  innerConstants : NameSet := {}

  isNonFlat : Bool := false

/-- Scroll one unit down from the top -/
def collectNextCommand : RefactorM Unit := do
  let { commands, .. } ← get
  let decl :: commands := commands | Refactor.fail "No commands left"
  modify ({ · with commands }) -- Prevents infinite loop

  if !decl.isSearchTarget then
    pushNewCommand' (⟨decl.stx⟩ : Syntax.Command)
    return

  -- This keeps track of two `NameSet`s. If the dependency structure is
  -- non-flat, we cannot refactor this.
  let ((series, commands), tracker) := (λ (z : StateM DependencyTracker _) => z.run {}) $
    commands.zipIdx.partitionM λ (command, _) => do
      let tracker ← get
      if command.dependencies.any tracker.innerConstants.contains then
        let innerConstants := command.constants.fold
          (init := tracker.innerConstants)
          λ acc n => acc.insert n
        modify ({· with innerConstants, isNonFlat := true})
        return true
      if command.dependencies.any decl.constants.contains then
        let innerConstants := command.constants.fold
          (init := tracker.innerConstants)
          λ acc n => acc.insert n
        modify ({· with innerConstants })
        return true
      else
        return false
  if series.isEmpty then
    pushNewCommand' (⟨decl.stx⟩ : Syntax.Command)
    return
  -- Find all intercalating declarations and just run them
  let maxIdx := series.map Prod.snd |>.max?.get!
  let (intercalating, tail) := commands.partition λ (_, idx) => idx < maxIdx
  -- `series` should then be rolled into a single declaration
  modify ({ · with commands := tail.map Prod.fst })

  if tracker.isNonFlat then
    Refactor.fail "Cannot refactor non-flat dependency structure"

  -- Push all intercalating commands
  for (command, _) in intercalating do
    pushNewCommand' (⟨command.stx⟩ : Syntax.Command)

  let f ← foldTheoremsFlat decl (series.map Prod.fst)
  pushNewCommand f

def messageHasError := "File has error!"

end Refactor

open Refactor in
def runRefactor (env : Environment) (source : String) : IO String := do
  let filename := "<anonymous>"
  let (fContext, fState) ← createContextStateFromFile source filename env {}
  let commands ← preprocessRefactor.run {} |>.run fContext |>.run' fState
  if commands.any (·.hasError) then
    throw $ IO.userError messageHasError
  let m : RefactorM Unit := do
    while !(← get).commands.isEmpty do
      collectNextCommand
  let outContext := {
    fContext.inputCtx with
    input := "",
    fileMap := "".toFileMap,
  }
  let parserState := {}
  let outState := {
    commandState := Elab.Command.mkState env {} {},
    parserState,
    cmdPos := parserState.pos,
  }
  let (_, state) ← m.run { inContext := fContext.inputCtx }
    |>.run { outContext, outState, commands }
  return state.outContext.input

export Refactor (RefactorM)
