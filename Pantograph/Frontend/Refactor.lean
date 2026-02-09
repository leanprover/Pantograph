/- A scrolling refactor algorithm: The algorithm ingests Lean compilation units
on one end and outputs compilation units on the other. -/
import Pantograph.Frontend.Basic
import Pantograph.Frontend.InfoTree
import Pantograph.Delab

open Lean

namespace Pantograph.Frontend

namespace Refactor

/-- A command in the input file, frozen in context -/
structure Command where
  dependencies : NameSet := .empty
  stx : Syntax
  trees : List Elab.InfoTree
  hasError : Bool := false
  constants : NameSet := .empty
  state : Elab.Command.State
  messages : List Message

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

structure Config where
  coreOptions : Options := {}
  deriving Inhabited

structure Context where
  inContext : Parser.InputContext
  config : Config := {}

structure State where
  outContext : Parser.InputContext
  outState : Elab.Frontend.State

  -- Collected top-level units, scrolling
  commands : List Command := []

/-- Two monads rolled into one -/
abbrev RefactorM := ReaderT Context $ StateRefT State IO

def readConfig : RefactorM Config := do
  return (← read).config
def readCoreOptions : RefactorM Options := do
  return (← readConfig).coreOptions

def fail { α } (s : String) : IO α :=
  throw <| .userError s

def mergeFileMap (fm1 fm2 : FileMap) : FileMap :=
  let bias := fm1.source.rawEndPos.byteIdx + 1
  let mappedPos := fm2.positions.map λ pos => { byteIdx := pos.byteIdx + bias }
  {
    source := s!"{fm1.source}\n{fm2.source}",
    positions := fm1.positions.take (fm1.positions.size - 1) ++ mappedPos
  }

/-- Add one command to the refactored file -/
def pushNewCommand (f : Format) : RefactorM Unit := do
  modify λ state@{ outContext := outContext@{ fileMap, .. }, .. } =>
    let payload := f.pretty
    let merged := mergeFileMap fileMap payload.toFileMap
    {
      state with outContext := {
        outContext with
        inputString := merged.source,
        fileMap := merged,
        endPos := merged.source.rawEndPos,
        endPos_valid := by simp,
      }
    }
  -- After modification, run the parser ahead by one position
  let { outContext := inputCtx, outState, .. } ← get
  let (_endFlag, outState@ { commandState := { messages, .. }, .. }) ←
    Elab.Frontend.processCommand.run { inputCtx } |>.run outState
  -- Ensure no error has occurred
  if messages.hasErrors then
    let messages ← messages.toList.mapM (·.toString)
    throw (.userError s!"Error messages: {messages}")
  modify ({ · with outState })

/-- Run `FrontendM` at the tail of the out file -/
def liftFrontend { α } (x : FrontendM α) : RefactorM α := do
  let { outContext := inputCtx, outState, .. } ← get
  x.run {} |>.run { inputCtx } |>.run' outState
/-- Run `CoreM` at the tail of the out file -/
def runCoreM { α } (x : CoreM α) : RefactorM α := do
  liftFrontend $ runCommandElabM $ Elab.Command.liftCoreM x

def pushNewCommand' (command : Syntax.Command) : RefactorM Unit := do
  let f ← runCoreM do
    PrettyPrinter.ppCommand command
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
    | .some v => s.append v.getUsedConstantsAsSet
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
def preprocess : FrontendM (List Command) := mapCompilationSteps λ step => do
  let constants ← step.newConstants
  let dependencies := constants.foldl (init := NameSet.empty) λ acc c =>
    acc.append $ constantDependencies step.after c
  let commandState := (← getThe Elab.Frontend.State).commandState
  let unit := if step.msgs.any (·.severity == .error) then
      {
        hasError := true,
        stx := step.stx,
        trees := step.trees,
        state := commandState,
        messages := step.msgs,
      }
    else
      {
        stx := step.stx,
        trees := step.trees,
        dependencies,
        constants,
        state := commandState,
        messages := step.msgs,
      }
  return unit

/-- Creates `combine (combine a[0] a[1]) a[2] ...` -/
def mkProdElem (combine : Name := ``And.intro) : List Expr → MetaM Expr
  | .nil => return .const `Unit []
  | [a] => return a
  | x :: xs => do
    let r ← mkProdElem combine xs
    Meta.mkAppM combine #[x, r]

private def mkDocComment (s : String) :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom s!"{s} -/"]

protected def _root_.Array.last! { α } [Inhabited α] (a : Array α) : α :=
  match h : a.size with
  | 0 => default
  | n+1 => a[n]

def distilSearchTarget { α } (head : Command) (tail : List Command) (f : (Expr × Expr) → List (Expr × Expr) → Elab.Term.TermElabM α)
  : RefactorM α := do
  let (headName, witness, witnessValue) ← head.runCommandElabM do
    Elab.Command.liftCoreM do
      let env := head.state.env
      let name := head.constants.toList.head!
      let info := env.find? name |>.get!
      let .some value := info.value?
        | throwError s!"Constant has no value: {name}"
      return (name, ← normalize info.type, ← normalize value)
  let companions ← tail.mapM λ command => command.runCommandElabM do
    Elab.Command.liftTermElabM do
      let env := command.state.env
      let name := command.constants.toList.head!
      let info := env.find? name |>.get!
      let type ← normalize info.type
      let c ← mkConstWithLevelParams headName
      let type ← Meta.kabstract type c
      let .some value := info.value?
        | throwError s!"Constant has no value: {name}"
      -- Normalization strips away matchers.
      let value ← normalize value
      let value ← Meta.kabstract value c
      return (type, value)
  liftFrontend $ runCommandElabM $ Elab.Command.liftTermElabM do
    f (witness, witnessValue) companions
  where
  normalize (e : Expr) : CoreM Expr := do
    unfoldAuxLemmas $ ← unfoldMatchers e

/-- Fold `sorry`s into one definition -/
def foldTheoremsFlat (head : Command) (tail : List Command) : RefactorM Syntax.Command := do
  -- Concatenate all doc comments
  let allDocs := "\n".intercalate $ (head :: tail).filterMap λ command =>
    let `(docComment|$comment) := command.comments
    let s := comment.getDocString
    if s.isEmpty then .none else s
  let headName := head.constants.toList.head!
  let binderName := match headName with
    | .str _ binderName => Name.mkSimple binderName
    | _ => `x
  let coreOptions ← readCoreOptions
  distilSearchTarget head tail λ (witness, _) companions => do
    -- Construct the companion
    let companion ← Meta.withLocalDeclD binderName witness λ binder => do
      let companion ← mkProdElem ``And <| companions.map (·.fst.instantiate1 binder)
      Meta.mkLambdaFVars #[binder] companion
    let target ← Meta.mkAppOptM ``Subtype #[witness, companion]
    Meta.check target
    -- Delaborate this back into syntax
    let target ← withOptions (λ _ => pp.analyze.set coreOptions true) do
      PrettyPrinter.delab target
    let theoremIdent := mkIdent $ Name.mkSimple s!"{binderName}_composite"
    let comment? := if allDocs.isEmpty then .none else .some $ mkDocComment allDocs
    `(command|$[$comment?:docComment]? def $theoremIdent : $target := sorry)

structure DependencyTracker where
  -- Constants generated during the next batch of commands to be processed
  innerConstants : NameSet := {}

  isNonFlat : Bool := false
structure DependencyStructure where
  -- Commands which depend on each other
  component : List Command := []
  -- Intercalating commands
  intercalating : List Command := []
  -- Remainder
  tail : List Command
  -- Structure
  tracker : DependencyTracker

def extractDependencyStructure (head : Command) (commands : List Command)
  : RefactorM DependencyStructure := do
  let ((series, other), tracker) := (λ (z : StateM DependencyTracker _) => z.run {}) $
    commands.zipIdx.partitionM λ (command, _) => do
      let tracker ← get
      if command.dependencies.any tracker.innerConstants.contains then
        let innerConstants := command.constants.foldl
          (init := tracker.innerConstants)
          λ acc n => acc.insert n
        modify ({· with innerConstants, isNonFlat := true})
        return true
      if command.dependencies.any head.constants.contains then
        let innerConstants := command.constants.foldl
          (init := tracker.innerConstants)
          λ acc n => acc.insert n
        modify ({· with innerConstants })
        return true
      else
        return false
  if series.isEmpty then
    return {
      tail := commands,
      tracker,
    }
  -- Find all intercalating declarations
  let maxIdx := series.map Prod.snd |>.max?.get!
  let (intercalating, tail) := other.partition λ (_, idx) => idx < maxIdx
  return {
    component := series.map Prod.fst,
    intercalating := intercalating.map Prod.fst,
    tail := tail.map Prod.fst,
    tracker
  }

/-- Scroll one unit down from the top -/
def collectNextCommand : RefactorM Unit := do
  let { commands, .. } ← get
  let decl :: commands := commands | Refactor.fail "No commands left"
  modify ({ · with commands }) -- Prevents infinite loop

  let isSearchTarget ← decl.runCoreM do
    if decl.constants.isEmpty then
      return false
    let name := decl.constants.toList.head!
    let info := (← getEnv).find? name |>.get!
    let .some value := info.value? | return false
    return value.hasSorry
  if !isSearchTarget then
    pushNewCommand' (⟨decl.stx⟩ : Syntax.Command)
    return

  let depstr ← extractDependencyStructure decl commands
  if depstr.component.isEmpty then
    pushNewCommand' (⟨decl.stx⟩ : Syntax.Command)
    return

  if depstr.tracker.isNonFlat then
    Refactor.fail "Cannot refactor non-flat dependency structure"
  modify ({ · with commands := depstr.tail })

  -- Push all intercalating commands
  for command in depstr.intercalating do
    pushNewCommand' (⟨command.stx⟩ : Syntax.Command)

  let f ← foldTheoremsFlat decl depstr.component
  pushNewCommand' f

end Refactor

open Refactor in
def runRefactor (env : Environment) (source : String)
  (config : Refactor.Config := {}) (fileName := defaultFileName) : IO String := do
  let (fContext, fState) ← createContextStateFromFile source fileName env {}
  let commands ← preprocess.run {} |>.run fContext |>.run' fState
  let errors := commands.filter (·.hasError)
  if let .some error := errors.head? then
    let message ← error.messages.mapM (·.toString)
    throw $ IO.userError $ "\n".intercalate message
  let m : RefactorM Unit := do
    while !(← get).commands.isEmpty do
      collectNextCommand
  let outContext := {
    fContext.inputCtx with
    inputString := "",
    fileMap := "".toFileMap,
    endPos := "".rawEndPos,
    endPos_valid := by simp,
  }
  let parserState := {}
  let outState := {
    commandState := Elab.Command.mkState env {} {},
    parserState,
    cmdPos := parserState.pos,
  }
  let (_, state) ← m.run { config, inContext := fContext.inputCtx }
    |>.run { outContext, outState, commands }
  return state.outContext.inputString

export Refactor (RefactorM)
