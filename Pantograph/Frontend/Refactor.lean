/- A scrolling refactor algorithm: The algorithm ingests Lean compilation units
on one end and outputs compilation units on the other. -/
import Pantograph.Frontend.Basic
import Pantograph.Frontend.Elab

open Lean

namespace Pantograph.Frontend

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

@[inline] def Command.runCommandElabM (command : Command) (x : Elab.Command.CommandElabM α) : FrontendM α := do
  let config ← read
  let ctx ← readThe Elab.Frontend.Context
  let s ← get
  let cmdCtx : Elab.Command.Context := {
    cmdPos       := s.cmdPos
    fileName     := ctx.inputCtx.fileName
    fileMap      := ctx.inputCtx.fileMap
    snap?        := none
    cancelTk?    := config.cancelTk?
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run command.state) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => Elab.Frontend.setCommandState sNew; return a

namespace Refactor

structure Context where
  deriving Inhabited

structure State where
  -- Collected top-level units
  commands : List Command := []
  deriving Inhabited

abbrev RefactorM := ReaderT Context $ StateRefT State FrontendM

def fail { α } (s : String) : IO α :=
  throw <| .userError s

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

/-- Scroll to the end of the file, ingesting all compilation units in the process  -/
def preprocessRefactor : RefactorM Unit := executeFrontend λ step => unsafe do
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
  modify λ state =>
    {
      commands := state.commands.append [unit],
    }

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
      let t := env.find? name |>.get!
      return (name, t.type)
  let companions ← tail.mapM λ command => command.runCommandElabM do
    Elab.Command.liftTermElabM do
      let env := command.state.env
      let name := command.constants.toList.head!
      let info := env.find? name |>.get!
      let c ← mkConstWithLevelParams headName
      Meta.kabstract info.type c
  -- Concatenate all comments
  let allDocs := "\n".intercalate $ (head :: tail).filterMap λ command =>
    let `(docComment|$comment) := command.comments
    let s := comment.getDocString
    if s.isEmpty then .none else s
  let .str _ binderName := headName | panic! s!"head name must be .str but it is {headName}"
  -- Under the environment of `head`, construct the companion type
  head.runCommandElabM do
    let target ← Elab.Command.liftTermElabM do
      -- Construct the companion
      let companion ← Meta.withLocalDeclD `binderName witness λ binder => do
        let companion ← mkProdElem ``And.intro <| companions.map (·.instantiate1 binder)
        Meta.mkLambdaFVars #[binder] companion
      let target ← Meta.mkAppOptM ``Subtype #[witness, companion]
      Meta.check target
      -- Delaborate this back into syntax
      withOptions (λ opt => pp.funBinderTypes.set (pp.proofs.set opt true) true) do
        PrettyPrinter.delab target
    let theoremIdent := mkIdent (.str .anonymous s!"{binderName}_composite")
    let command ← if allDocs.isEmpty then
        `(command|def $theoremIdent : $target := sorry)
      else
        let comment := mkDocComment allDocs
        `(command|$comment:docComment def $theoremIdent : $target := sorry)
    Elab.Command.liftCoreM do
      PrettyPrinter.formatCommand command

/-- Scroll one unit down from the top -/
def collectNextCommand : RefactorM Format := do
  let { commands, .. } ← get
  let decl :: commands := commands | Refactor.fail "No commands left"
  if !decl.isSearchTarget then
    return format decl.stx
  -- This keeps track of two `NameSet`s. If the dependency structure is
  -- non-flat, we cannot refactor this.
  let ((series, commands), (_, _, isNonFlat)) := (λ (z : StateM (NameSet × NameSet × Bool) _) => z.run (decl.constants, {}, false)) $
    commands.partitionM λ command => do
      let (headDeps, innerDeps, isNonFlat) ← get
      if command.dependencies.any (innerDeps.contains ·) then
        let innerDeps := command.constants.fold (init := innerDeps) λ acc n => acc.insert n
        set (headDeps, innerDeps, true)
        return true
      if command.dependencies.any (headDeps.contains ·) then
        let innerDeps := command.constants.fold (init := innerDeps) λ acc n => acc.insert n
        set (headDeps, innerDeps, isNonFlat)
        return true
      else
        return false
  if series.isEmpty then
    return format decl.stx
  -- `series` should then be rolled into a single declaration
  modify ({ · with commands })
  if isNonFlat then
    Refactor.fail "Cannot refactor non-flat dependency structure"
  foldTheoremsFlat decl series

end Refactor

open Refactor in
def runRefactor (env : Environment) (source: String) (rContext : Refactor.Context := {})
  : IO String := do
  let filename := "<anonymous>"
  let (fContext, fState) ← createContextStateFromFile source filename env {}
  let m : RefactorM _ := do
    preprocessRefactor
    let mut result := Format.nil
    while !(← get).commands.isEmpty do
      let command ← collectNextCommand
      result := result ++ Format.line ++ command
    return result.pretty
  m.run rContext |>.run' {}
    |>.run {}
    |>.run fContext |>.run' fState

export Refactor (RefactorM)
