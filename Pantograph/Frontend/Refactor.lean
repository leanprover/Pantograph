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
  deriving Inhabited

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

namespace Refactor

structure Context where
  deriving Inhabited

structure State where
  -- Collected top-level units
  commands : List Command := []
  deriving Inhabited

abbrev RefactorM := ReaderT Context $ StateRefT State FrontendM

end Refactor

export Refactor (RefactorM)

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
  let unit := if step.msgs.any (·.severity == .error) then
      {
        hasError := true,
        stx := step.stx,
        trees := step.trees,
      }
    else
      {
        stx := step.stx,
        trees := step.trees,
        dependencies,
        isSearchTarget := hasSorry step,
        constants,
      }
  modify λ state =>
    {
      commands := state.commands.append [unit],
    }

/-- Fold `sorry`s into one definition -/
def foldTheorems (commands : List Command) : ExceptT String FrontendM Syntax := do
  sorry

/-- Scroll one unit down from the top -/
def collectNextCommand : ExceptT String RefactorM Syntax := do
  let { commands, .. } ← get
  let decl := commands.head!
  if !decl.isSearchTarget then
    return decl.stx
  let (series, commands) ← (λ (z : StateT NameSet (Except String) _) => z.run' .empty) $
    commands.partitionM λ unit => do
      let deps ← get
      if unit.constants.any (deps.contains ·) then
        set $ unit.constants.fold (init := deps) λ acc n => acc.insert n
        return true
      else
        return false
  if series.isEmpty then
    return decl.stx
  -- `series` should then be rolled into a single declaration
  modify ({ · with commands })
  return decl.stx
