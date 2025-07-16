import Pantograph.Frontend.Basic
import Pantograph.Frontend.Elab

open Lean

namespace Pantograph.Frontend

structure TopLevel where
  dependencies : NameSet := .empty
  stx : Syntax
  trees : List Elab.InfoTree
  hasError : Bool := false
  isSearchTarget : Bool := false

protected def TopLevel.canFactorIntoDependentType (topLevel : TopLevel) : Bool := sorry

namespace Refactor

structure Context where

structure State where
  units : List TopLevel
  declaredIn : Std.HashMap Name (Fin units.length)

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

def preprocessRefactor : RefactorM Unit := executeFrontend λ step => unsafe do
  let constants ← collectNewDefinedConstants step
  let dependencies := constants.foldl (init := NameSet.empty) λ acc c =>
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
      }
  modify λ { units, declaredIn } =>
    let i := units.length
    let units' : List _ := units ++ [unit]
    let declaredIn : Std.HashMap Name (Fin units'.length) := unsafeCast declaredIn
    let declaredIn := constants.foldl (init := declaredIn) λ acc c =>
      have h : i < units'.length := by
        unfold units' i
        rewrite [List.length_append, List.length_singleton, Nat.lt_succ]
        apply Nat.le_refl
      acc.insert c ⟨i, h⟩
    {
      units := units',
      declaredIn,
    }

end Pantograph.Frontend
