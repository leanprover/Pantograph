import Lean.Elab
import Lean.Meta

open Lean

namespace Pantograph.Tactic

/-- WARNING: This should be used with a function like `elabTermWithHoles` that properly collects the mvar information from `expr`. -/
def assign (goal: MVarId) (expr: Expr) (nextGoals: List MVarId): MetaM (List MVarId) := do
  goal.checkNotAssigned `Pantograph.Tactic.assign

  -- This run of the unifier is critical in resolving mvars in passing
  let exprType ← Meta.inferType expr
  let goalType ← goal.getType
  unless ← Meta.isDefEq goalType exprType do
    throwError s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} ≠ {← Meta.ppExpr goalType}"
  goal.assign expr
  nextGoals.filterM (not <$> ·.isAssigned)

def evalAssign : Elab.Tactic.Tactic := fun stx => Elab.Tactic.withMainContext do
  let target ← Elab.Tactic.getMainTarget
  let goal ← Elab.Tactic.getMainGoal
  goal.checkNotAssigned `Pantograph.Tactic.evalAssign
  let (expr, nextGoals) ← Elab.Tactic.elabTermWithHoles stx
    (expectedType? := .some target)
    (tagSuffix := .anonymous )
    (allowNaturalHoles := true)
  goal.assign expr
  Elab.Tactic.replaceMainGoal nextGoals

/-- Converts `sorry`s in the source expression to goals. Execute `post` on the
types of the sorrys. -/
def sorryToHole (src : Expr) (post : Expr → MetaM Expr := pure)
    : StateRefT (List MVarId) MetaM Expr :=
  Meta.transform src λ expr =>
    if expr.isSorry then do
      let type ← instantiateMVars (expr.getArg! 0 |>.bindingBody!)
      if type.hasSorry then
        throwError s!"Coupling is not allowed in draft tactic: {← Meta.ppExpr type}"
      let type ← post type
      let mvar ← Meta.mkFreshExprSyntheticOpaqueMVar type
      modify (mvar.mvarId! :: .)
      return .done mvar
    else
      return .continue

-- Given a complete (no holes) expression, extract the sorry's from it and convert them into goals.
def draft (goal : MVarId) (expr : Expr) : MetaM (List MVarId) := do
  goal.checkNotAssigned `Pantograph.Tactic.draft
  let exprType ← Meta.inferType expr
  let goalType ← goal.getType
  unless ← Meta.isDefEq goalType exprType do
    throwError s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} ≠ {← Meta.ppExpr goalType}"

  let (expr', holes) ← sorryToHole expr |>.run []
  goal.assign expr'
  return holes.reverse

def evalDraft : Elab.Tactic.Tactic := fun stx ↦ Elab.Tactic.withMainContext do
  let target ← Elab.Tactic.getMainTarget
  let goal ← Elab.Tactic.getMainGoal
  let (expr, holeGoals) ← Elab.Tactic.elabTermWithHoles stx
    (expectedType? := .some target)
    (tagSuffix := .anonymous)
    (allowNaturalHoles := true)
  let draftGoals ← draft goal expr
  Elab.Tactic.replaceMainGoal $ holeGoals ++ draftGoals


end Pantograph.Tactic
