import Lean.Meta
import Std.Data.HashMap

open Lean

namespace Pantograph.Frontend

namespace MetaTranslate

structure Context where
  sourceMCtx : MetavarContext := {}
  sourceLCtx : LocalContext := {}

abbrev FVarMap := Std.HashMap FVarId FVarId

structure State where
  -- Stores mapping from old to new mvar/fvars
  mvarMap: Std.HashMap MVarId MVarId := {}
  fvarMap: Std.HashMap FVarId FVarId := {}

/-
Monadic state for translating a frozen meta state. The underlying `MetaM`
operates in the "target" context and state.
-/
abbrev MetaTranslateM := ReaderT Context StateRefT State MetaM

def getSourceLCtx : MetaTranslateM LocalContext := do pure (← read).sourceLCtx
def getSourceMCtx : MetaTranslateM MetavarContext := do pure (← read).sourceMCtx
def addTranslatedFVar (src dst: FVarId) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := state.fvarMap.insert src dst })
def addTranslatedMVar (src dst: MVarId) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with mvarMap := state.mvarMap.insert src dst })

def saveFVarMap : MetaTranslateM FVarMap := do
  return (← get).fvarMap
def restoreFVarMap (map: FVarMap) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := map })
def resetFVarMap : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := {} })

mutual
private partial def translateLevel (srcLevel: Level) : MetaTranslateM Level := do
  let sourceMCtx ← getSourceMCtx
  let (_, level) := instantiateLevelMVarsImp sourceMCtx srcLevel
  match level with
  | .zero => return .zero
  | .succ inner => do
    let inner' ← translateLevel inner
    return .succ inner'
  | .max l1 l2 => do
    let l1' ← translateLevel l1
    let l2' ← translateLevel l2
    return .max l1' l2'
  | .imax l1 l2 => do
    let l1' ← translateLevel l1
    let l2' ← translateLevel l2
    return .imax l1' l2'
  | .param p => return .param p
  | .mvar _ =>
    Meta.mkFreshLevelMVar
private partial def translateExpr (srcExpr: Expr) : MetaTranslateM Expr := do
  let sourceMCtx ← getSourceMCtx
  -- We want to create as few mvars as possible
  let (srcExpr, _) := instantiateMVarsCore (mctx := sourceMCtx) srcExpr
  trace[Pantograph.Frontend.MetaTranslate] "Transform src: {srcExpr}"
  let result ← Core.transform srcExpr λ e => do
    let state ← get
    match e with
    | .fvar fvarId =>
      let .some fvarId' := state.fvarMap[fvarId]? | panic! s!"FVar id not registered: {fvarId.name}"
      -- Delegating this to `Meta.check` later
      --assert! (← getLCtx).contains fvarId'
      return .done $ .fvar fvarId'
    | .mvar mvarId => do
      -- Must not be assigned
      assert! !(sourceMCtx.eAssignment.contains mvarId)
      match state.mvarMap[mvarId]? with
      | .some mvarId' => do
        return .done $ .mvar mvarId'
      | .none => do
        -- Entering another LCtx, must save the current one
        let fvarMap ← saveFVarMap
        let mvarId' ← translateMVarId mvarId
        restoreFVarMap fvarMap
        return .done $ .mvar mvarId'
    | .sort level => do
      let level' ← translateLevel level
      return .done $ .sort level'
    | _ => return .continue
  Meta.check result
  return result

partial def translateLocalInstance (srcInstance: LocalInstance) : MetaTranslateM LocalInstance := do
  return {
    className := srcInstance.className,
    fvar := ← translateExpr srcInstance.fvar
  }
partial def translateLocalDecl (srcLocalDecl: LocalDecl) : MetaTranslateM LocalDecl := do
  let fvarId ← mkFreshFVarId
  addTranslatedFVar srcLocalDecl.fvarId fvarId
  match srcLocalDecl with
  | .cdecl index _ userName type bi kind => do
    trace[Pantograph.Frontend.MetaTranslate] "[CD] {userName} {toString type}"
    return .cdecl index fvarId userName (← translateExpr type) bi kind
  | .ldecl index _ userName type value nonDep kind => do
    trace[Pantograph.Frontend.MetaTranslate] "[LD] {toString type} := {toString value}"
    return .ldecl index fvarId userName (← translateExpr type) (← translateExpr value) nonDep kind

partial def translateLCtx : MetaTranslateM LocalContext := do
  resetFVarMap
  let lctx ← MonadLCtx.getLCtx
  assert! lctx.isEmpty
  (← getSourceLCtx).foldlM (λ lctx srcLocalDecl => do
    let localDecl ← Meta.withLCtx' lctx do
      translateLocalDecl srcLocalDecl
    pure $ lctx.addDecl localDecl
  ) lctx

partial def translateMVarId (srcMVarId: MVarId) : MetaTranslateM MVarId := do
  if let .some mvarId' := (← get).mvarMap[srcMVarId]? then
    trace[Pantograph.Frontend.MetaTranslate] "Existing mvar id {srcMVarId.name} → {mvarId'.name}"
    return mvarId'
  let mvarId' ← Meta.withLCtx .empty #[] do
    let srcDecl := (← getSourceMCtx).findDecl? srcMVarId |>.get!
    withTheReader Context (λ ctx => { ctx with sourceLCtx := srcDecl.lctx }) do
      let lctx' ← translateLCtx
      let localInstances' ← srcDecl.localInstances.mapM translateLocalInstance
      Meta.withLCtx lctx' localInstances' do
        let target' ← translateExpr srcDecl.type
        let mvar' ← Meta.mkFreshExprMVar target' srcDecl.kind srcDecl.userName
        let mvarId' := mvar'.mvarId!
        if let .some { fvars, mvarIdPending }:= (← getSourceMCtx).getDelayedMVarAssignmentExp srcMVarId then
          -- Map the fvars in the pending context.
          let mvarIdPending' ← translateMVarId mvarIdPending
          let fvars' ← mvarIdPending'.withContext $ fvars.mapM translateExpr
          assignDelayedMVar mvarId' fvars' mvarIdPending'
        pure mvarId'
  trace[Pantograph.Frontend.MetaTranslate] "Translated {srcMVarId.name} → {mvarId'.name}"
  addTranslatedMVar srcMVarId mvarId'
  return mvarId'
end

def translateMVarFromTermInfo (termInfo : Elab.TermInfo) (context? : Option Elab.ContextInfo)
    : MetaTranslateM MVarId := do
  withTheReader Context (λ ctx => { ctx with
    sourceMCtx := context?.map (·.mctx) |>.getD {},
    sourceLCtx := termInfo.lctx,
  }) do
    let type := termInfo.expectedType?.get!
    let lctx' ← translateLCtx
    let mvar ← Meta.withLCtx lctx' #[] do
      Meta.withLocalInstances (lctx'.decls.toList.filterMap id) do
      let type' ← translateExpr type
      trace[Pantograph.Frontend.MetaTranslate] "Translating from term info {← Meta.ppExpr type'}"
      Meta.mkFreshExprSyntheticOpaqueMVar type'
    return mvar.mvarId!


def translateMVarFromTacticInfoBefore (tacticInfo : Elab.TacticInfo) (_context? : Option Elab.ContextInfo)
    : MetaTranslateM (List MVarId) := do
  withTheReader Context (λ ctx => { ctx with sourceMCtx := tacticInfo.mctxBefore }) do
    tacticInfo.goalsBefore.mapM translateMVarId


end MetaTranslate

export MetaTranslate (MetaTranslateM)

initialize
  registerTraceClass `Pantograph.Frontend.MetaTranslate

end Pantograph.Frontend
