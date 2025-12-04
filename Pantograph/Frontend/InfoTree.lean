/- Adapted from lean-training-data -/
import Lean.Elab.InfoTree
import Lean.Elab.Util
import Lean.Parser.Term
import Lean.PrettyPrinter

open Lean

namespace Lean.Elab

private def elaboratorToString : Name → String
  | .anonymous => ""
  | n => s!"⟨{n}⟩ "

/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
protected def Info.stx? : Info → Option Syntax
  | .ofTacticInfo         info => info.stx
  | .ofTermInfo           info => info.stx
  | .ofCommandInfo        info => info.stx
  | .ofMacroExpansionInfo info => info.stx
  | .ofOptionInfo         info => info.stx
  | .ofFieldInfo          info => info.stx
  | .ofCompletionInfo     info => info.stx
  | .ofUserWidgetInfo     info => info.stx
  | .ofCustomInfo         info => info.stx
  | .ofFVarAliasInfo      _    => none
  | .ofDocInfo            info    => info.stx
  | .ofDocElabInfo        info    => info.stx
  | .ofFieldRedeclInfo    info => info.stx
  | .ofChoiceInfo         info => info.stx
  | .ofPartialTermInfo    info => info.stx
  | .ofDelabTermInfo      info => info.stx
  | .ofErrorNameInfo      info => info.stx
/-- Is the `Syntax` for this `Lean.Elab.Info` original, or synthetic? -/
protected def Info.isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false

def ContextInfo.ppExpr (ctx : ContextInfo) (lctx : LocalContext) (e : Expr) : IO Format :=
  ctx.runMetaM lctx (do Meta.ppExpr (← instantiateMVars e))

def CommandInfo.toString (info : CommandInfo) (ctx : ContextInfo) : IO String := do
  let stx := (← ctx.ppSyntax {} info.stx).pretty
  return s!"{elaboratorToString info.elaborator}\n{stx}"

def TermInfo.toString (info : TermInfo) (ctx : ContextInfo) : IO String := do
  let stx := (← ctx.ppSyntax info.lctx info.stx).pretty
  let expectedType := (← info.expectedType?.mapM fun ty => do
    pure s!": {(← ctx.ppExpr info.lctx ty).pretty}").getD ""
  let expr := (← ctx.ppExpr info.lctx info.expr).pretty
  return s!"{elaboratorToString info.elaborator}{expr}{expectedType}\n{stx}"

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def TacticInfo.name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none
/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def TacticInfo.isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true
def TacticInfo.pp (info : TacticInfo) (ctx : ContextInfo) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"
def TacticInfo.toString (i : TacticInfo) (ctx : ContextInfo) : IO String := do
  let name := i.name?
  let stx := Format.pretty (← i.pp ctx)
  return s!"{name}\n{stx}"

/--
Keep `.node` nodes and `.hole` nodes satisfying predicates.

Returns a `List InfoTree`, although in most situations this will be a singleton.
-/
partial def InfoTree.filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
    InfoTree → List InfoTree
  | .context ctx tree => tree.filter p m |>.map (.context ctx)
  | .node info children =>
    if p info then
      [.node info (children.toList.map (filter p m)).flatten.toPArray']
    else
      (children.toList.map (filter p m)).flatten
  | .hole mvar => if m mvar then [.hole mvar] else []

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def InfoTree.findAllInfo
    (t : InfoTree)
    (context?: Option Elab.ContextInfo)
    (haltOnMatch : Bool := false)
    (pred : Elab.Info → Bool)
    : List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? context?) haltOnMatch pred
  | .node i children  =>
    let head := if pred i then [(i, context?, children)] else []
    let tail := if haltOnMatch ∧ !head.isEmpty then [] else children.toList.flatMap (fun t => findAllInfo t context? haltOnMatch pred)
    head ++ tail
  | _ => []

/-- Monadic analogue of `findAllInfo`, but predicate controls whether to recurse. -/
partial def InfoTree.findAllInfoM [Monad m]
    (t : InfoTree)
    (context?: Option Elab.ContextInfo)
    (pred : Elab.Info → Option Elab.ContextInfo → m (Bool × Bool))
    : m (List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree)) := do
  match t with
  | .context inner t => t.findAllInfoM (inner.mergeIntoOuter? context?) pred
  | .node i children  =>
    let (flagCollect, flagRecurse) ← pred i context?
    let head := if flagCollect then [(i, context?, children)] else []
    let tail := if ¬ flagRecurse then pure [] else children.toList.mapM (fun t => t.findAllInfoM context? pred)
    return head ++ (← tail).flatten
  | _ => return []

structure InfoTreePrintOptions where
  prettyPrint : Bool := true

@[export pantograph_infotree_to_string_m]
partial def InfoTree.toString (t : InfoTree) (ctx?: Option Elab.ContextInfo := .none) (options : InfoTreePrintOptions := {}) (indent : Nat := 0)
  : IO String := do
  let space := String.join $ List.replicate indent "  "
  match t with
  | .context ctx t =>
    let s ← t.toString (ctx.mergeIntoOuter? ctx?)
    pure s!"[context] {s}"
  | .node info children =>
    if let some ctx := ctx? then
      let node : String ← match info with
      | .ofTermInfo { stx, expr, .. } =>
        pure s!"[term] {stx.prettyPrint} ➡ {expr}"
      | .ofCommandInfo info =>
        let head := match info.stx.getArg 1 with
          | .missing => ""
          | other => s!" {other.getKind.toString}"
        let s := if options.prettyPrint then
            info.stx.prettyPrint
          else
            s!"{info.stx}"
        pure s!"[command/{info.stx.getKind.toString}{head}] {s}"
      | .ofTacticInfo  info => pure s!"[tactic] {info.stx.prettyPrint}"
      | .ofMacroExpansionInfo _ => pure "[macro_exp]"
      | .ofOptionInfo info => pure s!"[option] {info.stx.prettyPrint}"
      | .ofFieldInfo _ => pure "[field]"
      | .ofCompletionInfo info => pure s!"[completion] {info.stx.prettyPrint}"
      | .ofUserWidgetInfo _ => pure "[user_widget]"
      | .ofCustomInfo _ => pure "[custom]"
      | .ofFVarAliasInfo _ => pure "[fvar_alias]"
      | .ofFieldRedeclInfo _ => pure "[field_redecl]"
      | .ofDocElabInfo _ => pure "[doc_elab]"
      | .ofDocInfo _ => pure "[doc]"
      | .ofChoiceInfo _ => pure "[choice]"
      | .ofPartialTermInfo  _ => pure "[partial_term]"
      | .ofDelabTermInfo _ => pure "[delab_term]"
      | .ofErrorNameInfo _ => pure "[error_name]"
      let children ← children.toList.mapM λ t' => do
        t'.toString ctx options (indent := indent + 1)
      let children := String.join children
      return s!"{space}{node}\n{children}"
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
      let payload := (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty
      return s!"{space}[hole] {payload}"
    else throw <| IO.userError "No `ContextInfo` available."

end Lean.Elab
