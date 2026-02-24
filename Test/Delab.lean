import Pantograph.Delab
import Test.Common

open Lean Pantograph

namespace Pantograph.Test.Delab

deriving instance Repr, DecidableEq for Protocol.BoundExpression

def test_serializeName: LSpec.TestSeq :=
  let quote := "\""
  let escape := "\\"
  LSpec.test "a.b.1" (serializeName (Name.num (.str (.str .anonymous "a") "b") 1) = "a.b.1") ++
  LSpec.test "seg.«a.b»" (serializeName (Name.str (.str .anonymous "seg") "a.b") = s!"{quote}seg.«a.b»{quote}") ++
  -- Pathological test case
  LSpec.test s!"«̈{escape}{quote}»" (serializeName (Name.str .anonymous s!"{escape}{quote}") = s!"{quote}«{escape}{quote}»{quote}")

def test_expr_to_binder (env: Environment): IO LSpec.TestSeq := do
  let entries: List (Name × Protocol.BoundExpression) := [
    ("Nat.add_comm".toName, { binders := #[("n", "Nat"), ("m", "Nat")], target := "n + m = m + n" }),
    ("Nat.le_of_succ_le".toName, { binders := #[("n", "Nat"), ("m", "Nat"), ("h", "n.succ ≤ m")], target := "n ≤ m" })
  ]
  runCoreMSeq env $ entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := env.find? symbol |>.get! |>.type
    let test := LSpec.check symbol.toString ((← typeExprToBound expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done |>.run'

def test_sexp_of_symbol (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × String) := [
    -- This one contains unhygienic variable names which must be suppressed
    ("Nat.add", "(:forall a (:c Nat) (:forall a (:c Nat) (:c Nat)))"),
    -- These ones are normal and easy
    ("Nat.add_one", "(:forall n (:c Nat) ((:c Eq) (:c Nat) ((:c HAdd.hAdd) (:c Nat) (:c Nat) (:c Nat) ((:c instHAdd) (:c Nat) (:c instAddNat)) 0 ((:c OfNat.ofNat) (:c Nat) (:lit 1) ((:c instOfNatNat) (:lit 1)))) ((:c Nat.succ) 0)))"),
    ("Nat.le_of_succ_le", "(:forall n (:c Nat) (:forall m (:c Nat) (:forall h ((:c LE.le) (:c Nat) (:c instLENat) ((:c Nat.succ) 1) 0) ((:c LE.le) (:c Nat) (:c instLENat) 2 1)) :i) :i)"),
    -- Handling of higher order types
    ("Or", "(:forall a (:sort 0) (:forall b (:sort 0) (:sort 0)))"),
    ("List", "(:forall α (:sort (+ u 1)) (:sort (+ u 1)))")
  ]
  runMetaMSeq env $ entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := env.find? symbol.toName |>.get! |>.type
    let test := LSpec.check symbol ((← serializeExpressionSexp expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done

def test_sexp_of_elab (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × (List Name) × String) := [
    ("λ x: Nat × Bool => x.1", [], "(:lambda x ((:c Prod) (:c Nat) (:c Bool)) ((:c Prod.fst) (:c Nat) (:c Bool) 0))"),
    ("λ {α: Sort (u + 1)} => List α", [`u], "(:lambda α (:sort (+ u 1)) ((:c List) 0) :i)"),
    ("λ {α} => List α", [], "(:lambda α (:sort (+ (:mv _uniq.4) 1)) ((:c List) 0) :i)"),
    ("(2: Nat) <= (5: Nat)", [], "((:c LE.le) (:mv _uniq.16) (:mv _uniq.17) ((:c OfNat.ofNat) (:mv _uniq.4) (:lit 2) (:mv _uniq.5)) ((:c OfNat.ofNat) (:mv _uniq.11) (:lit 5) (:mv _uniq.12)))"),
  ]
  entries.foldlM (λ suites (source, levels, target) =>
    let termElabM := do
      let env ← MonadEnv.getEnv
      let s ← match parseTerm env source with
        | .ok s => pure s
        | .error e => return parseFailure e
      let expr ← match (← elabTerm s) with
        | .ok expr => pure expr
        | .error e => return elabFailure e
      return LSpec.check source ((← serializeExpressionSexp expr) = target)
    let metaM := (Elab.Term.withLevelNames levels termElabM).run' (ctx := defaultElabContext)
    return LSpec.TestSeq.append suites (← runMetaMSeq env metaM))
    LSpec.TestSeq.done

def test_sexp_of_expr (env: Environment): IO LSpec.TestSeq := do
  let entries: List (Expr × String) := [
    (.lam `p (.sort .zero)
        (.lam `q (.sort .zero)
          (.lam `k (mkApp2 (.const `And []) (.bvar 1) (.bvar 0))
            (.proj `And 1 (.bvar 0))
            .default)
        .implicit)
      .implicit,
      "(:lambda p (:sort 0) (:lambda q (:sort 0) (:lambda k ((:c And) 1 0) ((:c And.right) _ _ 0)) :i) :i)"
    ),
  ]
  let termElabM: Elab.TermElabM LSpec.TestSeq := entries.foldlM (λ suites (expr, target) => do
    let env ← MonadEnv.getEnv
    let testCaseName := target.take 10
    let test := LSpec.check testCaseName.toString ((← serializeExpressionSexp expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  runMetaMSeq env $ termElabM.run' (ctx := defaultElabContext)

-- Instance parsing
def test_instance (env: Environment): IO LSpec.TestSeq :=
  runMetaMSeq env do
    let env ← MonadEnv.getEnv
    let source := "λ x y: Nat => HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x y"
    let s := parseTerm env source |>.toOption |>.get!
    let _expr := (← runTermElabMInMeta <| elabTerm s) |>.toOption |>.get!
    return LSpec.TestSeq.done

def test_projection_prod (env: Environment) : IO LSpec.TestSeq:= runTest do
  let struct := .app (.bvar 1) (.bvar 0)
  let expr := .proj `Prod 1 struct
  let .field projector numParams := analyzeProjection env expr |
    fail "`Prod has fields"
  checkEq "projector" projector `Prod.snd
  checkEq "numParams" numParams 2

def test_projection_exists (env: Environment) : IO LSpec.TestSeq:= runTest do
  let struct := .app (.bvar 1) (.bvar 0)
  let expr := .proj `Exists 1 struct
  let .singular recursor numParams numFields := analyzeProjection env expr |
    fail "`Exists has no projectors"
  checkEq "recursor" recursor `Exists.recOn
  checkEq "numParams" numParams 2
  checkEq "numFields" numFields 2

def test_matcher : TestT Elab.TermElabM Unit := do
  let t ← parseSentence "Nat → Nat"
  let e ← parseSentence "fun (n : Nat) => match n with | 0 => 0 | k => k" (.some t)
  let .some _ ← Meta.matchMatcherApp? e.bindingBody! | fail "Must be a matcher app"
  let e' ← instantiateAll e
  checkTrue "ok" <| ← Meta.isTypeCorrect e'

def test_intro_delay_intro : TestT Elab.TermElabM Unit := do
  let statement ← Elab.Term.elabTerm (← `(term|∀ (i : Nat), { f : Nat → Nat // ∀ (j : Nat), f i = j  })) .none
  Meta.forallTelescope statement λ _fvars target => do
  let goal := (← Meta.mkFreshExprSyntheticOpaqueMVar target).mvarId!
  let [cond, f] ← goal.applyConst `Subtype.mk | fail "Incorrect number of goals"
  let (_fBinder, fBody) ← f.intro1
  cond.withContext do
    let opt ← toDelayedMVarInvocation (.mvar f)
    checkTrue "condBody/?f" opt.isNone
    let sexp ← serializeExpressionSexp (← instantiateAll $ ← cond.getType)
    checkTrue "condBody/target" $ sexp.startsWith "(:forall j (:c Nat) ((:c Eq) (:c Nat) ((:lambda a (:c Nat) (:subst"
  let (_condBinder, condBody) ← cond.intro1
  condBody.withContext do
    let opt ← toDelayedMVarInvocation (.mvar f)
    checkTrue "condBody/?f" opt.isNone
    let opt ← toDelayedMVarInvocation (.mvar fBody)
    checkTrue "condBody/?fBody" opt.isNone
    let sexp ← serializeExpressionSexp (← instantiateAll $ ← condBody.getType)
    checkTrue "condBody/target" $ sexp.startsWith "((:c Eq) (:c Nat) ((:lambda a (:c Nat) (:subst"

def test_doubly_nested_delayed_assigned : TestT Elab.TermElabM Unit := do
  let statement ← Elab.Term.elabTerm (← `(term|∀ (i : Nat), { t : Prop // ∃ f : Nat → Nat → t, ∀ (j : Nat), f j j = f i i })) .none
  Meta.forallTelescope statement λ _fvars target => do
  let goal := (← Meta.mkFreshExprSyntheticOpaqueMVar target).mvarId!
  let [cond1, _t] ← goal.applyConst `Subtype.mk | fail "Incorrect number of goals [1]"
  let [cond2, f] ← cond1.applyConst `Exists.intro | fail "Incorrect number of goals [2]"
  let (_cond2F, cond2B) ← cond2.intro1
  let (_f1F, f1B) ← f.intro1
  let (_f12, _f2B) ← f1B.intro1
  cond2B.withContext do
    let sexp ← serializeExpressionSexp (← instantiateAll $ ← cond2B.getType)
    checkTrue "cond2B/target" $ sexp.startsWith "((:c Eq)"

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("serializeName", do pure test_serializeName),
    ("Expression binder", test_expr_to_binder env),
    ("Sexp from symbol", test_sexp_of_symbol env),
    ("Sexp from elaborated expr", test_sexp_of_elab env),
    ("Sexp from expr", test_sexp_of_expr env),
    ("Instance", test_instance env),
    ("Projection Prod", test_projection_prod env),
    ("Projection Exists", test_projection_exists env),
    ("Matcher", runTestTermElabM env test_matcher),
    ("intro delay intro", runTestTermElabM env test_intro_delay_intro),
    ("doubly_nested_delayed_assigned", runTestTermElabM env test_doubly_nested_delayed_assigned),
  ]
