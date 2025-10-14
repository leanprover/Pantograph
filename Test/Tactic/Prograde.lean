import Pantograph.Tactic.Prograde
import Test.Common

open Lean

namespace Pantograph.Test.Tactic.Prograde

def test_define : TestT Elab.TermElabM Unit := do
  let expr := "forall (p q : Prop) (h: p), And (Or p q) (Or p q)"
  let expr ← parseSentence expr
  Meta.forallTelescope expr $ λ _ body => do
    let e ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "Or.inl h")
      (fileName := ← getFileName) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let target: Expr := mkAnd
      (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
      (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
    let h := .fvar ⟨uniq 8⟩
    addTest $ LSpec.test "goals before" ((← toCondensedGoal goal.mvarId!).devolatilize == {
      context := #[
        cdeclOf `p (.sort 0),
        cdeclOf `q (.sort 0),
        cdeclOf `h h
      ],
      target,
    })
    let tactic := Tactic.evalDefine `h2 e
    let m := .mvar ⟨uniq 13⟩
    let [newGoal] ← runTacticOnMVar tactic goal.mvarId! | panic! "Incorrect goal number"
    addTest $ LSpec.test "goals after" ((← toCondensedGoal newGoal).devolatilize == {
      context := #[
        cdeclOf `p (.sort 0),
        cdeclOf `q (.sort 0),
        cdeclOf `h h,
        {
          userName := `h2,
          type := mkOr h m,
          value? := .some $ mkApp3 (mkConst `Or.inl) h m (.fvar ⟨uniq 10⟩)
        }
      ],
      target,
    })
    let .some e ← getExprMVarAssignment? goal.mvarId! | panic! "Tactic must assign"
    addTest $ LSpec.test "assign" e.isLet

def test_define_proof : TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro p q h"
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq tactic ((← state1.serializeGoals).map (·.devolatilize))
    #[buildGoal [(`p, "Prop"), (`q, "Prop"), (`h, "p")] "(p ∨ q) ∨ p ∨ q"]

  let expr := "Or.inl (Or.inl h)"
  let state2 ← match ← state1.tryAssign (state1.get! 0) (expr := expr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[])

  let evalBind := `y
  let evalExpr := "Or.inl h"
  let state2 ← match ← state1.tryDefine (state1.get! 0) (binderName := evalBind) (expr := evalExpr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq s!"eval {evalBind} := {evalExpr}" ((← state2.serializeGoals).map (·.devolatilize))
    #[{
      target := { pp? := .some  "(p ∨ q) ∨ p ∨ q"},
      vars := #[
        { userName := `p, type? := .some { pp? := .some "Prop" } },
        { userName := `q, type? := .some { pp? := .some "Prop" } },
        { userName := `h, type? := .some { pp? := .some "p" } },
        { userName := `y,
          type? := .some { pp? := .some "p ∨ ?m.9" },
          value? := .some { pp? := .some "Or.inl h" },
        }
      ]
    }]

  let expr := "Or.inl y"
  let state3 ← match ← state2.tryAssign (state2.get! 0) (expr := expr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state3.serializeGoals).map (·.devolatilize) =
    #[])

  addTest $ LSpec.check "(3 root)" state3.rootExpr?.isSome

def fun_define_root_expr: ∀ (p: Prop), PProd (Nat → p) Unit → p := by
  intro p x
  apply x.fst
  exact 5

def test_define_root_expr : TestT Elab.TermElabM Unit := do
  --let rootExpr ← parseSentence "Nat"
  --let state0 ← GoalState.create rootExpr
  --let .success state1 _ ← state0.tacticOn (goalId := 0) "exact 5" | addTest $ assertUnreachable "exact 5"
  --let .some rootExpr := state1.rootExpr? | addTest $ assertUnreachable "Root expr"
  --addTest $ LSpec.check "root" ((toString $ ← Meta.ppExpr rootExpr) = "5")
  let rootExpr ← parseSentence "∀ (p: Prop), PProd (Nat → p) Unit → p"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro p x"
  let .success state1 _ ← state0.tacticOn (goalId := 0) tactic | addTest $ assertUnreachable tactic
  let binderName := `binder
  let value := "x.fst"
  let expr ← state1.goals[0]!.withContext $ strToTermSyntax value
  let tacticM := Tactic.evalDefine binderName expr
  let .success state2 _ ← state1.tryTacticM (state1.get! 0) tacticM | addTest $ assertUnreachable s!"define {binderName} := {value}"
  let tactic := s!"apply {binderName}"
  let .success state3 _ ← state2.tacticOn (goalId := 0) tactic | addTest $ assertUnreachable tactic
  let tactic := s!"exact 5"
  let .success state4 _ ← state3.tacticOn (goalId := 0) tactic | addTest $ assertUnreachable tactic
  let .some rootExpr := state4.rootExpr? | addTest $ assertUnreachable "Root expr"
  addTest $ LSpec.check "root" ((toString $ ← Meta.ppExpr rootExpr) = "fun p x =>\n  let binder := x.fst;\n  binder 5")

def test_have_proof : TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro p q h"
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq tactic ((← state1.serializeGoals).map (·.devolatilize))
    #[buildGoal [(`p, "Prop"), (`q, "Prop"), (`h, "p")] "(p ∨ q) ∨ p ∨ q"]

  let expr := "Or.inl (Or.inl h)"
  let state2 ← match ← state1.tryAssign (state1.get! 0) (expr := expr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[])

  let haveBind := `y
  let haveType := "p ∨ q"
  let state2 ← match ← state1.tryHave (state1.get! 0) (binderName := haveBind) (type := haveType) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq s!"have {haveBind}: {haveType}" ((← state2.serializeGoals).map (·.devolatilize))
    #[
      buildGoal [(`p, "Prop"), (`q, "Prop"), (`h, "p")] "p ∨ q",
      buildGoal [(`p, "Prop"), (`q, "Prop"), (`h, "p"), (`y, "p ∨ q")] "(p ∨ q) ∨ p ∨ q"
    ]

  let expr := "Or.inl h"
  let state3 ← match ← state2.tryAssign (state2.get! 0) (expr := expr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq s!":= {expr}" ((← state3.serializeGoals).map (·.devolatilize)) #[]

  let state2b ← match state3.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let expr := "Or.inl y"
  let state4 ← match ← state2b.tryAssign (state2b.get! 0) (expr := expr) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkEq s!":= {expr}" ((← state4.serializeGoals).map (·.devolatilize)) #[]

  let .some rootExpr := state4.rootExpr? | fail "Root expr"
  checkEq "root" (toString $ ← Meta.ppExpr rootExpr) "fun p q h y => Or.inl y"

def test_let (specialized: Bool): TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro a p h"
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[{
      target := { pp? := .some mainTarget },
      vars := interiorVars,
    }])

  let letType := "Nat"
  let expr := s!"let b: {letType} := _; _"
  let result2 ← match specialized with
    | true => state1.tryLet (state1.get! 0) (binderName := `b) (type := letType)
    | false => state1.tryAssign (state1.get! 0) (expr := expr)
  let state2 ← match result2 with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let serializedState2 ← state2.serializeGoals
  let letBindName := if specialized then `b else `_1
  checkEq expr (serializedState2.map (·.devolatilize))
    #[{
      target := { pp? := .some letType },
      vars := interiorVars,
      userName? := .some letBindName
    },
    {
      target := { pp? := .some mainTarget },
      vars := interiorVars ++ #[{
        userName := `b,
        type? := .some { pp? := .some letType },
        value? := .some { pp? := .some s!"?{letBindName}" },
      }],
      userName? := if specialized then .none else .some `_2,
    }]

  let tactic := "exact 1"
  let state3 ← match ← state2.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3.serializeGoals).map (·.devolatilize) = #[])

  let state3r ← match state3.continue state2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  checkEq "(continue)" ((← state3r.serializeGoals).map (·.devolatilize))
    #[{
      target := { pp? := .some mainTarget },
      vars := interiorVars ++ #[{
        userName := `b,
        type? := .some { pp? := .some "Nat" },
        value? := .some { pp? := .some "1" },
      }],
      userName? := if specialized then .none else `_2,
    }]

  let tactic := "exact h"
  match ← state3r.tacticOn (goalId := 0) (tactic := tactic) with
  | .failure #[message] =>
    checkEq tactic
      (← message.toString)
      s!"{← getFileName}:0:0: error: Type mismatch\n  h\nhas type\n  a\nbut is expected to have type\n  {mainTarget}\n"
  | other => do
    fail s!"Should be a failure: {other.toString}"

  let tactic := "exact Or.inl (Or.inl h)"
  let state4 ← match ← state3r.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(4 root)" state4.rootExpr?.isSome
  where
  mainTarget := "(a ∨ p) ∨ a ∨ p"
  interiorVars: Array Protocol.Variable := #[
      { userName := `a, type? := .some { pp? := .some "Prop" }, },
      { userName := `p, type? := .some { pp? := .some "Prop" }, },
      { userName := `h, type? := .some { pp? := .some "a" }, }
    ]

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("define", test_define),
    ("define proof", test_define_proof),
    ("define root expr", test_define_root_expr),
    ("have proof", test_have_proof),
    ("let via assign", test_let false),
    ("let via tryLet", test_let true),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))
