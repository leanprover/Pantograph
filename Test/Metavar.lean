import LSpec
import Pantograph.Goal
import Pantograph.Delate
import Test.Common
import Lean

namespace Pantograph.Test.Metavar
open Pantograph
open Lean

abbrev TestM := TestT $ ReaderT Protocol.Options Elab.TermElabM

-- Tests that all delay assigned mvars are instantiated
def test_instantiate_mvar: TestM Unit := do
  let env ← Lean.MonadEnv.getEnv
  let value := "@Nat.le_trans 2 2 5 (@of_eq_true (@LE.le Nat instLENat 2 2) (@eq_true (@LE.le Nat instLENat 2 2) (@Nat.le_refl 2))) (@of_eq_true (@LE.le Nat instLENat 2 5) (@eq_true_of_decide (@LE.le Nat instLENat 2 5) (@Nat.decLe 2 5) (@Eq.refl Bool Bool.true)))"
  let syn ← match parseTerm env value with
    | .ok s => pure $ s
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let expr ← match ← elabTerm syn with
    | .ok expr => pure $ expr
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let t ← Lean.Meta.inferType expr
  checkEq "typing" (toString (← serializeExpressionSexp t))
    "((:c LE.le) (:c Nat) (:c instLENat) ((:c OfNat.ofNat) (:mv _uniq.2) (:lit 2) (:mv _uniq.3)) ((:c OfNat.ofNat) (:mv _uniq.15) (:lit 5) (:mv _uniq.16)))"
  return ()

def startProof (expr: String): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  let syn? := parseTerm env expr
  addTest $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
  match syn? with
  | .error error =>
    IO.println error
    return Option.none
  | .ok syn =>
    let expr? ← elabType syn
    addTest $ LSpec.check s!"Elaborating" expr?.isOk
    match expr? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok expr =>
      let goal ← GoalState.create (expr := expr)
      return Option.some goal

def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none): Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
    })).toArray
  }
def proofRunner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context ← createCoreContext #[]
  let metaM := termElabM.run' (ctx := defaultElabContext)
  let coreM := metaM.run'
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok (_, a) =>
    return a

/-- M-coupled goals -/
def test_m_couple: TestM Unit := do
  let state? ← startProof "(2: Nat) ≤ 5"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := "apply Nat.le_trans") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.le_trans" ((← state1.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ ?m", .some "?m ≤ 5", .some "Nat"])
  checkTrue "(1 root)" $ ¬ state1.isSolved
  -- Set m to 3
  let state2 ← match ← state1.tacticOn (goalId := 2) (tactic := "exact 3") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkTrue "(1b root)" $ ¬ state2.isSolved
  let state1b ← match state2.continue state1 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "exact 3" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ 3", .some "3 ≤ 5"])
  checkTrue "(2 root)" $ ¬ state1b.isSolved

def test_m_couple_simp: TestM Unit := do
  let state? ← startProof "(2: Nat) ≤ 5"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := "apply Nat.le_trans") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let serializedState1 ← state1.serializeGoals (options := { ← read with printDependentMVars := true })
  addTest $ LSpec.check "apply Nat.le_trans" (serializedState1.map (·.target.pp?) =
    #[.some "2 ≤ ?m", .some "?m ≤ 5", .some "Nat"])
  let n := state1.goals[2]!
  addTest $ LSpec.check "(metavariables)" (serializedState1.map (·.target.dependentMVars?.get!) =
    #[#[toString n.name], #[toString n.name], #[]])

  let state2 ← match ← state1.tacticOn (goalId := 2) (tactic := "exact 2") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  checkTrue "(1b root)" $ ¬ state2.isSolved
  let state1b ← match state2.continue state1 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "exact 2" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ 2", .some "2 ≤ 5"])
  checkTrue "(2 root)" $ ¬ state1b.isSolved
  let state3 ← match ← state1b.tacticOn (goalId := 0) (tactic := "simp") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state4 ← match state3.continue state1b with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  let state5 ← match ← state4.tacticOn (goalId := 0) (tactic := "simp") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  state5.restoreMetaM
  let root ← match state5.rootExpr? with
    | .some e => pure e
    | .none =>
      addTest $ assertUnreachable "(5 root)"
      return ()
  let rootStr: String := toString (← Lean.Meta.ppExpr root)
  --checkEq "(5 root)" rootStr "Nat.le_trans (of_eq_true (_proof_4✝ 2)) (of_eq_true (eq_true_of_decide (Eq.refl true)))"
  let unfoldedRoot ←  unfoldAuxLemmas root
  checkEq "(5 root)" (toString (← Lean.Meta.ppExpr unfoldedRoot))
    "Nat.le_trans (of_eq_true (eq_true (Nat.le_refl 2))) (of_eq_true (eq_true_of_decide (Eq.refl true)))"
  return ()

def test_proposition_generation: TestM Unit := do
  let state? ← startProof "Σ' p:Prop, p"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := "apply PSigma.mk") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply PSigma.mk" ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      buildGoal [] "?fst" (userName? := .some "snd"),
      buildGoal [] "Prop" (userName? := .some "fst")
      ])
  if let #[goal1, goal2] := ← state1.serializeGoals (options := { (← read) with printExprAST := true }) then
    addTest $ LSpec.test "(1 reference)" (goal1.target.sexp? = .some s!"(:mv {goal2.name})")
  checkTrue "(1 root)" $ ¬ state1.isSolved

  let state2 ← match ← state1.tryAssign (state1.get! 0) (expr := "λ (x: Nat) => _") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check ":= λ (x: Nat), _" ((← state2.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "?m.30 x"])
  checkTrue "(2 root)" $ ¬ state2.isSolved

  let assign := "Eq.refl x"
  let state3 ← match ← state2.tryAssign (state2.get! 0) (expr := assign) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {assign}" ((← state3.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[])

  checkTrue "(3 root)" state3.isSolved
  return ()

def test_partial_continuation: TestM Unit := do
  let state? ← startProof "(2: Nat) ≤ 5"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := "apply Nat.le_trans") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.le_trans" ((← state1.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ ?m", .some "?m ≤ 5", .some "Nat"])

  let state2 ← match ← state1.tacticOn (goalId := 2) (tactic := "apply Nat.succ") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.succ" ((← state2.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "Nat"])

  -- Execute a partial continuation
  let coupled_goals := state1.goals ++ state2.goals
  let state1b ← match state2.resume (goals := coupled_goals) with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "(continue 1)" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ Nat.succ ?m", .some "Nat.succ ?m ≤ 5", .some "Nat"])
  checkTrue "(2 root)" state1b.rootExpr?.get!.hasExprMVar

  -- Roundtrip
  --let coupled_goals := coupled_goals.map (λ g =>
  --  { name := str_to_name $ serializeName g.name (sanitize := false)})
  let coupled_goals := coupled_goals.map (·.name.toString)
  let coupled_goals := coupled_goals.map ({ name := ·.toName })
  let state1b ← match state2.resume (goals := coupled_goals) with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  checkEq "(continue 2)" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?))
    #[.some "2 ≤ Nat.succ ?m", .some "Nat.succ ?m ≤ 5", .some "Nat"]
  checkTrue "(2 root)" state1b.rootExpr?.get!.hasExprMVar

  -- Continuation should fail if the state does not exist:
  match state0.resume coupled_goals with
  | .error error => checkEq "(continuation failure message)" error "Goals [_uniq.45, _uniq.46, _uniq.43, _uniq.52] are not in scope"
  | .ok _ => fail "(continuation should fail)"
  -- Continuation should fail if some goals have not been solved
  match state2.continue state1 with
  | .error error => checkEq "(continuation failure message)" error "Target state has unresolved goals"
  | .ok _ => fail "(continuation should fail)"
  return ()

def test_branch_unification : TestM Unit := do
  let .ok rootTarget ← elabTerm (← `(term|∀ (p q : Prop), p → p ∧ (p ∨ q))) .none | unreachable!
  let state ← GoalState.create rootTarget
  let .success state _  ← state.tacticOn' 0 (← `(tactic|intro p q h)) | fail "intro failed to run"
  let .success state _  ← state.tacticOn' 0 (← `(tactic|apply And.intro)) | fail "apply And.intro failed to run"
  let .success state1 _  ← state.tacticOn' 0 (← `(tactic|exact h)) | fail "exact h failed to run"
  let .success state2 _  ← state.tacticOn' 1 (← `(tactic|apply Or.inl)) | fail "apply Or.inl failed to run"
  checkEq "(state2 goals)" state2.goals.length 1
  let state' ← state2.replay state state1
  checkEq "(state' goals)" state'.goals.length 1
  let .success stateT _ ← state'.tacticOn' 0 (← `(tactic|exact h)) | fail "exact h failed to run"
  let .some root := stateT.rootExpr? | fail "Root expression must exist"
  checkEq "(root)" (toString $ ← Meta.ppExpr root) "fun p q h => ⟨h, Or.inl h⟩"

/-- Test generating multiple aux decls -/
def test_restore_ngen : TestM Unit := do
  let .ok rootTarget ← elabTerm (← `(term|(2: Nat) ≤ 3 ∧ (3: Nat) ≤ 5)) .none | unreachable!
  let auxDeclNGen := (← getThe Core.State).auxDeclNGen
  let state ← GoalState.create rootTarget
  let .success state _  ← state.tacticOn' 0 (← `(tactic|apply And.intro)) | fail "apply And.intro failed to run"
  let goal := state.goals[0]!
  let type ← goal.withContext do
    let .ok type ← elabTerm (← `(term|(2: Nat) ≤ 3)) (.some $ .sort 0) | unreachable!
    instantiateMVars type
  modifyThe Core.State ({ · with auxDeclNGen })
  let .success state _  ← state.tryTacticM .unfocus (Tactic.assignWithAuxLemma type) | fail "left"

  state.restoreMetaM
  let goal := state.goals[0]!
  let type ← goal.withContext do
    let .ok type ← elabTerm (← `(term|(3: Nat) ≤ 5)) (.some $ .sort 0) | unreachable!
    instantiateMVars type
  modifyThe Core.State ({ · with auxDeclNGen })
  let .success state _  ← state.tryTacticM .unfocus (Tactic.assignWithAuxLemma type) | fail "right"
  checkTrue "root" state.isSolved
  let .some root := state.rootExpr? | fail "Root expression must exist"
  checkTrue "root has aux lemma" $ root.getUsedConstants.any isAuxLemma
  checkEq "(root expression)" (toString $ ← Meta.ppExpr root) "⟨_proof_1, _proof_2⟩"

/-- Test merger when both branches have new aux lemmas -/
def test_replay_environment : TestM Unit := do
  let .ok rootTarget ← elabTerm (← `(term|(2: Nat) ≤ 3 ∧ (3: Nat) ≤ 5)) .none | unreachable!
  let auxDeclNGen := (← getThe Core.State).auxDeclNGen
  let state ← GoalState.create rootTarget
  let .success state _  ← state.tacticOn' 0 (← `(tactic|apply And.intro)) | fail "apply And.intro failed to run"
  let goal := state.goals[0]!
  let type ← goal.withContext do
    let .ok type ← elabTerm (← `(term|(2: Nat) ≤ 3)) (.some $ .sort 0) | unreachable!
    instantiateMVars type
  modifyThe Core.State ({ · with auxDeclNGen })
  let .success state1 _  ← state.tryTacticM goal (Tactic.assignWithAuxLemma type) | fail "left"

  state.restoreMetaM
  let goal := state.goals[1]!
  let type ← goal.withContext do
    let .ok type ← elabTerm (← `(term|(3: Nat) ≤ 5)) (.some $ .sort 0) | unreachable!
    instantiateMVars type
  modifyThe Core.State ({ · with auxDeclNGen })
  let .success state2 _  ← state.tryTacticM goal (Tactic.assignWithAuxLemma type) | fail "right"
  checkEq "(state1 goals)" state1.goals.length 0
  checkEq "(state2 goals)" state2.goals.length 0

  let stateT ← state2.replay state state1
  checkEq "(stateT goals)" stateT.goals.length 0
  let .some root := stateT.rootExpr? | fail "Root expression must exist"
  Meta.check root
  checkTrue "root has aux lemma" $ root.getUsedConstants.any isAuxLemma
  checkEq "(root)" (toString $ ← Meta.ppExpr root) "⟨_proof_2, _proof_1⟩"
  let root ← unfoldAuxLemmas root
  checkEq "(root unfold)" (toString $ ← Meta.ppExpr root) "⟨sorry, sorry⟩"

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("Instantiate", test_instantiate_mvar),
    ("2 < 5", test_m_couple),
    ("2 < 5", test_m_couple_simp),
    ("Proposition Generation", test_proposition_generation),
    ("Partial Continuation", test_partial_continuation),
    ("Branch Unification", test_branch_unification),
    ("Restore NGen", test_restore_ngen),
    ("Replay Environment", test_replay_environment),
  ]
  tests.map (fun (name, test) => (name, proofRunner env test))
