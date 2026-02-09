import Pantograph.Delab
import Pantograph.Environment
import Repl
import Test.Common

import LSpec

open Lean
namespace Pantograph.Test.Environment

open Pantograph

deriving instance DecidableEq, Repr for Protocol.InductInfo
deriving instance DecidableEq, Repr for Protocol.ConstructorInfo
deriving instance DecidableEq, Repr for Protocol.RecursorRule
deriving instance DecidableEq, Repr for Protocol.RecursorInfo
deriving instance DecidableEq, Repr for Protocol.EnvInspectResult

def test_catalog (env : Environment) : IO LSpec.TestSeq := do
  let symbolsWithNum := env.constants.fold (init := #[]) (λ acc name info =>
    match (toFilteredSymbol name info).isSome && (name matches .num _ _) with
    | false => acc
    | true => acc.push name
    )
  return LSpec.check "No num symbols" (symbolsWithNum.size == 0)

def test_symbol_visibility: IO LSpec.TestSeq := do
  let entries: List (Name × Bool) := [
    ("Nat.add_comm".toName, false),
    ("foo.bla.Init.Data.List.Basic.2.1.Init.Lean.Expr._hyg.4".toName, true),
  ]
  let suite := entries.foldl (λ suites (symbol, target) =>
    let test := LSpec.check symbol.toString ((isNameInternal symbol) == target)
    LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  return suite

inductive ConstantCat where
  | induct (info: Protocol.InductInfo)
  | ctor (info: Protocol.ConstructorInfo)
  | recursor (info: Protocol.RecursorInfo)

def test_inspect (env : Environment) : IO LSpec.TestSeq := do
  let testCases: List (Name × ConstantCat) := [
    (`Or, ConstantCat.induct {
      numParams := 2,
      numIndices := 0,
      all := #[`Or],
      ctors := #[`Or.inl, `Or.inr],
    }),
    (`Except.ok, ConstantCat.ctor {
      induct := `Except,
      cidx := 1,
      numParams := 2,
      numFields := 1,
    }),
    (`Eq.rec, ConstantCat.recursor {
      all := #[`Eq],
      numParams := 2,
      numIndices := 1,
      numMotives := 1,
      numMinors := 1,
      rules := #[{ ctor := `Eq.refl, nFields := 0, rhs := { pp? := .some "fun {α} a motive refl => refl" } }]
      k := true,
    }),
    (`ForM.rec, ConstantCat.recursor {
      all := #[`ForM],
      numParams := 3,
      numIndices := 0,
      numMotives := 1,
      numMinors := 1,
      rules := #[{ ctor := `ForM.mk, nFields := 1, rhs := { pp? := .some "fun m γ α motive mk forM => mk forM" } }]
      k := false,
    })
  ]
  let inner: CoreM LSpec.TestSeq := do
    let coreContext ← readThe Core.Context
    testCases.foldlM (λ acc (name, cat) => do
      let args: Protocol.EnvInspect := { name }
      let result ← match ← Repl.env_inspect args |>.run { coreContext } |>.run' { env := ← getEnv } with
        | .ok result => pure $ result
        | .error e => panic! s!"Error: {e.desc}"
      let testName := name.toString
      let p := match cat with
        | .induct info => LSpec.test testName (result.inductInfo? == .some info)
        | .ctor info => LSpec.test testName (result.constructorInfo? == .some info)
        | .recursor info => LSpec.test testName (result.recursorInfo? == .some info)
      return LSpec.TestSeq.append acc p
    ) LSpec.TestSeq.done
  runCoreMSeq env inner

def test_symbol_location (env : Environment) : TestT IO Unit := do
  addTest $ ← runTestCoreM env do
    let .ok result ← Repl.env_inspect { name := `Nat.le_of_succ_le, source? := .some true }
      |>.run { coreContext := ← readThe Core.Context }
      |>.run' { env := ← getEnv }
      | fail "Inspect failed"
    checkEq "module" result.module? <| .some `Init.Data.Nat.Basic

    -- Extraction of source doesn't work for symbols in `Init` for some reason
    checkTrue "file" result.sourceUri?.isNone
    checkEq "sourceStart" (result.sourceStart?.map (·.column)) <| .some 0
    checkEq "sourceEnd" (result.sourceEnd?.map (·.column)) <| .some 88
    let .ok { imports, constNames, .. } ← Repl.env_module_read ⟨`Init.Data.Nat.Basic⟩
      |>.run { coreContext := ← readThe Core.Context }
      |>.run' { env := ← getEnv }
      | fail "Module read failed"
    checkEq "imports" imports #[`Init.SimpLemmas, `Init.Data.NeZero, `Init.Grind.Tactics]
    checkTrue "constNames" $ constNames.contains `Nat.succ_add

def test_matcher (env : Environment) : TestT IO Unit := do
  checkTrue "not matcher" $ ¬ Meta.isMatcherCore env `Nat.strongRecOn

def suite (env : Environment) : List (String × IO LSpec.TestSeq) :=
  [
    ("Catalog", test_catalog env),
    ("Symbol Visibility", test_symbol_visibility),
    ("Inspect", test_inspect env),
    ("Symbol Location", runTest $ test_symbol_location env),
    ("Matcher", runTest $ test_matcher env),
  ]
