import Pantograph.Elab
import Pantograph.Protocol
import Lean.Environment
import Lean.Replay
import Lean.Util.Path

open Lean
open Pantograph

namespace Pantograph

def isAuxLemma (n : Name) : Bool :=
  match n with
  -- `mkAuxLemma` generally allows for arbitrary prefixes but these are the ones produced by core.
  | .str _ s => "_proof_".isPrefixOf s || "_simp_".isPrefixOf s
  | _ => false

@[export pantograph_is_name_internal]
def isNameInternal (n: Name): Bool :=
  -- Returns true if the name is an implementation detail which should not be shown to the user.
  isAuxLemma n ∨ n.hasMacroScopes

/-- Catalog all the non-internal and safe names -/
@[export pantograph_environment_catalog]
def envCatalog (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) λ acc name _ =>
    match isNameInternal name with
    | false => acc.push name
    | true => acc

@[export pantograph_environment_module_of_name]
def module_of_name (env: Environment) (name: Name): Option Name := do
  let moduleId ← env.getModuleIdxFor? name
  if h : moduleId.toNat < env.allImportedModuleNames.size then
    return env.allImportedModuleNames[moduleId.toNat]
  else
    .none

def toCompactSymbolName (n: Name) (info: ConstantInfo): String :=
  let pref := match info with
  | .axiomInfo  _ => "a"
  | .defnInfo   _ => "d"
  | .thmInfo    _ => "t"
  | .opaqueInfo _ => "o"
  | .quotInfo   _ => "q"
  | .inductInfo _ => "i"
  | .ctorInfo   _ => "c"
  | .recInfo    _ => "r"
  s!"{pref}{toString n}"

def toFilteredSymbol (n: Lean.Name) (info: Lean.ConstantInfo): Option String :=
  if isNameInternal n || info.isUnsafe
  then Option.none
  else Option.some <| toCompactSymbolName n info

abbrev ConstArray := Array (Name × ConstantInfo)
abbrev DistilledEnvironment := Array Import × ConstArray

def envDiff (src dst : Environment) : ConstArray :=
  dst.constants.map₂.foldl (init := #[]) λ acc name info =>
    if src.contains name then
      acc
    else
      acc.push (name, info)

/-- Boil an environment down to minimal components -/
def distilEnvironment (env : Environment) (background? : Option Environment := .none)
  : DistilledEnvironment :=
  let constants := match background? with
    | .some src => envDiff src env
    | .none => env.constants.map₂.toArray
  (env.header.imports, constants)

deriving instance BEq for Import

def checkEnvConflicts (src src' dst : Environment) : ExceptT String IO Environment := do
  let (srcImports, srcConstants) := distilEnvironment src' (background? := .some src)
  let mut srcConstants := srcConstants.foldl
    (init := Std.HashMap.emptyWithCapacity srcConstants.size)
    λ acc (k, v) => acc.insert k v
  let (dstImports, dstConstants) := distilEnvironment dst (background? := .some src)
  -- Replay all `dstConstants` in the environment
  if srcImports != dstImports then
    throw "Modification of imports is not allowed"
  -- Replay all dst constants in src
  let env ← try
      src.replay $ dstConstants.foldl (init := .emptyWithCapacity dstConstants.size) λ acc (k, v) => acc.insert k v
    catch ex : IO.Error =>
      throw ex.toString
  -- check if `constants` can fit into `src'`
  for (name, dstInfo) in dstConstants do
    if dstInfo.type.hasSorry then
      throw s!"Definition type has sorry: {name}"
    if dstInfo.value?.map Expr.hasSorry |>.getD false then
      throw s!"Definition value has sorry: {name}"
    match srcConstants[name]? with
    | .some srcInfo =>
      if srcInfo.type != dstInfo.type then
        throw s!"Type clash of {name}"
      if srcInfo.levelParams != dstInfo.levelParams then
        throw s!"Level param clash of {name}"
      if !(← infoCompare srcInfo dstInfo) then
        throw s!"Definition clash of {name}"
      if !isNoncomputable src' name ∧ isNoncomputable dst name then
        throw s!"Must not modify computability on {name}"
    | _ =>
      if dstInfo.isAxiom then
        throw s!"Adding axiom is not allowed: {name}"
    srcConstants := srcConstants.erase name
  let srcConstantsList := srcConstants.keys.filter (not ∘ isInternalSymbol)
  if !srcConstantsList.isEmpty then
    throw s!"{srcConstantsList} not accounted for"
  return env
  where
  isInternalSymbol (name: Name) : Bool := match name with
    | .str _ n => n == "_cstage1" || n == "_cstage2"
    | _ => false
  /-- Assumes type check has been done. -/
  infoCompare (srcInfo dstInfo : ConstantInfo) : ExceptT String IO Bool :=
    match srcInfo, dstInfo with
    | .axiomInfo _a1, .axiomInfo _a2 => return true
    | .defnInfo srcVal, .defnInfo dstVal => do
      if srcVal.safety != dstVal.safety then
        return false
      if srcVal.value.hasSorry then
        return true
      -- Value modification is prohibited otherwise
      return srcVal.value == dstVal.value
    | .thmInfo srcVal, .thmInfo dstVal => do
      if srcVal.value.hasSorry then
        return true
      -- Value modification is prohibited otherwise
      return srcVal.value == dstVal.value
    | .opaqueInfo _, .opaqueInfo _ => do
      return true
    | .quotInfo _, .quotInfo _ => return true
    | .inductInfo _, .inductInfo _ => return true
    | .ctorInfo _, .ctorInfo _ => return true
    | .recInfo _, .recInfo _ => return true
    | _, _ => return false

/-- Add constants to the environment, renaming the constants if necessary -/
def replayConstantsRenaming (constants : Std.HashMap Name ConstantInfo) : CoreM (Std.HashMap Name Name) := do
  let env' ← (← getEnv).replay constants
  setEnv env'
  -- FIXME: Deduplicate
  return .emptyWithCapacity 2
