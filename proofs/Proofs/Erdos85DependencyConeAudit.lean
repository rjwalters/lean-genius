import Mathlib.Util.AssertNoSorry

/-!
# Exact dependency-cone discovery for the Erdős-85 drop audit

`#erdos85_dependency_cone target` prints one machine-readable line for every
theorem in the target's transitive declaration cone whose defining module is a
project `Proofs.*` module.  The companion Python driver turns this inventory
into literal `#print axioms` commands and checks the disclosed axiom families.
The wider project prefix is intentional: a non-Erdős helper used by the final
theorem is still part of mandate 1318's dependency cone.
-/

open Lean Elab Command

namespace Erdos85.DependencyConeAudit

private def moduleNameMap (env : Environment) : Std.HashMap ModuleIdx Name := Id.run do
  let mut result : Std.HashMap ModuleIdx Name := {}
  for moduleName in env.header.moduleNames do
    result := result.insert (env.getModuleIdx? moduleName).get! moduleName
  return result

private def declarationModule? (env : Environment)
    (modules : Std.HashMap ModuleIdx Name) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  modules.get? index

private def isProjectProofModule (moduleName : Name) : Bool :=
  moduleName.toString.startsWith "Proofs."

private def declarationExprs (info : ConstantInfo) : Array Expr :=
  match info with
  | .axiomInfo value => #[value.type]
  | .defnInfo value => #[value.type, value.value]
  | .thmInfo value => #[value.type, value.value]
  | .opaqueInfo value => #[value.type, value.value]
  | .quotInfo _ => #[]
  | .ctorInfo value => #[value.type]
  | .recInfo value => #[value.type]
  | .inductInfo value => #[value.type]

private def directConstants (info : ConstantInfo) : NameSet := Id.run do
  let mut result : NameSet := {}
  for expr in declarationExprs info do
    for name in expr.getUsedConstants do
      result := result.insert name
  return result

private def commaNames (names : Array Name) : String :=
  String.intercalate "," ((names.qsort Name.lt).toList.map Name.toString)

structure WalkState where
  visited : NameSet := {}
  theoremCount : Nat := 0

partial def walk (name : Name) (modules : Std.HashMap ModuleIdx Name) :
    StateT WalkState CommandElabM Unit := do
  if (← get).visited.contains name then return
  modify fun state => { state with visited := state.visited.insert name }
  let env ← getEnv
  let some moduleName := declarationModule? env modules name | return
  unless isProjectProofModule moduleName do return
  let some info := env.find? name | return
  let direct := directConstants info
  if info.isTheorem then
    let axioms ← liftCoreM <| Lean.collectAxioms name
    let directAxioms := direct.toArray.filter fun dependency =>
      match env.find? dependency with
      | some (.axiomInfo _) => true
      | _ => false
    logInfo m!"ERDOS85_CONE\t{name}\t{moduleName}\t{commaNames directAxioms}\t{commaNames axioms}"
    modify fun state => { state with theoremCount := state.theoremCount + 1 }
  for dependency in direct.toArray.qsort Name.lt do
    walk dependency modules

elab "#erdos85_dependency_cone " target:ident : command => do
  let targetName ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo target
  let env ← getEnv
  let (_, state) ← (walk targetName (moduleNameMap env)).run {}
  logInfo m!"ERDOS85_CONE_SUMMARY\t{targetName}\t{state.theoremCount}"

end Erdos85.DependencyConeAudit
