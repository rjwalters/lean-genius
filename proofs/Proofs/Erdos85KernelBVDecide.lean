import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

/-!
# Kernel-checked LRAT replay for bounded quotient censuses

Lean's standard `bv_decide` verifies its reflected LRAT certificate by native
evaluation.  This variant keeps the same bit-blasting and SAT search but asks
the kernel to reduce the pure certificate checker when it validates the final
proof term.  It is intended for small, publication-facing finite censuses for
which an axiom-free audit matters more than compilation speed.
-/

open Lean Elab Tactic Meta

namespace Erdos85.KernelBVDecide

open Std.Sat
open Std.Tactic.BVDecide

/-- Check a pre-parsed LRAT action array against the bit-blasted formula. -/
def verifyBVExprActions (bv : BVLogicalExpr)
    (cert : Array LRAT.IntAction) : Bool :=
  LRAT.check cert (AIG.toCNF bv.bitblast.relabelNat)

/-- Soundness of typed LRAT replay, avoiding certificate-string parsing in
kernel reduction. -/
theorem unsat_of_verifyBVExprActions_eq_true (bv : BVLogicalExpr)
    (cert : Array LRAT.IntAction)
    (h : verifyBVExprActions bv cert = true) : bv.Unsat := by
  apply BVLogicalExpr.unsat_of_bitblast
  rw [← AIG.Entrypoint.relabelNat_unsat_iff]
  rw [← AIG.toCNF_equisat]
  exact LRAT.check_sound cert _ h

end Erdos85.KernelBVDecide

namespace Lean.Elab.Tactic.BVDecide.Frontend

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

private def LratCert.toKernelReflectionProof (cert : LratCert)
    (ctx : TacticContext) (reflectionResult : ReflectionResult) : MetaM Expr := do
  let mkAuxDecl (name : Name) (value type : Expr) : CoreM Unit :=
    withOptions (fun opt => opt.set `compiler.extract_closed false) do
      addAndCompile <| .defnDecl {
        name := name
        levelParams := []
        type := type
        value := value
        hints := .abbrev
        safety := .safe
      }
  let parsed ← IO.lazyPure (fun _ => LRAT.parseLRATProof cert.toUTF8)
  let actions ← IO.ofExcept parsed
  mkAuxDecl ctx.exprDef reflectionResult.expr (mkConst ``BVLogicalExpr)
  mkAuxDecl ctx.certDef (toExpr actions)
    (mkApp (mkConst ``Array [.zero]) (mkConst ``LRAT.IntAction))
  let reflectedExpr := mkConst ctx.exprDef
  let certExpr := mkConst ctx.certDef
  let reflectionTerm := mkApp2
    (mkConst ``Erdos85.KernelBVDecide.verifyBVExprActions)
      reflectedExpr certExpr
  let verificationEq ← mkEq reflectionTerm (mkConst ``Bool.true)
  let verificationProof :=
    mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.true)) verificationEq
  return mkApp3
    (mkConst ``Erdos85.KernelBVDecide.unsat_of_verifyBVExprActions_eq_true)
    reflectedExpr certExpr verificationProof

private def kernelLratBitblaster (ctx : TacticContext) : UnsatProver :=
  fun (goal : MVarId) (reflectionResult : ReflectionResult)
      (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) => do
    let bvExpr := reflectionResult.bvExpr
    let entry ← IO.lazyPure (fun _ => bvExpr.bitblast)
    let aigSize := entry.aig.decls.size
    let (cnf, map) ← IO.lazyPure (fun _ =>
      let (entry, map) := entry.relabelNat'
      (AIG.toCNF entry, map))
    let res ← runExternal cnf ctx.solver ctx.lratPath ctx.config.trimProofs
      ctx.config.timeout ctx.config.binaryProofs ctx.config.solverMode
    match res with
    | .ok cert =>
      let proof ← cert.toKernelReflectionProof ctx reflectionResult
      return .ok ⟨proof, cert⟩
    | .error assignment =>
      let equations := reconstructCounterExample map assignment aigSize atomsAssignment
      return .error {
        goal
        unusedHypotheses := reflectionResult.unusedHypotheses
        equations
      }

private def kernelBVUnsat (g : MVarId) (ctx : TacticContext) :
    MetaM (Except CounterExample LratCert) := M.run do
  closeWithBVReflection g (kernelLratBitblaster ctx)

private def kernelBVDecide (g : MVarId) (ctx : TacticContext) : MetaM Unit := do
  let g? ← Normalize.bvNormalize g ctx.config
  let some g := g? | return
  match ← kernelBVUnsat g ctx with
  | .ok _ => return
  | .error counterExample =>
    counterExample.goal.withContext do
      throwError (← explainCounterExampleQuality counterExample)

end Lean.Elab.Tactic.BVDecide.Frontend

syntax (name := kernelBVDecide) "kernel_bv_decide" optConfig : tactic

elab_rules : tactic
  | `(tactic| kernel_bv_decide $cfgStx:optConfig) => do
      let cfg ← Lean.Elab.Tactic.BVDecide.Frontend.elabBVDecideConfig cfgStx
      IO.FS.withTempFile fun _ lratFile => do
        let ctx ← Lean.Elab.Tactic.BVDecide.Frontend.TacticContext.new lratFile cfg
        liftMetaFinishingTactic fun g =>
          Lean.Elab.Tactic.BVDecide.Frontend.kernelBVDecide g ctx
