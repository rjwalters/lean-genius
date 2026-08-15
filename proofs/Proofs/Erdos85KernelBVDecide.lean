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
open Std.Tactic.BVDecide.LRAT.Internal

/-- Result of replaying a bounded number of LRAT actions.  A checkpoint
contains the updated formula and the next action index. -/
inductive ReplayResult (n : Nat) where
  | failure
  | success
  | checkpoint (formula : DefaultFormula n) (nextIdx : Nat)

/-- Proof-free serialization format for checkpoint formulas. -/
abbrev EncodedFormula := Array (Option (Array Int))

/-- Reconstruct a checker formula from its signed-literal clause arrays. -/
def decodeFormula (n : Nat) (encoded : EncodedFormula) : DefaultFormula n :=
  DefaultFormula.ofArray <| encoded.map fun
    | none => none
    | some literals => do
        let literals ← literals.mapM intToLiteral
        Clause.ofArray literals

theorem decodeFormula_readyForRupAdd (n : Nat) (encoded : EncodedFormula) :
    Formula.ReadyForRupAdd (decodeFormula n encoded) := by
  exact DefaultFormula.readyForRupAdd_ofArray _

theorem decodeFormula_readyForRatAdd (n : Nat) (encoded : EncodedFormula) :
    Formula.ReadyForRatAdd (decodeFormula n encoded) := by
  exact DefaultFormula.readyForRatAdd_ofArray _

/-- Replay at most `fuel` actions.  Unlike the stock checker, reaching the
fuel bound returns the current formula instead of recursively traversing the
entire certificate. -/
def replayChunk (f : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel : Nat) : ReplayResult n :=
  match fuel with
  | 0 => .checkpoint f idx
  | fuel + 1 =>
    if h : idx < proof.size then
      let step := intActionToDefaultClauseAction n proof[idx]
      match step with
      | none => replayChunk f proof (idx + 1) fuel
      | some (.addEmpty _ rupHints) =>
        let (_, checkSuccess) := Formula.performRupAdd f Clause.empty rupHints
        if checkSuccess then .success else .failure
      | some (.addRup _ c rupHints) =>
        let (f', checkSuccess) := Formula.performRupAdd f c rupHints
        if checkSuccess then replayChunk f' proof (idx + 1) fuel else .failure
      | some (.addRat _ c pivot rupHints ratHints) =>
        if pivot ∈ Clause.toList c then
          let (f', checkSuccess) := Formula.performRatAdd f c pivot rupHints ratHints
          if checkSuccess then replayChunk f' proof (idx + 1) fuel else .failure
        else
          replayChunk f proof (idx + 1) fuel
      | some (.del ids) => replayChunk (Formula.delete f ids) proof (idx + 1) fuel
    else
      .failure

/-- Semantic obligation represented by a bounded replay result. -/
def ReplayResult.Sound (initial : DefaultFormula n) : ReplayResult n → Prop
  | .failure => True
  | .success => Unsatisfiable (PosFin n) initial
  | .checkpoint formula _ =>
      Formula.ReadyForRupAdd formula ∧ Formula.ReadyForRatAdd formula ∧
        (Unsatisfiable (PosFin n) formula → Unsatisfiable (PosFin n) initial)

theorem replayChunk_sound (f : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f) :
    (replayChunk f proof idx fuel).Sound f := by
  induction fuel generalizing f idx with
  | zero => simp [replayChunk, ReplayResult.Sound, hrup, hrat]
  | succ fuel ih =>
      unfold replayChunk
      split
      · rename_i hidx
        simp only
        split
        · exact ih f (idx + 1) hrup hrat
        · rename_i _ hints _
          split
          · rename_i hok
            apply addEmptyCaseSound f hrup hints
            simpa using hok
          · trivial
        · rename_i _ c hints _
          cases heq : Formula.performRupAdd f c hints with
          | mk f' ok =>
            cases ok with
            | false => trivial
            | true =>
                have hiff := Formula.rupAdd_sound f c hints f' hrup heq
                have hs := ih f' (idx + 1) (by grind) (by grind)
                cases hres : replayChunk f' proof (idx + 1) fuel <;>
                  simp [hres, ReplayResult.Sound] at hs ⊢
                · exact fun p hp => hs p ((hiff p).mp hp)
                · exact ⟨hs.1, hs.2.1, fun hu p hp =>
                    hs.2.2 hu p ((hiff p).mp hp)⟩
        · rename_i _ c pivot hints ratHints _
          split
          · rename_i hpivot
            cases heq : Formula.performRatAdd f c pivot hints ratHints with
            | mk f' ok =>
              cases ok with
              | false => trivial
              | true =>
                have hequi := Formula.ratAdd_sound
                  f c pivot hints ratHints f' hrat hpivot heq
                have hs := ih f' (idx + 1) (by grind) (by grind)
                cases hres : replayChunk f' proof (idx + 1) fuel <;>
                  simp [hres, ReplayResult.Sound] at hs ⊢
                · exact hequi.mpr hs
                · exact ⟨hs.1, hs.2.1,
                    fun hu => hequi.mpr (hs.2.2 hu)⟩
          · exact ih f (idx + 1) hrup hrat
        · rename_i ids _
          have hs := ih (Formula.delete f ids) (idx + 1) (by grind) (by grind)
          cases hres : replayChunk (Formula.delete f ids) proof (idx + 1) fuel <;>
            simp [hres, ReplayResult.Sound] at hs ⊢
          · exact fun p hp => hs p (Formula.limplies_delete p hp)
          · exact ⟨hs.1, hs.2.1, fun hu p hp =>
              hs.2.2 hu p (Formula.limplies_delete p hp)⟩
      · trivial

theorem replayChunk_checkpoint_readyForRupAdd
    (f f' : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel nextIdx : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f)
    (h : replayChunk f proof idx fuel = .checkpoint f' nextIdx) :
    Formula.ReadyForRupAdd f' := by
  have hs := replayChunk_sound f proof idx fuel hrup hrat
  rw [h] at hs
  exact hs.1

theorem replayChunk_checkpoint_readyForRatAdd
    (f f' : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel nextIdx : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f)
    (h : replayChunk f proof idx fuel = .checkpoint f' nextIdx) :
    Formula.ReadyForRatAdd f' := by
  have hs := replayChunk_sound f proof idx fuel hrup hrat
  rw [h] at hs
  exact hs.2.1

theorem replayChunk_checkpoint_unsat
    (f f' : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel nextIdx : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f)
    (h : replayChunk f proof idx fuel = .checkpoint f' nextIdx) :
    Unsatisfiable (PosFin n) f' → Unsatisfiable (PosFin n) f := by
  have hs := replayChunk_sound f proof idx fuel hrup hrat
  rw [h] at hs
  exact hs.2.2

theorem replayChunk_success_unsat
    (f : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f)
    (h : replayChunk f proof idx fuel = .success) :
    Unsatisfiable (PosFin n) f := by
  have hs := replayChunk_sound f proof idx fuel hrup hrat
  rw [h] at hs
  exact hs

def replayChunkSucceeded (f : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel : Nat) : Bool :=
  match replayChunk f proof idx fuel with
  | .success => true
  | _ => false

theorem replayChunkSucceeded_unsat
    (f : DefaultFormula n) (proof : Array LRAT.IntAction)
    (idx fuel : Nat) (hrup : Formula.ReadyForRupAdd f)
    (hrat : Formula.ReadyForRatAdd f)
    (h : replayChunkSucceeded f proof idx fuel = true) :
    Unsatisfiable (PosFin n) f := by
  unfold replayChunkSucceeded at h
  split at h <;> try contradiction
  exact replayChunk_success_unsat f proof idx fuel hrup hrat (by assumption)

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

theorem unsat_of_convertLRAT_unsat (bv : BVLogicalExpr)
    (h : Unsatisfiable (PosFin ((AIG.toCNF bv.bitblast.relabelNat).numLiterals + 1))
      (CNF.convertLRAT (AIG.toCNF bv.bitblast.relabelNat))) : bv.Unsat := by
  apply BVLogicalExpr.unsat_of_bitblast
  rw [← AIG.Entrypoint.relabelNat_unsat_iff]
  rw [← AIG.toCNF_equisat]
  exact CNF.unsat_of_convertLRAT_unsat _ h

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
