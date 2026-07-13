/-
  ACT-READY SKELETON (build-pending) — concrete general-Finset Newton-Girard k=3.

  This is the literal target of problem.md: the closed form p₃ = e₁³ − 3e₁e₂ + 3e₃
  in the parent's concrete `Finset`-sum style (NOT the MvPolynomial API), with the
  elementary symmetric sums defined via `powersetCard`.

  The shipped file `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03.lean` already proves the
  universal MvPolynomial closed form `psum_three_closed` (a corollary of the proven
  recurrence) and the n=3 concrete case `cube_sum_three`. THIS skeleton finishes the
  general concrete Finset version. Every numbered fact below is verified exactly in
  `verify_newton_girard_k3.py`.

  TWO ROUTES (problem.md Approach 1 vs 2):

  ── Route A: direct ordered-triple partition (mirrors parent's template) ──
  Definitions (s : Finset ι, f : ι → R):
      e1 := ∑ i ∈ s, f i
      e2 := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
      e3 := ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, f i
      p2 := ∑ i ∈ s, f i ^ 2
      p3 := ∑ i ∈ s, f i ^ 3
  Lemma chain (all verified numerically):
    (L1) cube_eq_triple :  (∑ i ∈ s, f i)^3 = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i*f j*f k
         — two applications of `Finset.sum_mul_sum` (cf. parent `sq_sum_eq_double_sum`).
    (L2) partition      :  triple sum = p3 + 3*D + 6*e3,  where
                           D := ∑ i ∈ s, ∑ j ∈ s.erase i, f i^2 * f j.
         — CRUX. Partition s×s×s by coincidence pattern of (i,j,k):
             all-equal (1 ordering)        → ∑ f i^3 = p3
             exactly-two-equal (3 orders)  → 3*D
             all-distinct (6 orders)       → 6*e3
         Cleanest Lean handling: `Finset.sum_sigma`/`sum_product` + `Finset.filter`
         on the diagonal predicates, or induct via repeated `Finset.add_sum_erase`
         as the parent did for pairs. This is the only genuinely new combinatorial
         work; the 1/3/6 multiplicities are confirmed in the cert.
    (L3) D_collapse     :  D = e1*p2 - p3.
         — `∑_{j≠i} f j = e1 - f i` via `Finset.add_sum_erase`; then
           D = ∑ i, f i^2*(e1 - f i) = e1*p2 - p3 by `Finset.mul_sum`/`sum_sub_distrib`.
    (L4) e2_eq_off_diag :  2*e2 = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j.
         — each 2-subset {i,j} ↔ 2 ordered pairs; bridge powersetCard 2 to ordered
           distinct pairs (`Finset.sum_powersetCard` / pairing). The parent left this
           as a remark; supplying it is needed to phrase the answer via e2.
    Final: combine. e1^3 = p3 + 3D + 6e3 (L1,L2); sub D (L3): e1^3 = 3e1p2 - 2p3 + 6e3;
           sub p2 = e1^2 - 2e2 (parent k=2, in powerset form via L4): e1^3 =
           3e1^3 - 6e1e2 - 2p3 + 6e3 ⟹ 2p3 = 2e1^3 - 6e1e2 + 6e3 ⟹
           p3 = e1^3 - 3e1e2 + 3e3.  ← all steps `ring` once the sums are reconciled.

  ── Route B: bridge to the proven universal form (often shorter) ──
  Use σ := {x // x ∈ s} (Fintype), g : σ → R := fun i => f i.1, and evaluate
  `AMGMInequalityOQ02OQ01OQ03.psum_three_closed σ R` under `MvPolynomial.aeval g`:
      aeval g (psum σ R k)  = ∑ i, g i ^ k       (map_sum, aeval_X, map_pow)
                            = ∑ i ∈ s, f i ^ k   (Finset.sum_attach / sum_subtype)
      aeval g (esymm σ R k) = ∑ t ∈ (univ:Finset σ).powersetCard k, ∏ i ∈ t, g i
                            = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, f i
                              (map_sum, map_prod, aeval_X; reindex powersetCard of the
                               subtype-univ onto s — the one fiddly reindexing step).
  Then `psum_three_closed` maps termwise to the concrete identity. Risk concentrates
  in the esymm reindexing lemma; Route A avoids MvPolynomial entirely.

  RECOMMENDATION: try Route A L2 first (the partition lemma is the reusable artifact
  this OQ is meant to produce); fall back to Route B if the powerset reindexing in
  L4 proves lighter than the triple partition.
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01

namespace AmgmFinsetNewtonGirardK3

open Finset BigOperators

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

noncomputable def e1 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i
noncomputable def e2 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
noncomputable def e3 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, f i
def p2 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 2
def p3 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 3
def Doff (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, ∑ j ∈ s.erase i, f i ^ 2 * f j

/-- (L3) verified: Doff = e1*p2 - p3. -/
theorem D_collapse (s : Finset ι) (f : ι → R) :
    Doff s f = e1 s f * p2 s f - p3 s f := by
  sorry

/-- (L2) CRUX — verified multiplicities (1/3/6). -/
theorem cube_partition (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 3 = p3 s f + 3 * Doff s f + 6 * e3 s f := by
  sorry

/-- (L4) verified: 2*e2 = ordered distinct-pair sum. -/
theorem two_e2_eq_off_diag (s : Finset ι) (f : ι → R) :
    2 * e2 s f = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  sorry

/-- Main target: concrete general-Finset Newton-Girard k=3 closed form. -/
theorem newton_girard_three_finset (s : Finset ι) (f : ι → R) :
    p3 s f = e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f := by
  -- From cube_partition + D_collapse + parent k=2 (via two_e2_eq_off_diag), all `ring`.
  sorry

end AmgmFinsetNewtonGirardK3
