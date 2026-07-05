/-
  ============================================================================
  WIP DRAFT — NOT BUILD-VERIFIED (Docker + Aristotle tooling blackout 2026-07-04)
  ============================================================================

  cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02-oq-05
  Multi-block RCF via the K[X]-module structure theorem.

  This is the STATEMENT SKELETON for the first self-contained increment toward
  multi-block RCF: the CRT / elementary-divisor **coprime block-merge**. It is a
  design artifact only — the signatures were hand-checked against a local mathlib4
  checkout but NOT compiled (no build tooling available this session). Do not open
  a PR from this file. Move it into proofs/Proofs/ and discharge the sorries only
  after `docker-build.sh` is confirmed working.

  Reuses (as black boxes) from CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02:
    · minpoly_companionMx_eq
    · nonderogatory_iff_similar_to_companion
  See knowledge.md for the full L1–L5 proof plan and Mathlib API map.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02

set_option linter.unusedVariables false

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02OQ05

open Matrix Polynomial
open CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02
open GeneralCyclicVector

variable {K : Type*} [Field K]

/-- **L2** (Mathlib gap): the characteristic polynomial of a companion matrix is its
    defining polynomial. Bootstrap route: companion is cyclic at `e₀`, hence
    nonderogatory, hence `charpoly = minpoly = p` via `minpoly_companionMx_eq`. -/
theorem charpoly_companionMx {n : ℕ} (p : K[X])
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n) :
    (companionMx (n := n) p).charpoly = p := by
  sorry

/-- **L3**: charpoly of a two-block matrix factors (immediate from Mathlib's
    `Matrix.charpoly_fromBlocks_zero₂₁`). Stated over the `⊕`-index. -/
theorem charpoly_fromBlocks_companion {dp dq : ℕ}
    (A : Matrix (Fin dp) (Fin dp) K) (B : Matrix (Fin dq) (Fin dq) K) :
    (fromBlocks A 0 0 B).charpoly = A.charpoly * B.charpoly := by
  sorry

/-- **L1** (lynchpin, Mathlib gap): the minimal polynomial of a two-block matrix is the
    lcm of the blocks' minimal polynomials. Proof: `(fromBlocks A 0 0 B)^k =
    fromBlocks (A^k) 0 0 (B^k)` ⇒ `aeval` distributes over blocks ⇒ a polynomial
    annihilates the block matrix iff it annihilates each block ⇒ annihilator ideal is
    the meet `(minpoly A) ⊓ (minpoly B)`, whose monic generator (PID `K[X]`) is `lcm`. -/
theorem minpoly_fromBlocks_eq_lcm {dp dq : ℕ}
    (A : Matrix (Fin dp) (Fin dp) K) (B : Matrix (Fin dq) (Fin dq) K) :
    minpoly K (fromBlocks A 0 0 B) = lcm (minpoly K A) (minpoly K B) := by
  sorry

/-- **L5**: for coprime monic polynomials, lcm = product (normalize fixes monics). -/
theorem lcm_eq_mul_of_isCoprime_monic {p q : K[X]}
    (hp : p.Monic) (hq : q.Monic) (h : IsCoprime p q) :
    lcm p q = p * q := by
  sorry

/-- **Main increment — CRT coprime block-merge.**
    For coprime monic `p, q` (positive degree), the companion block-diagonal
    `fromBlocks (C p) 0 0 (C q)` is similar, after reindexing
    `Fin dₚ ⊕ Fin d_q ≃ Fin (dₚ + d_q)`, to the single companion `C (p*q)`.

    Strategy (see knowledge.md §Proof strategy):
      minpoly D = lcm p q = p*q    (L1 + L5)
      charpoly D = p*q             (L2 + L3)  ⇒ D nonderogatory (minpoly = charpoly)
      nonderogatory_iff_similar_to_companion ⇒ D ~ companionMx (minpoly D) = C (p*q). -/
theorem companion_blockmerge_coprime {dp dq : ℕ}
    (p q : K[X]) (hp : p.Monic) (hq : q.Monic)
    (hpdeg : p.natDegree = dp) (hqdeg : q.natDegree = dq)
    (hdp : 0 < dp) (hdq : 0 < dq) (hpq : IsCoprime p q) :
    ∃ P : Matrix (Fin (dp + dq)) (Fin (dp + dq)) K, IsUnit P ∧
      P⁻¹ *
        (reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks (companionMx (n := dp) p) 0 0 (companionMx (n := dq) q))) * P
        = companionMx (n := dp + dq) (p * q) := by
  sorry

end CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02OQ05
