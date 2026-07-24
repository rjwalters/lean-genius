/-
  # Roth k = 3: Discharging the k = 3 Instance of `density_increment_kAP`

  The parent file `Proofs/RothTheoremOQ03.lean` axiomatizes the density
  increment step for general k-term arithmetic progressions:

    axiom density_increment_kAP (N k : ℕ) [NeZero N] (hk : k ≥ 3) (hN : N ≥ 2) …

  For k ≥ 4 this is genuinely deep (it requires the inverse theorem for
  Gowers U^{k-1} norms). For k = 3, however, the parent already *proves*
  an explicit, stronger form — `density_increment_k3_explicit`, with the
  quantitative increment δ' ≥ δ + δ²/100 — from the Fourier-analytic
  density increment machinery of `Proofs/RothTheorem.lean` (0 axioms,
  0 sorries).

  This file closes the gap flagged by the `incomplete-01` node: it derives
  the *exact* k = 3 instance of the axiom's statement as a theorem, so the
  axiom is redundant at k = 3. The only bridging step is weakening the
  explicit bound `δ' ≥ δ + δ²/100` to the axiom's qualitative `δ' > δ`
  (valid since δ > 0 forces δ²/100 > 0).

  Supporting lemmas quantify why the increment iterates to Roth's theorem:
  densities are capped at 1 (`density_le_one`), so the explicit increment
  can fire at most 100/δ₀² times from initial density δ₀
  (`density_increment_iteration_bound`).

  ## References
  - Roth, "On certain sets of integers" (1953)
  - Gowers, "A new proof of Szemerédi's theorem" (2001) — why k ≥ 4 is deep
-/
import Proofs.RothTheoremOQ03

namespace RothTheoremK3OQ03Incomplete01

open RothTheoremOQ03

/-- **k = 3 instance of the parent axiom, proved.**
    This is verbatim the statement of `density_increment_kAP N 3 (by norm_num)
    hN A δ hδ hδ_pos hno_3AP` — same hypotheses, same conclusion shape
    (`∃ M, 0 < M, M < N, ∃ A' δ', δ' = A'.card / M ∧ δ' > δ ∧ 3-AP-free`) —
    derived without the axiom, from the parent's proved
    `density_increment_k3_explicit`. The explicit increment δ' ≥ δ + δ²/100
    is weakened to δ' > δ using 0 < δ²/100. -/
theorem density_increment_kAP_k3 (N : ℕ) [NeZero N] (hN : N ≥ 2)
    (A : Finset (ZMod N)) (δ : ℝ)
    (hδ : δ = A.card / N) (hδ_pos : 0 < δ)
    (hno_3AP : IsKAPFreeZMod A 3) :
    ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
      ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
        δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' 3 := by
  obtain ⟨M, hM_pos, hM_lt, A', δ', hδ', hδ'_incr, hAP'⟩ :=
    density_increment_k3_explicit N hN A δ hδ hδ_pos hno_3AP
  refine ⟨M, hM_pos, hM_lt, A', δ', hδ', ?_, hAP'⟩
  have h_sq_pos : 0 < δ ^ 2 / 100 := by positivity
  linarith

/-- Densities in `ZMod N` are capped at 1: for any `A : Finset (ZMod N)`
    with `N > 0`, the density `A.card / N` is at most 1. This is the
    ceiling that terminates the density increment iteration. -/
theorem density_le_one {N : ℕ} (hN : 0 < N) (A : Finset (ZMod N)) :
    (A.card : ℝ) / N ≤ 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [div_le_one (by exact_mod_cast hN)]
  have hcard : A.card ≤ N := by
    calc A.card ≤ (Finset.univ : Finset (ZMod N)).card :=
          Finset.card_le_card (Finset.subset_univ A)
      _ = N := by simp [Finset.card_univ, ZMod.card]
  exact_mod_cast hcard

/-- **Iteration-depth bound for the explicit k = 3 increment.**
    Each application of `density_increment_k3_explicit` raises the density
    by at least δ²/100 ≥ δ₀²/100 (densities never decrease below the
    starting value δ₀ along the iteration). Since densities are ≤ 1, if
    `n` steps of size δ₀²/100 still fit below the ceiling, then
    n ≤ 100/δ₀². Hence the increment fires at most ⌊100/δ₀²⌋ times —
    the O(δ₀⁻²) iteration count of Roth's density increment argument. -/
theorem density_increment_iteration_bound (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (n : ℕ)
    (h : δ₀ + n * (δ₀ ^ 2 / 100) ≤ 1) :
    (n : ℝ) ≤ 100 / δ₀ ^ 2 := by
  have hsq : (0 : ℝ) < δ₀ ^ 2 := by positivity
  rw [le_div_iff₀ hsq]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

#print axioms density_increment_kAP_k3

end RothTheoremK3OQ03Incomplete01
