/-
# Erdős Problem #340 (oq-01): the analytic `Ω(N^(1/3))` lower bound for the greedy Sidon counting function

The companion file `Erdos340GreedyGrowth.lean` proves the **cubic growth bound**
`aₙ ≤ (n+1) + (n+1)³` and its immediate discrete consequence
`greedy_count_ge`: whenever `N ≥ 2(n+1)³`, at least `n+1` greedy terms lie in `[1, N]`.

What remained — flagged there as the *only* missing piece of the known direction — was the
polished **`rpow` phrasing**: the statement actually appearing in the literature (and as the
axiom `greedy_sidon_lower_bound` in `Erdos340Problem.lean`),

  `∃ C > 0, ∀ N > 0,  C · N^(1/3) ≤ A(N)`,

where `A(N) = #{ k : aₖ ≤ N }` is the greedy Sidon counting function.  This file supplies it
as a fully verified, `0`-axiom theorem (`greedyCount_rpow_lower`), with the explicit constant
`C = 2^(-4/3)`.

## The argument

Define `greedyCount N = #{ k ≤ N : aₖ ≤ N }`.  Because `aₖ ≥ k` (strict monotonicity), the
window `range (N+1)` already captures every index with `aₖ ≤ N`, so this counts *all* greedy
terms in `[1, N]`.

The cubic bound `aₙ ≤ 2(n+1)³` gives the discrete count bound (`greedyCount_ge_index`):

  `2(n+1)³ ≤ N  ⟹  n+1 ≤ A(N)`.

Its **contrapositive**, applied at `n = A(N)`, is the clean inversion (`lt_two_mul_succ_cube`):

  `0 < N  ⟹  N < 2·(A(N) + 1)³`.

Since `A(N) ≥ 1` for `N ≥ 1` (the term `a₀ = 1` is counted), `A(N) + 1 ≤ 2·A(N)`, hence

  `N < 2·(2 A(N))³ = 16 · A(N)³`.

Taking cube roots (`rpow (1/3)`, which is monotone on `[0, ∞)`):

  `N^(1/3) < 16^(1/3) · A(N) = 2^(4/3) · A(N)`,   i.e.   `2^(-4/3) · N^(1/3) ≤ A(N)`.

NOTE on the `1/3`-vs-`1/2` gap: the `N^(1/3)` exponent is the *known* lower bound.  Improving
it for the greedy sequence is the OPEN part of Erdős #340 and is **not** attempted here.
-/
import Proofs.Erdos340GreedyGrowth

namespace Erdos340

open Finset

/- ## The greedy Sidon counting function -/

/- The greedy Sidon **counting function** `A(N)` is `greedyCount` from
`Erdos340GreedyGrowth.lean`: `A(N) = #{ x ∈ [1, N] : x ∈ greedySeqSet N }`, the number of
greedy terms in `[1, N]`.  (An identically-named local index-based definition previously
lived here; it now clashes with the imported declaration and has been merged into it —
the two counts agree since `aₖ ≥ k` puts every term `≤ N` at index `≤ N`.) -/

/-- `k ≤ aₖ`: a strictly increasing `ℕ → ℕ` sequence dominates the identity. -/
theorem index_le_greedySidonSeq (k : ℕ) : k ≤ greedySidonSeq k :=
  greedySidonSeq_strictMono.id_le k

/-- **Discrete count bound.**  Whenever `N ≥ 2(n+1)³`, the first `n+1` greedy terms all lie in
`[1, N]`, so `A(N) ≥ n+1`.  This repackages `greedySidonSeq_le_two_mul_cubic` against the
index-based counting function. -/
theorem greedyCount_ge_index {n N : ℕ} (hN : 2 * (n + 1) ^ 3 ≤ N) :
    n + 1 ≤ greedyCount N := by
  have hcube : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hnN : n ≤ N := by omega
  have h1 := greedy_count_ge hN
  unfold greedyCount
  refine h1.trans (Finset.card_le_card ?_)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, greedySeqSet_mono hnN hx.2⟩

/-- For `N ≥ 1` the term `a₀ = 1` is always counted, so `A(N) ≥ 1`. -/
theorem one_le_greedyCount {N : ℕ} (hN : 0 < N) : 1 ≤ greedyCount N := by
  have h10 : (1 : ℕ) ∈ greedySeqSet 0 := greedySidonSeq_mem 0
  have h1mem : (1 : ℕ) ∈ (Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet N) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, hN⟩, greedySeqSet_mono (Nat.zero_le N) h10⟩
  unfold greedyCount
  exact Finset.card_pos.mpr ⟨1, h1mem⟩

/-- **Inversion of the cubic bound** (contrapositive of `greedyCount_ge_index`).

`N < 2·(A(N) + 1)³`.  If instead `N ≥ 2·(A(N)+1)³`, the count bound would force
`A(N) + 1 ≤ A(N)`, impossible.  This is the key step turning the *upper* bound on the
sequence values into a *lower* bound on the counting function. -/
theorem lt_two_mul_succ_cube (N : ℕ) : N < 2 * (greedyCount N + 1) ^ 3 := by
  by_contra h
  push_neg at h
  have hge := greedyCount_ge_index (n := greedyCount N) h
  omega

/- ## The analytic `Ω(N^(1/3))` lower bound -/

/-- **The known `N^(1/3)` lower bound for the greedy Sidon sequence, in `rpow` form.**

There is an explicit constant `C = 2^(-4/3) > 0` such that the greedy Sidon counting function
`A(N) = #{ k : aₖ ≤ N }` satisfies

  `C · N^(1/3) ≤ A(N)`   for every `N ≥ 1`.

This is the polished analytic statement of Erdős #340's *known* direction — the form that
appears in the literature and as the axiom `greedy_sidon_lower_bound` in `Erdos340Problem.lean`
— here proved as a fully verified, `0`-axiom theorem from the elementary cubic growth bound.

The `1/3`→`1/2` exponent improvement remains the OPEN conjecture and is **not** addressed. -/
theorem greedyCount_rpow_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (greedyCount N : ℝ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  refine ⟨(2 : ℝ) ^ (-(4 : ℝ) / 3), Real.rpow_pos_of_pos h2 _, ?_⟩
  intro N hN
  set A := greedyCount N with hA
  have hA1 : 1 ≤ A := one_le_greedyCount hN
  -- Discrete inversion N < 16·A³.
  have hlt : N < 2 * (A + 1) ^ 3 := lt_two_mul_succ_cube N
  have hAA : A + 1 ≤ 2 * A := by omega
  have epow : (A + 1) ^ 3 ≤ (2 * A) ^ 3 := Nat.pow_le_pow_left hAA 3
  have eexp : (2 * A) ^ 3 = 8 * A ^ 3 := by ring
  have hN16 : N < 16 * A ^ 3 := by omega
  have hNR : (N : ℝ) ≤ 16 * (A : ℝ) ^ 3 := by exact_mod_cast hN16.le
  -- Package the constant: B = 2^(4/3)·A, with B³ = 16·A³.
  set B := (2 : ℝ) ^ ((4 : ℝ) / 3) * (A : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBcube : B ^ 3 = 16 * (A : ℝ) ^ 3 := by
    rw [hB, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((4 : ℝ) / 3)) 3, ← Real.rpow_mul h2.le]
    norm_num
  have hNB : (N : ℝ) ≤ B ^ 3 := by rw [hBcube]; exact hNR
  -- Cube roots: N^(1/3) ≤ B.
  have hroot : (B ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = B := by
    rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hB0 (by norm_num)
  have hcube_root : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ B := by
    calc (N : ℝ) ^ ((1 : ℝ) / 3)
        ≤ (B ^ 3) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hNB (by norm_num)
      _ = B := hroot
  -- Multiply by C = 2^(-4/3): C·B = A.
  have hCpos : (0 : ℝ) < (2 : ℝ) ^ (-(4 : ℝ) / 3) := Real.rpow_pos_of_pos h2 _
  calc (2 : ℝ) ^ (-(4 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)
      ≤ (2 : ℝ) ^ (-(4 : ℝ) / 3) * B :=
        mul_le_mul_of_nonneg_left hcube_root hCpos.le
    _ = (A : ℝ) := by
        rw [hB, ← mul_assoc, ← Real.rpow_add h2,
          show (-(4 : ℝ) / 3 + (4 : ℝ) / 3) = 0 by ring, Real.rpow_zero, one_mul]

end Erdos340
