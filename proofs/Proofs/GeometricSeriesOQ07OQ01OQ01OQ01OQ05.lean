/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-05:
# Combinatorial palindromy of the Eulerian numbers, and the vanishing alternating row sum

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01` builds the combinatorial
**Eulerian numbers** `⟨m,k⟩` from the classical triangle recurrence
`⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩`, `⟨m,0⟩ = 1`, and proves they are the
coefficients of the Eulerian polynomial.  A sibling entry
(`geometric-series-oq-07-oq-01-oq-01-oq-02`) proves the *polynomial* symmetry
`Eₘ(X) = Xᵐ⁺¹·Eₘ(1/X)` by coefficient extraction.  This entry settles the open question
`oq-05`: a direct, self-contained proof of the **combinatorial palindromy**

  **`eulerian_palindrome`** :  `⟨n+1, k⟩ = ⟨n+1, n−k⟩`   (for `k ≤ n`),

straight from the triangle recurrence by induction on `n` — no polynomial machinery.  This
is the descent–ascent reversal symmetry of the descent statistic: reversing a permutation
`σ ↦ σ_revⱼ = σ_{m+1−j}` turns `j` descents into `m−1−j` descents, so `⟨m,k⟩ = ⟨m,m−1−k⟩`.

As a genuinely new consequence we deduce the **vanishing of the alternating row sum on even
rows**:

  **`eulerian_alt_row_sum_eq_zero`** :  `∑_{k<2m} (−1)ᵏ·⟨2m,k⟩ = 0`   (for `m ≥ 1`).

This is the first step of the classical **Eulerian → tangent-number** phenomenon: the signed
row sums `∑_k (−1)ᵏ⟨m,k⟩` vanish on even rows `m ≥ 2`, while the odd rows produce the tangent
(zag) numbers `1, 2, 16, 272, …` (the Taylor coefficients of `tan`), corroborated by the
`example`s at the end.  Even-row vanishing follows from palindromy alone: the reflection
`k ↦ 2m−1−k` is a fixed-point-free involution on `{0,…,2m−1}` pairing equal Eulerian numbers
with opposite signs.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ05

open Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## The right corner of each Eulerian row -/

/-- The last (rightmost) entry of each Eulerian row is `1`: `⟨n+1, n⟩ = 1`
(the unique permutation of `{1,…,n+1}` with the maximal `n` descents is the reversal). -/
theorem eulerian_top (n : ℕ) : eulerian (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eulerian_succ_succ, eulerian_succ_self, mul_zero, zero_add]
    have h : n + 1 - n = 1 := by omega
    rw [h, one_mul, ih]

/-! ## Combinatorial palindromy of the Eulerian numbers -/

/-- **Palindromy of the Eulerian numbers**, proved directly from the triangle recurrence by
induction on the row: for `k ≤ n`, `⟨n+1, k⟩ = ⟨n+1, n−k⟩`. -/
theorem eulerian_palindrome : ∀ (n k : ℕ), k ≤ n →
    eulerian (n + 1) k = eulerian (n + 1) (n - k) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    rfl
  | succ n ih =>
    intro k hk
    rcases k with _ | k
    · -- corner: ⟨n+2, 0⟩ = 1 = ⟨n+2, n+1⟩
      rw [Nat.sub_zero, eulerian_succ_zero, eulerian_top]
    · have hkn : k ≤ n := by omega
      rcases eq_or_lt_of_le hkn with hk' | hk'
      · -- top corner: k = n, so ⟨n+2, n+1⟩ = ⟨n+2, 0⟩ = 1
        subst hk'
        rw [Nat.sub_self, eulerian_succ_zero, eulerian_top]
      · -- interior: 0 ≤ k < n.  Expand both sides via the recurrence and fold with the IH.
        obtain ⟨p, hp⟩ : ∃ p, n - k = p + 1 := ⟨n - k - 1, by omega⟩
        rw [Nat.succ_sub_succ, hp, eulerian_succ_succ]
        conv_rhs => rw [eulerian_succ_succ]
        -- reflect the two row-`n+1` entries appearing on the right
        have e1 : eulerian (n + 1) (p + 1) = eulerian (n + 1) k := by
          rw [← hp, ih (n - k) (by omega)]; congr 1; omega
        have e2 : eulerian (n + 1) p = eulerian (n + 1) (k + 1) := by
          rw [show p = n - k - 1 from by omega, ih (n - k - 1) (by omega)]
          congr 1; omega
        rw [e1, e2]
        have c1 : n + 1 - k = p + 2 := by omega
        have c2 : n + 1 - p = k + 2 := by omega
        rw [c1, c2]; ring

/-- Palindromy in row form: for `1 ≤ r` and `k < r`, `⟨r, k⟩ = ⟨r, r−1−k⟩`. -/
theorem eulerian_palindrome' {r k : ℕ} (hr : 1 ≤ r) (hk : k < r) :
    eulerian r k = eulerian r (r - 1 - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hidx : n + 1 - 1 - k = n - k := by omega
  rw [hidx, eulerian_palindrome n k (by omega)]

/-! ## The alternating row sum vanishes on even rows -/

/-- **The alternating row sum vanishes on even rows.**  For `m ≥ 1`,
`∑_{k=0}^{2m−1} (−1)ᵏ·⟨2m,k⟩ = 0`.  The reflection `k ↦ 2m−1−k` is a fixed-point-free
involution pairing equal Eulerian numbers (palindromy) with opposite signs. -/
theorem eulerian_alt_row_sum_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (2 * m), (-1 : ℤ) ^ k * (eulerian (2 * m) k : ℤ) = 0 := by
  set N := 2 * m with hN
  set S := ∑ k ∈ range N, (-1 : ℤ) ^ k * (eulerian N k : ℤ) with hS
  -- each reflected term equals minus the original term
  have hterm : ∀ j ∈ range N,
      (-1 : ℤ) ^ (N - 1 - j) * (eulerian N (N - 1 - j) : ℤ)
        = -((-1 : ℤ) ^ j * (eulerian N j : ℤ)) := by
    intro j hj
    rw [mem_range] at hj
    -- palindrome on row N (= 2m ≥ 2 ≥ 1)
    have hpal : eulerian N (N - 1 - j) = eulerian N j := by
      rw [eulerian_palindrome' (by omega : 1 ≤ N) (by omega : N - 1 - j < N)]
      congr 1; omega
    -- sign flip: (−1)^(N−1−j) = −(−1)^j since N−1 is odd
    have hsign : (-1 : ℤ) ^ (N - 1 - j) = -(-1 : ℤ) ^ j := by
      have hodd : Odd (N - 1) := ⟨m - 1, by omega⟩
      have h1 : (-1 : ℤ) ^ (N - 1 - j) * (-1 : ℤ) ^ j = -1 := by
        rw [← pow_add, show (N - 1 - j) + j = N - 1 from by omega, hodd.neg_one_pow]
      have h3 : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
        rw [← pow_add]; exact Even.neg_one_pow ⟨j, rfl⟩
      calc (-1 : ℤ) ^ (N - 1 - j)
            = (-1 : ℤ) ^ (N - 1 - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by rw [h3]; ring
        _ = ((-1 : ℤ) ^ (N - 1 - j) * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ j := by ring
        _ = -1 * (-1 : ℤ) ^ j := by rw [h1]
        _ = -(-1 : ℤ) ^ j := by ring
    rw [hpal, hsign]; ring
  -- reflect the sum, then use the termwise sign flip to get S = −S
  have hpair : S = -S := by
    rw [hS]
    conv_lhs => rw [← Finset.sum_range_reflect (fun k => (-1 : ℤ) ^ k * (eulerian N k : ℤ)) N]
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  -- the goal is `S = 0`; with `S = −S` this is immediate
  linarith

/-! ## Corroboration: palindromy and the tangent-number phenomenon -/

-- Palindromy on concrete rows (rows 4 and 5: `1,11,11,1` and `1,26,66,26,1`).
example : eulerian 4 0 = eulerian 4 3 := by decide
example : eulerian 4 1 = eulerian 4 2 := by decide
example : eulerian 5 1 = eulerian 5 3 := by decide

-- Even-row alternating sums vanish (rows 2, 4, 6).
example : ∑ k ∈ range 2, (-1 : ℤ) ^ k * (eulerian 2 k : ℤ) = 0 := by decide
example : ∑ k ∈ range 4, (-1 : ℤ) ^ k * (eulerian 4 k : ℤ) = 0 := by decide
example : ∑ k ∈ range 6, (-1 : ℤ) ^ k * (eulerian 6 k : ℤ) = 0 := by decide

-- The odd-row alternating sums are the signed tangent (zag) numbers `1, −2, 16, −272`,
-- the Taylor coefficients of `tan x = x + 2·x³/3! + 16·x⁵/5! + 272·x⁷/7! + …`.
example : ∑ k ∈ range 1, (-1 : ℤ) ^ k * (eulerian 1 k : ℤ) = 1 := by decide
example : ∑ k ∈ range 3, (-1 : ℤ) ^ k * (eulerian 3 k : ℤ) = -2 := by decide
example : ∑ k ∈ range 5, (-1 : ℤ) ^ k * (eulerian 5 k : ℤ) = 16 := by decide
example : ∑ k ∈ range 7, (-1 : ℤ) ^ k * (eulerian 7 k : ℤ) = -272 := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ05
