/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-06-oq-01:
# The inverse Eulerian ⇆ Stirling pairing (binomial inversion)

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01-oq-06` proves the **forward**
combinatorial Eulerian → Stirling identity (the per-coefficient dual of Worpitzky),

  `eulerian_stirling` :  `i!·S(n,i) = ∑_{j<n} C(j, n−i)·⟨n,j⟩`   (`1 ≤ n`, `i ≤ n`),

expressing the factorial-weighted Stirling row over the Eulerian row through the *plain*
binomial weights `C(j, n−i)`.  This entry settles the open question `oq-01`: the **inverse
pairing**, recovering the Eulerian numbers from the (factorial-weighted) Stirling row.  Together
the two exhibit the Eulerian and Stirling rows as mutually inverse under the binomial triangle.

## The corrected statement

The open question proposed the inverse as `⟨n,k⟩ = ∑_j (−1)^{k−j}·C(n−j, k−j)·j!·S(n,j)`.
That formula is **incorrect**: e.g. for `n = 3, k = 0` it evaluates to `0`, whereas `⟨3,0⟩ = 1`
(the only surviving term, `j = 0`, carries `0!·S(3,0) = 0`).  The correct binomial inverse — the
genuine inversion of the forward identity above — is

  **`eulerian_inverse`** :  `⟨n,k⟩ = ∑_{i≤n} (−1)^{n−i−k}·C(n−i, k)·i!·S(n,i)`   (`1 ≤ n`, `k ≤ n−1`).

(Verified numerically for all rows `n ≤ 7`; the derivation below is the proof.)

## Proof strategy

The forward identity says `c_i := i!·S(n,i) = ∑_j C(j, n−i)·E_j` with `E_j := ⟨n,j⟩`.  Writing
`m = n−i` this is `f(m) := c_{n−m} = ∑_j C(j, m)·E_j`, the *upper* binomial transform of the
Eulerian row.  Its inverse is governed by the orthogonality of the binomial triangle under the
alternating weight,

  **`binom_ortho`** :  `∑_{m≤N} (−1)^{m−k}·C(m,k)·C(j,m) = [j = k]`   (`j ≤ N`),

proved from the subset-of-a-subset identity `C(j,m)·C(m,k) = C(j,k)·C(j−k, m−k)`
(`Nat.choose_mul`) and the alternating row sum `∑_t (−1)^t·C(j−k, t) = [j = k]`
(`Int.alternating_sum_range_choose`).  Substituting the forward identity into the claimed sum,
swapping the order of summation, and reflecting the index `i ↦ n−i` reduces each inner sum to
`binom_ortho`, collapsing the double sum to the single term `⟨n,k⟩`.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ06

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ06OQ01

open Finset Nat GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## Binomial orthogonality (the inversion kernel) -/

/-- **Orthogonality of the binomial triangle under the alternating weight.**  For `j ≤ N`,
`∑_{m ≤ N} (−1)^{m−k}·C(m,k)·C(j,m) = [j = k]`.  This is the inversion kernel: the matrices
`(C(m,k))` and `((−1)^{m−k} C(m,k))` are mutually inverse, so it expresses that summing a binomial
transform against the signed transform recovers a single coefficient. -/
theorem binom_ortho (N j k : ℕ) (hjN : j ≤ N) :
    ∑ m ∈ range (N + 1), (-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) * (j.choose m : ℤ)
      = if j = k then 1 else 0 := by
  rcases lt_or_ge j k with hjk | hkj
  · -- `j < k`: every term vanishes (`C(m,k)=0` for `m ≤ j`, `C(j,m)=0` for `m > j`)
    rw [if_neg (by omega : ¬ j = k)]
    apply Finset.sum_eq_zero
    intro m _
    rcases le_or_gt m j with hmj | hmj
    · rw [Nat.choose_eq_zero_of_lt (by omega : m < k)]; ring
    · rw [Nat.choose_eq_zero_of_lt hmj]; ring
  · -- `k ≤ j`: split off the low terms `m < k`, reindex `m = k + t`, apply `Nat.choose_mul`
    have hsplit : range (N + 1) = range k ∪ Ico k (N + 1) := by
      rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    rw [hsplit, Finset.sum_union (by
      rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 k (N + 1))]
    -- the `range k` part is zero
    have hlow : ∑ m ∈ range k, (-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) * (j.choose m : ℤ) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [mem_range] at hm
      rw [Nat.choose_eq_zero_of_lt hm]; ring
    rw [hlow, zero_add]
    -- reindex `Ico k (N+1)` as `m = k + t`, `t ∈ range (N+1-k)`
    rw [Finset.sum_Ico_eq_sum_range]
    have hN1 : N + 1 - k = (j - k) + 1 + (N - j) := by omega
    -- rewrite each summand using the subset-of-subset identity
    have hterm : ∀ t ∈ range (N + 1 - k),
        (-1 : ℤ) ^ (k + t - k) * ((k + t).choose k : ℤ) * (j.choose (k + t) : ℤ)
          = (j.choose k : ℤ) * ((-1 : ℤ) ^ t * ((j - k).choose t : ℤ)) := by
      intro t _
      have hcm : j.choose (k + t) * (k + t).choose k
          = j.choose k * (j - k).choose ((k + t) - k) := Nat.choose_mul (by omega)
      have hkt : (k + t) - k = t := by omega
      rw [hkt] at hcm
      have hexp : k + t - k = t := by omega
      rw [hexp]
      have hcast2 : ((k + t).choose k : ℤ) * (j.choose (k + t) : ℤ)
          = (j.choose k : ℤ) * ((j - k).choose t : ℤ) := by
        have h2 := congrArg (Nat.cast : ℕ → ℤ) hcm
        push_cast at h2
        linear_combination h2
      linear_combination ((-1 : ℤ) ^ t) * hcast2
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    -- extend the alternating sum to the full row `range (j-k+1)` (extra terms vanish)
    have hext : ∑ t ∈ range (N + 1 - k), (-1 : ℤ) ^ t * ((j - k).choose t : ℤ)
        = ∑ t ∈ range ((j - k) + 1), (-1 : ℤ) ^ t * ((j - k).choose t : ℤ) := by
      rw [hN1, ← Finset.sum_range_add_sum_Ico _ (by omega : (j - k) + 1 ≤ (j - k) + 1 + (N - j))]
      have : ∑ t ∈ Ico ((j - k) + 1) ((j - k) + 1 + (N - j)),
          (-1 : ℤ) ^ t * ((j - k).choose t : ℤ) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_Ico] at ht
        rw [Nat.choose_eq_zero_of_lt (by omega : j - k < t)]; ring
      rw [this, add_zero]
    rw [hext, Int.alternating_sum_range_choose]
    rcases eq_or_ne j k with hjk | hjk
    · subst hjk; simp
    · rw [if_neg (by omega : ¬ j - k = 0), if_neg (by omega : ¬ j = k), mul_zero]

/-! ## The inverse pairing -/

/-- **The inverse Eulerian ⇆ Stirling pairing.**  For `1 ≤ n` and `k ≤ n−1`,
`⟨n,k⟩ = ∑_{i≤n} (−1)^{n−i−k}·C(n−i, k)·i!·S(n,i)`, where `⟨n,k⟩ = eulerian n k` is the
combinatorial Eulerian number and `S(n,i) = stirlingSecond n i` the Stirling number of the second
kind.  This is the binomial inverse of the forward identity `eulerian_stirling`; together they
exhibit the two rows as mutually inverse under the binomial triangle. -/
theorem eulerian_inverse (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    (eulerian n k : ℤ)
      = ∑ i ∈ range (n + 1),
          (-1 : ℤ) ^ (n - i - k) * ((n - i).choose k : ℤ) * (i ! * stirlingSecond n i : ℤ) := by
  symm
  -- substitute the forward identity `i!·S(n,i) = ∑_{j<n} C(j,n−i)·⟨n,j⟩` (cast to ℤ)
  have hsub : ∀ i ∈ range (n + 1),
      (-1 : ℤ) ^ (n - i - k) * ((n - i).choose k : ℤ) * (i ! * stirlingSecond n i : ℤ)
        = ∑ j ∈ range n,
            (-1 : ℤ) ^ (n - i - k) * ((n - i).choose k : ℤ) * (j.choose (n - i) : ℤ)
              * (eulerian n j : ℤ) := by
    intro i hi
    rw [mem_range] at hi
    have hfwd := GeometricSeriesOQ07OQ01OQ01OQ01OQ06.eulerian_stirling n i hn (by omega)
    have hcast : (i ! * stirlingSecond n i : ℤ)
        = ∑ j ∈ range n, (j.choose (n - i) : ℤ) * (eulerian n j : ℤ) := by
      have := congrArg (Nat.cast : ℕ → ℤ) hfwd
      push_cast at this
      exact this
    rw [hcast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
  -- for each `j`, factor `⟨n,j⟩` out and reflect the index `i ↦ n − i`
  have hinner : ∀ j ∈ range n,
      ∑ i ∈ range (n + 1),
          (-1 : ℤ) ^ (n - i - k) * ((n - i).choose k : ℤ) * (j.choose (n - i) : ℤ)
            * (eulerian n j : ℤ)
        = (eulerian n j : ℤ) * (if j = k then 1 else 0) := by
    intro j hj
    rw [mem_range] at hj
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    -- reflect: ∑_i g(n−i) = ∑_m g(m), with g(m) = (−1)^{m−k} C(m,k) C(j,m)
    rw [← binom_ortho n j k (by omega)]
    rw [← Finset.sum_range_reflect
      (fun m => (-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) * (j.choose m : ℤ)) (n + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have : n + 1 - 1 - i = n - i := by omega
    rw [this]
  rw [Finset.sum_congr rfl hinner]
  -- collapse: ∑_{j<n} ⟨n,j⟩·[j=k] = ⟨n,k⟩
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (range n) k (fun j => (eulerian n j : ℤ)),
    if_pos (mem_range.mpr (by omega))]

/-! ## Corroboration on concrete rows -/

-- `⟨3,1⟩ = 4 = ∑_{i≤3} (−1)^{3−i−1}·C(3−i,1)·i!·S(3,i)`.
example : (eulerian 3 1 : ℤ)
    = ∑ i ∈ range 4, (-1 : ℤ) ^ (3 - i - 1) * ((3 - i).choose 1 : ℤ)
        * (i ! * stirlingSecond 3 i : ℤ) := by decide

-- `⟨4,1⟩ = 11`.
example : (eulerian 4 1 : ℤ)
    = ∑ i ∈ range 5, (-1 : ℤ) ^ (4 - i - 1) * ((4 - i).choose 1 : ℤ)
        * (i ! * stirlingSecond 4 i : ℤ) := by decide

-- `⟨4,2⟩ = 11`.
example : (eulerian 4 2 : ℤ)
    = ∑ i ∈ range 5, (-1 : ℤ) ^ (4 - i - 2) * ((4 - i).choose 2 : ℤ)
        * (i ! * stirlingSecond 4 i : ℤ) := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ06OQ01
