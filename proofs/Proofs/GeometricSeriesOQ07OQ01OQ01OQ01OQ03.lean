/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-03:
# Worpitzky's identity for the combinatorial Eulerian numbers

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01` built the combinatorial Eulerian
numbers `⟨m,j⟩` (`eulerian m j`) from the classical triangle recurrence and identified them with
the coefficients of the Eulerian polynomial.  This entry proves the most celebrated identity
satisfied by those numbers, **Worpitzky's identity**, which expands the monomial `nᵐ` in the
binomial-coefficient basis `C(n+j, m)`:

  **`worpitzky`** :  `nᵐ = ∑_{j=0}^{m} ⟨m,j⟩ · C(n+j, m)`   (an identity of natural numbers).

For example `n² = C(n,2) + C(n+1,2)` (`⟨2,0⟩ = ⟨2,1⟩ = 1`) and
`n³ = C(n,3) + 4·C(n+1,3) + C(n+2,3)` (`⟨3,·⟩ = 1, 4, 1`).

## Method

Induction on `m`.  The heart is a single binomial identity, proved purely over `ℕ`:

  **`worpitzky_term`** :  for `k ≤ m`,
    `(k+1)·C(x+k, m+1) + (m−k)·C(x+k+1, m+1) = x·C(x+k, m)`,

obtained from Pascal's rule `C(a+1, m+1) = C(a, m) + C(a, m+1)` and the absorption identity
`C(a, m+1)·(m+1) = C(a, m)·(a−m)` (we transfer to `ℤ` once, where there is no truncated
subtraction, and close by `linear_combination`).  Re-indexing the order-`m+1` Eulerian row
through its triangle recurrence (the off-diagonal entry `⟨m,m+1⟩ = 0` makes the boundary term
vanish) turns the order-`m+1` Worpitzky sum into `x` times the order-`m` Worpitzky sum, closing
the induction.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ03

open Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## The key absorption identity -/

/-- **The Worpitzky per-term identity.**  For every `x` and every `k ≤ m`,
`(k+1)·C(x+k, m+1) + (m−k)·C(x+k+1, m+1) = x·C(x+k, m)`, an identity of natural numbers.
It is the absorption that drives the inductive step of Worpitzky's identity. -/
theorem worpitzky_term {x k m : ℕ} (hk : k ≤ m) :
    (k + 1) * (x + k).choose (m + 1) + (m - k) * (x + k + 1).choose (m + 1)
      = x * (x + k).choose m := by
  rcases Nat.lt_or_ge (x + k) m with hlt | hge
  · -- `x + k < m`: every binomial in sight vanishes
    rw [Nat.choose_eq_zero_of_lt (by omega : x + k < m + 1),
        Nat.choose_eq_zero_of_lt (by omega : x + k + 1 < m + 1),
        Nat.choose_eq_zero_of_lt hlt]
    ring
  · -- `m ≤ x + k`: transfer to `ℤ` and use Pascal + absorption
    have hpascal : ((x + k + 1).choose (m + 1) : ℤ)
        = ((x + k).choose m : ℤ) + ((x + k).choose (m + 1) : ℤ) := by
      exact_mod_cast Nat.choose_succ_succ (x + k) m
    have habs : ((x + k).choose (m + 1) : ℤ) * ((m : ℤ) + 1)
        = ((x + k).choose m : ℤ) * (((x : ℤ) + k) - m) := by
      have h2 : (((x + k).choose (m + 1) * (m + 1) : ℕ) : ℤ)
          = (((x + k).choose m * ((x + k) - m) : ℕ) : ℤ) := by
        exact_mod_cast Nat.choose_succ_right_eq (x + k) m
      push_cast [Nat.cast_sub hge] at h2
      linear_combination h2
    have key : ((k : ℤ) + 1) * ((x + k).choose (m + 1) : ℤ)
        + ((m : ℤ) - k) * ((x + k + 1).choose (m + 1) : ℤ)
        = (x : ℤ) * ((x + k).choose m : ℤ) := by
      linear_combination ((m : ℤ) - k) * hpascal + habs
    have hgoalℤ :
        (((k + 1) * (x + k).choose (m + 1) + (m - k) * (x + k + 1).choose (m + 1) : ℕ) : ℤ)
          = ((x * (x + k).choose m : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hk]
      linear_combination key
    exact_mod_cast hgoalℤ

/-! ## The Worpitzky sum and its triangle-recurrence reindexing -/

/-- The **Worpitzky sum** `Wₘ(n) = ∑_{j=0}^{m} ⟨m,j⟩ · C(n+j, m)`. -/
def worpitzkySum (m n : ℕ) : ℕ :=
  ∑ j ∈ range (m + 1), eulerian m j * (n + j).choose m

/-- `⟨m,0⟩ = 1` for every `m` (the all-ascending permutation is the unique one with `0` descents). -/
theorem eulerian_zero_left (m : ℕ) : eulerian m 0 = 1 := by
  cases m with
  | zero => rfl
  | succ _ => rfl

/-- **Reindexing the order-`m+1` Worpitzky sum through the Eulerian triangle recurrence.**
`W_{m+1}(n) = ∑_{k=0}^{m} ⟨m,k⟩ · [(k+1)·C(n+k, m+1) + (m−k)·C(n+k+1, m+1)]`. -/
theorem worpitzkySum_succ_eq (m n : ℕ) :
    worpitzkySum (m + 1) n
      = ∑ k ∈ range (m + 1),
          eulerian m k *
            ((k + 1) * (n + k).choose (m + 1) + (m - k) * (n + k + 1).choose (m + 1)) := by
  -- Expand the left-hand side: peel the `j = 0` term, expand the triangle recurrence, split.
  have hL : worpitzkySum (m + 1) n
      = (∑ k ∈ range (m + 1), (k + 2) * eulerian m (k + 1) * (n + k + 1).choose (m + 1))
        + (∑ k ∈ range (m + 1), (m - k) * eulerian m k * (n + k + 1).choose (m + 1))
        + (n).choose (m + 1) := by
    unfold worpitzkySum
    rw [Finset.sum_range_succ' (fun j => eulerian (m + 1) j * (n + j).choose (m + 1)) (m + 1),
        eulerian_succ_zero,
        show (∑ i ∈ range (m + 1), eulerian (m + 1) (i + 1) * (n + (i + 1)).choose (m + 1))
            = ∑ i ∈ range (m + 1),
                ((i + 2) * eulerian m (i + 1) * (n + i + 1).choose (m + 1)
                  + (m - i) * eulerian m i * (n + i + 1).choose (m + 1))
          from Finset.sum_congr rfl fun i _ => by
            rw [eulerian_succ_succ, add_mul, Nat.add_assoc n i 1],
        Finset.sum_add_distrib]
    simp only [one_mul, Nat.add_zero]
  -- Expand the right-hand side: distribute and split.
  have hR : (∑ k ∈ range (m + 1),
              eulerian m k *
                ((k + 1) * (n + k).choose (m + 1) + (m - k) * (n + k + 1).choose (m + 1)))
      = (∑ k ∈ range (m + 1), (k + 1) * eulerian m k * (n + k).choose (m + 1))
        + (∑ k ∈ range (m + 1), (m - k) * eulerian m k * (n + k + 1).choose (m + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- The two `(m−k)`-sums agree; reduce to the shift identity on the remaining sums.
  have hcore :
      (∑ k ∈ range (m + 1), (k + 2) * eulerian m (k + 1) * (n + k + 1).choose (m + 1))
        + (n).choose (m + 1)
      = ∑ k ∈ range (m + 1), (k + 1) * eulerian m k * (n + k).choose (m + 1) := by
    rw [Finset.sum_range_succ' (fun k => (k + 1) * eulerian m k * (n + k).choose (m + 1)) m,
        Finset.sum_range_succ
          (fun k => (k + 2) * eulerian m (k + 1) * (n + k + 1).choose (m + 1)) m,
        eulerian_eq_zero_of_lt (Nat.lt_succ_self m), eulerian_zero_left]
    -- the two `∑ over range m` are defeq termwise: `(k+2)·… (n+k+1)` ≡ `(k+1+1)·… (n+(k+1))`
    have h1 : ∀ k, (k + 2) * eulerian m (k + 1) * (n + k + 1).choose (m + 1)
        = (k + 1 + 1) * eulerian m (k + 1) * (n + (k + 1)).choose (m + 1) := fun _ => rfl
    simp only [h1, Nat.add_zero, Nat.zero_add, mul_zero, zero_mul, mul_one, one_mul]
  rw [hL, hR]
  omega

/-! ## Worpitzky's identity -/

/-- The Worpitzky sum equals the power: `Wₘ(n) = nᵐ`. -/
theorem worpitzkySum_eq_pow (m n : ℕ) : worpitzkySum m n = n ^ m := by
  induction m with
  | zero => simp [worpitzkySum]
  | succ m ih =>
    rw [worpitzkySum_succ_eq]
    have hterm : (∑ k ∈ range (m + 1),
          eulerian m k *
            ((k + 1) * (n + k).choose (m + 1) + (m - k) * (n + k + 1).choose (m + 1)))
        = ∑ k ∈ range (m + 1), eulerian m k * (n * (n + k).choose m) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [worpitzky_term (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    have hfac : (∑ k ∈ range (m + 1), eulerian m k * (n * (n + k).choose m))
        = n * worpitzkySum m n := by
      unfold worpitzkySum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hterm, hfac, ih]
    ring

/-- **Worpitzky's identity.**  Every power expands in the binomial basis with the Eulerian
numbers as coefficients: `nᵐ = ∑_{j=0}^{m} ⟨m,j⟩ · C(n+j, m)`. -/
theorem worpitzky (m n : ℕ) :
    n ^ m = ∑ j ∈ range (m + 1), eulerian m j * (n + j).choose m :=
  (worpitzkySum_eq_pow m n).symm

/-- Since `⟨m,m⟩ = 0` for `m ≥ 1`, the top term drops: for `m ≥ 1`,
`nᵐ = ∑_{j=0}^{m−1} ⟨m,j⟩ · C(n+j, m)`. -/
theorem worpitzky_succ (m n : ℕ) :
    n ^ (m + 1) = ∑ j ∈ range (m + 1), eulerian (m + 1) j * (n + j).choose (m + 1) := by
  rw [worpitzky (m + 1) n, Finset.sum_range_succ]
  rw [eulerian_succ_self, zero_mul, add_zero]

/-! ## Low-order instances

`⟨1,0⟩ = 1`; `⟨2,0⟩ = ⟨2,1⟩ = 1`; `⟨3,·⟩ = 1, 4, 1`. -/

/-- `n² = C(n,2) + C(n+1,2)`. -/
example (n : ℕ) : n ^ 2 = (n).choose 2 + (n + 1).choose 2 := by
  rw [worpitzky 2 n, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [show eulerian 2 0 = 1 from by decide, show eulerian 2 1 = 1 from by decide,
    show eulerian 2 2 = 0 from by decide, one_mul, zero_mul, add_zero]

/-- `n³ = C(n,3) + 4·C(n+1,3) + C(n+2,3)`. -/
example (n : ℕ) :
    n ^ 3 = (n).choose 3 + 4 * (n + 1).choose 3 + (n + 2).choose 3 := by
  rw [worpitzky 3 n, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [show eulerian 3 0 = 1 from by decide, show eulerian 3 1 = 4 from by decide,
    show eulerian 3 2 = 1 from by decide, show eulerian 3 3 = 0 from by decide,
    one_mul, zero_mul, add_zero]

/-- Numeric check: `4³ = 64 = C(4,3) + 4·C(5,3) + C(6,3) = 4 + 40 + 20`. -/
example : (4 : ℕ) ^ 3 = (4).choose 3 + 4 * (5).choose 3 + (6).choose 3 := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ03
