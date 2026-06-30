/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-04:
# The explicit closed form for the Eulerian numbers

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01` built the combinatorial Eulerian
numbers `⟨m,k⟩` (`eulerian m k`) from the classical triangle recurrence
`⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩`, `⟨m,0⟩ = 1`, and identified them with the coefficients
of the Eulerian polynomial.  Worpitzky's identity (`...-oq-03`) expands `nᵐ` in the binomial
basis.  This entry proves the celebrated **explicit closed form** that solves the triangle
recurrence outright — a single alternating binomial sum, with no recursion:

  **`eulerian_explicit`** :  `⟨m,k⟩ = ∑_{j=0}^{k} (−1)ʲ · C(m+1, j) · (k+1−j)ᵐ`   (over `ℤ`).

For example `⟨2,1⟩ = C(3,0)·2² − C(3,1)·1² = 4 − 3 = 1` and
`⟨3,1⟩ = C(4,0)·2³ − C(4,1)·1³ = 8 − 4 = 4`, matching the rows `1,1` and `1,4,1`.

## Method

Write `A(m,k) := ∑_{j=0}^{k} (−1)ʲ·C(m+1,j)·(k+1−j)ᵐ` (`eulExpl`).  We prove `⟨m,k⟩ = A(m,k)` by
induction on `m`, by showing `A` satisfies the *same* defining recurrence and boundary values as
`eulerian`.  The boundary cases `A(m,0) = 1` and `A(0,k) = [k=0]` are direct.  The heart is the
recurrence (`eulExpl_recurrence`)

  `A(m+1,k+1) = (k+2)·A(m,k+1) + (m−k)·A(m,k)`,

proved purely over `ℤ`.  Splitting `C(m+2,j)` by Pascal's rule and `(k+2−j)^{m+1}` as
`(k+2−j)·(k+2−j)ᵐ`, then applying the absorption identity `j·C(m+1,j) = (m+1)·C(m,j−1)` and a
single index shift `j ↦ j+1`, collapses the order-`m+1` sum into the order-`m` sums.  The residual
combinatorial fact is the clean Pascal identity (`eulExpl_pascal_step`)

  `∑_{i=0}^{k}(−1)ⁱC(m,i)(k+1−i)ᵐ − ∑_{i=0}^{k−1}(−1)ⁱC(m,i)(k−i)ᵐ = A(m,k)`,

itself just `C(m+1,j) = C(m,j) + C(m,j−1)` re-summed.  Because the integer coefficient `(m−k)`
agrees with the natural-number `(m−k)` exactly when `eulerian m k ≠ 0`, the integer recurrence
transfers to `eulerian`'s `ℕ`-truncated one.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ04

open Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-- The explicit alternating-binomial sum for the Eulerian numbers, as an integer:
`A(m,k) = ∑_{j=0}^{k} (−1)ʲ · C(m+1,j) · (k+1−j)ᵐ`. -/
def eulExpl (m k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ m

/-! ## Boundary values -/

theorem eulExpl_zero_right (m : ℕ) : eulExpl m 0 = 1 := by
  simp [eulExpl]

theorem eulExpl_zero_left (k : ℕ) : eulExpl 0 k = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [eulExpl]
  · rw [if_neg (by omega)]
    -- every factor `(k+1-j)^0 = 1`, and `C(1,j) = 0` for `j ≥ 2`
    have hsub : range 2 ⊆ range (k + 1) := by
      intro x hx; simp only [Finset.mem_range] at *; omega
    have hkey : eulExpl 0 k
        = ∑ j ∈ range 2, (-1) ^ j * ((0 + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ 0 := by
      rw [eulExpl]
      refine (Finset.sum_subset hsub ?_).symm
      intro x _ hx
      have hx2 : 2 ≤ x := by rwa [Finset.mem_range, not_lt] at hx
      rw [Nat.choose_eq_zero_of_lt (show (0 : ℕ) + 1 < x by omega)]
      simp
    rw [hkey]
    simp [Finset.sum_range_succ]

/-! ## A Pascal re-summation identity

`∑_{i=0}^{k}(−1)ⁱC(m,i)(k+1−i)ᵐ − ∑_{i=0}^{k−1}(−1)ⁱC(m,i)(k−i)ᵐ = A(m,k)`, obtained from
`C(m+1,i+1) = C(m,i) + C(m,i+1)` after peeling the leading term of each sum. -/
theorem eulExpl_pascal_step (m k : ℕ) :
    (∑ i ∈ range (k + 1), (-1) ^ i * (m.choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ m)
      - (∑ i ∈ range k, (-1) ^ i * (m.choose i : ℤ) * ((k - i : ℕ) : ℤ) ^ m)
      = eulExpl m k := by
  -- Peel the leading term off `A` (the order-`m` sum over `range (k+1)`).
  have hA : (∑ i ∈ range (k + 1), (-1) ^ i * (m.choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ m)
      = (∑ i ∈ range k, -((-1) ^ i * (m.choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ m))
          + ((k + 1 : ℕ) : ℤ) ^ m := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.succ_sub_succ]; ring
    · simp
  -- Peel the leading term off `S = eulExpl m k`.
  have hS : eulExpl m k
      = (∑ i ∈ range k, -((-1) ^ i * ((m + 1).choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ m))
          + ((k + 1 : ℕ) : ℤ) ^ m := by
    rw [eulExpl, Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.succ_sub_succ]; ring
    · simp
  rw [hA, hS]
  -- the two leading `(k+1)ᵐ` cancel; the order-`k` sums match termwise by Pascal
  have hcomb :
      (∑ i ∈ range k, -((-1) ^ i * (m.choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ m))
        - (∑ i ∈ range k, (-1) ^ i * (m.choose i : ℤ) * ((k - i : ℕ) : ℤ) ^ m)
        = ∑ i ∈ range k, -((-1) ^ i * ((m + 1).choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ m) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.choose_succ_succ m i]
    push_cast
    ring
  linarith [hcomb]

/-! ## Absorption and the absorbed alternating sum -/

/-- Absorption identity `(i+1)·C(m+1,i+1) = (m+1)·C(m,i)` over `ℤ`. -/
private theorem habsorb (m i : ℕ) :
    ((i : ℤ) + 1) * ((m + 1).choose (i + 1) : ℤ) = ((m : ℤ) + 1) * (m.choose i : ℤ) := by
  have h := Nat.add_one_mul_choose_eq m i
  have h2 : (((m + 1) * m.choose i : ℕ) : ℤ) = (((m + 1).choose (i + 1) * (i + 1) : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at h2
  linear_combination h2.symm

/-- The alternating sum weighted by `j` collapses, via absorption and an index shift, to
`−(m+1)` times an order-`m` alternating sum. -/
private theorem absorbed_sum (m N : ℕ) :
    (∑ j ∈ range (N + 1), (j : ℤ) * ((-1) ^ j * ((m + 1).choose j : ℤ) * ((N + 1 - j : ℕ) : ℤ) ^ m))
      = -((m : ℤ) + 1) * (∑ i ∈ range N, (-1) ^ i * (m.choose i : ℤ) * ((N - i : ℕ) : ℤ) ^ m) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.succ_sub_succ]
  push_cast
  linear_combination (-(-1 : ℤ) ^ i * ((N - i : ℕ) : ℤ) ^ m) * habsorb m i

/-! ## The core recurrence -/

theorem eulExpl_recurrence (m k : ℕ) :
    eulExpl (m + 1) (k + 1)
      = (k + 2) * eulExpl m (k + 1) + ((m : ℤ) - k) * eulExpl m k := by
  -- Split `(k+2−j)^{m+1}` and re-sum the order-`m+1` numerator over `range (k+2)`.
  have hstep1 :
      (∑ j ∈ range (k + 1 + 1),
          (-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ (m + 1))
        = (k + 2) * eulExpl m (k + 1)
          - (∑ j ∈ range (k + 1 + 1),
              (j : ℤ) * ((-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ m)) := by
    rw [eulExpl, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjk : j < k + 1 + 1 := Finset.mem_range.mp hj
    have hb : ((k + 1 + 1 - j : ℕ) : ℤ) = (k : ℤ) + 2 - (j : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [pow_succ]
    linear_combination
      ((-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ m) * hb
  -- Same split for the order-`m+1` sum over `range (k+1)`.
  have hstep2 :
      (∑ i ∈ range (k + 1),
          (-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
        = (k + 1) * eulExpl m k
          - (∑ i ∈ range (k + 1),
              (i : ℤ) * ((-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ m)) := by
    rw [eulExpl, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i < k + 1 := Finset.mem_range.mp hi
    have hb : ((k + 1 - i : ℕ) : ℤ) = (k : ℤ) + 1 - (i : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [pow_succ]
    linear_combination
      ((-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ m) * hb
  -- Now collapse the weighted sums via `absorbed_sum`.
  have hS1 :
      (∑ j ∈ range (k + 1 + 1),
          (-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ (m + 1))
        = (k + 2) * eulExpl m (k + 1)
          + ((m : ℤ) + 1)
            * (∑ i ∈ range (k + 1), (-1) ^ i * (m.choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ m) := by
    rw [hstep1, absorbed_sum m (k + 1)]; ring
  have hS2 :
      (∑ i ∈ range (k + 1),
          (-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
        = (k + 1) * eulExpl m k
          + ((m : ℤ) + 1)
            * (∑ i ∈ range k, (-1) ^ i * (m.choose i : ℤ) * ((k - i : ℕ) : ℤ) ^ m) := by
    rw [hstep2, absorbed_sum m k]; ring
  -- Pascal on `C(m+2,j)` writes the numerator as `S1 − S2`.
  have hP :
      eulExpl (m + 1) (k + 1)
        = (∑ j ∈ range (k + 1 + 1),
            (-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ (m + 1))
          - (∑ i ∈ range (k + 1),
              (-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1)) := by
    have e1 :
        eulExpl (m + 1) (k + 1)
          = (∑ i ∈ range (k + 1),
              (-1) ^ (i + 1) * ((m + 1 + 1).choose (i + 1) : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
            + ((k + 1 + 1 : ℕ) : ℤ) ^ (m + 1) := by
      rw [eulExpl, Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_); rw [Nat.succ_sub_succ]
      · simp
    have e2 :
        (∑ j ∈ range (k + 1 + 1),
            (-1) ^ j * ((m + 1).choose j : ℤ) * ((k + 1 + 1 - j : ℕ) : ℤ) ^ (m + 1))
          = (∑ i ∈ range (k + 1),
              (-1) ^ (i + 1) * ((m + 1).choose (i + 1) : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
            + ((k + 1 + 1 : ℕ) : ℤ) ^ (m + 1) := by
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_); rw [Nat.succ_sub_succ]
      · simp
    rw [e1, e2]
    have hterm :
        (∑ i ∈ range (k + 1),
            (-1) ^ (i + 1) * ((m + 1 + 1).choose (i + 1) : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
          = (∑ i ∈ range (k + 1),
              (-1) ^ (i + 1) * ((m + 1).choose (i + 1) : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1))
            - (∑ i ∈ range (k + 1),
                (-1) ^ i * ((m + 1).choose i : ℤ) * ((k + 1 - i : ℕ) : ℤ) ^ (m + 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.choose_succ_succ (m + 1) i]
      push_cast
      ring
    linarith [hterm]
  linear_combination hP + hS1 - hS2 + ((m : ℤ) + 1) * eulExpl_pascal_step m k

/-! ## The explicit formula -/

theorem eulerian_explicit (m k : ℕ) : (eulerian m k : ℤ) = eulExpl m k := by
  induction m generalizing k with
  | zero =>
    rw [eulExpl_zero_left]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [eulerian_zero_succ]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [eulExpl_zero_right]; simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      -- reconcile the `ℕ`-truncated `(m - k)` with the integer `(m : ℤ) - k`
      have hcast : ((m - k : ℕ) : ℤ) * (eulerian m k : ℤ) = ((m : ℤ) - k) * (eulerian m k : ℤ) := by
        rcases le_or_gt k m with h | h
        · rw [Nat.cast_sub h]
        · rw [eulerian_eq_zero_of_lt h]; simp
      rw [eulExpl_recurrence, ← ih (k + 1), ← ih k, eulerian_succ_succ]
      push_cast
      rw [hcast]

/-! ## Worked examples

The closed form reproduces the Eulerian rows `1, 1` (order 2), `1, 4, 1` (order 3) and
`1, 11, 11, 1` (order 4). -/

/-- `⟨2,1⟩ = C(3,0)·2² − C(3,1)·1² = 4 − 3 = 1`. -/
example : (eulerian 2 1 : ℤ) = 1 := by rw [eulerian_explicit]; decide

/-- `⟨3,1⟩ = C(4,0)·2³ − C(4,1)·1³ = 8 − 4 = 4`. -/
example : (eulerian 3 1 : ℤ) = 4 := by rw [eulerian_explicit]; decide

/-- `⟨4,2⟩ = C(5,0)·3⁴ − C(5,1)·2⁴ + C(5,2)·1⁴ = 81 − 80 + 10 = 11`. -/
example : (eulerian 4 2 : ℤ) = 11 := by rw [eulerian_explicit]; decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ04
