/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-06:
# The combinatorial Eulerian → Stirling identity

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01` builds the combinatorial
**Eulerian numbers** `⟨n,k⟩` (`eulerian n k`) from the triangle recurrence
`⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩`, and identifies them with the coefficients of the
Eulerian polynomial.  At the *polynomial* level it also records `stirlingForm_eq_eulerianNumbers`,
linking the Stirling numbers `S(n,k) = stirlingSecond n k` to the Eulerian row.  Siblings settled
Worpitzky's identity (`oq-03`), the explicit closed form (`oq-04`), and the combinatorial
palindromy (`oq-05`).

This entry settles `oq-06`: the **combinatorial Eulerian → Stirling identity**, the per-coefficient
companion of Worpitzky's identity,

  **`eulerian_stirling`** :  `i!·S(n,i) = ∑_{j<n} C(j, n−i)·⟨n,j⟩`   (for `1 ≤ n`, `i ≤ n`).

Worpitzky (`oq-03`) expands a power `xⁿ` over the Eulerian row using the *ascending* binomial
weights `C(x+j, n)`; this identity is its dual, expanding `i!·S(n,i)` — the number of surjections
from an `n`-set onto an `i`-set — over the same Eulerian row using the *plain* binomial weights
`C(j, n−i)`.  Equivalently, applying Vandermonde's convolution to Worpitzky and matching the
binomial basis `C(x,i)` of `xⁿ = ∑ᵢ i!·S(n,i)·C(x,i)` gives exactly this pairing.

The proof is self-contained and elementary: induction on the row `n`, reducing the inductive step —
via the Stirling recurrence `S(n+1,i) = i·S(n,i) + S(n,i−1)` and the Eulerian triangle recurrence —
to a single **per-term binomial identity** (`term_binom`) that follows from Pascal's rule together
with the absorption identity `C(j,d)·d = C(j,d−1)·(j−d+1)`.  The top corner uses the Worpitzky row
sum `∑_{j<n} ⟨n,j⟩ = n!` (`oq-01`).

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ06

open Finset Nat GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## The per-term binomial identity -/

/-- The per-term binomial identity driving the inductive step.  For `i' ≤ n` and `j ≤ n`,
writing `d = n+1−i'` (so `d−1 = n−i'`):
`(j+1)·C(j,d) + (n+1−j)·C(j+1,d) = (i'+1)·C(j,d−1) + (i'+1)·C(j,d)`.
It follows from Pascal's rule `C(j+1,d) = C(j,d−1) + C(j,d)` and the absorption identity
`C(j,d)·d = C(j,d−1)·(j−(d−1))`. -/
private theorem term_binom (n i' j : ℕ) (hi' : i' ≤ n) (hj : j ≤ n) :
    (j + 1) * j.choose (n + 1 - i') + (n + 1 - j) * (j + 1).choose (n + 1 - i')
      = (i' + 1) * j.choose (n - i') + (i' + 1) * j.choose (n + 1 - i') := by
  -- write the upper index as `(n - i') + 1` and apply Pascal
  have hd : n + 1 - i' = (n - i') + 1 := by omega
  rw [hd, Nat.choose_succ_succ j (n - i')]
  rcases Nat.lt_or_ge j (n - i') with hlt | hge
  · -- both binomials vanish (the lower index exceeds `j`)
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega : j < n - i' + 1)]
    ring
  · -- genuine subtraction; transfer the absorption identity to ℤ
    have habs : j.choose ((n - i') + 1) * ((n - i') + 1) = j.choose (n - i') * (j - (n - i')) :=
      Nat.choose_succ_right_eq j (n - i')
    zify [hge, hi'] at habs
    zify [show j ≤ n + 1 from by omega]
    linear_combination habs

/-! ## The Eulerian → Stirling identity -/

/-- Regrouping the Eulerian recurrence inside a binomial-weighted row sum.  For every `m` and
every fixed lower index `d ≥ 1`,
`∑_{j<m+1} C(j,d)·⟨m+1,j⟩ = ∑_{j<m} ⟨m,j⟩·((j+1)·C(j,d) + (m−j)·C(j+1,d))`.
The corner terms `C(0,d) = 0` (as `d ≥ 1`) and `⟨m,m⟩ = 0` make the index shift exact. -/
private theorem row_regroup (m d : ℕ) (hd : 1 ≤ d) :
    ∑ j ∈ range (m + 1), j.choose d * eulerian (m + 1) j
      = ∑ j ∈ range m, eulerian m j * ((j + 1) * j.choose d + (m - j) * (j + 1).choose d) := by
  -- peel the `j = 0` term (which vanishes since `C(0,d) = 0`) and expand the recurrence
  rw [Finset.sum_range_succ']
  have hzero : (0 : ℕ).choose d = 0 := Nat.choose_eq_zero_of_lt hd
  simp only [hzero, Nat.zero_mul, add_zero]
  -- substitute the Eulerian triangle recurrence in each remaining term
  have hstep : ∀ k ∈ range m,
      (k + 1).choose d * eulerian (m + 1) (k + 1)
        = (k + 1).choose d * (k + 2) * eulerian m (k + 1)
          + (k + 1).choose d * (m - k) * eulerian m k := by
    intro k _
    rw [eulerian_succ_succ]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  -- the second sum is already in the desired `B` shape
  -- the first sum `A'` reindexes `k ↦ k+1`
  have hA : ∑ k ∈ range m, (k + 1).choose d * (k + 2) * eulerian m (k + 1)
      = ∑ j ∈ range m, (j + 1) * j.choose d * eulerian m j := by
    -- define h j = (j+1)·C(j,d)·⟨m,j⟩; then the LHS is ∑_{k<m} h (k+1)
    have key : ∀ k ∈ range m,
        (k + 1).choose d * (k + 2) * eulerian m (k + 1)
          = ((k + 1) + 1) * (k + 1).choose d * eulerian m (k + 1) := by
      intro k _; ring
    rw [Finset.sum_congr rfl key]
    -- ∑_{k<m} h (k+1) = ∑_{j<m+1} h j (since h 0 = 0) ... = ∑_{j<m} h j (since h m = 0)
    have hshift : ∑ k ∈ range m, ((k + 1) + 1) * (k + 1).choose d * eulerian m (k + 1)
        = ∑ j ∈ range (m + 1), (j + 1) * j.choose d * eulerian m j - 0 := by
      rw [Finset.sum_range_succ']
      have h0 : (0 : ℕ).choose d = 0 := Nat.choose_eq_zero_of_lt hd
      simp [h0]
    rw [hshift, Nat.sub_zero, Finset.sum_range_succ]
    -- the top term `h m = (m+1)·C(m,d)·⟨m,m⟩` vanishes: ⟨m,m⟩ = 0 (m ≥ 1) or C(0,d)=0 (m=0)
    have htop : (m + 1) * m.choose d * eulerian m m = 0 := by
      cases m with
      | zero => simp [Nat.choose_eq_zero_of_lt hd]
      | succ p => rw [eulerian_succ_self]; ring
    rw [htop, add_zero]
  rw [hA]
  -- combine A' and B termwise
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **The combinatorial Eulerian → Stirling identity** (row-`n+1` form, by induction on the row).
For `i ≤ n+1`:  `i!·S(n+1,i) = ∑_{j<n+1} C(j, n+1−i)·⟨n+1,j⟩`. -/
private theorem eulerian_stirling_succ :
    ∀ (n i : ℕ), i ≤ n + 1 →
      i ! * stirlingSecond (n + 1) i
        = ∑ j ∈ range (n + 1), j.choose (n + 1 - i) * eulerian (n + 1) j := by
  intro n
  induction n with
  | zero =>
    intro i hi
    interval_cases i
    · decide
    · decide
  | succ n ih =>
    intro i hi
    rcases i with _ | i'
    · -- i = 0:  both sides vanish
      rw [Nat.factorial_zero, one_mul, stirlingSecond_succ_zero]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      rw [mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
    · rcases Nat.lt_or_ge (i' + 1) (n + 2) with hlt | hge
      · -- main case: 1 ≤ i = i'+1 ≤ n+1
        have hi'n : i' ≤ n := by omega
        -- Stirling recurrence: S(n+2, i'+1) = (i'+1)·S(n+1,i'+1) + S(n+1,i')
        rw [stirlingSecond_succ_succ (n + 1) i']
        -- expand the factorial-weighted Stirling combination using the IH on row n+1
        have hG1 : (i' + 1) ! * stirlingSecond (n + 1) (i' + 1)
            = ∑ j ∈ range (n + 1), j.choose (n - i') * eulerian (n + 1) j := by
          have := ih (i' + 1) (by omega)
          have he : n + 1 - (i' + 1) = n - i' := by omega
          rwa [he] at this
        have hG0 : i' ! * stirlingSecond (n + 1) i'
            = ∑ j ∈ range (n + 1), j.choose (n + 1 - i') * eulerian (n + 1) j := ih i' (by omega)
        -- LHS = (i'+1)·G(n+1,i'+1) + (i'+1)·G(n+1,i')
        have hLHS : (i' + 1) ! * ((i' + 1) * stirlingSecond (n + 1) (i' + 1)
              + stirlingSecond (n + 1) i')
            = (i' + 1) * (∑ j ∈ range (n + 1), j.choose (n - i') * eulerian (n + 1) j)
              + (i' + 1) * (∑ j ∈ range (n + 1), j.choose (n + 1 - i') * eulerian (n + 1) j) := by
          have hfac : (i' + 1) ! = (i' + 1) * i' ! := Nat.factorial_succ i'
          rw [mul_add]
          congr 1
          · rw [← hG1]; rw [hfac]; ring
          · rw [← hG0]; rw [hfac]; ring
        rw [hLHS]
        -- RHS: regroup row n+2 via `row_regroup` with d = n+1-i'
        have hidx : n + 2 - (i' + 1) = n + 1 - i' := by omega
        rw [hidx]
        rw [row_regroup (n + 1) (n + 1 - i') (by omega)]
        -- now match termwise
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mem_range] at hj
        have htb := term_binom n i' j hi'n (by omega)
        -- htb : (j+1)·C(j,n+1-i') + (n+1-j)·C(j+1,n+1-i')
        --        = (i'+1)·C(j,n-i') + (i'+1)·C(j,n+1-i')
        -- goal: ⟨n+1,j⟩·((j+1)·C(j,d) + (n+1-j)·C(j+1,d))
        --        = (i'+1)·(C(j,n-i')·⟨n+1,j⟩) + (i'+1)·(C(j,n+1-i')·⟨n+1,j⟩)
        rw [htb]; ring
      · -- top corner: i = n+2
        have hi2 : i' = n + 1 := by omega
        subst hi2
        rw [Nat.sub_self, stirlingSecond_self]
        -- LHS = (n+2)!
        rw [mul_one]
        -- RHS = ∑_{j<n+2} C(j,0)·⟨n+2,j⟩ = ∑_{j<n+2} ⟨n+2,j⟩ = (n+2)!
        have hchoose : ∀ j ∈ range (n + 2), j.choose 0 * eulerian (n + 2) j = eulerian (n + 2) j := by
          intro j _; rw [Nat.choose_zero_right, Nat.one_mul]
        rw [Finset.sum_congr rfl hchoose]
        -- relate to the Worpitzky row sum on row n+2
        have hrow := GeometricSeriesOQ07OQ01OQ01OQ01OQ01.eulerian_row_sum (n + 2)
        rw [Finset.sum_range_succ] at hrow
        rw [eulerian_succ_self] at hrow
        rw [add_zero] at hrow
        exact hrow.symm

/-- **The combinatorial Eulerian → Stirling identity.**  For `1 ≤ n` and `i ≤ n`,
`i!·S(n,i) = ∑_{j<n} C(j, n−i)·⟨n,j⟩`, where `S(n,i) = stirlingSecond n i` is the Stirling number
of the second kind (the number of partitions of an `n`-set into `i` blocks) and `⟨n,j⟩` is the
combinatorial Eulerian number.  This is the per-coefficient dual of Worpitzky's identity. -/
theorem eulerian_stirling (n i : ℕ) (hn : 1 ≤ n) (hin : i ≤ n) :
    i ! * stirlingSecond n i = ∑ j ∈ range n, j.choose (n - i) * eulerian n j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact eulerian_stirling_succ m i hin

/-! ## Corroboration on concrete rows -/

-- `2!·S(3,2) = 2·3 = 6 = ∑_{j<3} C(j,1)·⟨3,j⟩ = C(0,1)·1 + C(1,1)·4 + C(2,1)·1 = 0+4+2`.
example : 2 ! * stirlingSecond 3 2 = ∑ j ∈ range 3, j.choose (3 - 2) * eulerian 3 j := by decide

-- `1!·S(3,1) = 1 = ∑_{j<3} C(j,2)·⟨3,j⟩ = C(2,2)·⟨3,2⟩ = 1`.
example : 1 ! * stirlingSecond 3 1 = ∑ j ∈ range 3, j.choose (3 - 1) * eulerian 3 j := by decide

-- `3!·S(3,3) = 6 = ∑_{j<3} C(j,0)·⟨3,j⟩ = 1+4+1` (the row sum).
example : 3 ! * stirlingSecond 3 3 = ∑ j ∈ range 3, j.choose (3 - 3) * eulerian 3 j := by decide

-- Row 4:  `2!·S(4,2) = 2·7 = 14 = ∑_{j<4} C(j,2)·⟨4,j⟩ = C(2,2)·11 + C(3,2)·1 = 11+3`.
example : 2 ! * stirlingSecond 4 2 = ∑ j ∈ range 4, j.choose (4 - 2) * eulerian 4 j := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ06
