/-
Erdős Problem #220 (follow-up OQ-01): A matching LOWER bound for the squared gaps
between reduced residues.

Source: https://erdosproblems.com/220
Parent: Proofs/Erdos220Problem.lean (Montgomery–Vaughan upper bound, axiomatized)

Background:
Let n ≥ 2 and let 1 = a₁ < a₂ < ⋯ < a_{φ(n)} = n-1 be the reduced residues mod n,
i.e. the integers in [1, n-1] coprime to n.  Montgomery and Vaughan (1986) proved the
hard UPPER bound
        ∑_{k} (a_{k+1} - a_k)² ≪ n²/φ(n).
The parent entry states this as an axiom (the proof is genuinely analytic).

This file supplies the EASY but complementary LOWER bound, which the parent only
gestured at in its "Observation" comments and never proved:
        ∑_{k} (a_{k+1} - a_k)² ≥ (n-2)²/(φ(n)-1).
Since (n-2)²/(φ(n)-1) ≍ n²/φ(n), the two bounds together show that the
Montgomery–Vaughan bound is TIGHT IN ORDER:
        ∑_{k} (a_{k+1} - a_k)² ≍ n²/φ(n).

The mechanism is elementary and self-contained:

  • The φ(n)-1 gaps telescope: their sum is a_{φ(n)} - a₁ = (n-1) - 1 = n - 2.
  • The Cauchy–Schwarz / Chebyshev inequality (∑ gᵢ)² ≤ m · ∑ gᵢ²
    (`Finset.sq_sum_le_card_mul_sum_sq`) with m = φ(n)-1 gaps then forces
        (n-2)² ≤ (φ(n)-1) · ∑ gᵢ².

Everything below is proved with no `axiom`, no `sorry`, and no `native_decide`.

References:
- [MoVa86] Montgomery, Vaughan, "On the distribution of reduced residues",
           Ann. of Math. (2) 123 (1986), 311-333.
- [Er73]   Erdős posed the general γ ≥ 1 version.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Nat

namespace Erdos220OQ01

/-!
## Part I: Reduced residues and their cardinality
-/

/-- The reduced residues modulo `n`: integers in `[1, n-1]` coprime to `n`. -/
def reducedResidues (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun m => 1 ≤ m ∧ Nat.Coprime m n)

@[simp] theorem mem_reducedResidues {n m : ℕ} :
    m ∈ reducedResidues n ↔ m < n ∧ 1 ≤ m ∧ Nat.Coprime m n := by
  simp [reducedResidues, Finset.mem_filter, Finset.mem_range]

/-- For `n ≥ 2` the reduced residues are exactly `φ(n)` in number.
(The `1 ≤ m` clause only removes `m = 0`, which is already excluded since
`gcd 0 n = n ≠ 1`.) -/
theorem card_reducedResidues {n : ℕ} (hn : 2 ≤ n) :
    (reducedResidues n).card = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime, reducedResidues]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨_, hc⟩
    exact Nat.coprime_comm.mp hc
  · intro hc
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0
        rw [Nat.coprime_zero_right] at hc
        omega
      · exact h0
    exact ⟨hx1, Nat.coprime_comm.mp hc⟩

theorem totient_pos' {n : ℕ} (hn : 2 ≤ n) : 0 < Nat.totient n :=
  Nat.totient_pos.mpr (by omega)

/-!
## Part II: The endpoints of the reduced-residue enumeration

`1` is the least reduced residue and `n-1` is the greatest, for `n ≥ 2`.
-/

theorem coprime_pred_self {n : ℕ} (hn : 2 ≤ n) : Nat.Coprime (n - 1) n := by
  have h : (1 : ℕ) + (n - 1) = n := by omega
  have hco : Nat.Coprime (1 + (n - 1)) (n - 1) :=
    (Nat.coprime_add_self_left).mpr (Nat.coprime_one_left _)
  rw [h] at hco
  exact hco.symm

theorem one_mem_reducedResidues {n : ℕ} (hn : 2 ≤ n) : 1 ∈ reducedResidues n := by
  simp only [mem_reducedResidues]
  exact ⟨by omega, le_refl 1, Nat.coprime_one_left n⟩

theorem pred_mem_reducedResidues {n : ℕ} (hn : 2 ≤ n) : n - 1 ∈ reducedResidues n := by
  simp only [mem_reducedResidues]
  exact ⟨by omega, by omega, coprime_pred_self hn⟩

/-- The minimum reduced residue is `1` (for any chosen nonemptiness witness). -/
theorem min'_reducedResidues {n : ℕ} (hn : 2 ≤ n) (H : (reducedResidues n).Nonempty) :
    (reducedResidues n).min' H = 1 := by
  apply le_antisymm
  · exact Finset.min'_le _ 1 (one_mem_reducedResidues hn)
  · exact Finset.le_min' _ _ _ (fun y hy => (mem_reducedResidues.mp hy).2.1)

/-- The maximum reduced residue is `n-1` (for any chosen nonemptiness witness). -/
theorem max'_reducedResidues {n : ℕ} (hn : 2 ≤ n) (H : (reducedResidues n).Nonempty) :
    (reducedResidues n).max' H = n - 1 := by
  apply le_antisymm
  · exact Finset.max'_le _ _ _ (fun y hy => by
      have := (mem_reducedResidues.mp hy).1; omega)
  · exact Finset.le_max' _ (n - 1) (pred_mem_reducedResidues hn)

/-!
## Part III: The enumeration `E` and the gaps

`E n hn k` is the `k`-th reduced residue (as a real number), padded with `0`
outside the valid range so that telescoping is convenient.
-/

/-- The `k`-th reduced residue, as a real number (junk value `0` for `k ≥ φ(n)`). -/
noncomputable def E (n : ℕ) (hn : 2 ≤ n) : ℕ → ℝ := fun k =>
  if h : k < Nat.totient n then
    (((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k, h⟩ : ℕ) : ℝ)
  else 0

/-- The `k`-th gap `a_{k+1} - a_k`, as a real number. -/
noncomputable def gap (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : ℝ := E n hn (k + 1) - E n hn k

theorem E_zero {n : ℕ} (hn : 2 ≤ n) : E n hn 0 = 1 := by
  have hpos := totient_pos' hn
  rw [E, dif_pos hpos, Finset.orderEmbOfFin_zero (card_reducedResidues hn) hpos,
    min'_reducedResidues hn]
  norm_num

theorem E_last {n : ℕ} (hn : 2 ≤ n) : E n hn (Nat.totient n - 1) = (n : ℝ) - 1 := by
  have hpos := totient_pos' hn
  have hlt : Nat.totient n - 1 < Nat.totient n := by omega
  rw [E, dif_pos hlt]
  rw [Finset.orderEmbOfFin_last (card_reducedResidues hn) hpos, max'_reducedResidues hn]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num

/-!
## Part IV: The gaps telescope — their sum is `n - 2`
-/

/-- **Telescoping identity.** The `φ(n)-1` gaps between consecutive reduced residues
sum to `a_{φ(n)} - a₁ = (n-1) - 1 = n - 2`. -/
theorem sum_gaps {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (Nat.totient n - 1), gap n hn k = (n : ℝ) - 2 := by
  have htel : ∑ k ∈ Finset.range (Nat.totient n - 1), (E n hn (k + 1) - E n hn k)
      = E n hn (Nat.totient n - 1) - E n hn 0 :=
    Finset.sum_range_sub (E n hn) (Nat.totient n - 1)
  calc ∑ k ∈ Finset.range (Nat.totient n - 1), gap n hn k
      = ∑ k ∈ Finset.range (Nat.totient n - 1), (E n hn (k + 1) - E n hn k) := by
        simp only [gap]
    _ = E n hn (Nat.totient n - 1) - E n hn 0 := htel
    _ = ((n : ℝ) - 1) - 1 := by rw [E_last hn, E_zero hn]
    _ = (n : ℝ) - 2 := by ring

/-!
## Part V: The lower bound (main result)
-/

/-- **Cauchy–Schwarz lower bound (product form).**

    (n - 2)² ≤ (φ(n) - 1) · ∑ (a_{k+1} - a_k)².

Together with the Montgomery–Vaughan upper bound `∑ (a_{k+1}-a_k)² ≪ n²/φ(n)`
this pins the order of magnitude of the squared-gap sum. -/
theorem sq_le_card_mul_sumSq {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) - 2) ^ 2
      ≤ (Nat.totient n - 1 : ℕ) * ∑ k ∈ Finset.range (Nat.totient n - 1), (gap n hn k) ^ 2 := by
  have hcheb := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (Nat.totient n - 1)) (f := gap n hn)
  rw [sum_gaps hn, Finset.card_range] at hcheb
  exact hcheb

/-- **Matching lower bound (division form).**

    (n - 2)²/(φ(n) - 1) ≤ ∑ (a_{k+1} - a_k)².

For `n ≥ 3` the denominator `φ(n) - 1 ≥ 1` is positive, so dividing the product
form is legitimate.  Since `(n-2)²/(φ(n)-1) ≍ n²/φ(n)`, this is the lower-bound
companion of Montgomery–Vaughan, establishing
    ∑ (a_{k+1} - a_k)² ≍ n²/φ(n). -/
theorem sumSquaredGaps_lower_bound {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℝ) - 2) ^ 2 / (Nat.totient n - 1 : ℕ)
      ≤ ∑ k ∈ Finset.range (Nat.totient n - 1), (gap n (show 2 ≤ n by omega) k) ^ 2 := by
  have hn2 : 2 ≤ n := by omega
  have hφ : 2 ≤ Nat.totient n := by
    have hpos := totient_pos' hn2
    have hne1 : Nat.totient n ≠ 1 := by
      intro h
      rcases Nat.totient_eq_one_iff.mp h with h1 | h2 <;> omega
    omega
  have hden : (0 : ℝ) < (Nat.totient n - 1 : ℕ) := by
    have h1 : 1 ≤ Nat.totient n - 1 := by omega
    exact_mod_cast h1
  rw [div_le_iff₀ hden]
  have hprod := sq_le_card_mul_sumSq hn2
  rw [mul_comm] at hprod
  exact hprod

end Erdos220OQ01
