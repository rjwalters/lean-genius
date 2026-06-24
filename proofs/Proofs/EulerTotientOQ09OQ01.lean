import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic
import Proofs.EulerTotientOQ09

/-!
# Totient of a product via `gcd`, and exactly when `φ(m·n) = m·φ(n)`

**Open Question (`euler-totient-oq-09-oq-01`)**, an extension of
`euler-totient-oq-09`.  Mathlib has the *coprime* multiplicative law
`Nat.totient_mul` (`φ(mn) = φ(m)φ(n)` when `gcd(m,n) = 1`), and the parent entry
`euler-totient-oq-09` proved the power law `φ(nᵏ) = nᵏ⁻¹·φ(n)` together with its
engine

  `totient_mul_of_primeFactors_subset` :
      `m.primeFactors ⊆ n.primeFactors → φ(m·n) = m·φ(n)`.

This file fills the gap between coprimality and the prime-power law in two ways.

## Contents

* `totient_mul_mul_totient_gcd` — the **general product formula**
  `φ(m·n)·φ(gcd m n) = gcd(m,n)·φ(m)·φ(n)`, the exact non-coprime correction
  factor (a commutative rearrangement of Mathlib's
  `Nat.totient_gcd_mul_totient_mul`).  When `gcd(m,n) = 1` it collapses to
  `Nat.totient_mul`.

* `totient_mul_eq_iff_primeFactors_subset` — the **sharp characterisation**: for
  `n ≠ 0`,
  `φ(m·n) = m·φ(n) ↔ m.primeFactors ⊆ n.primeFactors`.
  The `←` direction is precisely the parent's engine; the new content is the `→`
  direction, which we obtain through Euler's rational product formula
  `(φ n : ℚ) = n·∏_{p ∣ n}(1 − 1/p)`.  Writing `(m·n).primeFactors` as the union
  `m.primeFactors ∪ n.primeFactors`, the identity forces
  `∏_{p ∈ m.primeFactors ∖ n.primeFactors}(1 − 1/p) = 1`; but every such factor
  lies strictly in `(0, 1)`, so a nonempty product would be `< 1`.  Hence the
  index set is empty, i.e. `m.primeFactors ⊆ n.primeFactors`.

* `totient_mul_eq_iff_primeFactors_subset'` — the symmetric statement
  `φ(m·n) = n·φ(m) ↔ n.primeFactors ⊆ m.primeFactors` (for `m ≠ 0`).

Fully machine-checked: `0` sorries, `0` axioms (only the foundational
`propext`, `Classical.choice`, `Quot.sound`; no `native_decide`).
-/

namespace EulerTotientOQ09OQ01

open Nat

/-- A finite product of reals each strictly between `0` and `1`, over a nonempty
index set, is strictly less than `1`.  (Stated over `ℚ` with the index type `ℕ`,
which is all we need below.) -/
private lemma prod_lt_one_aux :
    ∀ (s : Finset ℕ) (f : ℕ → ℚ), s.Nonempty →
      (∀ p ∈ s, 0 < f p) → (∀ p ∈ s, f p < 1) → ∏ p ∈ s, f p < 1 := by
  intro s f
  classical
  induction s using Finset.induction with
  | empty => intro hne; exact absurd hne (by simp)
  | @insert a t ha ih =>
    intro _ hpos hlt
    rw [Finset.prod_insert ha]
    have hfa0 : 0 < f a := hpos a (Finset.mem_insert_self a t)
    have hfa1 : f a < 1 := hlt a (Finset.mem_insert_self a t)
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simpa using hfa1
    · have hpt : ∏ p ∈ t, f p < 1 :=
        ih ht (fun p hp => hpos p (Finset.mem_insert_of_mem hp))
          (fun p hp => hlt p (Finset.mem_insert_of_mem hp))
      have hpt0 : 0 < ∏ p ∈ t, f p :=
        Finset.prod_pos (fun p hp => hpos p (Finset.mem_insert_of_mem hp))
      nlinarith [hfa0, hfa1, hpt, hpt0]

/-- For a prime `p`, the Euler factor `1 - 1/p` is positive. -/
private lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : (0 : ℚ) < 1 - (p : ℚ)⁻¹ := by
  have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hpinv : (p : ℚ) * (p : ℚ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp0)
  nlinarith [hpinv, h2, inv_pos.mpr hp0]

/-- For a prime `p`, the Euler factor `1 - 1/p` is less than `1`. -/
private lemma one_sub_inv_lt_one {p : ℕ} (hp : p.Prime) : (1 : ℚ) - (p : ℚ)⁻¹ < 1 := by
  have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have := inv_pos.mpr hp0
  linarith

/-- If the Euler product over `m.primeFactors ∖ n.primeFactors` equals `1`, that
difference set is empty, i.e. `m.primeFactors ⊆ n.primeFactors`. -/
private lemma primeFactors_subset_of_prod_eq_one {m n : ℕ}
    (h : ∏ p ∈ m.primeFactors \ n.primeFactors, (1 - (p : ℚ)⁻¹) = 1) :
    m.primeFactors ⊆ n.primeFactors := by
  rw [← Finset.sdiff_eq_empty_iff_subset]
  by_contra hne
  have hne' : (m.primeFactors \ n.primeFactors).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hlt :=
    prod_lt_one_aux (m.primeFactors \ n.primeFactors) (fun p => 1 - (p : ℚ)⁻¹) hne'
      (fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1))
      (fun p hp => one_sub_inv_lt_one (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1))
  rw [h] at hlt
  exact lt_irrefl 1 hlt

/-- **General product formula for the totient.**  The non-coprime correction
factor is governed by the `gcd`:
`φ(m·n)·φ(gcd m n) = gcd(m,n)·φ(m)·φ(n)`.

This is a commutative rearrangement of Mathlib's `Nat.totient_gcd_mul_totient_mul`.
When `gcd(m,n) = 1` it reduces to the coprime law `Nat.totient_mul`. -/
theorem totient_mul_mul_totient_gcd (m n : ℕ) :
    φ (m * n) * φ (Nat.gcd m n) = Nat.gcd m n * φ m * φ n := by
  calc φ (m * n) * φ (m.gcd n)
      = φ (m.gcd n) * φ (m * n) := by ring
    _ = φ m * φ n * m.gcd n := Nat.totient_gcd_mul_totient_mul m n
    _ = m.gcd n * φ m * φ n := by ring

/-- **Sharp characterisation.**  For `n ≠ 0`,
`φ(m·n) = m·φ(n)` holds **iff** every prime dividing `m` already divides `n`,
i.e. `m.primeFactors ⊆ n.primeFactors`.

The `←` direction is the parent engine `totient_mul_of_primeFactors_subset`;
the `→` direction goes through Euler's rational product formula. -/
theorem totient_mul_eq_iff_primeFactors_subset {m n : ℕ} (hn : n ≠ 0) :
    φ (m * n) = m * φ n ↔ m.primeFactors ⊆ n.primeFactors := by
  constructor
  · intro heq
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    -- Cast the totient identity to `ℚ` and expand via Euler's product formula.
    have hQ : (φ (m * n) : ℚ) = (m : ℚ) * (φ n : ℚ) := by exact_mod_cast heq
    rw [totient_eq_mul_prod_factors (m * n), totient_eq_mul_prod_factors n,
      Nat.primeFactors_mul hm hn] at hQ
    push_cast at hQ
    apply primeFactors_subset_of_prod_eq_one
    -- Notation: the `n`-product is positive (each prime factor is `> 1`).
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hQpos : (0 : ℚ) < ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
      Finset.prod_pos fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primeFactors hp)
    -- Split the union product `m.pf ∪ n.pf` as `(m.pf ∖ n.pf) · n.pf`.
    rw [← Finset.prod_sdiff (Finset.subset_union_right (s₁ := m.primeFactors)
        (s₂ := n.primeFactors)), Finset.union_sdiff_right] at hQ
    -- Cancel the common nonzero factor `m·n·∏_{n.pf}` to isolate the difference product.
    have hc0 : (m : ℚ) * n * (∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hm0 hn0) (ne_of_gt hQpos)
    have hDc :
        (∏ p ∈ m.primeFactors \ n.primeFactors, (1 - (p : ℚ)⁻¹))
          * ((m : ℚ) * n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹))
        = 1 * ((m : ℚ) * n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹)) := by
      rw [one_mul]; linear_combination hQ
    exact mul_right_cancel₀ hc0 hDc
  · intro h
    exact EulerTotientOQ09.totient_mul_of_primeFactors_subset h

/-- The symmetric form of the characterisation: for `m ≠ 0`,
`φ(m·n) = n·φ(m) ↔ n.primeFactors ⊆ m.primeFactors`. -/
theorem totient_mul_eq_iff_primeFactors_subset' {m n : ℕ} (hm : m ≠ 0) :
    φ (m * n) = n * φ m ↔ n.primeFactors ⊆ m.primeFactors := by
  rw [mul_comm m n]
  exact totient_mul_eq_iff_primeFactors_subset hm

end EulerTotientOQ09OQ01
