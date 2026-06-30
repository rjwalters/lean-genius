/-
# Eisenstein's Reciprocity Input: ∑_{k<q} {kp/q} = (q-1)/2 for coprime p, q

For coprime natural numbers `p` and `q` with `q ≥ 1`,
$$\sum_{k=0}^{q-1} \left\{ \frac{k p}{q} \right\} = \frac{q-1}{2},$$
where `{y} = y - ⌊y⌋` is the fractional part (`Int.fract`).

This is the clean evaluation requested as a follow-up to the companion sawtooth
identity (`HermiteSawtoothIdentity.lean`). It is the arithmetic ingredient that
feeds Eisenstein's lemma and the lattice-point proof of quadratic reciprocity:
the average of the sawtooth `{kp/q}` over a full residue system is exactly the
"diagonal" value `(q-1)/2`, independent of `p`.

## The argument

Two elementary facts combine:

1. **Sawtooth at `x = 0`.** Specialising the parent identity
   `∑_{k<n} {x + k/n} = {nx} + (n-1)/2` at `x = 0` gives
   `∑_{k<q} {k/q} = (q-1)/2`, since `{q·0} = 0`.

2. **Multiplication by `p` permutes residues.** Because `gcd(p,q) = 1`, the map
   `k ↦ k·p mod q` is a bijection of `{0, …, q-1}` onto itself. Hence the
   residues `k·p mod q` are a rearrangement of `0, …, q-1`, and since
   `{kp/q} = (k·p mod q)/q`, summing gives the same total as `∑_{k<q} {k/q}`.

Concretely we show `∑_{k<q} (k·p mod q) = ∑_{k<q} k = q(q-1)/2`, divide by `q`,
and read off `(q-1)/2`.

## What this adds

The parent entry proves the sawtooth identity for a single real `x`. This entry
applies it to the number-theoretic sum `∑_{k<q} {kp/q}`, supplying the
`p`-independent closed form `(q-1)/2`. Mathlib has `Int.fract` and the residue
permutation machinery but does not record this Gauss/Eisenstein reciprocity
input directly. Fully machine-checked, `0` sorries, no axioms.
-/
import Mathlib
import Proofs.HermiteSawtoothIdentity

open Finset

namespace HermiteSawtoothIdentity

/-- **Sawtooth at `x = 0`.** The equally spaced fractional parts `{k/q}`,
`k = 0, …, q-1`, sum to `(q-1)/2`. -/
theorem sum_fract_div (q : ℕ) (hq : 0 < q) :
    ∑ k ∈ range q, Int.fract ((k : ℝ) / (q : ℝ)) = ((q : ℝ) - 1) / 2 := by
  have h := hermite_sawtooth_identity 0 q hq
  simpa using h

/-- **Residue permutation.** When `gcd(p,q) = 1`, the map `k ↦ k·p mod q` permutes
`{0, …, q-1}`, so the residues `k·p mod q` sum to the same value as `0, …, q-1`. -/
theorem sum_mul_mod_coprime (p q : ℕ) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    ∑ k ∈ range q, (k * p % q) = ∑ k ∈ range q, k := by
  -- `σ k = k·p mod q` maps `range q` into itself injectively, hence bijectively.
  set σ : ℕ → ℕ := fun k => k * p % q with hσ
  have hmaps : ∀ k ∈ range q, σ k ∈ range q := by
    intro k _; simp only [hσ, mem_range]; exact Nat.mod_lt _ hq
  have hinj : Set.InjOn σ (range q) := by
    intro a ha b hb hab
    simp only [mem_coe, mem_range] at ha hb
    -- `σ a = σ b` is exactly `a·p ≡ b·p [MOD q]`.
    have hmod : a * p ≡ b * p [MOD q] := hab
    have hab' : a % q = b % q := Nat.ModEq.cancel_right_of_coprime hpq.symm hmod
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab'
  -- The image is contained in `range q` and has the same cardinality, so equals it.
  have himg : (range q).image σ = range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact hmaps k hk
    · rw [Finset.card_image_of_injOn hinj, card_range]
  have hsum := Finset.sum_image (f := fun x => x) hinj
  rw [himg] at hsum
  exact hsum.symm

/-- **Eisenstein reciprocity input.** For coprime `p, q` with `q ≥ 1`,
`∑_{k<q} {kp/q} = (q-1)/2`. -/
theorem sum_fract_mul_div_coprime (p q : ℕ) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    ∑ k ∈ range q, Int.fract ((k : ℝ) * (p : ℝ) / (q : ℝ)) = ((q : ℝ) - 1) / 2 := by
  -- Each fractional part is the residue `(k·p mod q)/q`.
  have hterm : ∀ k ∈ range q,
      Int.fract ((k : ℝ) * (p : ℝ) / (q : ℝ)) = ((k * p % q : ℕ) : ℝ) / (q : ℝ) := by
    intro k _
    rw [show (k : ℝ) * (p : ℝ) = ((k * p : ℕ) : ℝ) by push_cast; ring]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum,
    sum_mul_mod_coprime p q hq hpq]
  -- Remaining: `↑(∑_{k<q} k) / q = (q-1)/2`, via the Gauss sum.
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hgauss : ((∑ k ∈ range q, k : ℕ) : ℝ) * 2 = (q : ℝ) * ((q : ℝ) - 1) := by
    have hc := congrArg (fun m : ℕ => (m : ℝ)) (Finset.sum_range_id_mul_two q)
    push_cast [Nat.cast_sub hq] at hc
    rw [Nat.cast_sum]
    linarith [hc]
  field_simp
  linear_combination hgauss

end HermiteSawtoothIdentity
