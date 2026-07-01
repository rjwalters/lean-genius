import Proofs.CompositionPartsChooseOQ01OQ01
import Mathlib.Tactic

/-
# The generating function of the number of parts of a composition

## What this proves

A *composition* of `n` is an ordered tuple of positive integers summing to `n`
(Mathlib's `Composition n`); its number of parts is `c.length`. Earlier entries in this
family compute individual statistics of the part-count of a uniformly random composition:

* grandparent (`composition-card-2pow-oq-01`): there are `2^(n−1)` compositions of `n`;
* parent (`composition-parts-choose-oq-01`): exactly `C(n−1, k−1)` of them have `k` parts;
* parent (`…-oq-01-oq-01`): the **first moment** — mean part-count `(n+1)/2`;
* parent (`…-oq-01-oq-01-oq-01`): the **second moment** and **variance** `(n−1)/4`.

The parent's open question asks whether *all* the moments can be produced at once. They
can: this leaf computes the entire **generating function** of the part-count. Over any
commutative semiring `R` and any `t : R`, for `n ≥ 1`,

```
Σ_{c : Composition n} t^{c.length}  =  t · (1 + t)^{n−1}        (parts_genfun)
```

This single polynomial identity is the *probability generating function* of the
part-count (up to the normalising `2^{n−1}`): its evaluation at `t = 1` returns the count
`2^{n−1}` (`parts_genfun_eval_one`), the coefficient of `t^k` is the number of
compositions with `k` parts `C(n−1, k−1)` (`parts_genfun_binomial`), and every moment of
the part-count is obtained by differentiating it at `t = 1`. In particular it exhibits the
part-count as `1 + Binomial(n−1, 1/2)`, whose PGF is exactly `t·((1+t)/2)^{n−1}` after
normalising — recovering the mean `(n+1)/2` and variance `(n−1)/4` of the parents as the
first two derivatives, without recomputing any binomial sum.

## The mechanism

As for the moments, everything is transported along the bijection
`gapsEquiv n : Composition n ≃ Finset (Fin (n−1))` (a composition is the set of internal
gaps it cuts) together with the bridge `length_eq_card_gaps : c.length = (gaps c).card + 1`.
Pushing the sum across the equivalence turns `Σ_c t^{c.length}` into the subset sum
`Σ_{s ⊆ Fin (n−1)} t^{|s|+1} = t · Σ_{s ⊆ Fin (n−1)} t^{|s|}`, and the subset generating
function

```
Σ_{s ⊆ Fin m} t^{|s|}  =  (t + 1)^m                            (sum_pow_card)
```

is the `Finset.prod_add` expansion of `∏_{i : Fin m} (t + 1)`: each factor contributes
either the `t` (put `i ∈ s`) or the `1` (put `i ∉ s`).

## Originality

Where the parents each extracted one number from a *particular* weighted binomial sum
`Σ_k k^r C(m,k)`, this entry gives the closed-form generating function that packages all of
them simultaneously. Mathlib has neither the subset generating function
`Σ_{s ⊆ Fin m} t^{|s|} = (t+1)^m` in this form nor any statement about the part-count
distribution of a composition; the identity `Σ_c t^{c.length} = t(1+t)^{n−1}` is, to our
knowledge, not in the gallery.
-/

namespace CompositionPartsChooseOQ01OQ01OQ01OQ02

open Finset CompositionPartsChooseOQ01OQ01

/-! ## The subset-cardinality generating function -/

/-- **Subset generating function.** Over any commutative semiring `R` and `t : R`,
`Σ_{s ⊆ Fin m} t^{|s|} = (t + 1)^m`. This is the `Finset.prod_add` expansion of the product
`∏_{i : Fin m} (t + 1)`: expanding the product, each of the `2^m` monomials picks the `t`
from the factors in a subset `s` and the `1` from the rest, contributing `t^{|s|}`. -/
theorem sum_pow_card {R : Type*} [CommSemiring R] (t : R) (m : ℕ) :
    ∑ s : Finset (Fin m), t ^ s.card = (t + 1) ^ m := by
  have h := Finset.prod_add (fun _ : Fin m => t) (fun _ : Fin m => (1 : R)) Finset.univ
  simp only [Finset.prod_const, one_pow, mul_one, Finset.card_univ,
    Fintype.card_fin, Finset.powerset_univ] at h
  exact h.symm

/-! ## The generating function of the part-count -/

/-- **Generating function of the number of parts.** Over any commutative semiring `R`, for
every `t : R` and `n ≥ 1`,

`Σ_{c : Composition n} t^{c.length}  =  t · (1 + t)^{n−1}`.

This is the probability generating function of the part-count (up to the normalising
`2^{n−1}`): evaluating at `t = 1` gives the count `2^{n−1}`, the coefficient of `t^k` is the
number of compositions with `k` parts, and each moment is a derivative at `t = 1`. Proved
by transporting the sum across the gap bijection `gapsEquiv` to
`Σ_{s ⊆ Fin (n−1)} t^{|s|+1}`, factoring out one `t`, and applying `sum_pow_card`. -/
theorem parts_genfun {R : Type*} [CommSemiring R] (t : R) (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, t ^ c.length = t * (1 + t) ^ (n - 1) := by
  have e1 : ∑ c : Composition n, t ^ c.length
      = ∑ c : Composition n, t ^ ((gapsEquiv n c).card + 1) :=
    Finset.sum_congr rfl (fun c _ => by rw [length_eq_card_gaps n hn c])
  rw [e1, Equiv.sum_comp (gapsEquiv n) (fun s => t ^ (s.card + 1))]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, sum_pow_card t (n - 1)]
  ring

/-- **Evaluating the generating function at `t = 1` recovers the count.** Since
`1^{c.length} = 1` for every composition, the left side of `parts_genfun` counts the
compositions, while the right side is `1·(1+1)^{n−1} = 2^{n−1}`. This re-derives the
grandparent's `2^{n−1}` count — the total mass of the part-count distribution — as a
special value of the generating function, independently of Mathlib's `composition_card`. -/
theorem parts_genfun_eval_one (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (Composition n) : ℕ) = 2 ^ (n - 1) := by
  have h := parts_genfun (1 : ℕ) n hn
  simpa using h

/-- **Explicit polynomial form.** The generating function is the binomial polynomial
`Σ_{k<n} C(n−1,k) · t^{k+1}`. Comparing with `parts_genfun`, the coefficient of `t^{k+1}` is
`C(n−1, k) = C(n−1, (k+1)−1)` — exactly the number of compositions of `n` with `k+1` parts
(the grandparent's graded count). Proved directly from the binomial theorem `add_pow`. -/
theorem parts_genfun_binomial {R : Type*} [CommSemiring R] (t : R) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, ((n - 1).choose k : R) * t ^ (k + 1)
      = t * (1 + t) ^ (n - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  rw [show M + 1 - 1 = M from rfl, add_comm (1 : R) t, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [one_pow, mul_one]
  ring

end CompositionPartsChooseOQ01OQ01OQ01OQ02
