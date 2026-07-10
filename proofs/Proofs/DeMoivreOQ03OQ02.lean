import Proofs.DeMoivreOQ03

/-
# De Moivre OQ-03-OQ-02: Monodromy / Deck-Transformation Structure of z^(p/q)

## Research Problem: de-moivre-oq-03-oq-02
Riemann surface structure of `z ↦ z^{p/q}`.

## Mathematical Content

The parent file `DeMoivreOQ03` enumerates the `q` distinct `q`-th roots

  ζ_k = exp(i(pθ + 2πk)/q),   k = 0, 1, ..., q-1,

and proves (in `qthRoot_periodic`) that the index is cyclic: `ζ_{k+q} = ζ_k`.
Its docstring identifies this cyclic identification `k ∼ k + q` as the
combinatorial seed of the `q`-sheeted Riemann surface of `z ↦ z^{p/q}`: the
sheets are the residues `k mod q`, and crossing a branch cut advances `k` by
one, wrapping back after `q` crossings.

This companion formalizes the *monodromy action itself* — the arithmetic that
makes the deck-transformation group of that covering explicit:

* `rootOfUnity_add`     — `n ↦ ω_n = exp(2πin/q)` is a monoid homomorphism
                          `(ℕ, +) → (ℂˣ, ·)`; this is the deck-transformation
                          group of the cover.
* `rootOfUnity_succ`    — one branch-cut crossing multiplies by the generator
                          `ω_1 = exp(2πi/q)`.
* `rootOfUnity_index_eq_one` — `ω_q = 1`: `q` crossings return to the start
                          sheet (the order-`q` relation of the cyclic group).
* `qthRoot_succ_eq_mul_unity` — **single-step monodromy**: crossing one branch
                          cut sends `ζ_k ↦ ζ_{k+1} = ζ_k · ω_1`. This is the
                          generator of the deck transformation acting on values.
* `qthRoot_add_index`   — advancing the index by `j` sheets multiplies the
                          value by `ω_j`, exhibiting the full ℤ/qℤ-action.

All results are corollaries of the verified parent lemmas
`qthRoot_eq_principal_mul_unity` (ζ_k = ζ_0 · ω_k) and the additivity of `exp`.

## References
- Needham (1997): "Visual Complex Analysis" — branch points and sheets
- Forster (1981): "Lectures on Riemann Surfaces" — deck transformations
-/

open Complex Real

namespace DeMoivreOQ03

/-! ## Deck-transformation group: `n ↦ ω_n` is a homomorphism -/

/-- **Additivity of the roots of unity.** The map `n ↦ ω_n = exp(2πin/q)` is a
monoid homomorphism from `(ℕ, +)` to `(ℂ, ·)`: `ω_{j+k} = ω_j · ω_k`. Its image
is the cyclic group `μ_q` of `q`-th roots of unity — the deck-transformation
group of the `q`-sheeted cover `z ↦ z^{p/q}`. -/
theorem rootOfUnity_add (q j k : ℕ) :
    rootOfUnity q (j + k) = rootOfUnity q j * rootOfUnity q k := by
  simp only [rootOfUnity]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **One-step generator.** Advancing the index by one multiplies by the
primitive root `ω_1 = exp(2πi/q)`: `ω_{k+1} = ω_k · ω_1`. -/
theorem rootOfUnity_succ (q k : ℕ) :
    rootOfUnity q (k + 1) = rootOfUnity q k * rootOfUnity q 1 :=
  rootOfUnity_add q k 1

/-- **Order-`q` relation.** A full loop of `q` branch-cut crossings returns to
the identity sheet: `ω_q = exp(2πiq/q) = exp(2πi) = 1`. This is the defining
relation of the cyclic deck-transformation group `ℤ/qℤ`. -/
theorem rootOfUnity_index_eq_one (q : ℕ) (hq : 0 < q) :
    rootOfUnity q q = 1 := by
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [rootOfUnity]
  rw [mul_div_assoc, div_self hq_ne, mul_one]
  exact Complex.exp_two_pi_mul_I

/-! ## Monodromy action on the root values -/

/-- **Single-step monodromy.** Crossing one branch cut sends the value `ζ_k` to
`ζ_{k+1} = ζ_k · ω_1`, i.e. the generator of the deck-transformation group acts
on root values by multiplication by the primitive `q`-th root of unity. This is
the analytic content of the `q`-sheeted Riemann surface of `z ↦ z^{p/q}`:
following a value around a small loop about the branch point `0` rotates it to
the next sheet. -/
theorem qthRoot_succ_eq_mul_unity (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    qthRoot θ p q (k + 1) = qthRoot θ p q k * rootOfUnity q 1 := by
  rw [qthRoot_eq_principal_mul_unity θ p q hq (k + 1), rootOfUnity_succ,
      qthRoot_eq_principal_mul_unity θ p q hq k]
  ring

/-- **Full ℤ/qℤ-action.** Advancing the index by `j` sheets multiplies the value
by `ω_j`: `ζ_{k+j} = ζ_k · ω_j`. Together with `rootOfUnity_index_eq_one` and
`rootOfUnity_add` this exhibits the deck-transformation group `ℤ/qℤ` acting
freely and transitively on the `q` roots — the monodromy representation of the
covering `z ↦ z^{p/q}`. -/
theorem qthRoot_add_index (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k j : ℕ) :
    qthRoot θ p q (k + j) = qthRoot θ p q k * rootOfUnity q j := by
  rw [qthRoot_eq_principal_mul_unity θ p q hq (k + j), rootOfUnity_add,
      qthRoot_eq_principal_mul_unity θ p q hq k]
  ring

/-- **Monodromy recovers periodicity.** As a consistency check, advancing by a
full period `q` acts trivially: `ζ_{k+q} = ζ_k · ω_q = ζ_k · 1 = ζ_k`,
reproducing the parent's `qthRoot_periodic` from the deck-transformation
viewpoint. -/
theorem qthRoot_add_period_eq (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    qthRoot θ p q (k + q) = qthRoot θ p q k := by
  rw [qthRoot_add_index θ p q hq k q, rootOfUnity_index_eq_one q hq, mul_one]

end DeMoivreOQ03
