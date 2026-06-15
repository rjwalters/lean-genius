import Mathlib
import Proofs.ZsqrtdNegTwoOQ03

/-!
# Primes `p ≡ 1 (mod 3)` are represented by `x² + 3y²`  (Fermat, `n = 3`)

**Open Question (`zsqrtd-neg-two-oq-03-oq-01`)**: the parent file
`Proofs/ZsqrtdNegTwoOQ03.lean` constructs the Eisenstein integers `ℤ[ω]`
(`Proofs.Eisenstein`), proves they form a `EuclideanDomain`
(`Proofs.Eisenstein.instEuclideanDomain`), and establishes the
quadratic-reciprocity characterisation (`legendreSym_neg_three_eq_one_iff`)

  for an odd prime `p ≠ 3`,    `(-3 / p) = 1  ↔  p ≡ 1 (mod 3)`.

This file uses that infrastructure to reach the classical target

  `sq_add_three_sq_of_prime_one_mod_three :`
  `  p.Prime → p % 3 = 1 → ∃ a b : ℤ, (p : ℤ) = a² + 3·b²`,

the `n = 3` Heegner-number analogue of the parent gallery entry
`Proofs/ZsqrtdNegTwo.lean` (which handles `n = 2`, i.e. `p = a² + 2b²`).

## Proof architecture

The argument has two independent components.

1. **Form conversion** (`eisenstein_form_to_x_sq_add_three_y_sq`, PROVED below,
   pure `ℤ` arithmetic): the Eisenstein norm form `N(a + bω) = a² - ab + b²`
   represents the *same* integers as `x² + 3y²`. Concretely, every value
   `a² - ab + b²` equals some `x² + 3y²`. Proof: `4(a²-ab+b²) = (2a-b)² + 3b²`,
   and the order-6 unit rotations `(a,b) ↦ (-b, a-b) ↦ (b-a, -a)` of `ℤ[ω]`
   (all norm-preserving) let us assume the `ω`-coordinate is even, after which
   the witnesses are explicit. We prove it directly by parity case analysis
   with explicit witnesses, no Eisenstein machinery required.

2. **Norm realisation** (`exists_eisenstein_norm_eq_prime`, the remaining gap):
   for `p ≡ 1 (mod 3)` prime there is an Eisenstein integer `z` with `N(z) = p`.
   This is the splitting argument and is the genuine HARD step (see the long
   docstring on that lemma for the full plan). It is the natural Aristotle
   target once the prover backend is available.

Given (2), the main theorem is immediate: pick `z` with `N(z) = p`, write
`N(z) = z.re² - z.re·z.im + z.im²`, and apply (1).

## Status

- `eisenstein_form_to_x_sq_add_three_y_sq` — proved (pure `ℤ`, `ring`-closed
  in each parity branch).
- `eisensteinSqrtNegThree_sq` (`θ² = -3`) — proved (splitting step 2).
- `ofInt_sub_sqrt_mul_add_sqrt` (`(c-θ)(c+θ) = c²+3`) — proved (splitting step 3).
- `sq_add_three_sq_of_prime_one_mod_three` — proved **modulo** the single
  lemma `exists_eisenstein_norm_eq_prime`.
- `exists_eisenstein_norm_eq_prime` — `sorry` (HARD splitting step; the
  remaining gap is now isolated to the UFD `prime ↔ irreducible` norm-split
  extraction, steps 4–7, with the concrete algebra of steps 2–3 discharged
  above; Aristotle/Docker both unavailable this session, so build-pending
  and unverified).

axiomCount: 0  ·  sorryCount: 1 (HARD, on `exists_eisenstein_norm_eq_prime`)
-/

open Proofs Proofs.Eisenstein

namespace ZsqrtdNegTwoOQ03OQ01

/-! ## Part I — Form conversion `a² - ab + b² = x² + 3y²` (pure `ℤ`) -/

/-- The Eisenstein norm form `a² - ab + b²` represents the same integers as
`x² + 3y²`: every value of the former is a value of the latter.

Proof by parity case analysis. Underlying identity in each branch:
`4·(a² - ab + b²) = (2a - b)² + 3b²`, made integral by reducing to the case
where the second coordinate is even via the norm-preserving unit rotation
`(a,b) ↦ (-b, a-b)` of `ℤ[ω]`.

* `b = 2k` even           : `a² - ab + b² = (a-k)² + 3k²`.
* `a = 2m` even, `b` odd  : `= (b-m)² + 3m²`           (rotate once).
* `a = 2m+1`, `b = 2k+1`  : `= (-m-k-1)² + 3(m-k)²`    (rotate once). -/
theorem eisenstein_form_to_x_sq_add_three_y_sq (a b : ℤ) :
    ∃ x y : ℤ, a ^ 2 - a * b + b ^ 2 = x ^ 2 + 3 * y ^ 2 := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- b = k + k (even)
    exact ⟨a - k, k, by subst hk; ring⟩
  · -- b = 2k + 1 (odd); split on parity of a
    rcases Int.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- a = m + m (even), b odd
      exact ⟨b - m, m, by subst hm; ring⟩
    · -- a = 2m + 1, b = 2k + 1 (both odd)
      exact ⟨-m - k - 1, m - k, by subst hm; subst hk; ring⟩

/-! ## Part II — Norm realisation (the splitting argument)

The two concrete algebraic ingredients of the splitting argument (steps 2 and 3
of the plan below) are now proved as standalone lemmas; only the UFD
`prime ↔ irreducible` extraction (steps 4–7) remains as the documented gap. -/

/-- The Eisenstein `√-3`: `θ = 1 + 2ω = ⟨1, 2⟩`, satisfying `θ² = -3`.
This is the algebraic bridge from the quadratic-reciprocity step
`(-3 / p) = 1` to a divisibility statement in `ℤ[ω]`. -/
def eisensteinSqrtNegThree : Eisenstein := ⟨1, 2⟩

@[simp] theorem eisensteinSqrtNegThree_re : eisensteinSqrtNegThree.re = 1 := rfl
@[simp] theorem eisensteinSqrtNegThree_im : eisensteinSqrtNegThree.im = 2 := rfl

/-- **Splitting step 2 (proved).** `θ² = -3` in `ℤ[ω]`. Direct coordinate
computation: `re = 1·1 - 2·2 = -3`, `im = 1·2 + 2·1 - 2·2 = 0`. -/
theorem eisensteinSqrtNegThree_sq :
    eisensteinSqrtNegThree * eisensteinSqrtNegThree = Eisenstein.ofInt (-3) := by
  ext
  · simp only [Eisenstein.mul_re, eisensteinSqrtNegThree_re, eisensteinSqrtNegThree_im,
      Eisenstein.re_ofInt]
    norm_num
  · simp only [Eisenstein.mul_im, eisensteinSqrtNegThree_re, eisensteinSqrtNegThree_im,
      Eisenstein.im_ofInt]
    norm_num

/-- **Splitting step 3 (proved).** The difference-of-squares factorisation in
`ℤ[ω]` that turns the integer divisibility `p ∣ c² + 3` into a factored
divisibility `p ∣ (c - θ)(c + θ)`:

  `(ofInt c - θ) * (ofInt c + θ) = ofInt (c² + 3)`,

since `(c - θ)(c + θ) = c² - θ² = c² - (-3) = c² + 3`. Proved by direct
coordinate computation (no Eisenstein ring lemmas beyond the projections). -/
theorem ofInt_sub_sqrt_mul_add_sqrt (c : ℤ) :
    (Eisenstein.ofInt c - eisensteinSqrtNegThree) *
        (Eisenstein.ofInt c + eisensteinSqrtNegThree)
      = Eisenstein.ofInt (c ^ 2 + 3) := by
  ext
  · simp only [Eisenstein.mul_re, Eisenstein.sub_re, Eisenstein.sub_im,
      Eisenstein.add_re, Eisenstein.add_im, Eisenstein.re_ofInt, Eisenstein.im_ofInt,
      eisensteinSqrtNegThree_re, eisensteinSqrtNegThree_im]
    ring
  · simp only [Eisenstein.mul_im, Eisenstein.sub_re, Eisenstein.sub_im,
      Eisenstein.add_re, Eisenstein.add_im, Eisenstein.re_ofInt, Eisenstein.im_ofInt,
      eisensteinSqrtNegThree_re, eisensteinSqrtNegThree_im]
    ring

/-- **Splitting argument (HARD — remaining gap).** For a prime `p ≡ 1 (mod 3)`
there is an Eisenstein integer whose norm is `p`.

Full proof plan (to be discharged by Aristotle / a future session):

1. From `p ≡ 1 (mod 3)` and `legendreSym_neg_three_eq_one_iff` (parent file),
   `legendreSym p (-3) = 1`, hence `∃ c : ℤ, c² ≡ -3 (mod p)`
   (`legendreSym.eq_one_iff'` / `ZMod.exists_sq_eq` style).

2. Set `θ := eisensteinSqrtNegThree = ⟨1, 2⟩ = 1 + 2ω`; **proved** above as
   `eisensteinSqrtNegThree_sq : θ * θ = ofInt (-3)`, i.e. `θ² = -3`. So `√-3 = θ`.

3. Then `p ∣ c² + 3`, and **proved** above as `ofInt_sub_sqrt_mul_add_sqrt`,
   `(ofInt c - θ) * (ofInt c + θ) = ofInt (c² + 3)`.
   Hence `p ∣ (ofInt c - θ)(ofInt c + θ)` in `ℤ[ω]`.

4. `p` does **not** divide either factor `ofInt c ∓ θ`: their `ω`-coordinates
   are `∓2`, and `p ∤ 2` (as `p ≡ 1 mod 3` forces `p ≥ 7`, in particular odd).
   Hence `p` is **not prime** in `ℤ[ω]`.

5. `ℤ[ω]` is a `EuclideanDomain` (`instEuclideanDomain`), hence a UFD, where
   `prime ↔ irreducible` for nonzero nonunits. Since `(p : Eisenstein) ≠ 0` and
   is not a unit (`N(p) = p² ≠ 1`), non-primality gives a factorisation
   `p = α * β` with `α, β` nonunits.

6. Apply `norm_mul`: `p² = N(p) = N(α) · N(β)` with `N(α), N(β) > 1`
   (`norm_pos_of_ne_zero` + nonunit ⇒ norm ≠ 1). As `p` is prime in `ℤ`,
   `N(α) = N(β) = p`.

7. Take `z := α`; then `N(z) = p`. ∎

This is standard algebraic number theory but tedious to formalise; it is the
single remaining gap and an ideal `aristotle_prove` job once the backend
returns. -/
theorem exists_eisenstein_norm_eq_prime {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ z : Eisenstein, Eisenstein.norm z = (p : ℤ) := by
  sorry

/-! ## Part III — Main theorem -/

/-- **Fermat's theorem for `x² + 3y²`.** Every prime `p ≡ 1 (mod 3)` is of the
form `a² + 3b²`.

Assembled from the norm realisation (`exists_eisenstein_norm_eq_prime`) and the
form conversion (`eisenstein_form_to_x_sq_add_three_y_sq`). -/
theorem sq_add_three_sq_of_prime_one_mod_three {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2 := by
  obtain ⟨z, hz⟩ := exists_eisenstein_norm_eq_prime hp hmod
  obtain ⟨x, y, hxy⟩ := eisenstein_form_to_x_sq_add_three_y_sq z.re z.im
  refine ⟨x, y, ?_⟩
  rw [← hz]
  show z.re ^ 2 - z.re * z.im + z.im ^ 2 = x ^ 2 + 3 * y ^ 2
  exact hxy

end ZsqrtdNegTwoOQ03OQ01
