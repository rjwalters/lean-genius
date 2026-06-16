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

2. **Norm realisation** (`exists_eisenstein_norm_eq_prime`, now proved): for
   `p ≡ 1 (mod 3)` prime there is an Eisenstein integer `z` with `N(z) = p`.
   This is the splitting argument (see the long docstring on that lemma for the
   full plan), discharged via the UFD `prime ↔ irreducible` norm-split.

Given (2), the main theorem is immediate: pick `z` with `N(z) = p`, write
`N(z) = z.re² - z.re·z.im + z.im²`, and apply (1).

## Status

- `eisenstein_form_to_x_sq_add_three_y_sq` — proved (pure `ℤ`, `ring`-closed
  in each parity branch).
- `eisensteinSqrtNegThree_sq` (`θ² = -3`) — proved (splitting step 2).
- `ofInt_sub_sqrt_mul_add_sqrt` (`(c-θ)(c+θ) = c²+3`) — proved (splitting step 3).
- `isUnit_iff_norm_eq_one` — proved (unit ↔ `N = 1`, via `norm_mul` /
  `z · conj z = N(z)`; step-6 ingredient).
- `exists_eisenstein_norm_eq_prime` — **proved** (the UFD `prime ↔ irreducible`
  norm-split extraction, steps 1–7: QR square root → lift to `ℤ` → factor in
  `ℤ[ω]` → `p ∤` either factor → `p` not prime → (UFD) reducible → `norm_mul`
  gives `N(α) = N(β) = p` via the `ℕ` divisor structure of `p²`).
- `sq_add_three_sq_of_prime_one_mod_three` — **proved** (no remaining gap).

axiomCount: 0  ·  sorryCount: 0 (Docker-verified, 7744 jobs)
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

/-- The Eisenstein norm of an integer is its square: `N(ofInt n) = n²`. -/
theorem norm_ofInt (n : ℤ) : Eisenstein.norm (Eisenstein.ofInt n) = n ^ 2 := by
  simp only [Eisenstein.norm, Eisenstein.re_ofInt, Eisenstein.im_ofInt]; ring

/-- An Eisenstein integer is a unit iff its norm is `1`. The forward direction
uses multiplicativity of the norm (a unit's norm divides `1` and is positive);
the reverse uses `z · conj z = ⟨N(z), 0⟩`, so `N(z) = 1` exhibits `conj z` as a
multiplicative inverse. This is step 6's key ingredient: nonunit ⇒ `N > 1`. -/
theorem isUnit_iff_norm_eq_one (z : Eisenstein) :
    IsUnit z ↔ Eisenstein.norm z = 1 := by
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Eisenstein.norm z * Eisenstein.norm w = 1 := by
      rw [← Eisenstein.norm_mul, hw, Eisenstein.norm_one]
    have hz0 : z ≠ 0 := hu.ne_zero
    have hpos : 0 < Eisenstein.norm z := Eisenstein.norm_pos_of_ne_zero hz0
    have hdvd : Eisenstein.norm z ∣ 1 := ⟨Eisenstein.norm w, hmul.symm⟩
    have hle : Eisenstein.norm z ≤ 1 := Int.le_of_dvd one_pos hdvd
    omega
  · intro hn
    have hzc : z * Eisenstein.conj z = 1 := by
      rw [Eisenstein.mul_conj, hn]; ext <;> simp
    exact ⟨⟨z, Eisenstein.conj z, hzc, by rw [mul_comm]; exact hzc⟩, rfl⟩

/-- **Splitting argument (proved).** For a prime `p ≡ 1 (mod 3)` there is an
Eisenstein integer whose norm is `p`.

Proof (the steps below are exactly the proof structure):

1. From `p ≡ 1 (mod 3)` and `legendreSym_neg_three_eq_one_iff` (parent file),
   `legendreSym p (-3) = 1`, hence `∃ c : ℤ, c² ≡ -3 (mod p)`
   (`legendreSym.eq_one_iff`, then lift the `ZMod p` root to an integer).

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

Standard algebraic number theory, formalised here via Mathlib's
`UniqueFactorizationMonoid.irreducible_iff_prime` (available because the parent
`instEuclideanDomain` makes `ℤ[ω]` a PID, hence a UFD). -/
theorem exists_eisenstein_norm_eq_prime {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ z : Eisenstein, Eisenstein.norm z = (p : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hmod
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hmod
  -- Step 1: `(-3 / p) = 1`, hence `-3` is a nonzero square mod `p`.
  have hleg : legendreSym p (-3) = 1 :=
    (legendreSym_neg_three_eq_one_iff p hp2 hp3).mpr hmod
  have hns : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have h3 : (p : ℤ) ∣ 3 := (dvd_neg).mp hdvd
    have hle : (p : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) h3
    have hge : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hne2 : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
    have hne3 : (p : ℤ) ≠ 3 := by exact_mod_cast hp3
    omega
  have hsq : IsSquare ((-3 : ℤ) : ZMod p) := (legendreSym.eq_one_iff p hns).mp hleg
  obtain ⟨r, hr⟩ := hsq
  -- Lift the square root to an integer `c` with `(c : ZMod p) = r`.
  set c : ℤ := ((r.val : ℕ) : ℤ) with hc_def
  have hcr : (c : ZMod p) = r := by
    rw [hc_def]; push_cast; simp [ZMod.natCast_val, ZMod.cast_id]
  -- Hence `p ∣ c² + 3` in `ℤ`.
  have hdvd_int : (p : ℤ) ∣ c ^ 2 + 3 := by
    have hrr : (r * r : ZMod p) = -3 := by
      have h := hr.symm; push_cast at h; exact h
    have h0 : ((c ^ 2 + 3 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hcr, pow_two, hrr]; ring
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  -- Step 3: factor `c² + 3 = (c - θ)(c + θ)` in `ℤ[ω]`, so `p ∣ (c - θ)(c + θ)`.
  set A : Eisenstein := Eisenstein.ofInt c - eisensteinSqrtNegThree with hA
  set B : Eisenstein := Eisenstein.ofInt c + eisensteinSqrtNegThree with hB
  have hAB : A * B = Eisenstein.ofInt (c ^ 2 + 3) := ofInt_sub_sqrt_mul_add_sqrt c
  have hp_dvd_prod : Eisenstein.ofInt (p : ℤ) ∣ A * B := by
    rw [hAB]
    obtain ⟨k, hk⟩ := hdvd_int
    exact ⟨Eisenstein.ofInt k, by
      rw [hk]; ext <;>
        simp [Eisenstein.mul_re, Eisenstein.mul_im, Eisenstein.re_ofInt,
          Eisenstein.im_ofInt]⟩
  -- `ofInt p` is a nonzero nonunit (`N(ofInt p) = p² ≥ 4`).
  have hp_norm : Eisenstein.norm (Eisenstein.ofInt (p : ℤ)) = (p : ℤ) ^ 2 := norm_ofInt _
  have hge2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have hp_not_unit : ¬ IsUnit (Eisenstein.ofInt (p : ℤ)) := by
    rw [isUnit_iff_norm_eq_one, hp_norm]; intro h; nlinarith [h, hge2]
  have hp_ne_zero : Eisenstein.ofInt (p : ℤ) ≠ 0 := by
    intro h
    have hn : Eisenstein.norm (Eisenstein.ofInt (p : ℤ)) = 0 := by rw [h]; exact Eisenstein.norm_zero
    rw [hp_norm] at hn; nlinarith [hn, hge2]
  -- Step 4: `p` divides neither factor (their `ω`-coordinates are `∓2`, `p ∤ 2`).
  have him_dvd : ∀ {w : Eisenstein}, Eisenstein.ofInt (p : ℤ) ∣ w → (p : ℤ) ∣ w.im := by
    rintro w ⟨t, ht⟩
    exact ⟨t.im, by
      rw [ht]; simp [Eisenstein.mul_im, Eisenstein.re_ofInt, Eisenstein.im_ofInt]⟩
  have hA_im : A.im = -2 := by
    rw [hA]; simp [Eisenstein.sub_im, Eisenstein.im_ofInt, eisensteinSqrtNegThree_im]
  have hB_im : B.im = 2 := by
    rw [hB]; simp [Eisenstein.add_im, Eisenstein.im_ofInt, eisensteinSqrtNegThree_im]
  have hnotA : ¬ Eisenstein.ofInt (p : ℤ) ∣ A := by
    intro hd
    have hdim := him_dvd hd; rw [hA_im] at hdim
    have h2 : (p : ℤ) ∣ 2 := (dvd_neg).mp hdim
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
    have hne2 : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
    omega
  have hnotB : ¬ Eisenstein.ofInt (p : ℤ) ∣ B := by
    intro hd
    have hdim := him_dvd hd; rw [hB_im] at hdim
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdim
    have hne2 : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
    omega
  -- Step 5: so `ofInt p` is not prime, hence (UFD) not irreducible: it factors.
  have hnotprime : ¬ Prime (Eisenstein.ofInt (p : ℤ)) := by
    intro hpr
    rcases hpr.2.2 A B hp_dvd_prod with h | h
    · exact hnotA h
    · exact hnotB h
  have hnotirr : ¬ Irreducible (Eisenstein.ofInt (p : ℤ)) := fun h =>
    hnotprime (UniqueFactorizationMonoid.irreducible_iff_prime.mp h)
  rw [irreducible_iff, not_and_or] at hnotirr
  rcases hnotirr with h | h
  · exact absurd (not_not.mp h) hp_not_unit
  push_neg at h
  obtain ⟨a, b, hab, hna, hnb⟩ := h
  -- Step 6: `p² = N(a)·N(b)` with both factors `> 1`.
  have hnorm_eq : (p : ℤ) ^ 2 = Eisenstein.norm a * Eisenstein.norm b := by
    have hm := Eisenstein.norm_mul a b
    rw [← hab, hp_norm] at hm; exact hm
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hp_ne_zero hab
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hp_ne_zero hab
  have hnaP : 0 < Eisenstein.norm a := Eisenstein.norm_pos_of_ne_zero ha0
  have hnbP : 0 < Eisenstein.norm b := Eisenstein.norm_pos_of_ne_zero hb0
  have hna1 : Eisenstein.norm a ≠ 1 := fun hh => hna ((isUnit_iff_norm_eq_one a).mpr hh)
  have hnb1 : Eisenstein.norm b ≠ 1 := fun hh => hnb ((isUnit_iff_norm_eq_one b).mpr hh)
  have hna2 : 2 ≤ Eisenstein.norm a := by omega
  have hnb2 : 2 ≤ Eisenstein.norm b := by omega
  -- Step 7: transfer to `ℕ`; divisors of `p²` are `1, p, p²`, so `N(a) = p`.
  set Na := (Eisenstein.norm a).toNat with hNa_def
  set Nb := (Eisenstein.norm b).toNat with hNb_def
  have hNac : (Na : ℤ) = Eisenstein.norm a := Int.toNat_of_nonneg hnaP.le
  have hNbc : (Nb : ℤ) = Eisenstein.norm b := Int.toNat_of_nonneg hnbP.le
  have hNa2 : 2 ≤ Na := by omega
  have hNb2 : 2 ≤ Nb := by omega
  have hprod_nat : Na * Nb = p ^ 2 := by
    have h1 : (Na : ℤ) * (Nb : ℤ) = (p : ℤ) ^ 2 := by rw [hNac, hNbc]; exact hnorm_eq.symm
    exact_mod_cast h1
  have hNa_dvd : Na ∣ p ^ 2 := ⟨Nb, hprod_nat.symm⟩
  obtain ⟨m, hm_le, hm⟩ := (Nat.dvd_prime_pow hp).mp hNa_dvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; rw [pow_zero] at hm; omega
    · exact h0
  have hm_ne2 : m ≠ 2 := by
    intro h2; subst h2
    rw [hm] at hprod_nat
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    have heq : p ^ 2 * Nb = p ^ 2 * 1 := by rw [mul_one]; exact hprod_nat
    have hNb1 := Nat.eq_of_mul_eq_mul_left hp2pos heq
    omega
  have hm_eq : m = 1 := by omega
  subst hm_eq
  rw [pow_one] at hm
  refine ⟨a, ?_⟩
  rw [← hNac]; exact_mod_cast hm

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
