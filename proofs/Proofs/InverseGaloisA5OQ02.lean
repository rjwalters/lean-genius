import Mathlib

/-
# PSL(2,7) (order 168) as a Galois Group over ℚ — Trinks' polynomial (Inverse-Galois A₅, OQ-02)

## The open question

Extend the gallery's `inverse-galois-a5` (an explicit quintic with Galois group A₅,
the smallest non-solvable simple group) to the *next* simple non-solvable group,
`PSL(2,7) ≅ GL(3,2)`, the simple group of order 168 (automorphism group of the Klein
quartic and of the Fano plane).

## The witness

Trinks' polynomial (Trinks 1968)

  `f(x) = x⁷ − 7x + 3`,    `Gal(f/ℚ) ≅ PSL(2,7)`.

PSL(2,7) acts on the 7 points of the Fano plane (the 7 nonzero vectors of 𝔽₂³), giving
a degree-7 permutation realization inside S₇.

## The certificate (proved exactly in `verify_trinks_psl27.py`)

1. `f mod 2 = x⁷ + x + 1` is irreducible over 𝔽₂  ⟹  f irreducible over ℚ  ⟹  transitive
   ⟹  `7 ∣ |Gal|`.
2. `disc(f) = 3⁸·7⁸ = 194481²` is a perfect square  ⟹  `Gal ⊆ A₇`.
3. Frobenius cycle types `{(7),(1,2,4),(1,3,3),(1,1,1,2,2)}` (first witnessing primes
   2, 13, 17, 79) give elements of orders 7, 4, 3  ⟹  `lcm(7,4,3) = 84 ∣ |Gal|`.
4. The degree-15 PSL(2,7)-resolvent (`[A₇ : PSL(2,7)] = 15`) has a rational root
   ⟹  `Gal` is conjugate *into* `PSL(2,7)`, i.e. `|Gal| ∣ 168`.
5. **Simplicity collapse** (the key structural insight): `84 ∣ |Gal|` and `|Gal| ∣ 168`
   leave only `|Gal| ∈ {84, 168}`; a subgroup of `PSL(2,7)` of order 84 would have
   index 2, hence be normal, contradicting the *simplicity* of `PSL(2,7)`.  Therefore
   `|Gal| = 168` and `Gal = PSL(2,7)`.

## What this file proves vs. axiomatizes

This is a *staged* `axiomatized` entry (the full ACT is genuinely multi-week: the
degree-15 resolvent of step 4 and a Lean construction of `PSL(2,7)` are the heavy
parts, neither of which is in Mathlib).

**Proved here (genuine, build-checkable group theory — the session's key content):**
* `simple168_subgroup_card_collapse` — step 5 as a general theorem: a subgroup of a
  simple group of order 168 with `84 ∣ |H|` is the whole group.  This is the rigorous
  backing for the "collapse" that removes the need to classify all transitive subgroups
  of A₇.
* `card_eq_168_of_embeds_in_simple168` — the reusable corollary: any group with
  `84 ∣ |G|` that injects into a simple group of order 168 has order exactly 168.
* `trinks_disc_is_square` — the discriminant value is a perfect square (`194481²`).
* `trinks_gal_card` — *derives* `|Gal| = 168` from the embedding axiom + cycle-type
  divisibility via `card_eq_168_of_embeds_in_simple168` (no `≠ 84` assumption).

**Axiomatized (the deep analytic certificate — now only TWO axioms, steps 1–4):**
* `trinks_gal_84_dvd`            — steps 1+3 (Dedekind cycle types ⟹ `84 ∣ |Gal|`).
* `trinks_gal_embeds_simple168`  — steps 1+2+4 (irreducibility + square disc + resolvent
                                   ⟹ an injection `Gal ↪ PSL(2,7)`, a simple group of
                                   order 168).

This consolidates the previous **three** axioms into **two**: the old
`trinks_gal_card_dvd_168` and `trinks_gal_card_ne_84` are now *theorems* — the
embedding implies the divisibility (Lagrange) and, via the proven
`simple168_subgroup_card_collapse`, excludes `|Gal| = 84` (an index-2 subgroup of a
simple group cannot exist).

Mirrors the `InverseGaloisA5.lean` template (which carries out the analogous A₅
argument with hand-built "square-disc ⟹ ⊆ Aₙ" and per-prime cycle-type lemmas).
The Mathlib API used in the collapse proof matches `AbelRuffiniOQ04OQ01.lean`
(`Subgroup.normal_of_index_eq_two`, `IsSimpleGroup.eq_bot_or_eq_top_of_normal`,
`Subgroup.card_mul_index`, `Subgroup.card_subgroup_dvd_card`).
-/

set_option linter.unusedVariables false

open Polynomial

namespace InverseGaloisA5OQ02

/-! ## The polynomial -/

/-- **Trinks' polynomial** `f(x) = x⁷ − 7x + 3` (Trinks 1968), with
`Gal(f/ℚ) ≅ PSL(2,7)`. -/
noncomputable def trinks : Polynomial ℚ := X ^ 7 - 7 * X + 3

/-! ## Step 2 (arithmetic part): the discriminant is a perfect square

`disc(f) = 37822859361 = 3⁸·7⁸ = (3⁴·7⁴)² = 194481²`.  This integer identity is the
square-discriminant witness behind `Gal ⊆ A₇` (the bridge "square disc ⟹ ⊆ Aₙ" itself
is hand-built in the A₅ template; the actual `Polynomial.discr trinks = …` computation
for a degree-7 polynomial is part of the deferred ACT). -/
theorem trinks_disc_is_square : (37822859361 : ℤ) = 194481 ^ 2 := by norm_num

/-- The discriminant value also factors as `3⁸·7⁸`, confirming the prime structure
behind the unramified primes `{3, 7}`. -/
theorem trinks_disc_factorization : (37822859361 : ℤ) = 3 ^ 8 * 7 ^ 8 := by norm_num

/-! ## Step 5: the simplicity collapse (general finite group theory)

This is the substantive content proved in this session.  It isolates *why* the
order-168 conclusion follows from the divisibility data, without enumerating the
transitive subgroups of A₇. -/

/-- **Simplicity collapse.**  Let `G` be a finite simple group of order 168.  Any
subgroup `H` with `84 ∣ |H|` is the whole group.

Reason: `|H| ∣ 168` (Lagrange) together with `84 ∣ |H|` forces `|H| ∈ {84, 168}`.
If `|H| = 84` then `[G : H] = 2`, so `H` is normal; but `G` is simple, so `H = ⊥`
or `H = ⊤`, neither of which has order 84 — contradiction.  Hence `|H| = 168 = |G|`,
i.e. `[G : H] = 1` and `H = ⊤`. -/
theorem simple168_subgroup_card_collapse
    {G : Type*} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hG : Nat.card G = 168) (H : Subgroup G) (h84 : 84 ∣ Nat.card H) :
    H = ⊤ := by
  have hdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hmul : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
  rw [hG] at hdvd hmul
  have hpos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : Nat.card H ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := h84
  -- `|H| ∈ {84, 168}`.
  have hcase : Nat.card H = 84 ∨ Nat.card H = 168 := by
    rw [hk] at hpos hle ⊢
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with h | h <;> subst h <;> omega
  rcases hcase with h84' | h168
  · -- Order 84 ⟹ index 2 ⟹ normal ⟹ contradiction with simplicity.
    exfalso
    have hidx : H.index = 2 := by rw [h84'] at hmul; omega
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases hsimple.eq_bot_or_eq_top_of_normal H inferInstance with h | h
    · rw [h, Subgroup.index_bot, hG] at hidx; omega
    · rw [h, Subgroup.index_top] at hidx; omega
  · -- Order 168 = |G| ⟹ index 1 ⟹ `H = ⊤`.
    have hidx : H.index = 1 := by rw [h168] at hmul; omega
    exact Subgroup.index_eq_one.mp hidx

/-- **Embedding corollary.**  If a finite group `Gal` with `84 ∣ |Gal|` injects into a
simple group of order 168, then `|Gal| = 168` (and the injection is an isomorphism onto
the target).  This is the abstract form of the certificate's conclusion: the analytic
steps 1–4 supply an injection `Gal ↪ PSL(2,7)` with `84 ∣ |Gal|`. -/
theorem card_eq_168_of_embeds_in_simple168
    {Gal P : Type*} [Group Gal] [Finite Gal] [Group P] [Finite P]
    (hP : IsSimpleGroup P) (hPcard : Nat.card P = 168)
    (φ : Gal →* P) (hφ : Function.Injective φ) (h84 : 84 ∣ Nat.card Gal) :
    Nat.card Gal = 168 := by
  have e : Gal ≃* φ.range := MonoidHom.ofInjective hφ
  have hcard_eq : Nat.card φ.range = Nat.card Gal := Nat.card_congr e.toEquiv.symm
  have h84' : 84 ∣ Nat.card φ.range := by rw [hcard_eq]; exact h84
  have htop : (φ.range : Subgroup P) = ⊤ :=
    simple168_subgroup_card_collapse hP hPcard φ.range h84'
  have hrange : Nat.card φ.range = Nat.card P := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [← hcard_eq, hrange, hPcard]

/-! ## The deep certificate facts (steps 1–4, specialized to `f`)

These encode the analytic inputs of the certificate.  Each is verified exactly in
`verify_trinks_psl27.py`; the Lean discharge is the deferred multi-week ACT
(Dedekind's theorem and the degree-15 resolvent are not in Mathlib). -/

/-- **Steps 1 + 3** (Dedekind cycle types).  `f mod 2 = x⁷+x+1` irreducible ⟹ a 7-cycle
(`7 ∣ |Gal|`); `f mod 13` has type `(1,2,4)` ⟹ an order-4 element (`4 ∣ |Gal|`);
`f mod 17` has type `(1,3,3)` ⟹ an order-3 element (`3 ∣ |Gal|`).  Hence
`lcm(7,4,3) = 84 ∣ |Gal|`. -/
axiom trinks_gal_84_dvd : 84 ∣ Nat.card trinks.Gal

/-- **Steps 1 + 2 + 4** (irreducibility + square discriminant + degree-15 resolvent),
stated in their natural geometric form: `Gal(f/ℚ)` embeds into a finite **simple**
group of order 168 (namely `PSL(2,7)`).  Irreducibility gives transitivity; the
square discriminant gives `Gal ⊆ A₇`; the PSL(2,7)-resolvent's rational root gives an
injection `Gal ↪ PSL(2,7)`.

This is the single honest analytic input: it is strictly stronger than the bare
divisibility `|Gal| ∣ 168` (which follows by Lagrange), and — crucially — it lets the
*proven* `simple168_subgroup_card_collapse` discharge the former separate
`|Gal| ≠ 84` assumption as a **theorem** (`trinks_gal_card` below).  Net effect:
this replaces the previous two axioms (`… ∣ 168` and `… ≠ 84`) with one. -/
axiom trinks_gal_embeds_simple168 :
    ∃ (P : Type) (_ : Group P) (_ : Finite P),
      IsSimpleGroup P ∧ Nat.card P = 168 ∧ ∃ φ : trinks.Gal →* P, Function.Injective φ

/-! ## Main result -/

/-- **Trinks' polynomial realizes a Galois group of order 168 over ℚ.**

`|Gal(f/ℚ)| = 168 = |PSL(2,7)|`, the second simple non-solvable Galois group realized
in the gallery after A₅.  The order is now *derived* — not assumed — from the embedding
input `trinks_gal_embeds_simple168` and the cycle-type divisibility
`trinks_gal_84_dvd`, via the proven abstract collapse
`card_eq_168_of_embeds_in_simple168`.  In particular the previous `… ≠ 84` axiom is
eliminated: an index-2 subgroup of a simple group cannot exist. -/
theorem trinks_gal_card : Nat.card trinks.Gal = 168 := by
  obtain ⟨P, instGP, instFP, hsimple, hPcard, φ, hφ⟩ := trinks_gal_embeds_simple168
  haveI := instGP
  haveI := instFP
  exact card_eq_168_of_embeds_in_simple168 hsimple hPcard φ hφ trinks_gal_84_dvd

end InverseGaloisA5OQ02
