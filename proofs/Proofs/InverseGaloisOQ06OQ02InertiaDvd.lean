/-
  Authentic deterministic half of the mod-p Dedekind route, via the
  ring-of-integers / decomposition-group API now present in Mathlib 4.26.

  Continues the `inverse-galois-oq-06-oq-02` track (mod-7 Dedekind input).

  ## What this file adds

  Every prior iteration on this slug established the deterministic half of
  Dedekind's theorem ("factorization type => cycle type => n | |Gal|")
  *abstractly*: it assumed the existence of a Galois automorphism whose action
  on the roots has a prescribed cycle type, then ran the group-theory
  consequence (`orderOf`-divides-card via the injective `galActionHom`).  That
  is a faithful model, but it takes the number-theoretic input (a Frobenius with
  known cycle type) as a hypothesis.

  Mathlib 4.26 now ships the genuine number-field machinery this was modelling:
  `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank`
  (the Galois form of the fundamental identity `Σ eᵢfᵢ = n`), the decomposition
  group / residue-field surjection `Ideal.Quotient.stabilizerHom`, and the
  arithmetic Frobenius element (`arithFrobAt`, `IsArithFrobAt`) in
  `Mathlib/RingTheory/Frobenius.lean`.  With them the deterministic half becomes
  a *theorem with no cycle-type hypothesis at all*: the residue-field degree
  (inertia degree) of any prime `P` over `p` divides the order of the Galois
  group `G`.  This is strictly cleaner than the `galActionHom`-cycle-type route
  because it needs no assumption on how any automorphism permutes the roots — it
  reads the divisibility directly off the fundamental identity.

  ## Honesty

  This does NOT discharge the open axiom `three_dvd_gal_card`.  The residual gap
  is now sharper: it is the Kummer–Dedekind step relating `q mod 7`'s
  factorization type `(1,1,3)` to the inertia degree `f = 3` of a prime over `7`
  in the ring of integers of `q.SplittingField`.  That reduction (which IS now
  assemblable from Mathlib's Kummer–Dedekind and the API used here) is the only
  remaining input; once `inertiaDeg p P = 3` is supplied for such a `P`, the
  corollary `dvd_card_of_inertiaDeg_eq` below closes `3 ∣ |G|` mechanically.
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Galois.IsGaloisGroup

namespace InverseGaloisOQ06OQ02InertiaDvd

open Ideal

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

/-- **Deterministic half of Dedekind, authentic form.**  For a finite group `G`
acting as the Galois group of `S` over `R`, the inertia degree (residue-field
degree) of any maximal prime `P` of `S` lying over a maximal prime `p` of `R`
divides `Nat.card G`.

This is exactly the divisibility the earlier abstract `galActionHom`
cycle-type bridges were modelling, but with no hypothesis on how any
automorphism permutes the roots: it falls straight out of the Galois form of
the fundamental identity `(#primes over p) · e · f = |G|`. -/
theorem inertiaDeg_dvd_card
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    p.inertiaDeg P ∣ Nat.card G := by
  have H := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  refine ⟨(p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G), ?_⟩
  rw [Ideal.inertiaDeg_algebraMap p P, ← H]; ring

/-- Concrete eliminator: if some maximal prime `P` over `p` has inertia degree
exactly `n`, then `n ∣ Nat.card G`.  With `n = 3` (the degree of the irreducible
cubic factor of `q mod 7`) this is precisely the `3 ∣ |Gal|` that the open axiom
`three_dvd_gal_card` asserts — now reduced to supplying such a `P`. -/
theorem dvd_card_of_inertiaDeg_eq
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] {n : ℕ} (hn : p.inertiaDeg P = n) :
    n ∣ Nat.card G := by
  rw [← hn]; exact inertiaDeg_dvd_card p P

/-- The `n = 3` specialization, matching the shape of the open axiom. -/
theorem three_dvd_card_of_inertiaDeg_three
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] (h3 : p.inertiaDeg P = 3) :
    3 ∣ Nat.card G :=
  dvd_card_of_inertiaDeg_eq p P h3

end InverseGaloisOQ06OQ02InertiaDvd
