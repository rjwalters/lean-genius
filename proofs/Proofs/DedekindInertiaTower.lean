import Mathlib

/-!
# Tower + Galois-uniformity brick for inertia degrees (inverse-Galois A₅, OQ-04)

This file isolates one abstract, reusable, `0`-axiom step in the ongoing effort to
discharge the last assumption of `Proofs.InverseGaloisA5`,

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

The companion file `Proofs.InverseGaloisA5DedekindInstantiation` already reduces that
axiom to the single sharp arithmetic fact

```
3 ∣ Ideal.inertiaDegIn (Q.under ℤ) (𝓞 q.SplittingField)
```

at an unramified prime `Q` over `7`, and its "residual gap" note spells out a three-step
route to prove it:

1. **Kummer–Dedekind** (`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`):
   the prime of `𝓞 ℚ(α)` matching the *irreducible cubic factor* of `q mod 7` has inertia
   degree `3`;
2. **inertia-degree multiplicativity in a tower** (`Ideal.inertiaDeg_algebra_tower`, which
   needs **no** Galois hypothesis on the non-normal middle field `ℚ(α)`): a prime `Q` of
   `𝓞 q.SplittingField` over that cubic prime has `3 ∣ inertiaDeg(Q ∣ 7)`;
3. **Galois uniformity** (`Ideal.inertiaDegIn_eq_inertiaDeg`): all primes of the *splitting
   field* over `7` share this inertia degree, so `3 ∣ inertiaDegIn (7)`.

This file packages steps **2 and 3** as a single divisibility statement,
`inertiaDeg_dvd_inertiaDegIn`, in full generality (an arbitrary tower `R ⊆ S ⊆ T` with
`T / R` Galois via a group `G`, `S` possibly non-normal). It thereby reduces the residual
gap to producing *one* intermediate prime `P` with `d ∣ inertiaDeg p P`, which is exactly
what the Kummer–Dedekind step of (1) supplies. Only ordinary foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) are used — no `sorry`, no new `axiom`.
-/

open Ideal

namespace DedekindInertiaTower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
  (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] (Q : Ideal T) [Q.IsMaximal]
  [P.LiesOver p] [Q.LiesOver P]

-- `G` and `Q` (with their instances) do not appear in the theorem *statements* below,
-- only in their proofs, so Lean would otherwise omit them from the contexts. Force their
-- inclusion so the intermediate prime `Q` and Galois group `G` are quantified arguments.
include G Q

/-- **Tower + Galois-uniformity brick.** Let `R ⊆ S ⊆ T` be a tower of commutative rings
with `T / R` Galois (Galois group `G`). If `p` is a maximal ideal of `R`, `P` a maximal
ideal of the (possibly non-normal) intermediate ring `S` lying over `p`, and `Q` a maximal
ideal of `T` lying over `P`, then the intermediate inertia degree `inertiaDeg p P` divides
the Galois-invariant inertia degree `inertiaDegIn p T`.

Proof: `inertiaDeg_algebra_tower` gives `inertiaDeg p Q = inertiaDeg p P * inertiaDeg P Q`
(no Galois hypothesis needed on the middle field `S`), and `inertiaDegIn_eq_inertiaDeg`
identifies `inertiaDegIn p T` with `inertiaDeg p Q` because `T / R` is Galois. Hence
`inertiaDeg p P` is a factor of `inertiaDegIn p T`. -/
theorem inertiaDeg_dvd_inertiaDegIn : inertiaDeg p P ∣ inertiaDegIn p T := by
  haveI : Q.LiesOver p := LiesOver.trans Q P p
  have htower : inertiaDeg p Q = inertiaDeg p P * inertiaDeg P Q :=
    inertiaDeg_algebra_tower p P Q
  have huniform : inertiaDegIn p T = inertiaDeg p Q :=
    inertiaDegIn_eq_inertiaDeg p Q G
  rw [huniform, htower]
  exact dvd_mul_right _ _

/-- **Reduction form.** To prove that a natural number `d` divides the Galois-invariant
inertia degree `inertiaDegIn p T` of the top field, it suffices to exhibit *one*
intermediate prime `P` (over `p`, below a chosen prime `Q` of `T`) with
`d ∣ inertiaDeg p P`. This is the shape consumed by the A₅ inverse-Galois argument: the
Kummer–Dedekind factorization of `q mod 7` yields a prime `P` of `𝓞 ℚ(α)` with
`inertiaDeg (7) P = 3`, and this lemma promotes `3 ∣ inertiaDeg (7) P` to
`3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)`. -/
theorem dvd_inertiaDegIn_of_dvd_inertiaDeg {d : ℕ} (hd : d ∣ inertiaDeg p P) :
    d ∣ inertiaDegIn p T :=
  hd.trans (inertiaDeg_dvd_inertiaDegIn G p P Q)

end DedekindInertiaTower
