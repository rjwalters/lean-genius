import Mathlib

/-!
# The modular counterexample to Maschke's theorem: `𝔽_p[ℤ/p]` is not semisimple

Maschke's theorem (the parent entry `maschke-theorem-oq-01`) asserts that for a finite group
`G` and a field `k` with `char k ∤ |G|`, every representation is completely reducible and the
group algebra `k[G]` is a semisimple ring.  The hypothesis `char k ∤ |G|` is **essential**:
this file records the cleanest witness to its sharpness.

Take `k = 𝔽_p` and `G = ℤ/p` (so `char k = p` divides `|G| = p`).  Then the group algebra

```
A = 𝔽_p[ℤ/p]
```

is **not** semisimple.  The obstruction is a single nonzero nilpotent element.  Writing
`g` for the basis generator indexed by `1 ∈ ℤ/p`, the *freshman's dream* in characteristic
`p` gives

```
(g - 1) ^ p = g ^ p - 1 ^ p = 1 - 1 = 0,
```

since `g ^ p = 1` (the group element has order `p`), while `g - 1 ≠ 0`.  Thus `A` contains a
nonzero nilpotent, so it is **not reduced**.  A commutative semisimple ring is reduced
(`Mathlib`'s low-priority instance `IsSemisimpleRing → IsReduced` for commutative rings, a
consequence of `Ring.jacobson A = ⊥`), so `A` cannot be semisimple.  Equivalently, complete
reducibility fails: some submodule (the augmentation ideal, generated here by `g - 1`) has no
complement.

The element `g - 1` is precisely a generator of the **augmentation ideal**
`I = ker(ε)` where `ε : 𝔽_p[ℤ/p] → 𝔽_p`, `∑ a_g g ↦ ∑ a_g`; the short exact sequence
`0 → I → 𝔽_p[ℤ/p] → 𝔽_p → 0` does not split.  Unlike a `p = 2` `decide` check, the argument
below is uniform in the prime `p`.

## What this file packages

* `MaschkeModularCounterexample.g_pow_card` — the generator has order `p`: `g ^ p = 1`.
* `MaschkeModularCounterexample.g_sub_one_pow_card` — freshman's dream: `(g - 1) ^ p = 0`.
* `MaschkeModularCounterexample.g_sub_one_ne_zero` — `g - 1 ≠ 0`.
* `MaschkeModularCounterexample.isNilpotent_g_sub_one` — `g - 1` is a nonzero nilpotent.
* `MaschkeModularCounterexample.not_isReduced` — `𝔽_p[ℤ/p]` is not reduced.
* `MaschkeModularCounterexample.not_isSemisimpleRing` — **the counterexample**: `𝔽_p[ℤ/p]`
  is not a semisimple ring.
* `MaschkeModularCounterexample.not_isSemisimpleModule` — equivalently, not semisimple as a
  module over itself.
* `MaschkeModularCounterexample.exists_submodule_no_complement` — complete reducibility fails:
  some subrepresentation has no complement.

## References

* H. Maschke, *Beweis des Satzes …*, Math. Ann. 52 (1899) 363-368.
* R. Brauer, *Über die Darstellung von Gruppen in Galoisschen Feldern*, 1935.
* Mathlib: `Mathlib/RingTheory/Jacobson/Semiprimary.lean` (semisimple commutative rings are
  reduced), `Mathlib/Algebra/CharP/Lemmas.lean` (`sub_pow_char`).
-/

open scoped MonoidAlgebra

namespace MaschkeModularCounterexample

variable (p : ℕ) [hp : Fact p.Prime]

/-- The cyclic group `ℤ/p`, written multiplicatively so that its group algebra is a
`MonoidAlgebra`. -/
abbrev G : Type := Multiplicative (ZMod p)

/-- The modular group algebra `A = 𝔽_p[ℤ/p]`, i.e. the regular representation of the cyclic
group of order `p` over the field with `p` elements. -/
abbrev A : Type := MonoidAlgebra (ZMod p) (G p)

/-- `A = 𝔽_p[ℤ/p]` has characteristic `p`, inherited from its scalar field `𝔽_p`. -/
instance : CharP (A p) p := charP_of_injective_algebraMap' (ZMod p) (A := A p) p

/-- The standard generator `g = [1]` of the group algebra: the basis element indexed by the
additive generator `1 ∈ ℤ/p`. -/
noncomputable def g : A p :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) (1 : ZMod p)

/-- **The generator has order `p`.** `g ^ p = 1`, because the underlying group element
`1 ∈ ℤ/p` satisfies `p • 1 = 0`. -/
theorem g_pow_card : (g p) ^ p = 1 := by
  have hp1 : (p • (1 : ZMod p)) = 0 := by
    rw [nsmul_eq_mul, mul_one]; exact ZMod.natCast_self p
  show (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) (1 : ZMod p)) ^ p = 1
  rw [MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, hp1, ofAdd_zero, MonoidAlgebra.one_def]

/-- **Freshman's dream.** In characteristic `p`, `(g - 1) ^ p = g ^ p - 1 ^ p = 1 - 1 = 0`,
so `g - 1` is nilpotent. -/
theorem g_sub_one_pow_card : (g p - 1) ^ p = 0 := by
  rw [sub_pow_char, g_pow_card, one_pow, sub_self]

/-- The generator differs from the identity: `g ≠ 1`, since `1 ≠ 0` in `𝔽_p`. -/
theorem g_ne_one : g p ≠ 1 := by
  intro hg
  rw [show g p = MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) (1 : ZMod p) from rfl,
    MonoidAlgebra.one_def, Finsupp.single_eq_single_iff] at hg
  rcases hg with ⟨ha, -⟩ | ⟨hb, -⟩
  · exact one_ne_zero (ofAdd_eq_one.mp ha)
  · exact one_ne_zero hb

/-- `g - 1 ≠ 0`: the nilpotent witness is genuinely nonzero. -/
theorem g_sub_one_ne_zero : (g p - 1 : A p) ≠ 0 :=
  sub_ne_zero.mpr (g_ne_one p)

/-- **The augmentation generator `g - 1` is a nonzero nilpotent.** This single element is the
entire obstruction to semisimplicity. -/
theorem isNilpotent_g_sub_one : IsNilpotent (g p - 1 : A p) :=
  ⟨p, g_sub_one_pow_card p⟩

/-- **`𝔽_p[ℤ/p]` is not reduced.** It contains the nonzero nilpotent `g - 1`. -/
theorem not_isReduced : ¬ IsReduced (A p) := fun h => by
  haveI := h
  exact g_sub_one_ne_zero p (isNilpotent_iff_eq_zero.mp (isNilpotent_g_sub_one p))

/-- **The modular counterexample to Maschke's theorem.** Over the field `𝔽_p`, the group
algebra `𝔽_p[ℤ/p]` is *not* a semisimple ring.  This shows the hypothesis `char k ∤ |G|` of
Maschke's theorem cannot be dropped: a commutative semisimple ring is reduced, but
`𝔽_p[ℤ/p]` has the nonzero nilpotent `g - 1`. -/
theorem not_isSemisimpleRing : ¬ IsSemisimpleRing (A p) := fun h => by
  haveI := h
  exact not_isReduced p inferInstance

/-- Equivalently, `𝔽_p[ℤ/p]` is not semisimple as a module over itself: the regular
representation of `ℤ/p` over `𝔽_p` is not completely reducible. -/
theorem not_isSemisimpleModule : ¬ IsSemisimpleModule (A p) (A p) :=
  not_isSemisimpleRing p

/-- **Complete reducibility fails.** Some subrepresentation of `𝔽_p[ℤ/p]` (the augmentation
ideal) has *no* complement: there is no internal direct-sum decomposition splitting it off. -/
theorem exists_submodule_no_complement :
    ∃ I : Submodule (A p) (A p), ¬ ∃ J : Submodule (A p) (A p), IsCompl I J := by
  by_contra hcon
  push_neg at hcon
  haveI : ComplementedLattice (Submodule (A p) (A p)) := ⟨hcon⟩
  exact not_isSemisimpleModule p ⟨⟩

end MaschkeModularCounterexample
