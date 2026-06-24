/-
# General Orbit-Counting for Colorings under an Arbitrary Finite Group
## (burnside-counting-oq-03-oq-02)

**Open question** (from `burnside-counting-oq-03`): generalize the cyclic necklace
orbit-counting result to an **arbitrary finite group** acting on the positions — the
unweighted Cauchy–Frobenius / Burnside count for colorings.

Let `G` be a finite group acting on a finite set `X` (the positions), and color the
positions with `k` colors, i.e. a coloring is a function `c : X → Fin k`. The group acts
on colorings by `(g • c) x = c (g⁻¹ • x)`. For `g : G`, let

  `cyc g := Nat.card (orbitRel.Quotient (Subgroup.zpowers g) X)`

be the number of orbits of the cyclic subgroup `⟨g⟩` on `X` (equivalently, the number of
cycles of the permutation `x ↦ g • x`). We prove:

* **(A) Per-element fixed-point count** (`card_fixedBy_eq_pow_cyc`):
    `Nat.card (fixedBy (X → Fin k) g) = k ^ cyc g`.
  A coloring is fixed by `g` iff it is constant on each `⟨g⟩`-orbit, so fixed colorings
  biject with functions `(⟨g⟩-orbit quotient) → Fin k`.

* **(B) Burnside orbit-counting** (`sum_pow_cyc_eq_card_orbits_mul_card`):
    `∑ g : G, k ^ cyc g = (#distinct colorings) * |G|`,
  obtained from `(A)` and Mathlib's Burnside identity
  `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`. Hence the number of distinct
  colorings up to the `G`-symmetry is `(1/|G|) ∑_g k^{cyc g}`.

This is the group-agnostic master formula behind every concrete necklace/bracelet count in
the gallery: the cyclic value `k^{gcd(r,n)}` and the dihedral reflection counts are all
instances of `k^{cyc g}`.

The **full weighted Pólya cycle-index theorem** (cycle-index polynomial + weighted
generating function) is *out of scope*: Mathlib lacks cycle-index machinery. This leaf
proves the honest, tractable **unweighted** generalization, which is the genuine gallery gap.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

import Mathlib

open MulAction Finset

namespace BurnsideCountingOQ03OQ02

variable {G X : Type*} [Group G] [MulAction G X] {k : ℕ}

/-! ## Section I: The coloring action

`G` acts on colorings `X → Fin k` by permuting the domain: `(g • c) x = c (g⁻¹ • x)`.
The inverse makes this a genuine left action. There is no clash with Mathlib's
`Pi.mulAction` because `Fin k` carries no `G`-action. -/

/-- The domain-permutation action of `G` on colorings `X → Fin k`. -/
instance coloringAction : MulAction G (X → Fin k) where
  smul g c := fun x => c (g⁻¹ • x)
  one_smul c := by
    funext x
    show c (1⁻¹ • x) = c x
    rw [inv_one, one_smul]
  mul_smul g h c := by
    funext x
    change c ((g * h)⁻¹ • x) = c (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

/-- Unfold the coloring action. -/
@[simp] lemma coloring_smul_apply (g : G) (c : X → Fin k) (x : X) :
    (g • c) x = c (g⁻¹ • x) := rfl

/-! ## Section II: Fixed colorings are constant on `⟨g⟩`-orbits -/

/-- If `c` is fixed by `g`, then every element of the cyclic subgroup `⟨g⟩` fixes `c`.
    (The stabilizer of `c` is a subgroup containing `g`, hence contains `⟨g⟩`.) -/
lemma zpowers_smul_eq_of_fixed {g : G} {c : X → Fin k} (hc : g • c = c)
    {h : G} (hh : h ∈ Subgroup.zpowers g) : h • c = c := by
  have hg : g ∈ stabilizer G c := (mem_stabilizer_iff).2 hc
  exact (mem_stabilizer_iff).1 ((Subgroup.zpowers_le).2 hg hh)

/-- If `c` is fixed by `g`, it is constant along the `⟨g⟩`-action:
    `c (h • x) = c x` for any `h ∈ ⟨g⟩`. -/
lemma const_on_zpowers {g : G} {c : X → Fin k} (hc : g • c = c)
    {h : G} (hh : h ∈ Subgroup.zpowers g) (x : X) : c (h • x) = c x := by
  have hfix : h • c = c := zpowers_smul_eq_of_fixed hc hh
  have key := congrFun hfix (h • x)
  rw [coloring_smul_apply, inv_smul_smul] at key
  exact key.symm

/-! ## Section III: The orbit-quotient bijection

Fixed colorings of `g` biject with functions on the `⟨g⟩`-orbit quotient of `X`. -/

/-- The orbit quotient of the cyclic subgroup `⟨g⟩` acting on `X`. -/
abbrev CycQuot (g : G) : Type _ := orbitRel.Quotient (Subgroup.zpowers g) X

/-- The number of `⟨g⟩`-orbits on `X` (= number of cycles of `x ↦ g • x`). -/
noncomputable def cyc (g : G) : ℕ := Nat.card (CycQuot (X := X) g)

/-- **Key bijection.** A coloring fixed by `g` descends to a function on the
    `⟨g⟩`-orbit quotient (it is constant on orbits), and any such function pulls back to a
    fixed coloring. -/
noncomputable def fixedColoringEquiv (g : G) :
    {c : X → Fin k // g • c = c} ≃ (CycQuot (X := X) g → Fin k) where
  toFun := fun ⟨c, hc⟩ =>
    Quotient.lift c (by
      intro a b hab
      have hab' : a ∈ orbit (Subgroup.zpowers g) b := hab
      rw [mem_orbit_iff] at hab'
      obtain ⟨h, rfl⟩ := hab'
      exact const_on_zpowers hc h.2 b)
  invFun := fun f =>
    ⟨fun x => f (Quotient.mk _ x), by
      funext x
      show f (Quotient.mk _ (g⁻¹ • x)) = f (Quotient.mk _ x)
      congr 1
      exact Quotient.sound ⟨⟨g⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers g)⟩, rfl⟩⟩
  left_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    funext x
    rfl
  right_inv := by
    intro f
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-! ## Section IV: (A) per-element fixed-point count -/

/-- **(A)** The number of colorings fixed by `g` is `k ^ cyc g`. -/
theorem card_fixedBy_eq_pow_cyc [Finite X] (g : G) :
    Nat.card (fixedBy (X → Fin k) g) = k ^ cyc (X := X) g := by
  have e : (fixedBy (X → Fin k) g) ≃ (CycQuot (X := X) g → Fin k) :=
    (Equiv.subtypeEquivRight (fun c => mem_fixedBy)).trans (fixedColoringEquiv g)
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  rfl

/-! ## Section V: (B) Burnside orbit-counting (average over the group) -/

/-- The orbit quotient of the full coloring action: distinct colorings up to `G`-symmetry. -/
abbrev ColorOrbits : Type _ := orbitRel.Quotient G (X → Fin k)

/-- **(B)** Sum of the per-element fixed counts equals the number of distinct colorings
    times the group order: `∑ g, k ^ cyc g = (#distinct colorings) * |G|`. This is
    Burnside's averaging formula `#orbits = (1/|G|) ∑_g k^{cyc g}` in integer form. -/
theorem sum_pow_cyc_eq_card_orbits_mul_card [Fintype G] [Finite X] :
    (∑ g : G, k ^ cyc (X := X) g)
      = Nat.card (ColorOrbits (G := G) (X := X) (k := k)) * Nat.card G := by
  classical
  haveI : ∀ a : G, Fintype (fixedBy (X → Fin k) a) := fun a => Fintype.ofFinite _
  haveI : Fintype (ColorOrbits (G := G) (X := X) (k := k)) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X → Fin k)
  simp only [← Nat.card_eq_fintype_card] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun g _ => (card_fixedBy_eq_pow_cyc g).symm)

#check @card_fixedBy_eq_pow_cyc
#check @sum_pow_cyc_eq_card_orbits_mul_card

end BurnsideCountingOQ03OQ02
