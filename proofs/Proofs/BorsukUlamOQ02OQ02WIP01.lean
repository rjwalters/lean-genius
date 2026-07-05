import Proofs.BorsukUlam
import Mathlib.Tactic

/-
# Equivariant Borsuk-Ulam for Free Involutions (completion of BorsukUlamOQ02OQ02)

*Open question* (`borsuk-ulam-oq-02-oq-02-wip-01`): the parent file
`BorsukUlamOQ02OQ02` set up equivariant maps for compact Lie groups but left the
main theorem as the placeholder `EquivariantBorsukUlam := True`, observing that a
full compact-Lie-group treatment needs ~2000 lines of equivariant cohomology /
degree theory that Mathlib lacks.

This file replaces that placeholder with a *genuine* formal statement and derives
real consequences, following the same discipline used for classical Borsuk-Ulam
(`Proofs.BorsukUlam`): the deep topological input is isolated as a single named
axiom, and everything else is proved from it.

## What is formalized here

1. **General equivariant maps** between two explicit group actions (typeclass-free,
   so the framework applies uniformly to antipodal, involution, and Lie-group
   actions without instance plumbing).

2. **The ℤ/2 (free-involution) Borsuk-Ulam theorem, axiomatized.**
   For a free involution `σ` on `Sⁿ` and a fixed-point-free (away from 0) map `τ`
   on `ℝⁿ`, there is no continuous `(σ, τ)`-equivariant map `Sⁿ → ℝⁿ` that avoids
   `0`. This is the standard `G = ℤ/2` case of the general equivariant Borsuk-Ulam
   (Dold's theorem, 1983). It strictly generalizes the classical odd-map axiom in
   `Proofs.BorsukUlam`, which is the special case `σ = τ = negation`.

3. **`equivariant_borsuk_ulam`**: the usable zero-existence form -- every
   continuous equivariant map from the sphere into a strictly lower-dimensional
   space *vanishes somewhere on the sphere*. This is proved from the axiom.

4. **`classical_of_free_involution`**: a genuine reduction showing the framework
   subsumes the gallery's classical result -- we re-derive the *exact* classical
   theorem `BorsukUlam.HasAntipodalPair` from `equivariant_borsuk_ulam`,
   *without* using the classical odd-map axiom.

## Status
- [x] General equivariant map framework (typeclass-free)
- [x] Free-involution Borsuk-Ulam axiom (the single topological input)
- [x] Zero-existence theorem for arbitrary free involutions (proved)
- [x] Classical Borsuk-Ulam recovered as an instance (proved, non-circular)
- [ ] Full compact-Lie-group generalization (still needs equivariant cohomology)

The result is **axiomatized**: it depends on `borsuk_ulam_free_involution`, the
ℤ/2 equivariant no-retraction principle. No `sorry`.
-/

namespace BorsukUlamOQ02OQ02WIP01

open BorsukUlam

variable (n : ℕ)

/-! ## Part 1: General equivariant maps (typeclass-free)

We describe a group action by an explicit "action function" `a : G → V → V`
(`a g` is the map "act by `g`"). A map `f : V → W` is equivariant for actions
`aV`, `aW` when it intertwines them: `f (aV g x) = aW g (f x)`. Keeping the action
explicit (rather than via `SMul`) lets the same definitions cover the antipodal
action, an arbitrary free involution, and a linear Lie-group action with no
instance bookkeeping. -/

/-- `f` intertwines the actions `aV` (on the source) and `aW` (on the target). -/
def IsEquivariant' {G V W : Type*} (aV : G → V → V) (aW : G → W → W) (f : V → W) : Prop :=
  ∀ (g : G) (x : V), f (aV g x) = aW g (f x)

/-- The identity map is equivariant for any single action. -/
theorem isEquivariant'_id {G V : Type*} (aV : G → V → V) :
    IsEquivariant' aV aV (id : V → V) := fun _ _ => rfl

/-- Composition of equivariant maps is equivariant. -/
theorem isEquivariant'_comp {G V W X : Type*}
    {aV : G → V → V} {aW : G → W → W} {aX : G → X → X}
    {f : V → W} {g' : W → X}
    (hf : IsEquivariant' aV aW f) (hg : IsEquivariant' aW aX g') :
    IsEquivariant' aV aX (g' ∘ f) := by
  intro g x
  simp only [Function.comp_apply, hf g x, hg g (f x)]

/-! ## Part 2: The free-involution (ℤ/2) Borsuk-Ulam axiom

An **involution** `σ` satisfies `σ (σ x) = x`. It is **free on the sphere** when
`σ x ≠ x` for every sphere point (equivalently, the generated ℤ/2-action has no
fixed points on `Sⁿ`). The target map `τ` models a linear ℤ/2-action on `ℝⁿ`: it
fixes `0` and is free away from `0`.

The following axiom is the `G = ℤ/2` instance of the general equivariant
Borsuk-Ulam theorem (Dold, 1983): a continuous equivariant map from a free
ℤ/2-sphere into a strictly lower-dimensional free ℤ/2-representation cannot avoid
the origin. Topologically, normalizing such a map would yield a ℤ/2-equivariant
map `Sⁿ → Sⁿ⁻¹` between free actions, contradicting the Borsuk-Ulam / Dold
dimension bound. This requires equivariant algebraic topology beyond current
Mathlib, so it is isolated here as the single assumption.

This generalizes `BorsukUlam.no_continuous_odd_nonzero_on_sphere`, which is the
special case `σ = τ = fun x => -x`. -/
axiom borsuk_ulam_free_involution
    (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hn : n ≥ 1)
    (hσinv : ∀ x, σ (σ x) = x)
    (hσsphere : ∀ x ∈ Sphere n, σ x ∈ Sphere n)
    (hσfree : ∀ x ∈ Sphere n, σ x ≠ x)
    (hτzero : τ 0 = 0)
    (hτfree : ∀ v, v ≠ 0 → τ v ≠ v) :
    ¬ ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n),
        Continuous h ∧ (∀ x ∈ Sphere n, h x ≠ 0) ∧
        (∀ x, h (σ x) = τ (h x))

/-! ## Part 3: The general zero-existence theorem

The usable consequence: any continuous equivariant map from the sphere into the
lower-dimensional space must vanish somewhere on the sphere. This is proved from
the axiom by contradiction (a nowhere-zero map would be exactly the forbidden
object). It generalizes classical Borsuk-Ulam from the specific antipodal map to
an *arbitrary* free involution. -/
theorem equivariant_borsuk_ulam
    (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hn : n ≥ 1)
    (hσinv : ∀ x, σ (σ x) = x)
    (hσsphere : ∀ x ∈ Sphere n, σ x ∈ Sphere n)
    (hσfree : ∀ x ∈ Sphere n, σ x ≠ x)
    (hτzero : τ 0 = 0)
    (hτfree : ∀ v, v ≠ 0 → τ v ≠ v)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous h)
    (hequiv : ∀ x, h (σ x) = τ (h x)) :
    ∃ x ∈ Sphere n, h x = 0 := by
  by_contra hcon
  push_neg at hcon
  exact borsuk_ulam_free_involution n σ τ hn hσinv hσsphere hσfree hτzero hτfree
    ⟨h, hcont, hcon, hequiv⟩

/-! ## Part 4: The formal statement replacing the parent's `True` placeholder

`BorsukUlamOQ02OQ02.EquivariantBorsukUlam` was defined as `True`. Here is the real
mathematical content it stood for: the zero-existence conclusion for every free
involution and equivariant map at a fixed dimension `n`. -/
def EquivariantBorsukUlamStatement : Prop :=
  ∀ (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    n ≥ 1 →
    (∀ x, σ (σ x) = x) →
    (∀ x ∈ Sphere n, σ x ∈ Sphere n) →
    (∀ x ∈ Sphere n, σ x ≠ x) →
    τ 0 = 0 →
    (∀ v, v ≠ 0 → τ v ≠ v) →
    ∀ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)),
      Continuous h → (∀ x, h (σ x) = τ (h x)) →
      ∃ x ∈ Sphere n, h x = 0

/-- The stated principle holds (it is exactly `equivariant_borsuk_ulam`). -/
theorem equivariantBorsukUlamStatement_holds :
    EquivariantBorsukUlamStatement n := by
  intro σ τ hn hσinv hσsphere hσfree hτzero hτfree h hcont hequiv
  exact equivariant_borsuk_ulam n σ τ hn hσinv hσsphere hσfree hτzero hτfree h hcont hequiv

/-! ## Part 5: Recovering classical Borsuk-Ulam as an instance

The antipodal action `σ = τ = negation` is a free involution, so the general
theorem specializes to the *exact* classical gallery result
`BorsukUlam.HasAntipodalPair` -- proved here **without** invoking the classical
odd-map axiom, demonstrating that the involution framework genuinely subsumes it. -/

/-- In a real vector space, `-x = x` forces `x = 0` (no 2-torsion). -/
theorem eq_zero_of_neg_eq {m : ℕ} {x : EuclideanSpace ℝ (Fin m)}
    (h : -x = x) : x = 0 := by
  have e : x + x = 0 := by rw [← neg_add_cancel x, h]
  have h2 : (2 : ℝ) • x = 0 := by rw [two_smul]; exact e
  rcases smul_eq_zero.mp h2 with h0 | h0
  · norm_num at h0
  · exact h0

/-- Negation is a free involution on the sphere: `-x ≠ x` for `x ∈ Sⁿ`. -/
theorem neg_ne_self_on_sphere {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ Sphere n) : -x ≠ x := by
  rw [Sphere, Metric.mem_sphere, dist_zero_right] at hx
  intro heq
  rw [eq_zero_of_neg_eq heq, norm_zero] at hx
  exact one_ne_zero hx.symm

/-- **Classical Borsuk-Ulam, recovered.** Every continuous `f : Sⁿ → ℝⁿ`
(`n ≥ 1`) has an antipodal pair `f x = f (-x)` -- derived from the general
free-involution theorem via the gadget `g(x) = f x - f (-x)`, with no appeal to
`BorsukUlam.no_continuous_odd_nonzero_on_sphere`. -/
theorem classical_of_free_involution (hn : n ≥ 1) (f : SphereFun n) :
    HasAntipodalPair n f := by
  by_contra hcon
  -- The gadget g(x) = f x - f(-x) is continuous, nonzero on the sphere, and odd.
  have hcont : Continuous (gadget n f) := gadget_continuous n f
  have hnz : ∀ x ∈ Sphere n, gadget n f x ≠ 0 :=
    gadget_nonzero_of_no_antipodal n f hcon
  have hodd : ∀ x, gadget n f (-x) = -gadget n f x := by
    intro x
    simpa only [antipode] using gadget_odd n f x
  -- Apply the general theorem with σ = τ = negation.
  obtain ⟨x, hx, hgx⟩ :=
    equivariant_borsuk_ulam n (fun x => -x) (fun v => -v) hn
      (fun x => by simp)
      (fun x hx => by simpa only [antipode] using antipode_on_sphere n hx)
      (fun x hx => neg_ne_self_on_sphere n hx)
      (by simp)
      (fun v hv heq => hv (eq_zero_of_neg_eq heq))
      (gadget n f) hcont hodd
  -- A zero of the gadget is exactly an antipodal pair, contradicting `hcon`.
  exact hnz x hx hgx
