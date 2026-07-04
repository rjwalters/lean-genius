/-
# The antipodal PARITY engine: Tucker's odd seed lives on the diameter edges

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk-Ulam from
abstract door-counting").

## Where this sits — the frontier handed off by the directed no-go

`SpernerTuckerDirectedAntipodalNoGo` proved that the directed net-flow strict-imbalance
seed `himb` (`#{boundary-in doors} < #{boundary-out doors}`) is **self-defeating on a
genuinely antipodal disc**: the orientation-reversing antipodal *door* involution pairs
each boundary-out door with a boundary-in door, forcing
`#{boundary-out} = #{boundary-in}` and killing the strict inequality.  The directed seed
is *anti-invariant* under the antipodal map, so it **cancels to `0`** on any symmetric
disc.  That file's explicit moral:

  > the correct seed must be a **parity** (mod-2) quantity — the odd count of
  > complementary boundary edges — which *survives* the antipodal involution instead of
  > being cancelled by it.

This file builds that parity engine and proves the exact structural fact that makes the
parity seed survive.

## The engine

`SpernerTuckerAntipodalParity.even_card_of_free_involution` already showed that a **free**
antipodal involution (no fixed points) forces an *even* count — which is precisely why the
raw antipodal boundary count is always even and can never be Tucker's odd seed by itself.
This file supplies the missing general law of which that is the `Fix = ∅` special case:

* `card_modEq_card_fixed_of_involution` — **for any involution `σ` on a finite set `s`,
  `#s ≡ #{fixed points of σ} (mod 2)`.**  The count's parity is carried *entirely by the
  fixed points*; the non-fixed points pair off into antipodal 2-orbits and contribute
  nothing mod 2.  (Mathlib has only the much heavier `p`-group
  `card_modEq_card_fixedPoints`; this elementary `ZMod 2` form is proved from the free
  case by splitting `s` into fixed and non-fixed parts.)

Applied to the complementary boundary doors under the antipodal door map `neg`:

* `antipodal_complementary_parity` — `Odd #{complementary doors}
  ↔ Odd #{self-antipodal complementary doors}`.  The **fixed** doors are the
  self-antipodal ones (`neg d = d`), i.e. the **antipodal-diameter edges** `{v, -v}`.  So
  the Tucker odd seed's parity is invariant under the antipodal map (it equals the parity
  of the diameter-edge count), unlike the directed `himb` seed which is anti-invariant.

* `even_complementary_of_free` — the sharp converse: if the antipodal action on the
  complementary doors is **free** (no diameter edge), the complementary count is *even*, so
  **Tucker's odd seed is impossible without a self-antipodal (diameter) edge.**  This
  recovers `even_card_of_free_involution` for the complementary doors and pins down exactly
  where the odd parity must come from: the diameter edges the directed net-flow seed is
  structurally blind to.

## Honest status

Parity *infrastructure*, not new Tucker geometry.  It converts the directed no-go's
prose moral into a machine-checked, reusable parity law and localises Tucker's odd seed
onto the antipodal-diameter edges.  The construction of a triangulation actually carrying
an odd number of diameter complementary edges (and the dimension recursion consuming it)
remains the open frontier — but the engine now has the *right invariant*.

Self-contained.  0 sorries, 0 axioms (propext / Classical.choice / Quot.sound only); no
`decide` / `native_decide`, no `Lean.ofReduceBool`.
-/
import Mathlib.Data.ZMod.Basic
import Proofs.SpernerTuckerAntipodalParity

namespace SpernerTuckerAntipodalParityEngine

open Finset

/-! ## The general involution parity law: `#s ≡ #Fix(σ) (mod 2)` -/

/-- **The parity of a finite set is carried by the fixed points of any involution on it.**
If `σ : α → α` maps a finite set `s` into itself (`hmaps`) and is an involution on it
(`hinv`), then

  `#s ≡ #{a ∈ s | σ a = a}  (mod 2)`.

The non-fixed points of `σ` pair off into antipodal 2-orbits (a *free* involution on the
subset `{a ∈ s | σ a ≠ a}`), whose count is therefore even by
`SpernerTuckerAntipodalParity.even_card_of_free_involution`; only the fixed points survive
mod `2`.  This is the general law of which the free case (`Fix = ∅ ⇒ even`) is the special
case, and it is exactly the mechanism that lets a **parity** seed survive an antipodal
symmetry that *cancels* a directed net-flow seed. -/
theorem card_modEq_card_fixed_of_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (σ : α → α)
    (hmaps : ∀ a ∈ s, σ a ∈ s) (hinv : ∀ a ∈ s, σ (σ a) = a) :
    s.card ≡ (s.filter fun a => σ a = a).card [MOD 2] := by
  classical
  -- Split `s` into fixed and non-fixed points of `σ`.
  have hsplit :
      (s.filter fun a => σ a = a).card + (s.filter fun a => ¬ σ a = a).card = s.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  set t : Finset α := s.filter (fun a => ¬ σ a = a) with ht
  -- `σ` maps the non-fixed part into itself.
  have hmem : ∀ a ∈ t, σ a ∈ t := by
    intro a ha
    rw [ht, mem_filter] at ha ⊢
    obtain ⟨has, hne⟩ := ha
    refine ⟨hmaps a has, ?_⟩
    rw [hinv a has]
    exact fun h => hne h.symm
  -- `σ` restricts to a FREE involution on the non-fixed subtype, hence even card.
  let σ' : {a // a ∈ t} → {a // a ∈ t} := fun x => ⟨σ x.1, hmem x.1 x.2⟩
  have hinv' : Function.Involutive σ' := by
    intro x
    apply Subtype.ext
    exact hinv x.1 (mem_filter.mp x.2).1
  have hfree' : ∀ x, σ' x ≠ x := by
    intro x h
    exact (mem_filter.mp x.2).2 (congrArg Subtype.val h)
  have heven : Even (Fintype.card {a // a ∈ t}) :=
    SpernerTuckerAntipodalParity.even_card_of_free_involution hinv' hfree'
  rw [Fintype.card_coe] at heven
  obtain ⟨k, hk⟩ := heven
  -- Assemble: `#s = #fixed + #t` with `#t` even, so `#s ≡ #fixed (mod 2)`.
  unfold Nat.ModEq
  omega

/-- **Parity form of the involution law.**  `Odd #s ↔ Odd #{fixed points}`.  This is the
directly usable "seed survives" statement: the odd parity of the whole set is present iff
it is present on the fixed points alone. -/
theorem odd_card_iff_odd_fixed_of_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (σ : α → α)
    (hmaps : ∀ a ∈ s, σ a ∈ s) (hinv : ∀ a ∈ s, σ (σ a) = a) :
    Odd s.card ↔ Odd (s.filter fun a => σ a = a).card := by
  have h : s.card % 2 = (s.filter fun a => σ a = a).card % 2 :=
    card_modEq_card_fixed_of_involution s σ hmaps hinv
  rw [Nat.odd_iff, Nat.odd_iff, h]

/-! ## Application: the antipodal complementary-door parity seed -/

variable {Door : Type*} [Fintype Door] [DecidableEq Door]
variable (neg : Door → Door) (comp : Door → Prop) [DecidablePred comp]

/-- **The Tucker parity seed is antipodally invariant.**  Let `neg : Door → Door` be the
antipodal door map (an involution) under which the complementary predicate `comp` is
invariant (`comp (neg d) ↔ comp d`).  Then

  `Odd #{complementary doors} ↔ Odd #{self-antipodal complementary doors}`.

The right-hand count is the number of complementary **antipodal-diameter edges**
(`neg d = d`).  So — in sharp contrast to the directed net-flow seed `himb`, which the
antipodal *door* involution forces to `0` (`SpernerTuckerDirectedAntipodalNoGo`) — the
parity seed is *invariant* under the antipodal map: its odd/even status equals that of the
diameter-edge count and therefore **survives** the symmetry. -/
theorem antipodal_complementary_parity
    (hinv : Function.Involutive neg) (hcomp : ∀ d, comp (neg d) ↔ comp d) :
    Odd (univ.filter comp).card ↔
      Odd (univ.filter (fun d => comp d ∧ neg d = d)).card := by
  have key := odd_card_iff_odd_fixed_of_involution (univ.filter comp) neg
    (fun d hd => by
      simp only [mem_filter, mem_univ, true_and] at hd ⊢
      exact (hcomp d).mpr hd)
    (fun d _ => hinv d)
  rwa [Finset.filter_filter] at key

/-- **Tucker's odd seed requires a diameter edge.**  If the antipodal action on the
complementary doors is **free** (no self-antipodal / diameter edge, `neg d ≠ d` for all
`d`), then the complementary-door count is *even* — so the Tucker odd seed is impossible.

This is the sharp localisation the directed no-go pointed to: the odd parity that closes
Tucker can only be supplied by the **antipodal-diameter edges** `{v, -v}` (the fixed points
of `neg`), the very edges the anti-invariant directed net-flow seed is structurally blind
to.  It recovers `SpernerTuckerAntipodalParity.even_card_of_free_involution` for the
complementary doors as the `Fix = ∅` special case of `antipodal_complementary_parity`. -/
theorem even_complementary_of_free
    (hinv : Function.Involutive neg) (hcomp : ∀ d, comp (neg d) ↔ comp d)
    (hfree : ∀ d, neg d ≠ d) :
    Even (univ.filter comp).card := by
  have hmaps : ∀ d ∈ univ.filter comp, neg d ∈ univ.filter comp := by
    intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact (hcomp d).mpr hd
  have h := card_modEq_card_fixed_of_involution (univ.filter comp) neg hmaps
    (fun d _ => hinv d)
  have hfix : ((univ.filter comp).filter fun d => neg d = d) = ∅ := by
    ext d
    simp only [mem_filter, mem_univ, true_and, not_mem_empty, iff_false, not_and]
    exact fun _ hd => hfree d hd
  rw [hfix, card_empty] at h
  rw [Nat.even_iff]
  unfold Nat.ModEq at h
  omega

/-! ## The diameter edges are automatically complementary

A concrete corollary at the labelling level: on the antipodal boundary a self-antipodal
edge is *always* complementary, so the fixed-point count above is exactly the number of
antipodal-diameter edges present in the triangulation. -/

/-- **A self-antipodal edge under an antipodal labelling is complementary.**  Model a door
as an unordered vertex pair and the complementary predicate as `λ u = - λ v`.  If the
labelling `λ` is antipodal (`λ (neg v) = - λ v`) and the door is self-antipodal
(`{u, v}` maps to `{neg u, neg v} = {u, v}` with `neg v = u`), then it is automatically
complementary: `λ u = λ (neg v) = - λ v`.  Hence every antipodal-diameter edge counts
toward the parity seed — the seed's parity equals the parity of the diameter-edge count. -/
theorem diameter_edge_complementary {V M : Type*} [Neg M]
    (lam : V → M) (negV : V → V)
    (hanti : ∀ v, lam (negV v) = - lam v)
    (u v : V) (hdiam : negV v = u) :
    lam u = - lam v := by
  rw [← hdiam, hanti]

#check @card_modEq_card_fixed_of_involution
#check @odd_card_iff_odd_fixed_of_involution
#check @antipodal_complementary_parity
#check @even_complementary_of_free
#check @diameter_edge_complementary

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms card_modEq_card_fixed_of_involution
#print axioms odd_card_iff_odd_fixed_of_involution
#print axioms antipodal_complementary_parity
#print axioms even_complementary_of_free
#print axioms diameter_edge_complementary

end SpernerTuckerAntipodalParityEngine
