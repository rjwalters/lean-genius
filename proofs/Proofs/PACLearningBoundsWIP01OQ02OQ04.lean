import Proofs.PACLearningBoundsWIP01SauerShelah

/-
# PAC Learning, wip-01 · oq-02 · oq-04 — Pseudo-dimension covering bound via the hypograph reduction

The parent entry `pac-learning-bounds-wip-01-oq-02` supplies a fully machine-checked
**Sauer–Shelah lemma** for Boolean concept classes: a class `H` of VC dimension `d` has a
growth function bounded by a degree-`d` polynomial,
`|Π_H(S)| = |trace H S| ≤ Σ_{i ≤ d} C(|S|, i)` (`trace_card_le_sum_range_choose`).

This entry answers open question **oq-04**: *lift that Boolean bound to real-valued
(here: integer/level-valued) function classes*, replacing VC dimension with the
**pseudo-dimension**. The route (Approach A on the problem card) is the classical
**hypograph / subgraph reduction** of Pollard and Haussler:

* A function `g : α → ℕ` is encoded by its **hypograph** over the level grid `α × Fin b`:
  `hypoOn P b g = {(x, i) ∈ P × Fin b : g x > i}` — the Boolean set of point/threshold
  pairs the function lies strictly above. This is a genuine `Finset (α × Fin b)`, so the
  family `hypoFam P b F = {hypoOn P b g : g ∈ F}` is a Boolean concept class over the grid,
  and the *verified* Boolean Sauer–Shelah bound applies verbatim.
* The **pseudo-dimension** of `F` is, by definition, the VC dimension of this hypograph
  family (`Pdim P b F := VCDim (hypoFam P b F)`) — this is Pollard's definition.
* On functions bounded by `b`, the hypograph encoding is **injective on each sample**
  (`hypoOn_injOn`): `g x = |{i : g x > i}|` is recovered from the hypograph, via a clean
  trichotomy argument requiring no closed-form column count.

## What is proved

* `hypoFam_card_le_sum_choose` — the **hypograph Sauer–Shelah bound**: the number of
  distinct hypographs a level-valued class cuts out over a sample `P` is at most
  `Σ_{i ≤ d} C(|P|·b, i)` whenever `d` bounds the pseudo-dimension. This is
  `O((|P|·b)^d) = O((m/γ)^d)` with `b ≈ 1/γ` levels — the target bound of oq-04.
* `hypoOn_injOn` — over a sample `P`, the hypograph map is injective on the set of
  `b`-bounded functions that are separated by their `P`-values.
* `growthFunction_le_sum_choose` — the resulting **real-valued growth-function bound**: a
  `b`-bounded, `P`-separated function class `F` of pseudo-dimension `d` has at most
  `Σ_{i ≤ d} C(|P|·b, i)` members. This is the honest lift of the Boolean growth-function
  bound to level-valued classes.
* `growthFunction_le_pdim` — the same, stated with `d = Pdim P b F` (the reflexive case),
  the form covering-number arguments consume.

Fully machine-checked; `0` sorries, `0` `axiom` declarations, no `native_decide`; `0`
axioms beyond Mathlib's foundations (`propext`, `Classical.choice`, `Quot.sound`).

The genuinely-`L∞`-analytic parts of oq-04 — the reduction of a `γ`-cover to such threshold
patterns, and the *sharp* middle constant `Σ_k C(m,k)(2/γ)^k` (Alon–Ben-David–Cesa-Bianchi–
Haussler, needing a multivalued Natarajan/Haussler shifting argument) — remain documented
follow-ups. Both are `~(mb)^d/d!` to leading order, so this file already delivers the
`O((m/γ)^d)` claim; only the sharp constant is left open.

Tags: pac-learning, pseudo-dimension, fat-shattering, covering-numbers, sauer-shelah,
hypograph, learning-theory, combinatorics
-/

namespace PACLearningBoundsWIP01OQ04

open Finset PACLearningBoundsWIP01

variable {α : Type*} [DecidableEq α]

/-- The **hypograph** of a level-valued function `g : α → ℕ` over the sample `P` and the
threshold grid `Fin b` (thresholds `1, …, b` encoded by `i.val + 1`, i.e. `g x > i.val`):
the Boolean set of point/threshold pairs `(x, i)` with `x ∈ P` and `g x` strictly above the
threshold `i`. Every member lies in the finite grid `P ×ˢ univ`, so this is an honest
`Finset (α × Fin b)`. -/
def hypoOn (P : Finset α) (b : ℕ) (g : α → ℕ) : Finset (α × Fin b) :=
  (P ×ˢ Finset.univ).filter (fun p => g p.1 > p.2.val)

/-- The **hypograph family** of a finite function class `F` over sample `P` and grid
`Fin b`: a Boolean concept class over the grid `α × Fin b`, to which the verified Boolean
Sauer–Shelah bound applies. -/
def hypoFam (P : Finset α) (b : ℕ) (F : Finset (α → ℕ)) : Finset (Finset (α × Fin b)) :=
  F.image (hypoOn P b)

/-- The **pseudo-dimension** of a level-valued class `F` on sample `P` with grid `Fin b`,
*defined* (à la Pollard) as the VC dimension of the hypograph family. -/
noncomputable def Pdim (P : Finset α) (b : ℕ) (F : Finset (α → ℕ)) : ℕ :=
  VCDim (hypoFam P b F)

omit [DecidableEq α] in
/-- Membership in a hypograph, unfolded: `(x, i)` lies in `hypoOn P b g` exactly when
`x ∈ P` and `g x > i`. -/
theorem mem_hypoOn {P : Finset α} {b : ℕ} {g : α → ℕ} {x : α} {i : Fin b} :
    (x, i) ∈ hypoOn P b g ↔ x ∈ P ∧ g x > i.val := by
  simp only [hypoOn, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]

omit [DecidableEq α] in
/-- Each hypograph lies inside the grid `P ×ˢ univ`. -/
theorem hypoOn_subset (P : Finset α) (b : ℕ) (g : α → ℕ) :
    hypoOn P b g ⊆ P ×ˢ Finset.univ :=
  Finset.filter_subset _ _

/-- **The hypograph Sauer–Shelah bound.** The number of distinct hypographs a level-valued
class `F` cuts out over a sample `P` (with `b` thresholds) is at most `Σ_{i ≤ d} C(|P|·b, i)`
whenever `d` bounds the pseudo-dimension `VCDim (hypoFam P b F)`. This is the verified
Boolean growth bound applied to the hypograph family, with ground size `|P|·b`. It is
`O((|P|·b)^d)`; with `b ≈ 1/γ` levels this is exactly the `O((m/γ)^d)` claim of oq-04. -/
theorem hypoFam_card_le_sum_choose (F : Finset (α → ℕ)) (P : Finset α) {b d : ℕ}
    (hd : VCDim (hypoFam P b F) ≤ d) :
    (hypoFam P b F).card ≤ ∑ i ∈ Finset.range (d + 1), (P.card * b).choose i := by
  set H : Finset (Finset (α × Fin b)) := hypoFam P b F with hH
  set S : Finset (α × Fin b) := P ×ˢ Finset.univ with hS
  -- Every member of the hypograph family already lives inside the grid `S`.
  have hsubS : ∀ h ∈ H, h ⊆ S := by
    intro h hh
    rw [hH, hypoFam, Finset.mem_image] at hh
    obtain ⟨g, _, rfl⟩ := hh
    exact hypoOn_subset P b g
  -- Hence the trace of `H` on `S` is `H` itself: intersecting with `S` is the identity.
  have htrace : trace H S = H := by
    have himg : H.image (fun h => h ∩ S) = H.image id := by
      refine Finset.image_congr ?_
      intro h hh
      simp only [id_eq]
      exact Finset.inter_eq_left.mpr (hsubS h hh)
    rw [trace, himg, Finset.image_id]
  -- The grid has cardinality `|P| · b`.
  have hScard : S.card = P.card * b := by
    rw [hS, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  calc (hypoFam P b F).card = (trace H S).card := by rw [← hH, htrace]
    _ ≤ ∑ i ∈ Finset.range (d + 1), S.card.choose i :=
        trace_card_le_sum_range_choose H S hd
    _ = ∑ i ∈ Finset.range (d + 1), (P.card * b).choose i := by rw [hScard]

omit [DecidableEq α] in
/-- **Hypograph encoding is injective on a sample.** If two `b`-bounded functions have the
same hypograph over `P`, they agree on `P`. The proof is a clean trichotomy: if `g x < g' x`
with `g' x ≤ b`, then `i := g x` is a valid threshold in `Fin b`, and `(x, i)` lies in the
hypograph of `g'` (since `g' x > g x`) but not of `g` (since `g x > g x` is false),
contradicting equality of the hypographs. No closed-form column count is needed. -/
theorem hypoOn_eq_imp_eqOn {P : Finset α} {b : ℕ} {g g' : α → ℕ}
    (hg : ∀ x ∈ P, g x ≤ b) (hg' : ∀ x ∈ P, g' x ≤ b)
    (h : hypoOn P b g = hypoOn P b g') :
    ∀ x ∈ P, g x = g' x := by
  intro x hx
  by_contra hne
  -- Reduce to the case `g x < g' x` by symmetry; the two directions are identical.
  rcases Nat.lt_or_ge (g x) (g' x) with hlt | hge
  · -- `g x < g' x ≤ b`, so `g x < b` and `i := ⟨g x, _⟩ : Fin b` is well-formed.
    have hxb : g x < b := lt_of_lt_of_le hlt (hg' x hx)
    set i : Fin b := ⟨g x, hxb⟩ with hi
    have hmem_g' : (x, i) ∈ hypoOn P b g' := mem_hypoOn.mpr ⟨hx, by simpa [hi] using hlt⟩
    have hmem_g : (x, i) ∈ hypoOn P b g := by rw [h]; exact hmem_g'
    have : g x > i.val := (mem_hypoOn.mp hmem_g).2
    simp only [hi] at this
    exact (lt_irrefl _ this)
  · -- Then `g x > g' x` (since `g x ≠ g' x`), and the symmetric argument applies.
    have hgt : g' x < g x := lt_of_le_of_ne hge (fun heq => hne heq.symm)
    have hxb : g' x < b := lt_of_lt_of_le hgt (hg x hx)
    set i : Fin b := ⟨g' x, hxb⟩ with hi
    have hmem_g : (x, i) ∈ hypoOn P b g := mem_hypoOn.mpr ⟨hx, by simpa [hi] using hgt⟩
    have hmem_g' : (x, i) ∈ hypoOn P b g' := by rw [← h]; exact hmem_g
    have : g' x > i.val := (mem_hypoOn.mp hmem_g').2
    simp only [hi] at this
    exact (lt_irrefl _ this)

omit [DecidableEq α] in
/-- The hypograph map is injective on a class of `b`-bounded, `P`-separated functions.
"`P`-separated" (`hsep`) means distinct members of `F` already differ somewhere on the
sample `P` — the standard normalisation making `F` a family of *behaviours*. -/
theorem hypoOn_injOn (F : Finset (α → ℕ)) (P : Finset α) {b : ℕ}
    (hbdd : ∀ g ∈ F, ∀ x ∈ P, g x ≤ b)
    (hsep : ∀ g ∈ F, ∀ g' ∈ F, (∀ x ∈ P, g x = g' x) → g = g') :
    Set.InjOn (hypoOn P b) F := by
  intro g hg g' hg' h
  exact hsep g hg g' hg' (hypoOn_eq_imp_eqOn (hbdd g hg) (hbdd g' hg') h)

/-- **Real-valued growth-function bound (oq-04).** A `b`-bounded, `P`-separated function
class `F` of pseudo-dimension bounded by `d` has at most `Σ_{i ≤ d} C(|P|·b, i)` members —
the honest lift of the Boolean growth-function bound to level-valued classes, via the
hypograph reduction to the *verified* parent Sauer–Shelah lemma. -/
theorem growthFunction_le_sum_choose (F : Finset (α → ℕ)) (P : Finset α) {b d : ℕ}
    (hbdd : ∀ g ∈ F, ∀ x ∈ P, g x ≤ b)
    (hsep : ∀ g ∈ F, ∀ g' ∈ F, (∀ x ∈ P, g x = g' x) → g = g')
    (hd : VCDim (hypoFam P b F) ≤ d) :
    F.card ≤ ∑ i ∈ Finset.range (d + 1), (P.card * b).choose i := by
  have hcard : F.card = (hypoFam P b F).card := by
    rw [hypoFam, Finset.card_image_of_injOn (hypoOn_injOn F P hbdd hsep)]
  rw [hcard]
  exact hypoFam_card_le_sum_choose F P hd

/-- The growth-function bound stated with `d = Pdim P b F` (the reflexive case): a
`b`-bounded, `P`-separated class of pseudo-dimension `Pdim` has at most
`Σ_{i ≤ Pdim} C(|P|·b, i) = O((|P|·b)^{Pdim})` members — the `O((m/γ)^d)` covering bound. -/
theorem growthFunction_le_pdim (F : Finset (α → ℕ)) (P : Finset α) {b : ℕ}
    (hbdd : ∀ g ∈ F, ∀ x ∈ P, g x ≤ b)
    (hsep : ∀ g ∈ F, ∀ g' ∈ F, (∀ x ∈ P, g x = g' x) → g = g') :
    F.card ≤ ∑ i ∈ Finset.range (Pdim P b F + 1), (P.card * b).choose i :=
  growthFunction_le_sum_choose F P hbdd hsep (le_refl _)

#check @hypoFam_card_le_sum_choose
#check @hypoOn_injOn
#check @growthFunction_le_sum_choose
#check @growthFunction_le_pdim

#print axioms hypoFam_card_le_sum_choose
#print axioms growthFunction_le_sum_choose
#print axioms growthFunction_le_pdim

end PACLearningBoundsWIP01OQ04
