/-
  Knight's Tour Oblique Angles: Distribution Structural Skeleton (OQ-02)

  Open question OQ-02: distribution of oblique counts across all closed
  knight's tours on the 8×8 chessboard. Knuth (2025 Christmas Lecture)
  proved every tour has ≥ 4 oblique turns and the minimum is achieved by
  a unique tour up to D4 symmetry. The histogram values
  `obliqueDistribution 5, 6, …` are unreachable in Lean (would require
  enumerating ~1.3 × 10^13 tours), but the **structural skeleton** of the
  distribution — support, D4-orbit divisibility, reversal symmetry — is
  reachable using only the parent file's existing infrastructure.

  ## What this file provides (S2 ORIENT)

  - A `Fintype` instance for `ClosedTour` (Target A1, prerequisite for the
    histogram definition; the parent file uses `Classical.choice` and does
    not expose this).
  - `obliqueDistribution : ℕ → ℕ` (Target A2): the histogram function
    defined as a `Finset.filter` over `Finset.univ : Finset ClosedTour`.
  - `obliqueDistribution_zero_below_four` (Target B): the support lower
    bound — a direct lift of the parent's `oblique_lower_bound`.

  ## What is deferred to S3+

  - D4 group action on `ClosedTour` and `obliqueCount`-invariance (Target C).
  - Reversal symmetry `obliqueCount (reverse t) = obliqueCount t` (Target D).
  - Winding-parity joint constraint on `#turnAngle = 3` and `#turnAngle = 5`
    sub-distributions (Target E).

  ## Status

  - [x] Fintype instance via injection into `Fin 64 → Square`
  - [x] Distribution definition
  - [x] Support lower bound (k < 4)
  - [ ] D4 invariance (S3)
  - [ ] Reversal symmetry (S3)
  - [ ] Winding-parity constraint (S4)

  Parent proof: `KnightsTourOblique.lean` (8×8 minimum + uniqueness).
  Sibling: `KnightsTourObliqueOQ01.lean` (n×n minimum, n ≥ 5).

  References
  - Knuth, D. E. (2025). *29th Annual Christmas Lecture: Knight's Tours
    and Oblique Turns*. Stanford University.
  - Knuth, D. E. *TAOCP Volume 4, Fascicle 8a: Knight's Tours* (forthcoming).
-/

import Mathlib
import Proofs.KnightsTourOblique

namespace KnightsTourOblique

/-!
## Fintype instance for ClosedTour

`ClosedTour` is a structure with one data field (`squares : List Square`)
of length 64, plus several propositional fields. To get a `Fintype`
instance we inject `ClosedTour ↪ (Fin 64 → Square)` by sending a tour to
its indexing function and use `Fintype.ofInjective`. Two tours with the
same indexing function have the same `squares` list (by `List.ext_get`),
and structure-equality of `ClosedTour` is determined by `squares` since
all other fields are propositions.
-/

/-- The indexing function of a closed tour: `toFn t i = t.squares[i]`. -/
def toFn (t : ClosedTour) : Fin 64 → Square := fun i =>
  t.squares.get ⟨i.val, by rw [t.length_eq]; exact i.isLt⟩

theorem toFn_injective : Function.Injective toFn := by
  rintro ⟨s1, h1, n1, p1, ne1, c1⟩ ⟨s2, h2, n2, p2, ne2, c2⟩ heq
  -- First, show the underlying lists are equal.
  have hsq : s1 = s2 := by
    apply List.ext_get
    · exact h1.trans h2.symm
    · intro i hi1 hi2
      have hi64 : i < 64 := by rw [h1] at hi1; exact hi1
      have := congrFun heq ⟨i, hi64⟩
      simpa [toFn] using this
  -- Then the propositional fields collapse by proof irrelevance.
  subst hsq
  rfl

/-- The set of closed knight's tours on the 8×8 board is finite.
    `Fintype.ofInjective` is `noncomputable` (uses `Classical.choice`),
    which is acceptable here because the distribution is studied
    abstractly — we never reduce `Finset.univ : Finset ClosedTour`
    computationally. -/
noncomputable instance : Fintype ClosedTour :=
  Fintype.ofInjective toFn toFn_injective

/-!
## The oblique-count distribution

`obliqueDistribution k` counts the closed tours with exactly `k` oblique
turns. The full histogram is determined by external enumeration (Knuth
2025, McKay 1997); this file does not commit to those values and instead
exposes the structural lemmas.
-/

/-- Number of closed knight's tours with exactly `k` oblique turns.
    `noncomputable` because it depends on the `Fintype ClosedTour`
    instance, which uses `Classical.choice`. -/
noncomputable def obliqueDistribution (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : ClosedTour => obliqueCount t = k)).card

/-!
## Support lower bound

The first structural fact: the distribution is supported on `k ≥ 4`.
This is a one-line lift of `oblique_lower_bound : obliqueCount t ≥ 4`
from the parent file.
-/

/-- Support lower bound: no tour has fewer than 4 oblique turns. -/
theorem obliqueDistribution_zero_below_four (k : ℕ) (hk : k < 4) :
    obliqueDistribution k = 0 := by
  unfold obliqueDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_not_mem
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, hcount⟩ := ht
  have hbound : obliqueCount t ≥ 4 := oblique_lower_bound t
  rw [hcount] at hbound
  omega

/-- Equivalent statement: the distribution vanishes on `{0, 1, 2, 3}`. -/
theorem obliqueDistribution_support_le_three :
    ∀ k, k ≤ 3 → obliqueDistribution k = 0 := fun k hk =>
  obliqueDistribution_zero_below_four k (Nat.lt_succ_of_le hk)

/-- The unique minimum tour from Knuth's classification (combined with
    `oblique_lower_bound`) shows the support is non-empty at `k = 4`. The
    concrete value `obliqueDistribution 4` is determined by the D4-orbit
    of `minimalObliqueTour` (the parent's canonical witness) and is at
    most 8 — but the exact value depends on Knuth's classification of
    self-symmetric tours, which is deferred to S3. -/

/-!
## Support upper bound

`obliqueCount` is the length of a filtered list of move-pair adjacencies in
a tour of length 64, so it is bounded by 64. Combined with the support
lower bound this confines the distribution's support to `[4, 64]`. -/

/-- Pointwise upper bound: every tour has at most 64 oblique turns
    (one per move-pair adjacency in a 64-move closed tour). -/
theorem obliqueCount_le_64 (t : ClosedTour) : obliqueCount t ≤ 64 := by
  -- `obliqueCount` filters a list of length 64 (=`(tourMoves t).length`).
  -- Use a definitional unfolding via `rfl` to avoid `let`-binding issues.
  have heq : obliqueCount t =
      ((tourMoves t).zip ((tourMoves t).tail ++ [(tourMoves t).head!])
        |>.filter fun (v1, v2) => isOblique v1 v2).length := rfl
  rw [heq]
  refine le_trans (List.length_filter_le _ _) ?_
  simp [List.length_zip, List.length_tail, List.length_append, tourMoves_length]

/-- Support upper bound: no tour has more than 64 oblique turns, so the
    distribution vanishes above 64. -/
theorem obliqueDistribution_zero_above_64 (k : ℕ) (hk : 64 < k) :
    obliqueDistribution k = 0 := by
  unfold obliqueDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_not_mem
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, hcount⟩ := ht
  have hbound : obliqueCount t ≤ 64 := obliqueCount_le_64 t
  rw [hcount] at hbound
  omega

/-!
## Normalization: histogram sums to total tour count

Combining the lower bound (`k ≥ 4`) and upper bound (`k ≤ 64`), the
distribution is supported on the finite interval `[4, 64]`. Its sum over
`Finset.range 65` (which covers the support) equals the cardinality of
`ClosedTour`. This is the histogram-completeness statement: every closed
tour contributes to exactly one bucket. -/

/-- The histogram sums to the total number of closed tours. The sum is
    taken over `Finset.range 65` since `obliqueCount t ≤ 64` for every
    tour (`obliqueCount_le_64`). -/
theorem obliqueDistribution_sum_eq_card :
    (∑ k ∈ Finset.range 65, obliqueDistribution k) = Fintype.card ClosedTour := by
  unfold obliqueDistribution
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := obliqueCount) (s := Finset.univ)
    (t := Finset.range 65)
    (fun t _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (obliqueCount_le_64 t)))).symm

/-- Equivalent normalisation taking the sum over the actual support
    `Finset.Icc 4 64`: the histogram restricted to `[4, 64]` already
    accounts for every closed tour, since `obliqueDistribution` vanishes
    on `{0, 1, 2, 3}` by the parent's lower bound. -/
theorem obliqueDistribution_sum_Icc_eq_card :
    (∑ k ∈ Finset.Icc 4 64, obliqueDistribution k) = Fintype.card ClosedTour := by
  rw [← obliqueDistribution_sum_eq_card]
  -- The terms in `range 65 \ Icc 4 64 = {0,1,2,3}` are all zero by
  -- `obliqueDistribution_zero_below_four`.
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k _ hkn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hkn
    rcases hkn with hlt | h
    · exact obliqueDistribution_zero_below_four k hlt
    · exact obliqueDistribution_zero_above_64 k h

/-!
## Section: D4 action on level sets (S3 ACT)

The parent file provides `oblique_count_invariant`: `obliqueCount` is
preserved pointwise under every D4 transformation. This section lifts
that pointwise invariance to the **level sets** of `obliqueDistribution`:
for any `k` and any `g : Bool × Fin 4`, the endomap `applyD4Tour g`
restricts to a bijection of `levelSet k` onto itself.

Combined with the orbit-size bound `d4Orbit_card_le_eight` (below), this
is the infrastructure for the mod-8 orbit-decomposition picture: in the
absence of self-symmetric tours, `8 ∣ obliqueDistribution k`. Classifying
self-symmetric tours at each level is deferred to S4.

No new axioms are introduced in this section; every result reduces to
the parent's public surface (`applyD4Tour`, `applyD4Tour_inv_left`,
`oblique_count_invariant`, `closedTour_eq_iff`).
-/

/-- `Finset.image` over a `ClosedTour`-valued function requires
    `DecidableEq ClosedTour`. The classical instance is consistent with
    the existing `noncomputable instance : Fintype ClosedTour`, which
    already opted into `Classical.choice`. -/
noncomputable instance : DecidableEq ClosedTour := Classical.decEq _

/-- The level set of `obliqueCount` at value `k`: closed tours with
    exactly `k` oblique turns. Definitionally equal to the underlying
    filter used in `obliqueDistribution`. -/
noncomputable def levelSet (k : ℕ) : Finset ClosedTour :=
  Finset.univ.filter (fun t => obliqueCount t = k)

/-- Reformulation of the histogram in terms of the level set: a direct
    cardinality identity (true by `rfl`). -/
theorem obliqueDistribution_eq_levelSet_card (k : ℕ) :
    obliqueDistribution k = (levelSet k).card := rfl

/-- `applyD4Tour g` is injective on `ClosedTour`: the parent's
    `applyD4Tour_inv_left` exhibits `applyD4Tour (d4Inv g)` as a left
    inverse, so any function with a left inverse is injective. -/
theorem applyD4Tour_injective (g : Bool × Fin 4) :
    Function.Injective (applyD4Tour g) := by
  intro t1 t2 h
  have e1 := applyD4Tour_inv_left g t1
  have e2 := applyD4Tour_inv_left g t2
  rw [h] at e1
  exact e1.symm.trans e2

/-- Closure of the level set under D4: applying `applyD4Tour g` to a
    tour in `levelSet k` keeps the oblique count at `k`, so the image
    lies in the same level set (parent's `oblique_count_invariant`). -/
theorem levelSet_image_applyD4Tour_subset (g : Bool × Fin 4) (k : ℕ) :
    (levelSet k).image (applyD4Tour g) ⊆ levelSet k := by
  intro u hu
  simp only [Finset.mem_image, levelSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hu ⊢
  obtain ⟨t, htk, hgu⟩ := hu
  rw [← hgu, oblique_count_invariant]
  exact htk

/-- The image of the level set under `applyD4Tour g` has the same
    cardinality as the level set itself (injectivity). -/
theorem levelSet_image_applyD4Tour_card (g : Bool × Fin 4) (k : ℕ) :
    ((levelSet k).image (applyD4Tour g)).card = (levelSet k).card :=
  Finset.card_image_of_injective _ (applyD4Tour_injective g)

/-- **Level-set invariance** (headline S3 result): every D4 element
    `g` induces a bijection of `levelSet k` onto itself. Image equality
    follows from closure (subset) + cardinality preservation
    (injectivity) + finiteness, via `Finset.eq_of_subset_of_card_le`. -/
theorem levelSet_image_applyD4Tour_eq (g : Bool × Fin 4) (k : ℕ) :
    (levelSet k).image (applyD4Tour g) = levelSet k := by
  apply Finset.eq_of_subset_of_card_le (levelSet_image_applyD4Tour_subset g k)
  rw [levelSet_image_applyD4Tour_card]

/-!
## Section: D4 orbits

The 8-element D4 group acts on `ClosedTour` via `applyD4Tour`. Each tour
`t` generates a D4-orbit `d4Orbit t : Finset ClosedTour` of size at most
`|D4| = 8`, with equality iff the D4-stabilizer of `t` is trivial (i.e.,
`t` is not self-symmetric). By the level-set invariance above, the orbit
of `t` is contained in `levelSet (obliqueCount t)`.

Downstream (S4): partition `levelSet k` into D4 orbits, classify
orbit-size divisors of 8, and conclude `obliqueDistribution k ≡ s_k (mod 8)`
where `s_k` is the count of self-symmetric tours with oblique count `k`. -/

/-- The D4 orbit of a tour: image of the 8-element finset
    `Finset.univ : Finset (Bool × Fin 4)` under `applyD4Tour · t`. -/
noncomputable def d4Orbit (t : ClosedTour) : Finset ClosedTour :=
  (Finset.univ : Finset (Bool × Fin 4)).image (fun g => applyD4Tour g t)

/-- A D4 orbit has at most `|D4| = 8` elements (the bound is achieved
    iff the tour's D4-stabilizer is trivial). -/
theorem d4Orbit_card_le_eight (t : ClosedTour) : (d4Orbit t).card ≤ 8 := by
  unfold d4Orbit
  refine le_trans (Finset.card_image_le) ?_
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- Every D4 orbit is contained in the level set at its common oblique
    count: `oblique_count_invariant` forces every element of `d4Orbit t`
    to share `obliqueCount t`. -/
theorem d4Orbit_subset_levelSet (t : ClosedTour) :
    d4Orbit t ⊆ levelSet (obliqueCount t) := by
  intro u hu
  unfold d4Orbit at hu
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
  obtain ⟨g, hgu⟩ := hu
  simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hgu, oblique_count_invariant]

/-- The identity element of D4 maps a tour to itself: `(false, 0)`
    encodes no reflection (`false`) and zero rotations (`0`), and acts
    as the identity on every `Square`. -/
theorem applyD4Tour_id (t : ClosedTour) : applyD4Tour (false, 0) t = t := by
  rw [closedTour_eq_iff]
  show t.squares.map (applyD4 (false, 0)) = t.squares
  have h : (applyD4 (false, 0) : Square → Square) = id := by
    funext s; rfl
  rw [h, List.map_id]

/-- Every tour lies in its own D4 orbit (witness: the identity
    `(false, 0)` paired with `applyD4Tour_id`). -/
theorem tour_mem_d4Orbit_self (t : ClosedTour) : t ∈ d4Orbit t := by
  unfold d4Orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(false, 0), applyD4Tour_id t⟩

/-!
## D4 right-inverse and bijectivity (S4-prep)

The parent file's `applyD4Tour_inv_left` exhibits `applyD4Tour (d4Inv g)`
as a **left** inverse of `applyD4Tour g`. The matching **right** inverse
follows from injectivity (which we already have from inv_left): applying
`applyD4Tour (d4Inv g)` to both sides of the desired equality reduces it
to a second instance of inv_left, completing the bijection picture
without needing to prove `d4Inv (d4Inv g) = g` explicitly.

This unlocks: (i) `applyD4Tour g` is a bijection of `ClosedTour` (with
named inverse `applyD4Tour (d4Inv g)`); (ii) every tour `u` has a unique
preimage `applyD4Tour (d4Inv g) u` under `applyD4Tour g` — useful for
counting arguments and for the surjectivity direction of the symmetric
law in the `d4Equiv` framework below.
-/

/-- D4 **right inverse**: `applyD4Tour (d4Inv g)` is also a right inverse
    of `applyD4Tour g`. Apply the injective endomap `applyD4Tour (d4Inv g)`
    to both sides and reduce the resulting goal by parent's
    `applyD4Tour_inv_left g (applyD4Tour (d4Inv g) t)`. -/
theorem applyD4Tour_inv_right (g : Bool × Fin 4) (t : ClosedTour) :
    applyD4Tour g (applyD4Tour (d4Inv g) t) = t := by
  apply applyD4Tour_injective (d4Inv g)
  exact applyD4Tour_inv_left g (applyD4Tour (d4Inv g) t)

/-- `applyD4Tour g` is bijective on `ClosedTour`: injectivity from
    `applyD4Tour_injective` (S3), surjectivity from `applyD4Tour_inv_right`
    with explicit preimage `applyD4Tour (d4Inv g) t`. -/
theorem applyD4Tour_bijective (g : Bool × Fin 4) :
    Function.Bijective (applyD4Tour g) :=
  ⟨applyD4Tour_injective g,
   fun t => ⟨applyD4Tour (d4Inv g) t, applyD4Tour_inv_right g t⟩⟩

/-!
## D4-equivalence relation (S4-prep)

The D4 action partitions `ClosedTour` into orbits. We expose the
underlying relation `d4Equiv t u := ∃ g, applyD4Tour g t = u` and prove
**reflexivity** (witness `(false, 0)` via `applyD4Tour_id`) and
**symmetry** (witness `d4Inv g` via `applyD4Tour_inv_left`). The
oblique-count invariance lifts pointwise to the relation
(`d4Equiv_preserves_obliqueCount`), and level-set membership is preserved
(`d4Equiv_preserves_levelSet`).

**Transitivity is deferred to S4** — constructing a witness `g₃` from
`g₁, g₂` requires a multiplication law `d4Mul : (Bool × Fin 4) →
(Bool × Fin 4) → (Bool × Fin 4)` with `applyD4Tour (d4Mul g₂ g₁) =
applyD4Tour g₂ ∘ applyD4Tour g₁`. That composition lemma needs a 4-case
split on `(g₁.1, g₂.1)` using parent's `rotate_reflect_conjugate`,
`rotate90_four_times`, `reflect_twice` and is the planned S4-prep follow-up.

What we *do* get this iteration: a `mem_d4Orbit_iff` / `d4Orbit_eq_filter_d4Equiv`
bridge between the `Finset` orbit (S3) and the `Prop`-valued relation,
plus the level-set preservation lemma — together enough to refactor the
S3 closure arguments through the equivalence-relation lens.
-/

/-- Two tours are **D4-equivalent** iff one is obtained from the other
    by a single D4 transformation. Reflexive and symmetric; transitivity
    deferred to S4 (needs `d4Mul`). -/
def d4Equiv (t u : ClosedTour) : Prop :=
  ∃ g : Bool × Fin 4, applyD4Tour g t = u

/-- Reflexivity of `d4Equiv`: identity witness `(false, 0)`. -/
theorem d4Equiv_refl (t : ClosedTour) : d4Equiv t t :=
  ⟨(false, 0), applyD4Tour_id t⟩

/-- Symmetry of `d4Equiv`: if `applyD4Tour g t = u`, then
    `applyD4Tour (d4Inv g) u = t` by parent's `applyD4Tour_inv_left`. -/
theorem d4Equiv_symm {t u : ClosedTour} (h : d4Equiv t u) : d4Equiv u t := by
  obtain ⟨g, hg⟩ := h
  refine ⟨d4Inv g, ?_⟩
  rw [← hg]
  exact applyD4Tour_inv_left g t

/-- D4-equivalent tours have the same oblique count: lifts parent's
    `oblique_count_invariant` from elements to the relation. -/
theorem d4Equiv_preserves_obliqueCount {t u : ClosedTour} (h : d4Equiv t u) :
    obliqueCount t = obliqueCount u := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, oblique_count_invariant]

/-- Membership in the D4 orbit `Finset` is the same as D4-equivalence
    — the `Finset.image` definition unwraps to the existential. -/
theorem mem_d4Orbit_iff (t u : ClosedTour) :
    u ∈ d4Orbit t ↔ d4Equiv t u := by
  unfold d4Orbit d4Equiv
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

/-- Bridge: the D4 orbit `Finset` is the filter of `Finset.univ` by the
    equivalence relation `d4Equiv t ·`. -/
theorem d4Orbit_eq_filter_d4Equiv (t : ClosedTour) :
    d4Orbit t = Finset.univ.filter (d4Equiv t) := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact mem_d4Orbit_iff t u

/-- Level-set membership is preserved by D4-equivalence: a refinement of
    the S3 closure result `levelSet_image_applyD4Tour_subset` routed
    through the equivalence relation. -/
theorem d4Equiv_preserves_levelSet {t u : ClosedTour} {k : ℕ}
    (h : d4Equiv t u) (ht : t ∈ levelSet k) : u ∈ levelSet k := by
  simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  rw [← d4Equiv_preserves_obliqueCount h]
  exact ht

/-!
## S8: D4 multiplication law and `d4Equiv` transitivity

S7 gave reflexivity and symmetry of `d4Equiv`. **Transitivity** requires a
multiplication law `d4Mul g₂ g₁ : Bool × Fin 4` satisfying
`applyD4 (d4Mul g₂ g₁) s = applyD4 g₂ (applyD4 g₁ s)`. This lifts via
`List.map_map` (parent's `map_applyD4_comp`) to `applyD4Tour_mul`, and then
to `d4Equiv_trans` as an existential combinator.

### Composition formula

Recall `applyD4 (b, k) s = rotateSquareN k (if b then reflectSquare s else s)`.

* **Outer non-reflecting** (`b₂ = false`): rotations compose,
  `d4Mul (false, k₂) (b₁, k₁) = (b₁, (k₁ + k₂) % 4)`.
* **Outer reflecting** (`b₂ = true`): the outer reflection conjugates the
  inner rotation via `reflectSquare ∘ rotateSquareN k₁ = rotateSquareN
  ((4 - k₁) % 4) ∘ reflectSquare`, and the reflection bits flip. So
  `d4Mul (true, k₂) (b₁, k₁) = (!b₁, (k₂ + (4 - k₁)) % 4)`.

### Proof strategy

We first prove two pure-rotation/reflection helpers:

* `rotateSquareN_add` — rotation composition.
* `reflect_rotateN_conjugate` — conjugation of rotation by reflection.

Each is a `fin_cases`-driven coordinate computation closed by `omega`.
Then `applyD4_mul` is a 4-case split on `(b₂, b₁)` using these helpers,
avoiding the full 4 × 4 × 2 × 2 = 64-case grid.

`applyD4Tour_mul` lifts via the parent's `map_applyD4_comp` plus
pointwise `applyD4_mul`. `d4Equiv_trans` then packages two existential
witnesses with `d4Mul`. Finally `d4Equiv_equivalence` and the matching
`Setoid ClosedTour` bundle the relation.

This sets up S9: a `Group (Bool × Fin 4)` structure (with `d4Mul` and
`d4Inv`) and a `MulAction (Bool × Fin 4) ClosedTour` via `applyD4Tour` —
the bearer of Mathlib's `MulAction.card_orbit_dvd_card_group` for the
mod-8 divisibility headline. The associativity proof for `Group` requires
one more 8-case bash on the rotation triple, deferred to S9.
-/

/-- Composition of rotations: rotating by `m` after `n` equals rotating by
    `(m.val + n.val) % 4`. The proof bashes 16 cases on `(m, n)`. -/
theorem rotateSquareN_add (m n : Fin 4) (s : Square) :
    rotateSquareN m (rotateSquareN n s) =
    rotateSquareN ⟨(m.val + n.val) % 4, by omega⟩ s := by
  fin_cases m <;> fin_cases n <;>
    simp only [rotateSquareN, rotateSquare90, Fin.val_mk, Fin.isValue] <;>
    ext <;> simp only [Fin.ext_iff] <;> omega

/-- Reflection conjugates rotation: `reflectSquare ∘ rotateSquareN k =
    rotateSquareN ((4 - k.val) % 4) ∘ reflectSquare`. The proof bashes 4
    cases on `k`. -/
theorem reflect_rotateN_conjugate (k : Fin 4) (s : Square) :
    reflectSquare (rotateSquareN k s) =
    rotateSquareN ⟨(4 - k.val) % 4, by omega⟩ (reflectSquare s) := by
  fin_cases k <;>
    simp only [rotateSquareN, rotateSquare90, reflectSquare,
               Fin.val_mk, Fin.isValue] <;>
    ext <;> simp only [Fin.ext_iff] <;> omega

/-- D4 multiplication encoded on `Bool × Fin 4`. Defined by pattern
    matching on the outer reflection bit to make `applyD4_mul`'s case
    split reduce cleanly. -/
def d4Mul : Bool × Fin 4 → Bool × Fin 4 → Bool × Fin 4
  | (false, k₂), (b₁, k₁) => (b₁, ⟨(k₁.val + k₂.val) % 4, by omega⟩)
  | (true,  k₂), (b₁, k₁) => (!b₁, ⟨(k₂.val + (4 - k₁.val)) % 4, by omega⟩)

/-- Specialization of `applyD4` to the non-reflecting case. Reduces to a
    pure rotation by `rfl` (the `if (false : Bool) then` branch is
    definitionally the `else` branch). -/
private lemma applyD4_false (k : Fin 4) (s : Square) :
    applyD4 (false, k) s = rotateSquareN k s := rfl

/-- Specialization of `applyD4` to the reflecting case. Reduces to
    rotation after reflection by `rfl`. -/
private lemma applyD4_true (k : Fin 4) (s : Square) :
    applyD4 (true, k) s = rotateSquareN k (reflectSquare s) := rfl

/-- **D4 composition law**: `applyD4 (d4Mul g₂ g₁) s = applyD4 g₂ (applyD4 g₁ s)`.
    4-case split on `(b₂, b₁)`; the rotation arithmetic reduces via
    `rotateSquareN_add` and `reflect_rotateN_conjugate`, with `congr` +
    `omega` closing the residual Fin 4 equalities. -/
theorem applyD4_mul (g₂ g₁ : Bool × Fin 4) (s : Square) :
    applyD4 (d4Mul g₂ g₁) s = applyD4 g₂ (applyD4 g₁ s) := by
  obtain ⟨b₂, k₂⟩ := g₂
  obtain ⟨b₁, k₁⟩ := g₁
  cases b₂ with
  | false =>
    cases b₁ with
    | false =>
      -- d4Mul (false, k₂) (false, k₁) = (false, ⟨(k₁+k₂)%4, _⟩)
      simp only [d4Mul, applyD4_false]
      rw [rotateSquareN_add k₂ k₁]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    | true =>
      -- d4Mul (false, k₂) (true, k₁) = (true, ⟨(k₁+k₂)%4, _⟩)
      simp only [d4Mul, applyD4_false, applyD4_true]
      rw [rotateSquareN_add k₂ k₁]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  | true =>
    cases b₁ with
    | false =>
      -- d4Mul (true, k₂) (false, k₁) = (true, ⟨(k₂+(4-k₁))%4, _⟩)  (since !false = true)
      simp only [d4Mul, applyD4_false, applyD4_true, Bool.not_false]
      rw [reflect_rotateN_conjugate k₁ s,
          rotateSquareN_add k₂ ⟨(4 - k₁.val) % 4, by omega⟩]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    | true =>
      -- d4Mul (true, k₂) (true, k₁) = (false, ⟨(k₂+(4-k₁))%4, _⟩)  (since !true = false)
      simp only [d4Mul, applyD4_false, applyD4_true, Bool.not_true]
      rw [reflect_rotateN_conjugate k₁ (reflectSquare s),
          reflect_twice,
          rotateSquareN_add k₂ ⟨(4 - k₁.val) % 4, by omega⟩]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- **D4 composition law on tours**: lifts `applyD4_mul` pointwise to the
    `List.map (applyD4 _)` definition of `applyD4Tour`, via the parent's
    `map_applyD4_comp`. -/
theorem applyD4Tour_mul (g₂ g₁ : Bool × Fin 4) (t : ClosedTour) :
    applyD4Tour (d4Mul g₂ g₁) t = applyD4Tour g₂ (applyD4Tour g₁ t) := by
  apply (closedTour_eq_iff _ _).mpr
  show t.squares.map (applyD4 (d4Mul g₂ g₁)) =
       (t.squares.map (applyD4 g₁)).map (applyD4 g₂)
  rw [map_applyD4_comp]
  congr 1
  funext s
  -- goal after Function.comp reduction:
  --   applyD4 (d4Mul g₂ g₁) s = applyD4 g₂ (applyD4 g₁ s)
  exact applyD4_mul g₂ g₁ s

/-- **Transitivity of `d4Equiv`**: completes the equivalence-relation
    framework. Witness combinator `d4Mul g₂ g₁` from the two existentials,
    closed by `applyD4Tour_mul`. -/
theorem d4Equiv_trans {t u v : ClosedTour}
    (h₁ : d4Equiv t u) (h₂ : d4Equiv u v) : d4Equiv t v := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  refine ⟨d4Mul g₂ g₁, ?_⟩
  rw [applyD4Tour_mul, hg₁, hg₂]

/-- `d4Equiv` is an equivalence relation. -/
theorem d4Equiv_equivalence : Equivalence d4Equiv :=
  ⟨d4Equiv_refl, d4Equiv_symm, d4Equiv_trans⟩

/-- The D4 quotient setoid on `ClosedTour`. The orbits of `applyD4Tour`
    correspond to the equivalence classes; this is the structural input
    for the planned mod-8 divisibility argument
    (`obliqueDistribution k = 8 · (#free orbits) + Σ (8 / stab)`). -/
def d4Setoid : Setoid ClosedTour where
  r := d4Equiv
  iseqv := d4Equiv_equivalence

/-!
## S9: Algebraic laws for `d4Mul` (`Group (Bool × Fin 4)` bearer)

The next milestone is the mod-8 divisibility headline via Mathlib's
`MulAction.card_orbit_dvd_card_group`. That requires a
`Group (Bool × Fin 4)` instance with `mul := d4Mul`, `one := (false, 0)`,
`inv := d4Inv`, plus a `MulAction (Bool × Fin 4) ClosedTour` via
`applyD4Tour` (`one_smul` from `applyD4Tour_id` (S3); `mul_smul` from
`applyD4Tour_mul` (S8)).

This S9 ACT ships the five algebraic laws on the `d4Mul`/`d4Inv` carrier
needed for the `Group` instance: associativity, left/right identity, and
left/right inverse. The actual `instance : Group (Bool × Fin 4)`
packaging and the `MulAction` instance are deferred to S10 to keep this
PR atomic and to isolate any Mathlib v4.26.0 instance-resolution risk
that the S8 next-action plan flagged.

All five proofs are pure case-bashes on the `Bool` components followed
by `simp only [d4Mul, ...]` to reduce both sides to `Prod.mk` form,
`Prod.mk.injEq.mpr ⟨rfl, ?_⟩` to dispatch the bit equality (`rfl` after
`Bool.not_*` normalization), and `Fin.ext + omega` on the residual
modular Fin 4 identity.
-/

/-- **D4 multiplication is associative**. 8-case bash on
    `(b₃, b₂, b₁) ∈ Bool³`; each case reduces by `simp only [d4Mul,
    Bool.not_*]` to a modular Fin 4 identity discharged by `omega`. -/
theorem d4Mul_assoc (g₃ g₂ g₁ : Bool × Fin 4) :
    d4Mul (d4Mul g₃ g₂) g₁ = d4Mul g₃ (d4Mul g₂ g₁) := by
  obtain ⟨b₃, k₃⟩ := g₃
  obtain ⟨b₂, k₂⟩ := g₂
  obtain ⟨b₁, k₁⟩ := g₁
  cases b₃ <;> cases b₂ <;> cases b₁ <;>
    (simp only [d4Mul, Bool.not_false, Bool.not_true]
     refine Prod.mk.injEq.mpr ⟨rfl, ?_⟩
     apply Fin.ext
     simp only [Fin.val_mk]
     omega)

/-- **Left identity**: `(false, 0)` is a left unit for `d4Mul`. Single
    pattern match on the second argument; `(k.val + 0) % 4 = k.val`
    closes by `omega` using `k.isLt`. -/
theorem d4Mul_one_left (g : Bool × Fin 4) :
    d4Mul (false, 0) g = g := by
  obtain ⟨b, k⟩ := g
  simp only [d4Mul]
  refine Prod.mk.injEq.mpr ⟨rfl, ?_⟩
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- **Right identity**: `(false, 0)` is a right unit for `d4Mul`.
    Case-split on the first argument's reflection bit. -/
theorem d4Mul_one_right (g : Bool × Fin 4) :
    d4Mul g (false, 0) = g := by
  obtain ⟨b, k⟩ := g
  cases b <;>
    (simp only [d4Mul, Bool.not_false]
     refine Prod.mk.injEq.mpr ⟨rfl, ?_⟩
     apply Fin.ext
     simp only [Fin.val_mk]
     omega)

/-- **Left inverse**: `d4Inv g` is a left inverse of `g` under `d4Mul`.
    Case-split on the reflection bit. For pure rotations
    (`b = false`): `(k + (4-k) % 4) % 4 = 0`. For reflections
    (`b = true`): `d4Inv` is the identity (reflections are self-inverse),
    so the goal reduces to `(k + (4-k)) % 4 = 0`. Both branches close
    by `omega`. -/
theorem d4Mul_inv_left (g : Bool × Fin 4) :
    d4Mul (d4Inv g) g = (false, 0) := by
  obtain ⟨b, k⟩ := g
  cases b <;>
    (simp only [d4Inv, d4Mul, Bool.not_true, ↓reduceIte]
     refine Prod.mk.injEq.mpr ⟨rfl, ?_⟩
     apply Fin.ext
     simp only [Fin.val_mk]
     omega)

/-- **Right inverse**: `d4Inv g` is a right inverse of `g` under
    `d4Mul`. Symmetric to `d4Mul_inv_left`. -/
theorem d4Mul_inv_right (g : Bool × Fin 4) :
    d4Mul g (d4Inv g) = (false, 0) := by
  obtain ⟨b, k⟩ := g
  cases b <;>
    (simp only [d4Inv, d4Mul, Bool.not_true, ↓reduceIte]
     refine Prod.mk.injEq.mpr ⟨rfl, ?_⟩
     apply Fin.ext
     simp only [Fin.val_mk]
     omega)

end KnightsTourOblique
