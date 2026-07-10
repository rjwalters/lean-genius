/-
Erdős Problem #703: Forbidden r-Intersection Families

Source: https://erdosproblems.com/703
Status: SOLVED
Prize: $250

Statement:
Let r ≥ 1 and define T(n,r) to be the maximum size of a family F of subsets
of {1,...,n} such that |A ∩ B| ≠ r for all A, B ∈ F.

Estimate T(n,r) for r ≥ 2. In particular, is it true that for every ε > 0
there exists δ > 0 such that for all εn < r < (1/2 - ε)n we have
T(n,r) < (2 - δ)^n?

Known Results:
- T(n,0) = 2^{n-1} (trivial: take all sets containing a fixed element)
- Frankl (1977): Determined T(n,1) for all n
- Frankl-Füredi (1984): Determined T(n,r) for fixed r and n large
- Frankl-Rödl (1987): Proved YES to the main question (exponential bound)

The answer is YES: T(n,r) < (2 - δ)^n for εn < r < (1/2 - ε)n.

References:
- [Fr77]: Frankl "An intersection problem for finite sets" (1977)
- [FrFu84]: Frankl-Füredi "Hypergraphs without two edges intersecting in r vertices" (1984)
- [FrRo87]: Frankl-Rödl "Forbidden intersections" (1987)
- [FrWi81]: Frankl-Wilson "Intersection theorems with geometric consequences" (1981)

Formalization note.
This file formalizes the structural statement and the trivial case `T(n,0) = 2^{n-1}`
completely (no `sorry`). The deep Frankl-Rödl exponential bound (the answer to the
main question) is recorded as the axiom `frankl_rodl_1987`; this is the sole
assumption in the file. The `T(n,0)` proof
below is fully machine-checked: it pairs each subset of `[n]` with its complement
to bound any `0`-avoiding (intersecting) family by `2^{n-1}`, and exhibits the
star family of all sets through a fixed point as an extremal example.
-/

import Mathlib

open Nat Finset
open scoped Classical

namespace Erdos703

/-
## Part I: Forbidden r-Intersection Families
-/

/--
**r-Intersection:**
Two sets A and B have r-intersection if |A ∩ B| = r.
-/
def hasRIntersection (r : ℕ) (A B : Finset ℕ) : Prop :=
  (A ∩ B).card = r

/--
**r-Avoiding Family:**
A family F avoids r-intersection if no two sets in F have exactly r elements
in their intersection.
-/
def avoidsRIntersection (r : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ A B : Finset ℕ, A ∈ F → B ∈ F → (A ∩ B).card ≠ r

/--
**T(n,r):**
The maximum size of a family `F ⊆ 2^{[n]}` avoiding r-intersection.

The maximisation ranges over all families `F` of subsets of `[n] = range n`
(i.e. `F ∈ (range n).powerset.powerset`) satisfying `avoidsRIntersection r`.
-/
noncomputable def T (n r : ℕ) : ℕ :=
  (((Finset.range n).powerset.powerset).filter (avoidsRIntersection r)).sup
    (fun F => F.card)

/-
## Part II: The Trivial Case T(n,0)
-/

/--
**0-Avoiding means intersecting:**
|A ∩ B| ≠ 0 means A ∩ B ≠ ∅, i.e. A and B intersect.
-/
theorem zero_avoiding_is_intersecting (F : Finset (Finset ℕ)) :
    avoidsRIntersection 0 F ↔ ∀ A B : Finset ℕ, A ∈ F → B ∈ F → (A ∩ B).Nonempty := by
  unfold avoidsRIntersection
  simp [Finset.card_eq_zero, Finset.nonempty_iff_ne_empty]

/--
**Complement bound for 0-avoiding families:**
Any family `F` of subsets of `[n]` that avoids `0`-intersections (i.e. any two
members meet) has at most `2^{n-1}` members. Pairing each `A ∈ F` with its
complement `[n] \ A` is an injection whose image is disjoint from `F` (since
`A ∩ ([n] \ A) = ∅` is forbidden), so `2|F| ≤ |2^{[n]}| = 2^n`.
-/
theorem card_le_of_avoids_zero (n : ℕ) (hn : n ≥ 1) (F : Finset (Finset ℕ))
    (hFP : F ⊆ (Finset.range n).powerset) (hF : avoidsRIntersection 0 F) :
    F.card ≤ 2 ^ (n - 1) := by
  -- The complement map within `[n]`.
  set c : Finset ℕ → Finset ℕ := fun A => Finset.range n \ A with hc
  -- Members of `F` are subsets of `[n]`.
  have hsub : ∀ A ∈ F, A ⊆ Finset.range n := fun A hA =>
    Finset.mem_powerset.mp (hFP hA)
  -- The complement of a member is again a subset of `[n]`.
  have hcP : ∀ A ∈ F, c A ∈ (Finset.range n).powerset := by
    intro A _
    rw [Finset.mem_powerset]
    exact Finset.sdiff_subset
  -- `c` is an involution on members of `F`.
  have hinv : ∀ A ∈ F, c (c A) = A := by
    intro A hA
    simp only [hc]
    exact Finset.sdiff_sdiff_eq_self (hsub A hA)
  -- A member and its complement cannot both lie in `F`.
  have hnotmem : ∀ A ∈ F, c A ∉ F := by
    intro A hA hcA
    have hempty : A ∩ c A = ∅ := by
      simp only [hc]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter, Finset.mem_sdiff] at hx
      exact hx.2.2 hx.1
    have hne : (A ∩ c A).card ≠ 0 := hF A (c A) hA hcA
    rw [hempty, Finset.card_empty] at hne
    exact hne rfl
  -- Disjointness of `F` and its complement image.
  have hdisj : Disjoint F (F.image c) := by
    rw [Finset.disjoint_left]
    intro X hXF hXimg
    rw [Finset.mem_image] at hXimg
    obtain ⟨A, hA, rfl⟩ := hXimg
    exact hnotmem A hA hXF
  -- `c` is injective on `F`.
  have hinjOn : Set.InjOn c F := by
    intro A hA B hB hcc
    have := congrArg c hcc
    rwa [hinv A hA, hinv B hB] at this
  have hcard_img : (F.image c).card = F.card := Finset.card_image_of_injOn hinjOn
  -- The union lies inside `2^{[n]}`.
  have hunion_sub : F ∪ F.image c ⊆ (Finset.range n).powerset := by
    apply Finset.union_subset hFP
    intro X hX
    rw [Finset.mem_image] at hX
    obtain ⟨A, hA, rfl⟩ := hX
    exact hcP A hA
  have hcard_union : (F ∪ F.image c).card = F.card + F.card := by
    rw [Finset.card_union_of_disjoint hdisj, hcard_img]
  have hle : F.card + F.card ≤ 2 ^ n := by
    rw [← hcard_union]
    calc (F ∪ F.image c).card
        ≤ ((Finset.range n).powerset).card := Finset.card_le_card hunion_sub
      _ = 2 ^ n := by rw [Finset.card_powerset, Finset.card_range]
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ']
  omega

/--
**The star family is `0`-avoiding with `2^{n-1}` members.**
All subsets of `[n]` containing the fixed element `0` pairwise intersect (they
share `0`), and there are exactly `2^{n-1}` of them.
-/
theorem star_family_card (n : ℕ) (hn : n ≥ 1) :
    ((Finset.range n).powerset.filter (fun A => (0 : ℕ) ∈ A)).card = 2 ^ (n - 1) := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hcard : ((Finset.range n).erase 0).card = n - 1 := by
    rw [Finset.card_erase_of_mem h0, Finset.card_range]
  rw [← hcard, ← Finset.card_powerset]
  apply Finset.card_nbij' (fun A => A.erase 0) (fun B => insert 0 B)
  · -- maps the star family into `2^{[n] \ {0}}`
    intro A hA
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hA.1 hx.2⟩
  · -- maps `2^{[n] \ {0}}` back into the star family
    intro B hB
    rw [Finset.mem_coe, Finset.mem_powerset] at hB
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, Finset.mem_insert_self 0 B⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact h0
    · exact (Finset.mem_erase.mp (hB hx)).2
  · -- left inverse on the star family
    intro A hA
    rw [Finset.mem_coe, Finset.mem_filter] at hA
    exact Finset.insert_erase hA.2
  · -- right inverse on `2^{[n] \ {0}}`
    intro B hB
    rw [Finset.mem_coe, Finset.mem_powerset] at hB
    have h0B : (0 : ℕ) ∉ B := fun h => (Finset.mem_erase.mp (hB h)).1 rfl
    exact Finset.erase_insert h0B

/--
**T(n,0) = 2^{n-1}:**
The `0`-avoiding families are exactly the intersecting families. The complement
pairing bounds every such family by `2^{n-1}`, and the star family of all sets
containing a fixed element attains it.
-/
theorem T_n_0 (n : ℕ) (hn : n ≥ 1) : T n 0 = 2 ^ (n - 1) := by
  apply le_antisymm
  · -- upper bound
    unfold T
    apply Finset.sup_le
    intro F hF
    rw [Finset.mem_filter] at hF
    exact card_le_of_avoids_zero n hn F (Finset.mem_powerset.mp hF.1) hF.2
  · -- lower bound: the star family is a witness
    unfold T
    rw [← star_family_card n hn]
    have hmem : (Finset.range n).powerset.filter (fun A => (0 : ℕ) ∈ A) ∈
        ((Finset.range n).powerset.powerset).filter (avoidsRIntersection 0) := by
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_powerset]
        exact Finset.filter_subset _ _
      · intro A B hA hB
        rw [Finset.mem_filter] at hA hB
        have h0AB : (0 : ℕ) ∈ A ∩ B := Finset.mem_inter.mpr ⟨hA.2, hB.2⟩
        have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr ⟨0, h0AB⟩
        omega
    exact Finset.le_sup hmem

/-
## Part III: Frankl's Result for r = 1
-/

/--
**Construction for r = 1 (Frankl, 1977):**
Large sets (size > (n+1)/2) cannot have intersection exactly 1 with each other,
by inclusion-exclusion: `|A ∪ B| + |A ∩ B| = |A| + |B|` and `|A ∪ B| ≤ n`.
-/
theorem large_sets_avoid_1 (n : ℕ) (A B : Finset ℕ)
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n)
    (hAsize : A.card > (n + 1) / 2) (hBsize : B.card > (n + 1) / 2) :
    (A ∩ B).card ≠ 1 := by
  intro h
  have hie := Finset.card_union_add_card_inter A B
  have hunion : (A ∪ B).card ≤ n := by
    calc (A ∪ B).card ≤ (Finset.range n).card :=
          Finset.card_le_card (Finset.union_subset hA hB)
      _ = n := Finset.card_range n
  omega

/--
**The family of large sets (Frankl's `r = 1` lower-bound construction).**
`F = {A ⊆ [n] : |A| > (n+1)/2}`. Every pair of members — including a set with
itself — has intersection size `≠ 1`, so this is a valid `1`-avoiding family.
-/
def largeSetsFamily (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun A => A.card > (n + 1) / 2)

/--
**The large-set family avoids `1`-intersections.**
Immediate from `large_sets_avoid_1`: any two sets both larger than `(n+1)/2`
cannot meet in exactly one point.
-/
theorem largeSetsFamily_avoids_1 (n : ℕ) : avoidsRIntersection 1 (largeSetsFamily n) := by
  intro A B hA hB
  rw [largeSetsFamily, Finset.mem_filter, Finset.mem_powerset] at hA hB
  exact large_sets_avoid_1 n A B hA.1 hB.1 hA.2 hB.2

/--
**Lower bound on `T(n,1)` from the large-set construction.**
Since the large-set family is a valid `1`-avoiding subfamily of `2^{[n]}`, its
cardinality is a lower bound for `T(n,1)`. This is Frankl's (1977) lower-bound
construction: the extremal `1`-avoiding families are (essentially) the large
sets together with a small-set tail.
-/
theorem largeSetsFamily_card_le_T (n : ℕ) : (largeSetsFamily n).card ≤ T n 1 := by
  have hmem : largeSetsFamily n ∈
      ((Finset.range n).powerset.powerset).filter (avoidsRIntersection 1) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), largeSetsFamily_avoids_1 n⟩
  exact Finset.le_sup hmem

/-
## Part IV: Frankl-Füredi Optimal Families
-/

/--
**Frankl-Füredi Optimal Family (n + r odd):**
`F = {A ⊆ [n] : |A| > (n+r)/2 or |A| < r}`.
-/
def franklFurediOdd (n r : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun A => A.card > (n + r) / 2 ∨ A.card < r)

/--
**Frankl-Füredi Optimal Family (n + r even):**
`F = {A ⊆ [n] : |A \ {0}| ≥ (n+r)/2 or |A| < r}`.
-/
def franklFurediEven (n r : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter
    (fun A => (A.filter (· ≠ 0)).card ≥ (n + r) / 2 ∨ A.card < r)

/--
**Two members of `franklFurediOdd` avoid `r`-intersection.**
Generalizes `large_sets_avoid_1` (the `r = 1` case) to all `r`. Three cases:
* both sets large (`|A|, |B| > (n+r)/2`): inclusion–exclusion gives
  `|A ∩ B| ≥ |A| + |B| - n ≥ 2⌊(n+r)/2⌋ + 2 - n ≥ r + 1 > r` (both parities);
* either set small (`|·| < r`): `|A ∩ B| ≤ min(|A|,|B|) < r`.
In every case `|A ∩ B| ≠ r`.
-/
theorem franklFurediOdd_avoids_r (n r : ℕ) : avoidsRIntersection r (franklFurediOdd n r) := by
  intro A B hA hB
  rw [franklFurediOdd, Finset.mem_filter, Finset.mem_powerset] at hA hB
  obtain ⟨hAsub, hAcond⟩ := hA
  obtain ⟨hBsub, hBcond⟩ := hB
  have hie := Finset.card_union_add_card_inter A B
  have hunion : (A ∪ B).card ≤ n := by
    calc (A ∪ B).card ≤ (Finset.range n).card :=
          Finset.card_le_card (Finset.union_subset hAsub hBsub)
      _ = n := Finset.card_range n
  have hiA : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hiB : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  rcases hAcond with hAlarge | hAsmall <;> rcases hBcond with hBlarge | hBsmall <;> omega

/--
**Lower bound on `T(n,r)` from the Frankl–Füredi `franklFurediOdd` construction.**
Since `franklFurediOdd n r` is a valid `r`-avoiding subfamily of `2^{[n]}`, its
cardinality bounds `T(n,r)` below. This is the general-`r` analogue of
`largeSetsFamily_card_le_T`.
-/
theorem franklFurediOdd_card_le_T (n r : ℕ) : (franklFurediOdd n r).card ≤ T n r := by
  have hmem : franklFurediOdd n r ∈
      ((Finset.range n).powerset.powerset).filter (avoidsRIntersection r) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), franklFurediOdd_avoids_r n r⟩
  exact Finset.le_sup hmem

/--
**Two members of `franklFurediEven` avoid `r`-intersection (`n + r` even, `n ≥ 1`).**
The even-parity companion of `franklFurediOdd_avoids_r`. Here the "large" condition
is on the *centred* set `A₀ = A \ {0}` (`|A₀| ≥ (n+r)/2`), living in the
`(n−1)`-element ground set `{1,…,n−1}`. For two large sets, inclusion–exclusion on
the centred sets gives
`|A ∩ B| ≥ |A₀ ∩ B₀| ≥ 2·⌊(n+r)/2⌋ − (n−1) = (n+r) − (n−1) = r+1 > r`,
using `n + r` even so `2·⌊(n+r)/2⌋ = n+r`; if either set is small (`|·| < r`) then
`|A ∩ B| ≤ min(|A|,|B|) < r`. In every case `|A ∩ B| ≠ r`. -/
theorem franklFurediEven_avoids_r (n r : ℕ) (hn : 1 ≤ n) (hpar : (n + r) % 2 = 0) :
    avoidsRIntersection r (franklFurediEven n r) := by
  intro A B hA hB
  rw [franklFurediEven, Finset.mem_filter, Finset.mem_powerset] at hA hB
  obtain ⟨hAsub, hAcond⟩ := hA
  obtain ⟨hBsub, hBcond⟩ := hB
  set A0 := A.filter (· ≠ 0) with hA0
  set B0 := B.filter (· ≠ 0) with hB0
  have hA0subA : A0 ⊆ A := Finset.filter_subset _ _
  have hB0subB : B0 ⊆ B := Finset.filter_subset _ _
  -- The centred intersection sits inside the actual intersection.
  have hcard_int : (A0 ∩ B0).card ≤ (A ∩ B).card :=
    Finset.card_le_card (Finset.inter_subset_inter hA0subA hB0subB)
  -- The centred sets live in `{1,…,n−1}`, which has `n−1` elements.
  have hground : ((Finset.range n).filter (· ≠ 0)).card = n - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.mpr hn),
      Finset.card_range]
  have hA0sub : A0 ⊆ (Finset.range n).filter (· ≠ 0) :=
    Finset.filter_subset_filter (· ≠ 0) hAsub
  have hB0sub : B0 ⊆ (Finset.range n).filter (· ≠ 0) :=
    Finset.filter_subset_filter (· ≠ 0) hBsub
  have hunion0 : (A0 ∪ B0).card ≤ n - 1 := by
    calc (A0 ∪ B0).card ≤ ((Finset.range n).filter (· ≠ 0)).card :=
          Finset.card_le_card (Finset.union_subset hA0sub hB0sub)
      _ = n - 1 := hground
  have hie0 := Finset.card_union_add_card_inter A0 B0
  have hiA : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hiB : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  rcases hAcond with hAlarge | hAsmall <;> rcases hBcond with hBlarge | hBsmall <;> omega

/--
**Lower bound on `T(n,r)` from the `franklFurediEven` construction (`n + r` even).**
The even-parity analogue of `franklFurediOdd_card_le_T`: `franklFurediEven n r` is a
valid `r`-avoiding subfamily of `2^{[n]}`, so its cardinality bounds `T(n,r)` below. -/
theorem franklFurediEven_card_le_T (n r : ℕ) (hn : 1 ≤ n) (hpar : (n + r) % 2 = 0) :
    (franklFurediEven n r).card ≤ T n r := by
  have hmem : franklFurediEven n r ∈
      ((Finset.range n).powerset.powerset).filter (avoidsRIntersection r) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
      franklFurediEven_avoids_r n r hn hpar⟩
  exact Finset.le_sup hmem

/-
## Part IV.b: Structural Properties of `T`

Elementary structural facts about the extremal function `T(n,r)` that hold for
all `n, r`, independent of the deep Frankl–Rödl bound. They frame the problem:
the trivial upper bound `T(n,r) ≤ 2^n` is exactly what Frankl–Rödl improves to
`(2 − δ)^n` in the middle range, and `T` is monotone in the ground set.
-/

/--
**Trivial upper bound `T(n,r) ≤ 2^n`.**
Every `r`-avoiding family lives inside `2^{[n]}`, which has `2^n` members, so the
sup of family sizes is at most `2^n`. The Frankl–Rödl axiom sharpens this to
`(2 − δ)^n` in the middle range `εn < r < (1/2 − ε)n`.
-/
theorem T_le_pow (n r : ℕ) : T n r ≤ 2 ^ n := by
  unfold T
  apply Finset.sup_le
  intro F hF
  rw [Finset.mem_filter, Finset.mem_powerset] at hF
  calc F.card ≤ ((Finset.range n).powerset).card := Finset.card_le_card hF.1
    _ = 2 ^ n := by rw [Finset.card_powerset, Finset.card_range]

/--
**`T` is monotone in the ground set.**
If `m ≤ n` then any `r`-avoiding family of subsets of `[m]` is also an
`r`-avoiding family of subsets of `[n]` (the predicate `avoidsRIntersection r`
depends only on the sets, not on the ground set), so `T(m,r) ≤ T(n,r)`.
-/
theorem T_mono_ground {m n r : ℕ} (h : m ≤ n) : T m r ≤ T n r := by
  unfold T
  apply Finset.sup_mono
  apply Finset.filter_subset_filter
  apply Finset.powerset_mono.mpr
  apply Finset.powerset_mono.mpr
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/--
**Positivity `1 ≤ T(n,r)` for `r ≥ 1`.**
The singleton family `{∅}` is `r`-avoiding whenever `r ≠ 0` (the only intersection
is `∅ ∩ ∅ = ∅`, of size `0 ≠ r`), witnessing a family of size `1`.
-/
theorem one_le_T (n r : ℕ) (hr : 1 ≤ r) : 1 ≤ T n r := by
  unfold T
  have hmem : ({∅} : Finset (Finset ℕ)) ∈
      ((Finset.range n).powerset.powerset).filter (avoidsRIntersection r) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro A hA
      rw [Finset.mem_singleton] at hA
      subst hA
      rw [Finset.mem_powerset]
      exact Finset.empty_subset _
    · intro A B hA hB
      rw [Finset.mem_singleton] at hA hB
      subst hA; subst hB
      simp only [Finset.inter_empty, Finset.card_empty]
      omega
  calc 1 = ({∅} : Finset (Finset ℕ)).card := (Finset.card_singleton _).symm
    _ ≤ _ := Finset.le_sup hmem

/--
**When `r` exceeds the ground set, the forbidden intersection size is
unattainable.** Every `A, B ⊆ [n]` satisfy `|A ∩ B| ≤ |A| ≤ n < r`, so the
entire powerset `2^{[n]}` is (vacuously) an `r`-avoiding family. -/
theorem full_powerset_avoids_r_of_lt (n r : ℕ) (h : n < r) :
    avoidsRIntersection r ((Finset.range n).powerset) := by
  intro A B hA _hB
  rw [Finset.mem_powerset] at hA
  have hle : (A ∩ B).card ≤ n :=
    calc (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ (Finset.range n).card := Finset.card_le_card hA
      _ = n := Finset.card_range n
  omega

/--
**Exact value `T(n,r) = 2ⁿ` for `r > n`.**
Once the forbidden intersection size `r` exceeds the ground-set size `n`, no two
subsets of `[n]` can meet in exactly `r` points (`|A ∩ B| ≤ n < r`), so the whole
powerset is a valid `r`-avoiding family of size `2ⁿ`. Together with the ceiling
`T_le_pow`, this pins the value exactly. This is the degenerate large-`r`
boundary of `T`, complementing the trivial small case `T(n,0) = 2^{n-1}`.
-/
theorem T_eq_pow_of_lt (n r : ℕ) (h : n < r) : T n r = 2 ^ n := by
  refine le_antisymm (T_le_pow n r) ?_
  unfold T
  have hmem : (Finset.range n).powerset ∈
      ((Finset.range n).powerset.powerset).filter (avoidsRIntersection r) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),
      full_powerset_avoids_r_of_lt n r h⟩
  calc 2 ^ n = ((Finset.range n).powerset).card := by
        rw [Finset.card_powerset, Finset.card_range]
    _ ≤ _ := Finset.le_sup hmem

/--
**For subsets of `[n]`, an intersection of size `n` fills the ground set.**
If `A, B ⊆ [n]` and `|A ∩ B| = n`, then `A ∩ B = [n]` (it is an `n`-element subset
of the `n`-element set `[n]`), forcing `A = B = [n]`. This is the structural fact
behind the diagonal value `T(n,n)`. -/
theorem inter_card_eq_n_iff {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n) :
    (A ∩ B).card = n ↔ A = Finset.range n ∧ B = Finset.range n := by
  constructor
  · intro h
    have hsub : A ∩ B ⊆ Finset.range n := (Finset.inter_subset_left).trans hA
    have heq : A ∩ B = Finset.range n :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, h])
    have hAn : Finset.range n ⊆ A := heq ▸ Finset.inter_subset_left
    have hBn : Finset.range n ⊆ B := heq ▸ Finset.inter_subset_right
    exact ⟨Finset.Subset.antisymm hA hAn, Finset.Subset.antisymm hB hBn⟩
  · rintro ⟨rfl, rfl⟩
    rw [Finset.inter_self, Finset.card_range]

/--
**The diagonal value `T(n,n) = 2^n − 1`.**
A family `F ⊆ 2^{[n]}` avoids `n`-intersection iff it omits the full ground set
`[n]`: the *only* pair of subsets of `[n]` meeting in `n` elements is `[n]` with
itself (`inter_card_eq_n_iff`), and `avoidsRIntersection` forbids that self-pair.
Hence the largest `n`-avoiding family is the powerset minus the single set `[n]`,
of size `2^n − 1`. Together with `T(n,0) = 2^{n-1}` and `T(n,r) = 2^n` for `n < r`,
this pins the third exactly-known boundary value of `T`, at the diagonal `r = n`. -/
theorem T_n_n (n : ℕ) : T n n = 2 ^ n - 1 := by
  apply le_antisymm
  · -- Upper bound: every avoiding family omits `[n]`, so embeds in `powerset \ {[n]}`.
    apply Finset.sup_le
    intro F hF
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    obtain ⟨hFsub, hFavoid⟩ := hF
    have hnotmem : Finset.range n ∉ F := fun hmem =>
      hFavoid (Finset.range n) (Finset.range n) hmem hmem
        (by rw [Finset.inter_self, Finset.card_range])
    have hsub : F ⊆ (Finset.range n).powerset.erase (Finset.range n) := by
      intro A hA
      rw [Finset.mem_erase]
      exact ⟨fun h => hnotmem (h ▸ hA), hFsub hA⟩
    calc F.card ≤ ((Finset.range n).powerset.erase (Finset.range n)).card :=
          Finset.card_le_card hsub
      _ = (Finset.range n).powerset.card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.Subset.refl _))
      _ = 2 ^ n - 1 := by rw [Finset.card_powerset, Finset.card_range]
  · -- Lower bound: `powerset \ {[n]}` is itself `n`-avoiding, of size `2^n − 1`.
    have hmem : (Finset.range n).powerset.erase (Finset.range n) ∈
        ((Finset.range n).powerset.powerset).filter (avoidsRIntersection n) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.erase_subset _ _, ?_⟩
      intro A B hA hB
      rw [Finset.mem_erase, Finset.mem_powerset] at hA hB
      intro hcontra
      exact hA.1 ((inter_card_eq_n_iff hA.2 hB.2).mp hcontra).1
    calc 2 ^ n - 1 = ((Finset.range n).powerset.erase (Finset.range n)).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.Subset.refl _)),
            Finset.card_powerset, Finset.card_range]
      _ ≤ T n n := Finset.le_sup hmem

/--
**The `r = 1` large-set family is contained in `franklFurediOdd n 1`.**
`largeSetsFamily n` filters on `|A| > (n+1)/2`, exactly the "large" disjunct of
`franklFurediOdd n 1` (whose threshold `(n+1)/2` coincides). So the general-`r`
Frankl–Füredi construction specializes to Frankl's `r = 1` construction.
-/
theorem largeSetsFamily_subset_franklFurediOdd_one (n : ℕ) :
    largeSetsFamily n ⊆ franklFurediOdd n 1 := by
  intro A hA
  rw [largeSetsFamily, Finset.mem_filter] at hA
  rw [franklFurediOdd, Finset.mem_filter]
  exact ⟨hA.1, Or.inl hA.2⟩

/-!
### Concrete `r = 1` lower bounds from the Frankl–Füredi construction

`T n r` is a supremum over exponentially many families, so it is not directly
`decide`-able; but the explicit family `franklFurediOdd n 1 = {A ⊆ [n] : |A| > (n+1)/2
or A = ∅}` is a *valid* `1`-avoiding family (`franklFurediOdd_avoids_r`), and its
cardinality — a small, kernel-`decide`-able number — is a certified lower bound for
`T n 1` (`franklFurediOdd_card_le_T`). For `n = 4` the family is
`{∅} ∪ {|A| ∈ {3,4}}`, size `1 + C(4,3) + C(4,4) = 6`; for `n = 5` it is
`{∅} ∪ {|A| ∈ {4,5}}`, size `1 + C(5,4) + C(5,5) = 7`. These give the first concrete
numeric anchors for the (otherwise only-asymptotically-bounded) `r = 1` line, alongside
the exact `T n 0 = 2^{n-1}` and `T n n = 2^n - 1`. -/

/-- **`T(4,1) ≥ 6`**: the `n = 4` Frankl–Füredi family `{∅, and all 3- or 4-subsets of
    [4]}` is `1`-avoiding with `6` members, so it is a concrete lower bound for `T 4 1`. -/
theorem six_le_T_4_1 : 6 ≤ T 4 1 := by
  have h : (franklFurediOdd 4 1).card = 6 := by decide
  have hle := franklFurediOdd_card_le_T 4 1
  omega

/-- **`T(5,1) ≥ 7`**: the `n = 5` Frankl–Füredi family `{∅, and all 4- or 5-subsets of
    [5]}` is `1`-avoiding with `7` members, so it is a concrete lower bound for `T 5 1`. -/
theorem seven_le_T_5_1 : 7 ≤ T 5 1 := by
  have h : (franklFurediOdd 5 1).card = 7 := by decide
  have hle := franklFurediOdd_card_le_T 5 1
  omega

/-- **Uniform lower bound `T(n,1) ≥ 6` for every ground set of size `n ≥ 4`.** The
    concrete `n = 4` anchor `six_le_T_4_1` propagates to all larger `n` by monotonicity
    of `T` in the ground-set size (`T_mono_ground`): a `1`-avoiding family on `[4]` is
    still `1`-avoiding when the ground set is enlarged to `[n]`, so the extremal size can
    only grow.  This turns the isolated decidable anchor into an infinite family of
    certified lower bounds without any further `decide`. -/
theorem six_le_T_n_1 (n : ℕ) (hn : 4 ≤ n) : 6 ≤ T n 1 :=
  le_trans six_le_T_4_1 (T_mono_ground (r := 1) hn)

/-- **Uniform lower bound `T(n,1) ≥ 7` for every ground set of size `n ≥ 5`.** The same
    monotone propagation (`T_mono_ground`) of the `n = 5` anchor `seven_le_T_5_1`,
    sharpening `six_le_T_n_1` on the range `n ≥ 5`. -/
theorem seven_le_T_n_1 (n : ℕ) (hn : 5 ≤ n) : 7 ≤ T n 1 :=
  le_trans seven_le_T_5_1 (T_mono_ground (r := 1) hn)

/-
## Part V: The Main Question - Exponential Bound

For fixed `r` and `n` sufficiently large, Frankl-Füredi (1984) determined
`T(n,r)` exactly as the size of the optimal family above.
-/

/--
**The Main Question:**
For every ε > 0, is there δ > 0 such that for εn < r < (1/2 - ε)n,
we have `T(n,r) < (2 - δ)^n`?
-/
def mainQuestion : Prop :=
  ∀ ε : ℚ, ε > 0 → ε < 1 / 2 →
    ∃ δ : ℚ, δ > 0 ∧
      ∀ n r : ℕ, (r : ℚ) > ε * n → (r : ℚ) < (1 / 2 - ε) * n →
        (T n r : ℚ) < (2 - δ) ^ n

/--
**Frankl-Rödl (1987) - Main Theorem:**
The answer to the main question is YES. For `r` in the "middle range"
`εn < r < (1/2 - ε)n`, the family size is exponentially bounded away from `2^n`.
-/
axiom frankl_rodl_1987 : mainQuestion

/-
## Part VI: Connection to Chromatic Numbers

The affirmative answer to the main question implies that `χ(n)`, the chromatic
number of the unit-distance graph in `ℝ^n`, grows exponentially in `n` (also
proved by Frankl-Wilson (1981) via the Frankl-Wilson theorem on set systems
avoiding fixed intersection sizes mod `p`). This geometric consequence is
recorded here informally; it requires the chromatic number of an infinite
unit-distance graph, which is not yet available in Mathlib, so no opaque symbol
is introduced for it.

## Part VII: The Frankl-Wilson Theorem
-/

/--
**L-Avoiding Family:**
A family F avoids a set L of intersection sizes if no two sets in F
have intersection size in L.
-/
def avoidsLIntersections (L : Finset ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ A B : Finset ℕ, A ∈ F → B ∈ F → (A ∩ B).card ∉ L

/--
**Single-forbidden-size is `r`-avoidance.** The `L`-avoiding predicate specializes to
`avoidsRIntersection r` exactly when `L = {r}`: forbidding the single intersection size
`r` is the same as avoiding `r`-intersection. This is the bridge that places
`avoidsRIntersection` inside the Frankl–Wilson `L`-avoiding hierarchy.
-/
theorem avoidsRIntersection_iff_avoidsLIntersections_singleton
    (r : ℕ) (F : Finset (Finset ℕ)) :
    avoidsRIntersection r F ↔ avoidsLIntersections {r} F := by
  unfold avoidsRIntersection avoidsLIntersections
  simp only [Finset.mem_singleton, ne_eq]

/--
**Monotone in the family (subfamily closure).** Any subfamily of an `L`-avoiding
family is again `L`-avoiding: the constraint on pairs is inherited by any subset.
-/
theorem avoidsLIntersections_of_subset_family
    {L : Finset ℕ} {F F' : Finset (Finset ℕ)} (hsub : F' ⊆ F)
    (hF : avoidsLIntersections L F) : avoidsLIntersections L F' :=
  fun A B hA hB => hF A B (hsub hA) (hsub hB)

/--
**Antitone in the forbidden-size set.** Forbidding a *larger* set of intersection
sizes is a stronger condition: if `F` avoids every size in `L'` and `L ⊆ L'`, then `F`
avoids every size in `L`. Combined with the singleton bridge this recovers, e.g., that
an `L`-avoiding family with `r ∈ L` is in particular `r`-avoiding.
-/
theorem avoidsLIntersections_of_subset_forbidden
    {L L' : Finset ℕ} {F : Finset (Finset ℕ)} (hL : L ⊆ L')
    (hF : avoidsLIntersections L' F) : avoidsLIntersections L F :=
  fun A B hA hB hmem => hF A B hA hB (hL hmem)

/--
**Every family avoids the empty set of sizes.** The vacuous base case of the
hierarchy: with no forbidden intersection sizes there is nothing to avoid.
-/
theorem avoidsLIntersections_empty (F : Finset (Finset ℕ)) :
    avoidsLIntersections ∅ F := by
  intro A B _ _
  simp

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #703 Summary:**

PROBLEM: Estimate T(n,r), the maximum size of a family avoiding r-intersection.
Is T(n,r) < (2 - δ)^n for r in the "middle range" εn < r < (1/2 - ε)n?

STATUS: SOLVED (YES)

KEY RESULTS:
1. T(n,0) = 2^{n-1} (trivial, intersecting families) — proved here
2. Frankl (1977): Determined T(n,1) for all n
3. Frankl-Füredi (1984): Determined T(n,r) for fixed r and large n
4. Frankl-Rödl (1987): Proved T(n,r) < (2 - δ)^n for middle range (main question)
5. Connection: This implies exponential chromatic number of unit distance graph
-/
theorem erdos_703_solved :
    -- The main question is answered YES
    mainQuestion ∧
    -- T(n,0) is exactly determined
    (∀ n : ℕ, n ≥ 1 → T n 0 = 2 ^ (n - 1)) := by
  refine ⟨frankl_rodl_1987, ?_⟩
  exact T_n_0

/--
**Main Theorem:**
T(n,r) < (2 - δ)^n for r in the middle range, resolving Erdős #703.
-/
theorem erdos_703 : mainQuestion := frankl_rodl_1987

end Erdos703
