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
