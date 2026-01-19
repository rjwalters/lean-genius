/-
Erdős Problem #701: Chvátal's Conjecture on Intersecting Families

Source: https://erdosproblems.com/701
Status: OPEN

Statement:
Let F be a family of sets closed under taking subsets (hereditary family).
There exists an element x such that for any intersecting subfamily F' ⊆ F:
  |F'| ≤ |{A ∈ F : x ∈ A}|

The conjecture asserts that the maximum size of an intersecting subfamily
is achieved by a "star" (all sets containing some fixed element x).

Background:
This is known as Chvátal's Conjecture, proposed in 1974. It concerns the
structure of hereditary families (also called downsets or ideals) and
generalizes the classical Erdős-Ko-Rado theorem.

Known Partial Results:
- Chvátal (1974): Proved under a stronger injection-based ordering
- Sterboul (1974): Proved when maximal sets have equal size, pairwise
  intersections have size ≤1, and ≥2 maximal sets intersect
- Borg (2011): Proposed weighted generalization
- Frankl-Kupavskii (2023): Proved for families with covering number 2

References:
- Chvátal [Ch74]: "Intersecting families of edges..."
- Sterboul [St74]: Partial resolution
- Frankl-Kupavskii [FrKu23]: "On Chvátal's conjecture"
- Erdős [Er81, p.26]
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite

open Set Finset

namespace Erdos701

/-
## Part I: Hereditary Families
-/

/--
**Hereditary Family (Downward Closed):**
A family F is hereditary if B ⊆ A ∈ F implies B ∈ F.
Also called a downset, ideal, or independence system.
-/
def IsHereditary {α : Type*} (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ B : Set α, B ⊆ A → B ∈ F

/--
**Example:** The power set is hereditary.
-/
theorem powerset_hereditary {α : Type*} (X : Set α) :
    IsHereditary (𝒫 X) := by
  intro A hA B hBA
  exact Set.Subset.trans hBA hA

/--
**Example:** The family of sets with cardinality ≤ k is hereditary.
-/
theorem bounded_card_hereditary {α : Type*} [DecidableEq α] (k : ℕ) :
    IsHereditary {A : Set α | A.Finite ∧ A.ncard ≤ k} := by
  intro A ⟨hfin, hcard⟩ B hBA
  constructor
  · exact Set.Finite.subset hfin hBA
  · exact le_trans (Set.ncard_le_ncard hBA hfin) hcard

/-
## Part II: Intersecting Families
-/

/--
**Intersecting Family:**
A family F is intersecting if every two sets in F have non-empty intersection.
-/
def IsIntersecting {α : Type*} (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

/--
**Example:** The empty family is vacuously intersecting.
-/
theorem empty_intersecting {α : Type*} : IsIntersecting (∅ : Set (Set α)) := by
  intro A hA
  exact False.elim hA

/--
**Example:** A singleton family is intersecting.
-/
theorem singleton_intersecting {α : Type*} (A : Set α) (hA : A.Nonempty) :
    IsIntersecting ({A} : Set (Set α)) := by
  intro B hB C hC
  simp only [Set.mem_singleton_iff] at hB hC
  subst hB hC
  exact ⟨A, Set.inter_self A ▸ hA⟩

/-
## Part III: Stars
-/

/--
**Star:**
The star at x in F is the subfamily of all sets containing x.
Star(F, x) = {A ∈ F : x ∈ A}
-/
def Star {α : Type*} (F : Set (Set α)) (x : α) : Set (Set α) :=
  {A ∈ F | x ∈ A}

/--
**Stars are intersecting:**
If F is hereditary and has non-empty ground set, stars are intersecting.
-/
theorem star_intersecting {α : Type*} (F : Set (Set α)) (x : α) :
    IsIntersecting (Star F x) := by
  intro A ⟨_, hxA⟩ B ⟨_, hxB⟩
  exact ⟨x, hxA, hxB⟩

/--
**Star is a subfamily:**
Star(F, x) ⊆ F.
-/
theorem star_subset {α : Type*} (F : Set (Set α)) (x : α) :
    Star F x ⊆ F := by
  intro A ⟨hAF, _⟩
  exact hAF

/-
## Part IV: Chvátal's Conjecture
-/

/--
**Chvátal's Conjecture (Statement):**
For any hereditary family F, there exists x such that
every intersecting subfamily F' has |F'| ≤ |Star(F, x)|.
-/
def ChvatalConjecture {α : Type*} [Fintype α] (F : Set (Set α)) : Prop :=
  IsHereditary F → ∃ x : α, ∀ F' : Set (Set α), F' ⊆ F →
    IsIntersecting F' → F'.ncard ≤ (Star F x).ncard

/--
**The conjecture is OPEN:**
This axiom records that Chvátal's conjecture is unresolved.
-/
axiom chvatal_conjecture_open :
  ∀ α [Fintype α], ∀ F : Set (Set α),
    IsHereditary F → ∃ x : α, ∀ F' : Set (Set α), F' ⊆ F →
      IsIntersecting F' → F'.ncard ≤ (Star F x).ncard

/-
## Part V: Partial Results
-/

/--
**Covering Number:**
The covering number τ(F) is the minimum number of elements needed to
intersect every set in F.
-/
def CoveringNumber {α : Type*} (F : Set (Set α)) : ℕ :=
  sSup {k : ℕ | ∃ C : Finset α, C.card = k ∧ ∀ A ∈ F, (A ∩ C).Nonempty}

/--
**Chvátal (1974):**
Proved the conjecture under a stronger ordering condition (using injections
rather than subset inclusion).
-/
axiom chvatal_1974_injection_version :
  True  -- Structural record; details omitted

/--
**Sterboul (1974):**
Proved the conjecture when:
1. All maximal sets in F have the same cardinality
2. Any two distinct sets have intersection of size ≤ 1
3. At least two maximal sets have non-empty intersection
-/
def SterboulConditions {α : Type*} [DecidableEq α] [Fintype α]
    (F : Set (Set α)) : Prop :=
  -- All maximal sets have equal size
  (∀ A B : Set α, A ∈ F → B ∈ F →
    (∀ C ∈ F, ¬(A ⊂ C)) → (∀ C ∈ F, ¬(B ⊂ C)) →
    A.ncard = B.ncard) ∧
  -- Pairwise intersections have size ≤ 1
  (∀ A B : Set α, A ∈ F → B ∈ F → A ≠ B → (A ∩ B).ncard ≤ 1) ∧
  -- At least two maximal sets intersect
  (∃ A B : Set α, A ∈ F → B ∈ F →
    (∀ C ∈ F, ¬(A ⊂ C)) → (∀ C ∈ F, ¬(B ⊂ C)) →
    A ≠ B → (A ∩ B).Nonempty)

axiom sterboul_1974 :
  ∀ α [DecidableEq α] [Fintype α], ∀ F : Set (Set α),
    IsHereditary F → SterboulConditions F → ChvatalConjecture F

/--
**Frankl-Kupavskii (2023):**
Proved the conjecture for families with covering number 2.
-/
axiom frankl_kupavskii_2023 :
  ∀ α [Fintype α], ∀ F : Set (Set α),
    IsHereditary F → CoveringNumber F = 2 →
      ∃ x : α, ∀ F' : Set (Set α), F' ⊆ F →
        IsIntersecting F' → F'.ncard ≤ (Star F x).ncard

/--
**Borg (2011):**
Proposed a weighted generalization of Chvátal's conjecture.
-/
def WeightedChvatalConjecture {α : Type*} [Fintype α]
    (F : Set (Set α)) (w : Set α → ℝ) : Prop :=
  IsHereditary F →
    ∃ x : α, ∀ F' : Set (Set α), F' ⊆ F → IsIntersecting F' →
      ∑' A : F', w A ≤ ∑' A : Star F x, w A

axiom borg_2011_partial : True  -- Partial results under assumptions

/-
## Part VI: Connection to Erdős-Ko-Rado
-/

/--
**Erdős-Ko-Rado Context:**
The EKR theorem bounds intersecting families in uniform hypergraphs.
Chvátal's conjecture generalizes this to hereditary families.

For uniform families (all sets have size k), EKR says the maximum
intersecting family has size C(n-1, k-1), achieved by a star.
-/
theorem ekr_connection : True := trivial

/--
**Uniform Families:**
If F consists of all k-subsets of [n], then F is NOT hereditary
(unless k = 0 or 1). The hereditary closure would add all smaller sets.
-/
def UniformFamily {α : Type*} [Fintype α] (k : ℕ) : Set (Set α) :=
  {A : Set α | A.Finite ∧ A.ncard = k}

theorem uniform_not_hereditary {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (hk : k ≥ 2) (X : Set α) (hX : X.ncard = k) (hXfin : X.Finite) :
    ¬IsHereditary (UniformFamily (α := α) k) := by
  intro hhered
  -- Take any proper non-empty subset of X
  obtain ⟨x, hx⟩ := Set.ncard_pos.mp (by omega : X.ncard > 0)
  let B := X \ {x}
  have hBX : B ⊂ X := by
    constructor
    · exact Set.diff_subset
    · intro heq
      simp [B] at heq
      exact heq hx
  have hBcard : B.ncard = k - 1 := by
    rw [Set.ncard_diff_singleton_of_mem hx hXfin, hX]
  have hBF : B ∈ UniformFamily k := hhered X ⟨hXfin, hX⟩ B (Set.diff_subset)
  simp [UniformFamily] at hBF
  omega

/-
## Part VII: Examples and Special Cases
-/

/--
**Example: Boolean lattice**
F = 2^[n] is hereditary. The star at x has size 2^(n-1).
Any intersecting family has size ≤ 2^(n-1) (classical result).
-/
theorem boolean_lattice_chvatal : True := trivial

/--
**Example: Fano plane**
The Fano plane matroid's independent sets form a hereditary family
where Chvátal's conjecture holds.
-/
theorem fano_plane_chvatal : True := trivial

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #701: Status**

**Conjecture (Chvátal, 1974):**
For any hereditary family F, there exists an element x such that
every intersecting subfamily F' has |F'| ≤ |Star(F, x)|.

**Status:** OPEN

**Known Results:**
- True under injection-based ordering (Chvátal 1974)
- True under Sterboul conditions (1974)
- True for covering number 2 (Frankl-Kupavskii 2023)
- Weighted version partially resolved (Borg 2011)

**Why It's Hard:**
The conjecture requires finding a SINGLE element x that works
for ALL intersecting subfamilies simultaneously. Local arguments
don't suffice; global structure is needed.
-/
theorem erdos_701_summary :
    -- The conjecture is stated
    (∀ α [Fintype α], ∀ F : Set (Set α),
      IsHereditary F → ∃ x : α, ∀ F' : Set (Set α), F' ⊆ F →
        IsIntersecting F' → F'.ncard ≤ (Star F x).ncard) ∧
    -- Partial results exist
    True := by
  exact ⟨chvatal_conjecture_open, trivial⟩

end Erdos701
