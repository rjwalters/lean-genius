import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Proofs.BallotProblemOQ01OQ02OQ01

/-
# Mathlib Contribution Analysis: ncard_biUnion_eq_of_uniform

## Open Question (ballot-problem-oq-01-oq-02-oq-01-oq-01)

**Could the abstract `ncard_biUnion_eq_of_uniform` lemma be contributed to Mathlib?**

## Answer: Yes

The lemma `ncard_biUnion_eq_of_uniform` from `BallotProblemOQ01OQ02OQ01.lean` is:
- Not currently in Mathlib (as of Mathlib4)
- General enough to be useful beyond the ballot problem
- Provable cleanly from `Set.ncard_biUnion` in 5-10 lines

## What Mathlib Has

Mathlib has `Set.ncard_biUnion`:
  `(⋃ i ∈ I, s i).ncard = ∑ i ∈ I.toFinset, (s i).ncard`
  (when I is finite and the sets are pairwise disjoint)

And `Finset.sum_const`:
  `∑ i ∈ s, c = s.card • c`

The missing gap: a direct corollary for the *uniform fiber* case:
  all `(s i).ncard = k` → `(⋃ i ∈ I, s i).ncard = k * I.ncard`

## Mathlib-Ready Formulation

This file reformulates the lemma using Mathlib's `Set.PairwiseDisjoint`:
  `I.PairwiseDisjoint s` (more standard than the nested ∀∀ form)

And demonstrates key specializations and corollaries.

## Relationship to Parent File

`BallotProblemOQ01OQ02OQ01.lean` proved this for the ballot problem's fiber structure.
This file extracts the general form and adds specializations for:
1. Finset index sets
2. Nat-indexed families
3. The Fintype case (simpler hypothesis)

References:
- Parent: `BallotProblemOQ01OQ02OQ01.lean` (ballot fiber counting)
- Mathlib: `Set.ncard_biUnion`, `Set.PairwiseDisjoint`
-/

namespace NcardBiUnionUniform

open Set BigOperators

-- ============================================================
-- PART 1: The Core Lemma (re-exported, Mathlib-ready form)
-- ============================================================

/-- **`Set.ncard_biUnion_eq_of_uniform`** (Mathlib contribution candidate)

    If a pairwise-disjoint family of finite sets indexed by a finite set I
    all have the same cardinality k, then the cardinality of their union is k × |I|.

    This is the uniform-fiber special case of `Set.ncard_biUnion`. -/
theorem ncard_biUnion_eq_of_uniform {α ι : Type*} {s : ι → Set α}
    {I : Set ι} (hI : I.Finite)
    (hfin : ∀ i ∈ I, (s i).Finite)
    (hdisj : I.PairwiseDisjoint s)
    {k : ℕ} (hk : ∀ i ∈ I, (s i).ncard = k) :
    (⋃ i ∈ I, s i).ncard = k * I.ncard := by
  -- Reduce to hI.toFinset for the sum
  rw [Set.ncard_biUnion hI (fun i j hi hj hne => hdisj hi hj hne) (fun i hi => hfin i hi)]
  have hmem : ∀ i ∈ hI.toFinset, (s i).ncard = k :=
    fun i hi => hk i (hI.mem_toFinset.mp hi)
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, smul_eq_mul,
      mul_comm, hI.toFinset_card]

-- ============================================================
-- PART 2: Specialization to Finset Index Sets
-- ============================================================

/-- Finset version: when the index set is a Finset rather than a Set.finite,
    the hypotheses are slightly simpler. -/
theorem ncard_biUnion_eq_of_uniform_finset {α ι : Type*} {s : ι → Set α}
    {I : Finset ι}
    (hfin : ∀ i ∈ I, (s i).Finite)
    (hdisj : (I : Set ι).PairwiseDisjoint s)
    {k : ℕ} (hk : ∀ i ∈ I, (s i).ncard = k) :
    (⋃ i ∈ I, s i).ncard = k * I.card := by
  have hI : (I : Set ι).Finite := I.finite_toSet
  rw [← Set.ncard_coe_Finset]
  exact ncard_biUnion_eq_of_uniform hI hfin hdisj (fun i hi => hk i (Finset.mem_coe.mp hi))

-- ============================================================
-- PART 3: The Fintype Version (Strongest Form)
-- ============================================================

/-- Fintype version: when the index type is Fintype, the universe covers all fibers. -/
theorem ncard_iUnion_eq_of_uniform {α ι : Type*} [Fintype ι] {s : ι → Set α}
    (hfin : ∀ i, (s i).Finite)
    (hdisj : Pairwise (Disjoint on s))
    {k : ℕ} (hk : ∀ i, (s i).ncard = k) :
    (⋃ i, s i).ncard = k * Fintype.card ι := by
  rw [← Set.biUnion_univ]
  rw [ncard_biUnion_eq_of_uniform Set.finite_univ (fun i _ => hfin i)
      (fun _ _ hne => hdisj hne)
      (fun i _ => hk i)]
  simp [Set.ncard_univ]

-- ============================================================
-- PART 4: Consequence — Probability Transfer
-- ============================================================

/-- If a function f has uniform fiber sizes (each fiber has k elements),
    and the domain decomposes as a disjoint union over the image,
    then |S| = k * |f(S)| for any subset S of the domain that is
    f-saturated (closed under fibers). -/
theorem ncard_eq_mul_of_uniform_fibers {α β : Type*}
    (f : α → β)
    {A : Set α} {B : Set β}
    (hB : B.Finite)
    (hfib : A = ⋃ b ∈ B, f ⁻¹' {b} ∩ A)
    (hfin : ∀ b ∈ B, (f ⁻¹' {b} ∩ A).Finite)
    (hdisj : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      Disjoint (f ⁻¹' {b₁} ∩ A) (f ⁻¹' {b₂} ∩ A))
    {k : ℕ} (hk : ∀ b ∈ B, (f ⁻¹' {b} ∩ A).ncard = k) :
    A.ncard = k * B.ncard := by
  conv_lhs => rw [hfib]
  exact ncard_biUnion_eq_of_uniform hB hfin
    (fun b₁ hb₁ b₂ hb₂ hne => hdisj b₁ hb₁ b₂ hb₂ hne) hk

-- ============================================================
-- PART 5: Compatibility with Parent File
-- ============================================================

/-- The version in the parent file (with explicit ∀ quantifiers for disjointness)
    follows from our PairwiseDisjoint version. This shows both forms are equivalent. -/
theorem ncard_biUnion_eq_of_uniform_compat {α ι : Type*} {s : ι → Set α}
    {I : Set ι} (hI : I.Finite)
    (hfin : ∀ i ∈ I, (s i).Finite)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (s i) (s j))
    {k : ℕ} (hk : ∀ i ∈ I, (s i).ncard = k) :
    (⋃ i ∈ I, s i).ncard = k * I.ncard :=
  ncard_biUnion_eq_of_uniform hI hfin (fun hi hj hne => hdisj _ hi _ hj hne) hk

-- ============================================================
-- PART 6: Concrete Examples (Verifying the Lemma is Non-Trivial)
-- ============================================================

/-- Example: three disjoint pairs of naturals, each of size 2. -/
example :
    (⋃ i ∈ ({0, 1, 2} : Finset ℕ), ({2 * i, 2 * i + 1} : Set ℕ)).ncard =
    2 * 3 := by
  have hfin : ∀ i ∈ ({0, 1, 2} : Finset ℕ),
      ({2 * i, 2 * i + 1} : Set ℕ).Finite := fun i _ => Set.finite_pair _ _
  have hdisj : ({0, 1, 2} : Set ℕ).PairwiseDisjoint
      (fun i => ({2 * i, 2 * i + 1} : Set ℕ)) := by
    intro a ha b hb hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hk : ∀ i ∈ ({0, 1, 2} : Finset ℕ),
      ({2 * i, 2 * i + 1} : Set ℕ).ncard = 2 := by
    intro i hi
    have : (2 * i : ℕ) ≠ 2 * i + 1 := by omega
    rw [Set.ncard_pair this]
  rw [ncard_biUnion_eq_of_uniform_finset hfin hdisj hk]
  rfl

-- ============================================================
-- PART 7: Mathlib Contribution Assessment
-- ============================================================

/-
## Why This Lemma Is Mathlib-Ready

**Not in Mathlib**: As of Mathlib4, there is no direct lemma for the uniform-fiber case
of `Set.ncard_biUnion`. The closest lemmas are:
- `Set.ncard_biUnion`: sum formula (not uniform specialization)
- `Finset.card_biUnion`: Finset version (not Set.ncard)
- `Set.ncard_iUnion_of_disjoint`: ∑ version, not uniform case

**Proof length**: ~10 lines from `Set.ncard_biUnion` (short, clean)

**Generality**: Works for any type α, ι without additional typeclasses

**Use cases**:
1. Ballot problem fiber analysis (this gallery)
2. Group coset counting (|G| = k × |G/H| when all cosets have size k)
3. Graph theory (|V| = k × |V/∼| for k-regular equivalence relations)
4. Probability theory (uniform partition counting)

**Naming**: `Set.ncard_biUnion_eq_of_uniform` follows Mathlib conventions

**Recommendation**: Submit to Mathlib as `Set.ncard_biUnion_of_uniform` or
`Set.ncard_biUnion_const` (naming TBD by Mathlib maintainers)
-/

end NcardBiUnionUniform
