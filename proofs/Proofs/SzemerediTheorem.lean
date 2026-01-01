/-
# Szemerédi's Theorem

Every subset of natural numbers with positive upper density contains
arbitrarily long arithmetic progressions.

**Status**: COMPLETED for k=3 (Roth's theorem via Mathlib)
- General k-AP definition and formal statement
- Trivial cases k=1,2 proved
- k=3 (Roth's theorem): PROVED using Mathlib's corner theorem chain
- Equivalence between our IsAPFree and Mathlib's ThreeAPFree
- k≥4: Still requires hypergraph regularity (stated as axiom)

**What's in Mathlib already**:
- `AddSalemSpencer`: Sets without 3-term APs (Mathlib.Combinatorics.Additive.SalemSpencer)
- `rothNumberNat`: Maximum size of 3-AP-free subset of [n]
- Behrend's lower bound on Roth numbers
- Szemerédi Regularity Lemma (Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma)
- Triangle Removal Lemma (Mathlib.Combinatorics.SimpleGraph.Triangle.Removal)
- Corners Theorem (Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite)

**What's missing for full proof**:
- k≥4: Hypergraph regularity (NOT in Mathlib)
- Or: Furstenberg ergodic theory approach

**References**:
- Szemerédi, "On sets of integers containing no k elements in AP" (1975)
- Furstenberg, "Ergodic behavior of diagonal measures" (1977)
- Gowers, "A new proof of Szemerédi's theorem" (2001)
- Dillies & Mehta, "Formalising Szemerédi's Regularity Lemma in Lean" (ITP 2022)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Tactic

namespace Szemeredi

/-!
## Arithmetic Progressions of Length k

An arithmetic progression of length k in ℕ is a sequence
  a, a+d, a+2d, ..., a+(k-1)d
where d > 0 (non-trivial).
-/

/-- A set contains an arithmetic progression of length k with positive common difference -/
def HasAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ ∀ i : ℕ, i < k → (a + i * d) ∈ S

/-- A finset contains an arithmetic progression of length k -/
def hasAPOfLengthFinset (S : Finset ℕ) (k : ℕ) : Prop :=
  HasAPOfLength (S : Set ℕ) k

/-- A set is k-AP-free if it contains no arithmetic progression of length k -/
def IsAPFree (S : Set ℕ) (k : ℕ) : Prop := ¬ HasAPOfLength S k

/-!
## Szemerédi's Theorem Statement

For any k ≥ 1 and δ > 0, there exists N₀ such that any subset
of {1,...,N} with at least δN elements contains a k-term AP.
-/

/-- **Szemerédi's Theorem**: Dense subsets of [1,N] contain arbitrarily long APs -/
def SzemerediTheorem : Prop :=
  ∀ (k : ℕ) (δ : ℝ), k ≥ 1 → δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S k

/-!
## Trivial Cases

k=1: Any non-empty set contains a 1-AP
k=2: Any set with ≥2 elements contains a 2-AP
-/

/-- k=1: any non-empty set has a 1-AP (single element) -/
theorem szemeredi_k1 (S : Set ℕ) (hne : S.Nonempty) : HasAPOfLength S 1 := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, 1, Nat.one_pos, fun i hi => by simp [Nat.lt_one_iff.mp hi, ha]⟩

/-- k=2: any set with 2 distinct elements has a 2-AP -/
theorem szemeredi_k2 (S : Finset ℕ) (h : S.card ≥ 2) : hasAPOfLengthFinset S 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.one_lt_two.trans_le h)
  by_cases hlt : a < b
  · refine ⟨a, b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · simp only [Nat.one_mul, Set.mem_setOf_eq]
      have : a + (b - a) = b := Nat.add_sub_cancel' (Nat.le_of_lt hlt)
      rw [this]
      exact hb
  · push_neg at hlt
    have hlt' : b < a := Nat.lt_of_le_of_ne hlt (Ne.symm hab)
    refine ⟨b, a - b, Nat.sub_pos_of_lt hlt', ?_⟩
    intro i hi
    interval_cases i
    · simpa using hb
    · simp only [Nat.one_mul, Set.mem_setOf_eq]
      have : b + (a - b) = a := Nat.add_sub_cancel' (Nat.le_of_lt hlt')
      rw [this]
      exact ha

/-!
## Full Theorem (Axiom)

The full proof for k ≥ 3 requires:
1. k=3: Roth's theorem (in Mathlib via corners theorem)
2. k≥4: Hypergraph regularity (NOT in Mathlib)

We state the full theorem as an axiom.
-/

/-- The full Szemerédi theorem (1975) -/
axiom szemeredi_theorem : SzemerediTheorem

/-- Corollary: every dense set contains arbitrarily long APs -/
theorem dense_set_has_long_ap (k : ℕ) (δ : ℝ) (hk : k ≥ 1) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S k :=
  szemeredi_theorem k δ hk hδ

/-!
## Connection to Mathlib's ThreeAPFree

Mathlib provides (in `Mathlib.Combinatorics.Additive.AP.Three.Defs`):
- `ThreeAPFree`: Predicate for sets without 3-term APs
- `rothNumberNat`: Maximum size of 3-AP-free subset of {0,...,n-1}
- `addRothNumber`: General version for finite sets

And in `Mathlib.Combinatorics.Additive.Corner.Roth`:
- `roth_3ap_theorem`: Dense subsets of finite abelian groups contain 3-APs
- `roth_3ap_theorem_nat`: Dense subsets of {0,...,n-1} contain 3-APs

We show the connection between our definitions and Mathlib's.
-/

/-- Our 3-AP-free definition implies Mathlib's ThreeAPFree -/
theorem isAPFree_three_of_threeAPFree (S : Set ℕ) (h : ThreeAPFree S) : IsAPFree S 3 := by
  intro ⟨a, d, hd, hap⟩
  -- We have a 3-AP: a, a+d, a+2d all in S
  have h0 : a ∈ S := by simpa using hap 0 (by omega)
  have h1 : a + d ∈ S := by simpa using hap 1 (by omega)
  have h2 : a + 2 * d ∈ S := by simpa using hap 2 (by omega)
  -- ThreeAPFree signature: (x_mem, y_mem, z_mem, x + z = y + y) → x = y
  -- For our 3-AP: first=a, middle=a+d, last=a+2d
  -- We need: a + (a+2d) = (a+d) + (a+d), and this implies a = a+d
  have heq : a + (a + 2 * d) = (a + d) + (a + d) := by ring
  -- Apply ThreeAPFree: h h0 h1 h2 gives us a = a+d from the equation
  have := h h0 h1 h2 heq
  -- But a = a+d with d > 0 is a contradiction
  omega

/-- Our definition HasAPOfLength 3 implies NOT ThreeAPFree -/
theorem not_threeAPFree_of_hasAP (S : Set ℕ) (h : HasAPOfLength S 3) : ¬ ThreeAPFree S := by
  intro hfree
  exact isAPFree_three_of_threeAPFree S hfree h

/-- Roth's theorem (k=3 case): Dense subsets contain 3-APs -/
def RothTheorem : Prop :=
  ∀ (δ : ℝ), δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S 3

/-- Connection: Roth's theorem is the k=3 special case of Szemerédi -/
theorem roth_from_szemeredi (hsz : SzemerediTheorem) : RothTheorem := by
  intro δ hδ
  exact hsz 3 δ (by omega) hδ

/-- Alternative formulation: large subsets of [n] are NOT 3-AP-free -/
theorem roth_theorem_contrapositive (hroth : RothTheorem) :
    ∀ (δ : ℝ), δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
          ¬ IsAPFree (S : Set ℕ) 3 := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := hroth δ hδ
  use N₀
  intro N hN S hS hcard hfree
  exact hfree (hN₀ N hN S hS hcard)

/-!
## Mathlib's Roth Theorem (k=3 Case)

**BREAKTHROUGH**: Mathlib actually contains a complete proof of Roth's theorem!

The chain is:
  Regularity Lemma → Triangle Removal → Corners Theorem → Roth's Theorem

Key theorems in `Mathlib.Combinatorics.Additive.Corner.Roth`:
- `corners_theorem`: For any ε > 0 and sufficiently large |G|, any corner-free
  subset of G × G has density < ε
- `roth_3ap_theorem`: For any ε > 0 and sufficiently large |G|, any 3AP-free
  subset of G has density < ε
- `roth_3ap_theorem_nat`: Same for subsets of {0, ..., n-1}

The bound depends on `cornersTheoremBound`, which uses `SzemerediRegularity.bound`
(a tower-type exponential, making the bound tiny in practice).

## What's Still Missing for Full Szemerédi

For k ≥ 4, we would need:
- Hypergraph regularity lemma (Rödl-Skokan, Gowers) - NOT in Mathlib
- Or: Furstenberg's ergodic theory approach - NOT in Mathlib

The k=3 case (Roth) is complete in Mathlib; k≥4 remains open.
-/

/-- Connection between ThreeAPFree and our IsAPFree for ℕ -/
theorem threeAPFree_iff_isAPFree (S : Set ℕ) : ThreeAPFree S ↔ IsAPFree S 3 := by
  constructor
  · exact isAPFree_three_of_threeAPFree S
  · -- IsAPFree S 3 → ThreeAPFree S
    -- ThreeAPFree: ∀ a b c ∈ S, a + c = b + b → a = b
    intro hfree a ha b hb c hc hab
    -- We need to show a = b
    by_contra hne
    -- If a ≠ b with a + c = 2b, then we have a 3-AP: (a, b, c) or (c, b, a)
    apply hfree
    -- From a + c = 2b: either a < b < c or c < b < a
    by_cases hab' : a < b
    · -- a < b case: b - a > 0 is the common difference
      have _ : b < c := by omega  -- b is strictly between a and c
      have hdiff : b - a = c - b := by omega
      use a, b - a
      refine ⟨by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa
      · simp only [Nat.one_mul]
        have : a + (b - a) = b := Nat.add_sub_cancel' (Nat.le_of_lt hab')
        rw [this]; exact hb
      · have : a + 2 * (b - a) = c := by omega
        simp only [Set.mem_setOf_eq, this]; exact hc
    · -- b ≤ a case
      push_neg at hab'
      have hba : b < a := Nat.lt_of_le_of_ne hab' (Ne.symm hne)
      have hcb : c < b := by omega
      have hdiff : b - c = a - b := by omega
      use c, b - c
      refine ⟨by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa
      · simp only [Nat.one_mul]
        have : c + (b - c) = b := Nat.add_sub_cancel' (Nat.le_of_lt hcb)
        rw [this]; exact hb
      · have : c + 2 * (b - c) = a := by omega
        simp only [Set.mem_setOf_eq, this]; exact ha

/-- **Roth's Theorem**: Mathlib's roth_3ap_theorem_nat directly gives us Roth's theorem.

For any δ > 0, there exists N₀ such that any subset of {0,...,N-1} with at least δN
elements contains a 3-term arithmetic progression. -/
theorem roth_theorem_via_mathlib : RothTheorem := by
  intro δ hδ
  use cornersTheoremBound (δ / 3)
  intro N hN S hS hcard
  -- We show S contains a 3-AP by contradiction
  by_contra hnoAP
  -- Convert to ThreeAPFree
  rw [hasAPOfLengthFinset] at hnoAP
  have hfree : ThreeAPFree (S : Set ℕ) := (threeAPFree_iff_isAPFree S).mpr hnoAP
  -- Apply Mathlib's Roth theorem
  exact roth_3ap_theorem_nat δ hδ hN S hS hcard hfree

end Szemeredi
