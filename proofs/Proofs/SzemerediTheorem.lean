/-
# Szemerédi's Theorem

Every subset of natural numbers with positive upper density contains
arbitrarily long arithmetic progressions.

**Status**: Full theorem proved by cases (axiom reduced to k≥4 only)
- General k-AP definition and formal statement
- Trivial cases k=1,2 proved (including density versions)
- k=3 (Roth's theorem): PROVED using Mathlib's corner theorem chain
- Equivalence between our IsAPFree and Mathlib's ThreeAPFree
- k≥4: Axiomatized (requires hypergraph regularity, not in Mathlib)
- Full SzemerediTheorem assembled from k=1,2,3 proofs + k≥4 axiom

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
## Axiom Reduction

The full Szemerédi theorem holds for all k ≥ 1:
- k=1: Trivial (any nonempty set has a 1-AP)
- k=2: Trivial (any set with ≥2 elements has a 2-AP)
- k=3: Roth's theorem (proved in Mathlib via corners chain)
- k≥4: Requires hypergraph regularity (NOT in Mathlib)

We axiomatize ONLY k ≥ 4 and prove the full theorem by combining all cases.
-/

/-- Szemerédi's theorem for k ≥ 4 (axiom — requires hypergraph regularity, not in Mathlib) -/
axiom szemeredi_k_ge_4 : ∀ (k : ℕ) (δ : ℝ), k ≥ 4 → δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S k

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

/-!
## Full Theorem (Proved by Cases)

We assemble the full Szemerédi theorem from:
- k=1: `szemeredi_k1` (trivial)
- k=2: `szemeredi_k2` (trivial)
- k=3: `roth_theorem_via_mathlib` (Mathlib's corners chain)
- k≥4: `szemeredi_k_ge_4` (axiom)
-/

/-- k=1 density version: any δ-dense subset of [N] has a 1-AP -/
theorem szemeredi_k1_density (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S 1 := by
  use 1
  intro N hN S _ hcard
  have hN_pos : (0 : ℝ) < ↑N := by exact_mod_cast (show 0 < N by omega)
  have hcard_pos : 0 < S.card := by
    by_contra h
    push_neg at h
    have : S.card = 0 := Nat.le_zero.mp h
    rw [this, Nat.cast_zero] at hcard
    linarith [mul_pos hδ hN_pos]
  exact szemeredi_k1 (↑S) (Finset.coe_nonempty.mpr (Finset.card_pos.mp hcard_pos))

/-- k=2 density version: any δ-dense subset of [N] has a 2-AP -/
theorem szemeredi_k2_density (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S 2 := by
  use ⌈2 / δ⌉₊
  intro N hN S _ hcard
  have hN_ge : (N : ℝ) ≥ 2 / δ := by
    calc (N : ℝ) ≥ (⌈2 / δ⌉₊ : ℝ) := by exact_mod_cast hN
    _ ≥ 2 / δ := Nat.le_ceil (2 / δ)
  have h2 : S.card ≥ 2 := by
    suffices h : (2 : ℝ) ≤ (S.card : ℝ) by exact_mod_cast h
    calc (2 : ℝ) = δ * (2 / δ) := by field_simp
    _ ≤ δ * ↑N := by nlinarith
    _ ≤ ↑S.card := hcard
  exact szemeredi_k2 S h2

/-- **Szemerédi's Theorem** (proved by cases).
The full theorem, with only k ≥ 4 axiomatized.
k=1,2 are trivial, k=3 is Roth via Mathlib. -/
theorem szemeredi_theorem : SzemerediTheorem := by
  intro k δ hk hδ
  rcases Nat.lt_or_ge k 4 with hlt | hge
  · -- k ∈ {1, 2, 3}
    interval_cases k
    · exact szemeredi_k1_density δ hδ
    · exact szemeredi_k2_density δ hδ
    · exact roth_theorem_via_mathlib δ hδ
  · exact szemeredi_k_ge_4 k δ hge hδ

/-- Corollary: every dense set contains arbitrarily long APs -/
theorem dense_set_has_long_ap (k : ℕ) (δ : ℝ) (hk : k ≥ 1) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S k :=
  szemeredi_theorem k δ hk hδ

/-!
## Monotonicity and Transfer Lemmas

These infrastructure lemmas support downstream formalizations (Erdős problems,
Van der Waerden, etc.) that build on the AP definitions and Szemerédi's theorem.
-/

/-- AP monotonicity: a k-AP contains a j-AP for any j ≤ k -/
theorem hasAP_mono {S : Set ℕ} {j k : ℕ} (hjk : j ≤ k)
    (h : HasAPOfLength S k) : HasAPOfLength S j := by
  obtain ⟨a, d, hd, hap⟩ := h
  exact ⟨a, d, hd, fun i hi => hap i (lt_of_lt_of_le hi hjk)⟩

/-- AP superset transfer: APs are preserved by taking supersets -/
theorem hasAP_superset {S T : Set ℕ} {k : ℕ} (hST : S ⊆ T)
    (h : HasAPOfLength S k) : HasAPOfLength T k := by
  obtain ⟨a, d, hd, hap⟩ := h
  exact ⟨a, d, hd, fun i hi => hST (hap i hi)⟩

/-- Szemerédi is monotone in k: the threshold N₀ for k-APs also gives j-APs (j ≤ k) -/
theorem szemeredi_mono {j k : ℕ} (hjk : j ≤ k) (hj : j ≥ 1) (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → (S.card : ℝ) ≥ δ * N →
        hasAPOfLengthFinset S j := by
  obtain ⟨N₀, hN₀⟩ := szemeredi_theorem k δ (by omega) hδ
  exact ⟨N₀, fun N hN S hS hcard => hasAP_mono hjk (hN₀ N hN S hS hcard)⟩

/-- Contrapositive of Szemerédi: k-AP-free subsets of [N] have vanishing density.
    For any δ > 0, sufficiently large k-AP-free subsets have density < δ. -/
theorem ap_free_density_bound (k : ℕ) (hk : k ≥ 1) (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → IsAPFree (↑S) k →
        (S.card : ℝ) < δ * N := by
  obtain ⟨N₀, hN₀⟩ := szemeredi_theorem k δ hk hδ
  exact ⟨N₀, fun N hN S hS hfree => by
    by_contra h
    push_neg at h
    exact hfree (hN₀ N hN S hS h)⟩

end Szemeredi
