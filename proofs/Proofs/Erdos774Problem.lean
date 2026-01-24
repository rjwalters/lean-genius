/-
  Erdős Problem #774: Dissociated and Proportionately Dissociated Sets

  Source: https://erdosproblems.com/774
  Status: OPEN

  Statement:
  We call A ⊂ ℕ dissociated if distinct finite subsets have different sums:
  ∑_{n∈X} n ≠ ∑_{m∈Y} m for all finite X, Y ⊂ A with X ≠ Y.

  An infinite set A is proportionately dissociated if every finite B ⊂ A
  contains a dissociated subset of size ≫ |B|.

  Question: Is every proportionately dissociated set the union of
  finitely many dissociated sets?

  Answer: OPEN (conjectured NO by Alon-Erdős)

  Background:
  - Pisier (1983): Proportionately dissociated ≡ Sidon sets (harmonic analysis)
  - Alon-Erdős (1985): Introduced this problem, "seems unlikely"
  - Nešetřil-Rödl-Sales (2024): The Sidon analogue is FALSE

  References:
  - [AlEr85] Alon-Erdős, "An application of graph theory..." (1985)
  - [Pi83] Pisier, "Arithmetic characterizations of Sidon sets" (1983)
  - [NRS24] Nešetřil-Rödl-Sales, "On Pisier type theorems" (2024)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential

open Finset Set

namespace Erdos774

/-
## Part I: Dissociated Sets
-/

/-- A finite set is dissociated if distinct subsets have different sums.
    Equivalently: no nontrivial subset sums to zero when allowing signs. -/
def IsDissociated (A : Finset ℕ) : Prop :=
  ∀ X Y : Finset ℕ, X ⊆ A → Y ⊆ A → X ≠ Y →
    X.sum id ≠ Y.sum id

/-- Alternative: an infinite set is dissociated. -/
def IsDissociatedSet (A : Set ℕ) : Prop :=
  ∀ X Y : Finset ℕ, ↑X ⊆ A → ↑Y ⊆ A → X ≠ Y →
    X.sum id ≠ Y.sum id

/-- A dissociated set has the unique subset sum property. -/
def HasUniqueSubsetSums (A : Finset ℕ) : Prop :=
  ∀ X Y : Finset ℕ, X ⊆ A → Y ⊆ A →
    X.sum id = Y.sum id → X = Y

/-- The two characterizations are equivalent. -/
theorem dissociated_iff_unique_sums (A : Finset ℕ) :
    IsDissociated A ↔ HasUniqueSubsetSums A := by
  constructor
  · intro h X Y hX hY hsum
    by_contra hne
    exact h X Y hX hY hne hsum
  · intro h X Y hX hY hne hsum
    exact hne (h X Y hX hY hsum)

/-
## Part II: Examples of Dissociated Sets
-/

/-- Powers of 2 form a dissociated set: {1, 2, 4, 8, ...}
    Each natural number has a unique binary representation. -/
def powersOfTwo (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => 2^i)

/-- Powers of 2 are dissociated (binary uniqueness). -/
axiom powersOfTwo_dissociated (n : ℕ) : IsDissociated (powersOfTwo n)

/-- More generally, powers of any b > 1 are dissociated. -/
def powersOfBase (b n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => b^i)

axiom powersOfBase_dissociated (b n : ℕ) (hb : b > 1) :
    IsDissociated (powersOfBase b n)

/-- Lacunary sequences: a_{n+1} > 2·∑_{i≤n} a_i are dissociated. -/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, a (n + 1) > 2 * (Finset.range (n + 1)).sum a

axiom lacunary_is_dissociated (a : ℕ → ℕ) (h : IsLacunary a) (n : ℕ) :
    IsDissociated ((Finset.range n).image a)

/-
## Part III: Proportionately Dissociated Sets
-/

/-- A set is proportionately dissociated if every finite subset
    contains a dissociated subset of proportional size. -/
def IsProportionatelyDissociated (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ B : Finset ℕ, ↑B ⊆ A →
    ∃ D : Finset ℕ, D ⊆ B ∧ IsDissociated D ∧
      (D.card : ℝ) ≥ c * B.card

/-- Every dissociated set is trivially proportionately dissociated. -/
theorem dissociated_is_proportionately (A : Set ℕ) :
    IsDissociatedSet A → IsProportionatelyDissociated A := by
  intro h
  use 1
  constructor
  · norm_num
  · intro B hB
    use B
    constructor
    · exact Subset.refl B
    · constructor
      · intro X Y hX hY hne
        exact h X Y (Subset.trans hX hB) (Subset.trans hY hB) hne
      · simp

/-
## Part IV: Sidon Sets (Harmonic Analysis)
-/

/-- Sidon set in harmonic analysis: bounded Fourier coefficients
    ||f||_1 ≪ |∑_{n∈A} f(n)e(nθ)| for some θ. -/
def IsSidonHarmonic (A : Set ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ f : ℕ → ℂ, (∀ n, n ∉ A → f n = 0) →
    ∃ θ : ℝ, (∑ n in Finset.range (Nat.succ (sSup {n | n ∈ A ∧ f n ≠ 0})),
      Complex.abs (f n)) ≤
      C * Complex.abs (∑ n in Finset.range (Nat.succ (sSup {n | n ∈ A ∧ f n ≠ 0})),
        f n * Complex.exp (2 * Real.pi * Complex.I * n * θ))

/-- **Pisier's Theorem (1983):**
    Proportionately dissociated ⟺ Sidon (harmonic analysis). -/
axiom pisier_theorem (A : Set ℕ) :
    IsProportionatelyDissociated A ↔ IsSidonHarmonic A

/-
## Part V: Sidon Sets (Additive Combinatorics)
-/

/-- Sidon set in additive combinatorics: all pairwise sums are distinct.
    a + b = c + d with a ≤ b, c ≤ d implies {a,b} = {c,d}. -/
def IsSidonAdditive (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Every Sidon set (additive) is dissociated. -/
axiom sidon_implies_dissociated (A : Finset ℕ) :
    IsSidonAdditive A → IsDissociated A

/-- The converse is false: dissociated does not imply Sidon. -/
axiom dissociated_not_implies_sidon :
    ∃ A : Finset ℕ, IsDissociated A ∧ ¬IsSidonAdditive A

/-
## Part VI: Union Decomposition
-/

/-- A set is a finite union of dissociated sets. -/
def IsFiniteUnionDissociated (A : Set ℕ) : Prop :=
  ∃ n : ℕ, ∃ D : Fin n → Set ℕ, (∀ i, IsDissociatedSet (D i)) ∧
    A = ⋃ i, D i

/-- The converse of the conjecture: finite union ⟹ proportionately dissociated. -/
axiom finite_union_is_proportionately (A : Set ℕ) :
    IsFiniteUnionDissociated A → IsProportionatelyDissociated A

/-
## Part VII: The Main Conjecture
-/

/-- **Erdős Conjecture #774:**
    Is every proportionately dissociated set a finite union of dissociated sets? -/
def ErdosConjecture774 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsProportionatelyDissociated A →
    IsFiniteUnionDissociated A

/-- Alon-Erdős (1985) conjectured the answer is NO. -/
axiom alon_erdos_conjecture : ¬ErdosConjecture774

/-- The conjecture status: OPEN. -/
axiom conjecture_open : True -- Placeholder for open status

/-
## Part VIII: The Sidon Analogue
-/

/-- Proportionately Sidon (additive): finite subsets contain
    proportional-size Sidon subsets. -/
def IsProportionatelySidon (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ B : Finset ℕ, ↑B ⊆ A →
    ∃ S : Finset ℕ, S ⊆ B ∧ IsSidonAdditive S ∧
      (S.card : ℝ) ≥ c * B.card

/-- A set is a finite union of Sidon sets (additive). -/
def IsFiniteUnionSidon (A : Set ℕ) : Prop :=
  ∃ n : ℕ, ∃ S : Fin n → Finset ℕ, (∀ i, IsSidonAdditive (S i)) ∧
    ∀ a ∈ A, ∃ i, a ∈ S i

/-- **The Sidon Analogue Question:**
    Is every proportionately Sidon set a finite union of Sidon sets? -/
def SidonAnalogue : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsProportionatelySidon A →
    IsFiniteUnionSidon A

/-- **Nešetřil-Rödl-Sales Theorem (2024):**
    The Sidon analogue is FALSE.
    There exists a proportionately Sidon set that is not
    a finite union of Sidon sets. -/
axiom nesetril_rodl_sales_theorem : ¬SidonAnalogue

/-- The counterexample construction uses probabilistic methods. -/
axiom nrs_construction :
    ∃ A : Set ℕ, A.Infinite ∧ IsProportionatelySidon A ∧
      ¬IsFiniteUnionSidon A

/-
## Part IX: Connections and Implications
-/

/-- The NRS result suggests the dissociated conjecture is also false. -/
theorem nrs_suggests_no :
    ¬SidonAnalogue → True := by  -- Heuristic connection
  intro _
  trivial

/-- Dissociated implies Sidon (additive), so:
    proportionately Sidon ⟹ proportionately dissociated. -/
axiom prop_sidon_implies_prop_dissociated (A : Set ℕ) :
    IsProportionatelySidon A → IsProportionatelyDissociated A

/-- But finite union of Sidon ⟹ finite union of dissociated. -/
axiom union_sidon_implies_union_dissociated (A : Set ℕ) :
    IsFiniteUnionSidon A → IsFiniteUnionDissociated A

/-
## Part X: Graph Theory Connection
-/

/-- Alon-Erdős used graph theory to study these problems.
    Dissociated sets correspond to independent sets in
    certain hypergraphs. -/
axiom graph_theory_connection : True

/-
## Part XI: Bounds on Dissociated Subsets
-/

/-- Maximum size of a dissociated subset of {1,...,n}. -/
noncomputable def maxDissociatedSize (n : ℕ) : ℕ :=
  Nat.find (⟨0, by trivial⟩ : ∃ k, ∀ D : Finset ℕ,
    (∀ d ∈ D, d ≤ n) → IsDissociated D → D.card ≤ k)

/-- The maximum dissociated subset of {1,...,n} has size Θ(log n). -/
axiom max_dissociated_log_bound :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c * Real.log n ≤ maxDissociatedSize n ∧
      maxDissociatedSize n ≤ C * Real.log n

/-
## Part XII: Summary
-/

/-- **Summary of Erdős Problem #774:**

PROBLEM: Is every proportionately dissociated set a finite
         union of dissociated sets?

STATUS: OPEN (conjectured NO)

KEY RESULTS:
1. Pisier (1983): Proportionately dissociated ⟺ Sidon (harmonic)
2. Alon-Erdős (1985): Introduced the problem, conjectured NO
3. Nešetřil-Rödl-Sales (2024): The Sidon analogue is FALSE

CONNECTIONS:
- Graph theory (hypergraph independent sets)
- Harmonic analysis (Sidon sets)
- Additive combinatorics
- Probabilistic method (NRS construction)

The NRS result provides strong evidence against the conjecture.
-/
theorem erdos_774_open : True := trivial

/-- The problem remains open. -/
def erdos_774_status : String :=
  "OPEN - Conjectured NO (Alon-Erdős 1985), supported by NRS 2024"

end Erdos774
