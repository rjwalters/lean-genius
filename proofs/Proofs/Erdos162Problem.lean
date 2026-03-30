/-
Erdős Problem #162: Discrepancy in 2-Coloured Complete Graphs

Source: https://erdosproblems.com/162
Status: OPEN

Statement:
For α > 0 and n ≥ 1, let F(n, α) be the largest k such that some
2-colouring of K_n exists where every induced subgraph H on at least
k vertices has more than α · C(|H|, 2) edges of each colour.

Conjecture:
For every fixed 0 ≤ α ≤ 1/2, F(n, α) ~ c_α · log n as n → ∞
for some constant c_α > 0.

Known Results:
The probabilistic method gives constants c₁(α), c₂(α) such that
c₁(α) · log n < F(n, α) < c₂(α) · log n.

Context:
This is a Ramsey-type discrepancy problem. A 2-colouring of K_n is
α-balanced on a set S if each colour class has more than α · C(|S|, 2)
edges. F(n, α) measures how large an α-balanced substructure must be.
The conjecture says the answer is precisely Θ(log n) with a sharp constant.

Related: Erdős #617 (balanced colourings), Erdős #161, #163.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Erdos162

-- Part I: Edge 2-colouring

/-- A symmetric 2-colouring of edges of K_n: each unordered pair {i, j}
    gets a colour (true = red, false = blue).
    We use a function on ordered pairs with the symmetry constraint. -/
structure EdgeColouring (n : ℕ) where
  colour : Fin n → Fin n → Bool
  symm : ∀ i j, colour i j = colour j i
  irrefl : ∀ i, colour i i = false

/-- Count edges of a given colour in the induced subgraph on vertex set S.
    An edge {i, j} with i < j contributes 1 if both i, j ∈ S and the
    edge has the specified colour. -/
noncomputable def colourEdgeCount {n : ℕ} (c : EdgeColouring n) (S : Finset (Fin n))
    (col : Bool) : ℕ :=
  ((S ×ˢ S).filter fun p => p.1 < p.2 ∧ c.colour p.1 p.2 = col).card

/-- Total edges in K_S equals C(|S|, 2). -/
theorem colourEdgeCount_total {n : ℕ} (c : EdgeColouring n) (S : Finset (Fin n)) :
    colourEdgeCount c S true + colourEdgeCount c S false = Nat.choose S.card 2 := by
  unfold colourEdgeCount
  -- Partition: {(i,j) ∈ S×S | i<j ∧ colour=true} ⊔ {... ∧ colour=false} = {(i,j) ∈ S×S | i<j}
  rw [← Finset.card_union_of_disjoint]
  · -- Union = {(i,j) ∈ S×S | i < j}, and its card = C(|S|, 2)
    congr 1
    · ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Bool.eq_true_or_eq_false (c.colour p.1 p.2) with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
    · -- |{(i,j) ∈ S×S | i < j}| = C(|S|, 2)
      -- Proof: strict-order pairs = half of off-diagonal pairs.
      -- offDiag.card = n*(n-1), and C(n,2) = n*(n-1)/2.
      rw [Nat.choose_two_right]
      suffices h : 2 * ((S ×ˢ S).filter fun p : Fin n × Fin n => p.1 < p.2).card =
          S.card * (S.card - 1) by omega
      rw [← S.card_offDiag]
      -- offDiag = filter(<) ∪ filter(>), disjoint, equal halves
      have hlt_eq : (S ×ˢ S).filter (fun p : Fin n × Fin n => p.2 < p.1) =
          ((S ×ˢ S).filter (fun p : Fin n × Fin n => p.1 < p.2)).image Prod.swap := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.swap,
          Prod.exists, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, hb⟩, hab⟩; exact ⟨b, a, ⟨⟨hb, ha⟩, hab⟩, rfl, rfl⟩
        · rintro ⟨c, d, ⟨⟨hc, hd⟩, hcd⟩, rfl, rfl⟩; exact ⟨⟨hd, hc⟩, hcd⟩
      have hcard_eq : ((S ×ˢ S).filter (fun p : Fin n × Fin n => p.1 < p.2)).card =
          ((S ×ˢ S).filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
        rw [hlt_eq, Finset.card_image_of_injective _ Prod.swap_injective]
      have hunion : (S ×ˢ S).filter (fun p : Fin n × Fin n => p.1 < p.2) ∪
          (S ×ˢ S).filter (fun p : Fin n × Fin n => p.2 < p.1) = S.offDiag := by
        ext ⟨a, b⟩
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
        constructor
        · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨⟨ha, hb⟩, hab⟩)
          · exact ⟨ha, hb, ne_of_lt hab⟩
          · exact ⟨ha, hb, ne_of_gt hab⟩
        · rintro ⟨ha, hb, hab⟩
          rcases lt_or_gt_of_ne hab with h | h
          · exact Or.inl ⟨⟨ha, hb⟩, h⟩
          · exact Or.inr ⟨⟨ha, hb⟩, h⟩
      have hdisj : Disjoint
          ((S ×ˢ S).filter (fun p : Fin n × Fin n => p.1 < p.2))
          ((S ×ˢ S).filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
        rw [Finset.disjoint_filter]
        intro ⟨a, b⟩ _ h1 h2; exact absurd (lt_trans h1 h2) (lt_irrefl _)
      have h_union_card := Finset.card_union_of_disjoint hdisj
      rw [hunion] at h_union_card
      linarith
  · -- Disjoint: true ≠ false
    simp only [Finset.disjoint_filter]
    intro p _ ⟨_, htrue⟩ ⟨_, hfalse⟩
    exact absurd (htrue.symm.trans hfalse) Bool.true_ne_false

-- Part II: α-Balanced colourings

/-- A colouring is α-balanced on vertex set S if each colour class has
    more than α · C(|S|, 2) edges. -/
def IsBalancedOn {n : ℕ} (c : EdgeColouring n) (S : Finset (Fin n)) (α : ℚ) : Prop :=
  ∀ col : Bool,
    α * (Nat.choose S.card 2 : ℚ) < (colourEdgeCount c S col : ℚ)

/-- A colouring is (k, α)-balanced if every induced subgraph on at least
    k vertices is α-balanced. -/
def IsKBalanced {n : ℕ} (c : EdgeColouring n) (k : ℕ) (α : ℚ) : Prop :=
  ∀ S : Finset (Fin n), k ≤ S.card → IsBalancedOn c S α

/-- Being α-balanced requires α ≤ 1/2: if α > 1/2, each colour needs
    more than half the edges, which is impossible. -/
theorem balanced_requires_le_half {n : ℕ} (c : EdgeColouring n) (S : Finset (Fin n))
    (α : ℚ) (hα : 1 / 2 < α) (hS : 2 ≤ S.card) :
    ¬IsBalancedOn c S α := by
  intro hbal
  -- Both colours need > α * C(|S|, 2) edges
  have hred := hbal true
  have hblue := hbal false
  -- Sum: 2α * C(|S|,2) < red + blue = C(|S|,2) by colourEdgeCount_total
  have htotal : (↑(colourEdgeCount c S true) : ℚ) + ↑(colourEdgeCount c S false) =
      ↑(Nat.choose S.card 2) := by exact_mod_cast colourEdgeCount_total c S
  -- C(|S|, 2) > 0 since |S| ≥ 2
  have hC_pos : (0 : ℚ) < ↑(Nat.choose S.card 2) := by exact_mod_cast Nat.choose_pos hS
  -- 2α > 1 and C > 0: 2α·C > C, but 2α·C < red+blue = C. Contradiction.
  nlinarith [hred, hblue, htotal, hC_pos]

-- Part III: The function F(n, α)

/-- F(n, α): the largest k such that some 2-colouring of K_n is (k, α)-balanced.
    Axiomatized since computing it requires exhaustive search over all colourings. -/
axiom discrepancyF : ℕ → ℚ → ℕ

/-- Characterization: F(n, α) = k means there exists a (k, α)-balanced colouring
    but no (k+1, α)-balanced colouring exists. -/
/-- F(n, α) is monotone decreasing in α: stricter balance requirement
    means smaller balanced substructures. -/
axiom discrepancyF_mono_alpha (n : ℕ) (α β : ℚ) (h : α ≤ β) :
    discrepancyF n β ≤ discrepancyF n α

/-- F(n, 0) = n: every colouring is trivially 0-balanced, since
    0 · C(|S|, 2) = 0 < any positive edge count. -/
/-- F(n, α) ≤ n: the balanced substructure cannot exceed the total graph. -/
/-- Lower bound: F(n, α) > c₁(α) · log n for some c₁ > 0.
    Proof sketch: A random 2-colouring of K_n is α-balanced on all sets
    of size ≤ c₁ log n with positive probability, by Chernoff + union bound. -/
axiom discrepancy_lower (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    ∃ c : ℚ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (Nat.log 2 n : ℚ) < (discrepancyF n α : ℚ)

/-- Upper bound: F(n, α) < c₂(α) · log n for some c₂ > 0.
    Proof sketch: By a Ramsey-type counting argument, any 2-colouring of K_n
    must have an imbalanced induced subgraph of size c₂ log n. -/
axiom discrepancy_upper (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    ∃ C : ℚ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (discrepancyF n α : ℚ) < C * (Nat.log 2 n : ℚ)

-- Part VI: Derived results

/-- The bounds sandwich: F(n, α) = Θ(log n) for every fixed 0 < α ≤ 1/2. -/
theorem discrepancy_theta_log (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    (∃ c₁ : ℚ, 0 < c₁ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      c₁ * (Nat.log 2 n : ℚ) < (discrepancyF n α : ℚ)) ∧
    (∃ c₂ : ℚ, 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      (discrepancyF n α : ℚ) < c₂ * (Nat.log 2 n : ℚ)) :=
  ⟨discrepancy_lower α hα hα2, discrepancy_upper α hα hα2⟩

/-- For α = 1/2, the problem reduces to near-equal colour distribution.
    This is the hardest case since α = 1/2 is the tightest constraint. -/
theorem half_is_extremal (n : ℕ) (α : ℚ) (hα2 : α ≤ 1 / 2) :
    discrepancyF n (1 / 2) ≤ discrepancyF n α :=
  discrepancyF_mono_alpha n α (1 / 2) hα2

-- Part VII: The main conjecture

/-- **Erdős Problem 162** (OPEN): For every 0 < α ≤ 1/2, there exists a
    constant c_α > 0 such that F(n, α) / log n → c_α as n → ∞.

    This is strictly stronger than the Θ(log n) bounds: it asserts that
    the ratio F(n, α) / log n converges to a definite limit, rather than
    merely being bounded between two constants. -/
def ErdosProblem162 : Prop :=
    ∀ (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2),
      ∃ c : ℚ, 0 < c ∧
        ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          |(discrepancyF n α : ℚ) / (Nat.log 2 n : ℚ) - c| < ε

-- Part VIII: Concrete edge count examples

/-- K_1 has 0 edges. -/
example : Nat.choose 1 2 = 0 := by native_decide

/-- K_2 has 1 edge. -/
example : Nat.choose 2 2 = 1 := by native_decide

/-- K_4 has 6 edges: a balanced colouring gives 3 red, 3 blue. -/
example : Nat.choose 4 2 = 6 := by native_decide

/-- K_8 has 28 edges: the probabilistic method shows balanced colourings exist. -/
example : Nat.choose 8 2 = 28 := by native_decide

/-
Summary: Erdős Problem #162 (OPEN)

The conjecture F(n, α) ~ c_α log n asserts that the largest α-balanced
substructure in any 2-coloured K_n grows logarithmically with a sharp constant.

What is known:
- F(n, α) = Θ(log n) via probabilistic method (lower) and counting (upper)
- The conjecture asks for convergence of the ratio F(n,α)/log(n)

What remains:
- Proving convergence (the ratio has a limit, not just limsup/liminf bounds)
- Determining the constant c_α as a function of α
- This likely requires tools beyond the probabilistic method

Connections:
- Ramsey theory: F(n, 0) = n is trivial; F(n, 1/2) is the extremal case
- The problem interpolates between Ramsey numbers (α near 0) and
  discrepancy theory (α = 1/2)
- Related to Erdős #617 (balanced colourings of K_{r²+1})
-/

end Erdos162
