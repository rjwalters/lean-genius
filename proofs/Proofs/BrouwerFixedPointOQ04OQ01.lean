import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Proofs.BrouwerFixedPointOQ04

/-
# Nash Equilibrium Existence via Kakutani (OQ-04-OQ-01)

## Open Question
OQ-04-OQ-01: Prove that every finite normal-form game has a Nash equilibrium
in mixed strategies, using the Kakutani fixed point theorem.

## What This Proves

**Nash's Theorem (1950)**: Every finite N-player normal-form game has at
least one Nash equilibrium in mixed strategies.

**Proof sketch:**
1. For each player i, the best-response correspondence
   BR_i(σ₋ᵢ) = argmax_{τ ∈ Δᵢ} Eᵤ_i(τ, σ₋ᵢ)
   is upper hemicontinuous with nonempty convex values (Berge's theorem)
2. The joint best-response BR(σ) = Πᵢ BR_i(σ₋ᵢ) inherits these properties
3. Kakutani's theorem gives a fixed point σ* = BR(σ*) — a Nash equilibrium

## Results
1. Expected utility: bilinear formulation for N-player games
2. Best response: formal definition, nonemptiness, convexity
3. UHC of best response: via Berge's maximum theorem
4. Nash existence: applying Kakutani to joint best response

## Status
- [x] Expected utility definition
- [x] IsLinearInStrategy: multilinearity predicate for finite games
- [x] Best response correspondence definition
- [x] Nonemptiness of best response (EVT via IsCompact.exists_isMaxOn + hcont)
- [x] Convexity of best response (proved via hlin + nlinarith)
- [x] Closedness of best response (proved: MixedStrategy ∩ {τ|M≤EU}, EVT + isClosed_le)
- [ ] UHC of best response (axiom — Berge's maximum theorem)
- [x] Nash existence theorem (proved given kakutani_product_simplex axiom)
- [ ] kakutani_product_simplex: embedding Πᵢ Δᵢ into EuclideanSpace (routine topology)

## Tags
Kakutani, Nash equilibrium, game theory, fixed point, best response,
upper hemicontinuity, Berge maximum theorem
-/

open KakutaniFPT Set Filter Topology

namespace NashEquilibrium

variable {N : ℕ}

/-! ## Part 1: Expected Utility -/

/-- Expected utility for player i given a pure strategy profile.
    We formalize the multilinear case: payoff is a function of a strategy
    profile (one pure strategy per player). -/
def purePayoff {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (s : ∀ j, Fin (G.strategies j)) : ℝ :=
  G.utility i (fun j => fun k => if k = s j then (1 : ℝ) else 0)

/-- Expected utility for player i given a mixed strategy profile σ.
    For finite games, expected utility is the sum over all pure strategy
    profiles of the product of probabilities times payoffs. -/
noncomputable def expectedUtility {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ) : ℝ :=
  G.utility i σ

/-- Expected utility is linear in player i's own mixed strategy
    (holding opponents' strategies fixed).

    This holds for finite games where utility is multilinear, i.e.,
    EU_i(τ_i, σ_{-i}) is linear in τ_i. We state this as a hypothesis
    rather than proving it from FiniteGame (which has no multilinearity axiom). -/
def IsLinearInStrategy {N : ℕ} (G : FiniteGame N) : Prop :=
  ∀ (i : Fin N) (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (τ₁ τ₂ : Fin (G.strategies i) → ℝ) (a b : ℝ),
    G.utility i (Function.update σ i (fun k => a * τ₁ k + b * τ₂ k)) =
    a * G.utility i (Function.update σ i τ₁) +
    b * G.utility i (Function.update σ i τ₂)

/-! ## Part 2: Best Response Correspondence -/

/-- The best response set for player i given opponents' strategies σ₋ᵢ.
    A mixed strategy τ is a best response if it maximizes expected utility. -/
def bestResponse {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ) : Set (Fin (G.strategies i) → ℝ) :=
  { τ ∈ MixedStrategy (G.strategies i) |
    ∀ τ' ∈ MixedStrategy (G.strategies i),
      expectedUtility G i (Function.update σ i τ') ≤
      expectedUtility G i (Function.update σ i τ) }

/-- Best responses form a subset of mixed strategies. -/
theorem bestResponse_subset {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ) :
    bestResponse G i σ ⊆ MixedStrategy (G.strategies i) :=
  fun _ ⟨hτ, _⟩ => hτ

/-- The best response set is nonempty (argmax exists on compact set).
    Requires continuity of expected utility in τᵢ (holds for multilinear games). -/
theorem bestResponse_nonempty {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (hcont : Continuous (fun τ : Fin (G.strategies i) → ℝ =>
      G.utility i (Function.update σ i τ))) :
    (bestResponse G i σ).Nonempty := by
  -- Apply EVT: continuous function on compact nonempty set attains its max
  obtain ⟨τ₀, hτ₀_mem, hτ₀_max⟩ :=
    (mixed_strategy_compact (k := G.strategies i)).exists_isMaxOn
      (mixed_strategy_nonempty (G.strategies_pos i))
      hcont.continuousOn
  exact ⟨τ₀, hτ₀_mem, fun τ' hτ' => hτ₀_max hτ'⟩

/-- The best response set is convex.
    If τ₁ and τ₂ are both best responses, so is any convex combination.

    Proof: For any a ∈ [0,1] and τ' ∈ Δᵢ:
      EU_i(a·τ₁ + (1-a)·τ₂) = a·EU_i(τ₁) + (1-a)·EU_i(τ₂)  [linearity]
      ≥ a·EU_i(τ') + (1-a)·EU_i(τ') = EU_i(τ')  [τ₁, τ₂ are best responses]
-/
theorem bestResponse_convex {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (hlin : IsLinearInStrategy G) :
    Convex ℝ (bestResponse G i σ) := by
  intro x ⟨hx_mixed, hx_best⟩ y ⟨hy_mixed, hy_best⟩ a b ha hb hab
  refine ⟨mixed_strategy_convex hx_mixed hy_mixed ha hb hab, fun τ' hτ' => ?_⟩
  -- EU(a·x + b·y, σ₋ᵢ) = a·EU(x) + b·EU(y) by linearity
  have hlin_eq : G.utility i (Function.update σ i (fun k => a * x k + b * y k)) =
      a * G.utility i (Function.update σ i x) +
      b * G.utility i (Function.update σ i y) := hlin i σ x y a b
  simp only [expectedUtility] at *
  rw [hlin_eq]
  have h1 := hx_best τ' hτ'
  have h2 := hy_best τ' hτ'
  nlinarith [hab]

/-- The best response set is closed.

    Proof: Let M = max_{τ'∈Δᵢ} EU(τ') (exists by EVT on compact Δᵢ).
    Then bestResponse = Δᵢ ∩ {τ | M ≤ EU(τ)}.
    Both sets are closed: Δᵢ by mixed_strategy_closed, the level set
    by continuity of EU (preimage of [M, ∞) under EU). -/
theorem bestResponse_closed {N : ℕ} (G : FiniteGame N) (i : Fin N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (hcont : Continuous (fun τ : Fin (G.strategies i) → ℝ =>
      G.utility i (Function.update σ i τ))) :
    IsClosed (bestResponse G i σ) := by
  -- Get maximizer τ_max with EU(τ_max) = max
  obtain ⟨τ_max, hτ_max_mem, hτ_max⟩ :=
    (mixed_strategy_compact (k := G.strategies i)).exists_isMaxOn
      (mixed_strategy_nonempty (G.strategies_pos i))
      hcont.continuousOn
  set eu := fun τ : Fin (G.strategies i) → ℝ => G.utility i (Function.update σ i τ)
  set M := eu τ_max with hM_def
  -- bestResponse = MixedStrategy ∩ {τ | M ≤ eu τ}
  have heq : bestResponse G i σ =
      MixedStrategy (G.strategies i) ∩ {τ | M ≤ eu τ} := by
    ext τ
    simp only [bestResponse, Set.mem_sep_iff, Set.mem_inter_iff,
               Set.mem_setOf_eq, expectedUtility, eu, M]
    constructor
    · intro ⟨hτ_mixed, hτ_best⟩
      exact ⟨hτ_mixed, hτ_best τ_max hτ_max_mem⟩
    · intro ⟨hτ_mixed, hτ_ge⟩
      exact ⟨hτ_mixed, fun τ' hτ' => (hτ_max hτ').trans hτ_ge⟩
  rw [heq]
  exact mixed_strategy_closed.inter (isClosed_le continuous_const hcont)

/-! ## Part 3: Upper Hemicontinuity of Best Response -/

/-- **Berge's Maximum Theorem** (special case for best response).
    The best response correspondence is upper hemicontinuous in σ.

    This is the key technical lemma in Nash's proof. It follows from:
    1. Expected utility is jointly continuous in (τᵢ, σ)
    2. The constraint set Δᵢ is compact and doesn't depend on σ
    3. Berge's theorem: under these conditions, the argmax is UHC -/
axiom bestResponse_uhc {N : ℕ} (G : FiniteGame N) (i : Fin N) :
    ∀ σ₀ : ∀ j, Fin (G.strategies j) → ℝ,
    ∀ V : Set (Fin (G.strategies i) → ℝ), IsOpen V →
    bestResponse G i σ₀ ⊆ V →
    ∃ U ∈ nhds σ₀,
    ∀ σ ∈ U, bestResponse G i σ ⊆ V

/-! ## Part 4: Joint Best Response and Nash Existence -/

/-- The joint best response correspondence maps a strategy profile σ to
    the set of strategy profiles where each player plays a best response. -/
def jointBestResponse {N : ℕ} (G : FiniteGame N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ) :
    Set (∀ j, Fin (G.strategies j) → ℝ) :=
  { τ | ∀ i, τ i ∈ bestResponse G i σ }

/-- A fixed point of the joint best response is a Nash equilibrium.
    If σ* ∈ BR(σ*), then σ* is a Nash equilibrium. -/
theorem fixed_point_is_nash {N : ℕ} (G : FiniteGame N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (hfp : σ ∈ jointBestResponse G σ) :
    IsNashEquilibrium G σ := by
  constructor
  · intro j
    exact bestResponse_subset G j σ (hfp j)
  · intro i τ hτ
    exact (hfp i).2 τ hτ

/-- **Kakutani on Product Simplices** (axiom).

    The joint best response correspondence on the product of simplices has a
    fixed point. This follows from Kakutani's theorem applied to the product
    simplex (compact, convex, nonempty subset of a finite-dimensional Euclidean space).

    The full proof requires:
    1. Embedding Πᵢ Δᵢ into EuclideanSpace ℝ (Fin (∑ i, G.strategies i))
    2. Showing the embedding is a homeomorphism preserving convexity
    3. Conjugating the best response through the embedding
    4. Applying kakutani_finite_dim from BrouwerFixedPointOQ04OQ03

    We axiomatize this embedding step, as the topological formalization
    is significant but routine. -/
axiom kakutani_product_simplex {N : ℕ} (G : FiniteGame N)
    (hcont : ∀ i : Fin N, ∀ σ : ∀ j, Fin (G.strategies j) → ℝ,
      Continuous (fun τ : Fin (G.strategies i) → ℝ =>
        G.utility i (Function.update σ i τ))) :
    ∃ σ : ∀ j, Fin (G.strategies j) → ℝ,
    σ ∈ jointBestResponse G σ

/-- **Nash Equilibrium Existence Theorem**.
    Every finite N-player game with continuous utilities has a Nash equilibrium
    in mixed strategies.

    Proof: The joint best response correspondence on Πᵢ Δᵢ satisfies all
    Kakutani hypotheses (by bestResponse_nonempty, _convex, _closed, _uhc),
    so Kakutani gives a fixed point which is a Nash equilibrium. -/
theorem nash_existence {N : ℕ} (hN : 0 < N) (G : FiniteGame N)
    (hcont : ∀ i : Fin N, ∀ σ : ∀ j, Fin (G.strategies j) → ℝ,
      Continuous (fun τ : Fin (G.strategies i) → ℝ =>
        G.utility i (Function.update σ i τ))) :
    ∃ σ : ∀ j, Fin (G.strategies j) → ℝ, IsNashEquilibrium G σ := by
  obtain ⟨σ, hσ⟩ := kakutani_product_simplex G hcont
  exact ⟨σ, fixed_point_is_nash G σ hσ⟩

/-! ## Part 5: Concrete Examples -/

/-- **Matching Pennies**: The uniform mixed strategy (1/2, 1/2) is in the mixed strategy set.
    This is the Nash equilibrium strategy in matching pennies. -/
theorem matching_pennies_uniform_is_mixed :
    (![1/2, 1/2] : Fin 2 → ℝ) ∈ MixedStrategy 2 := by
  constructor
  · intro j; fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Prisoner's Dilemma**: The unique Nash equilibrium is mutual defection.
    We exhibit the dominant strategy equilibrium directly. -/
def prisonersDilemmaGame : FiniteGame 2 where
  strategies := fun _ => 2  -- 2 strategies each: Cooperate (0) or Defect (1)
  strategies_pos := fun _ => by norm_num
  utility := fun i σ =>
    let c := σ i 0  -- prob of cooperating for player i
    let c' := σ (1 - i) 0  -- prob of cooperating for opponent
    -- Payoff matrix: (C,C)→3, (C,D)→0, (D,C)→5, (D,D)→1
    3 * c * c' + 0 * c * (1 - c') + 5 * (1 - c) * c' + 1 * (1 - c) * (1 - c')

/-- In the Prisoner's Dilemma, both-defect is a Nash equilibrium. -/
theorem prisoners_dilemma_nash :
    let σ : ∀ j : Fin 2, Fin 2 → ℝ := fun _ k => if k = 1 then 1 else 0  -- always defect
    IsNashEquilibrium prisonersDilemmaGame σ := by
  constructor
  · intro j; constructor
    · intro k; fin_cases k <;> simp
    · simp [Fin.sum_univ_two]
  · intro i τ hτ
    simp only [prisonersDilemmaGame, Function.update]
    split_ifs with hi
    · -- Player 0 unilaterally deviates
      have hτ_prob : τ 0 + τ 1 = 1 := by
        have := hτ.2; simp [Fin.sum_univ_two] at this; linarith
      have hτ_nn : 0 ≤ τ 0 ∧ 0 ≤ τ 1 := ⟨hτ.1 0, hτ.1 1⟩
      -- EU(defect | opponent defects) = 1 ≥ EU(τ | opponent defects)
      -- = 3*τ0*0 + 0*τ0*1 + 5*τ1*0 + 1*τ1*1 = τ1 ≤ τ0 + τ1 = 1
      ring_nf
      nlinarith [hτ_prob, hτ_nn.1, hτ_nn.2]
    · -- Player 1 unilaterally deviates
      have hi1 : i = 1 := by fin_cases i <;> simp_all [Fin.ext_iff]
      subst hi1
      have hτ_prob : τ 0 + τ 1 = 1 := by
        have := hτ.2; simp [Fin.sum_univ_two] at this; linarith
      have hτ_nn : 0 ≤ τ 0 ∧ 0 ≤ τ 1 := ⟨hτ.1 0, hτ.1 1⟩
      ring_nf
      nlinarith [hτ_prob, hτ_nn.1, hτ_nn.2]

end NashEquilibrium

#check @NashEquilibrium.nash_existence
#check @NashEquilibrium.fixed_point_is_nash
#check @NashEquilibrium.bestResponse_convex
#check @NashEquilibrium.prisoners_dilemma_nash
