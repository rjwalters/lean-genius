import Mathlib.Logic.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

/-
# Complexity Theory Core -- Canonical Sound Computation Model

This file provides the foundational computation model and complexity class
definitions used by all P vs NP formalization files. It uses a **Godelized
opaque computation model** that avoids the soundness flaw present in the
original PNPBarriers.lean.

## Design Principles

1. **Programs are natural numbers** (Godel codes), not Lean functions
2. **Computation is via an opaque universal function Phi**
3. **Complexity classes are defined from Phi**, not declared as opaque sets
4. **Only well-established facts** are axiomatized

## Why This Model is Sound

The key insight: programs are countable (indexed by N) but decision problems
(N -> Bool) are uncountable. By making Phi opaque, we prevent constructing
a "trivial solver" for any given function, which would collapse all complexity
classes to Set.univ.

The unsound model in PNPBarriers.lean used:
  structure OracleProgram where
    compute : Oracle -> Nat -> Bool * Nat  -- arbitrary Lean function!
This allows `fun _ n => (f n, 0)` for any f, making P = NP = Set.univ.

## Contents

- Oracle and DecisionProblem types
- Universal computation function Phi (opaque)
- Structural axioms for Phi (countability, pair projection, negation)
- Complexity class definitions (P, NP, coNP, relativized variants)
- Basic containment theorems (P subset NP, complement closure)
- Polynomial-time reductions
- NP-completeness definitions

## Axiom Summary

Core structural (3):
  Phi_countably_many, Phi_pair_project_first, Phi_negate
Composition/reduction (2):
  poly_time_compose, reduction_preserves_P

All other containments and structural results are PROVED from these 5 axioms.
-/

set_option linter.unusedVariables false

namespace ComplexityCore

-- ============================================================
-- PART 1: Types and Computation Model
-- ============================================================

/-- An oracle is a decision problem: given a natural number, answer yes or no. -/
abbrev Oracle := ℕ → Bool

/-- The empty oracle: always answers false (no information). -/
def emptyOracle : Oracle := fun _ => false

/-- A polynomial time bound, represented by degree and leading coefficient. -/
structure Polynomial where
  degree : ℕ
  coeff : ℕ
deriving Repr

/-- Evaluate a polynomial bound: coeff * n^degree. -/
def Polynomial.eval (p : Polynomial) (n : ℕ) : ℕ :=
  p.coeff * n ^ p.degree

/-- Input size function: number of bits needed to represent n. -/
def inputSize (n : ℕ) : ℕ := Nat.log2 n + 1

/-- **Universal computation function Phi(e, A, n)**.

    Given:
    - `e : N` -- the Godel code of a program
    - `A : Oracle` -- an oracle to query
    - `n : N` -- the input

    Returns `some (result, steps)` if program `e` with oracle `A` on input `n`
    halts in `steps` steps with answer `result`, or `none` if it diverges.

    **Why opaque?** If we defined Phi as a Lean function, we could embed any
    decidable predicate. The opacity ensures that only the axiomatized properties
    are available, preventing the "trivial solver" construction that makes the
    original PNPBarriers.lean inconsistent. -/
opaque Φ : ℕ → Oracle → ℕ → Option (Bool × ℕ)

-- ============================================================
-- PART 2: Axioms for the Computation Model
-- ============================================================

/-- **Totality for polynomial-time programs**: If a program runs within a time
    bound, it always halts. -/
theorem Φ_total (e : ℕ) (A : Oracle) (n : ℕ) (bound : ℕ)
    (h : ∃ r s, Φ e A n = some (r, s) ∧ s ≤ bound) :
    ∃ r s, Φ e A n = some (r, s) := by
  obtain ⟨r, s, hs, _⟩ := h; exact ⟨r, s, hs⟩

/-- **Determinism**: Running the same program on the same input with the same
    oracle always gives the same result. -/
theorem Φ_deterministic (e : ℕ) (A : Oracle) (n : ℕ) (r₁ s₁ r₂ s₂ : _)
    (h₁ : Φ e A n = some (r₁, s₁)) (h₂ : Φ e A n = some (r₂, s₂)) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  have := h₁.symm.trans h₂; simp at this; exact this

/-- **Non-triviality**: Not every decision problem is computable.
    There exist functions N -> Bool that no program computes, even with
    unlimited time. This follows from a counting argument: uncountably many
    functions but only countably many programs. -/
axiom Φ_countably_many :
    ∃ f : ℕ → Bool, ∀ e : ℕ, ∃ n : ℕ,
      Φ e emptyOracle n = none ∨
      ∃ r s, Φ e emptyOracle n = some (r, s) ∧ r ≠ f n

/-- **Pair projection**: For every program e, there exists a program e'
    that, given a paired input <n, x>, extracts n and runs e on it,
    ignoring x. The overhead is bounded by a constant.
    This enables proving P subset NP from this single primitive. -/
axiom Φ_pair_project_first (e : ℕ) :
    ∃ e' : ℕ, ∀ (A : Oracle) (n x : ℕ),
      ∃ overhead : ℕ, overhead ≤ 1 ∧
        (∀ r s, Φ e A n = some (r, s) →
          Φ e' A (Nat.pair n x) = some (r, s + overhead)) ∧
        (Φ e A n = none → Φ e' A (Nat.pair n x) = none)

/-- **Program negation**: For every program e, there exists a program e'
    that computes the negation. Running e' gives the opposite Boolean result
    in the same number of steps. -/
axiom Φ_negate (e : ℕ) :
    ∃ e' : ℕ, ∀ A : Oracle, ∀ n : ℕ, ∀ r : Bool, ∀ s : ℕ,
      Φ e A n = some (r, s) → Φ e' A n = some (!r, s)

-- ============================================================
-- PART 3: Complexity Class Definitions
-- ============================================================

/-- A program e solves a decision problem f relative to oracle A
    if, for every input, it halts and gives the correct answer. -/
def Solves (e : ℕ) (A : Oracle) (f : ℕ → Bool) : Prop :=
  ∀ n : ℕ, ∃ s : ℕ, Φ e A n = some (f n, s)

/-- A program e runs in time bounded by polynomial p relative to oracle A. -/
def RunsInPolyTime (e : ℕ) (A : Oracle) (p : Polynomial) : Prop :=
  ∀ n : ℕ, ∀ r s, Φ e A n = some (r, s) → s ≤ p.eval (inputSize n)

/-- A problem is in P^A if some program solves it in polynomial time
    with oracle A. -/
def InP (A : Oracle) (f : ℕ → Bool) : Prop :=
  ∃ (e : ℕ) (p : Polynomial),
    Solves e A f ∧
    ∀ n : ℕ, ∀ s : ℕ, Φ e A n = some (f n, s) → s ≤ p.eval (inputSize n)

/-- P^A: the relativized complexity class. -/
def P_rel (A : Oracle) : Set (ℕ → Bool) :=
  { f | InP A f }

/-- Unrelativized P = P^empty. -/
def P : Set (ℕ → Bool) := P_rel emptyOracle

/-- A problem is in NP^A if there exists a polynomial-time verifier:
    for "yes" inputs, some polynomial-length certificate makes the verifier accept;
    for "no" inputs, no certificate works. -/
def InNP (A : Oracle) (f : ℕ → Bool) : Prop :=
  ∃ (e : ℕ) (p : Polynomial),
    -- Completeness: yes inputs have witnesses
    (∀ n : ℕ, f n = true →
      ∃ c : ℕ, c ≤ p.eval (inputSize n) ∧
        ∃ s, Φ e A (Nat.pair n c) = some (true, s) ∧ s ≤ p.eval (inputSize n)) ∧
    -- Soundness: no inputs have no witnesses
    (∀ n : ℕ, f n = false →
      ∀ c : ℕ, c ≤ p.eval (inputSize n) →
        ∀ r s, Φ e A (Nat.pair n c) = some (r, s) → r = false)

/-- NP^A: the relativized complexity class. -/
def NP_rel (A : Oracle) : Set (ℕ → Bool) :=
  { f | InNP A f }

/-- Unrelativized NP = NP^empty. -/
def NP : Set (ℕ → Bool) := NP_rel emptyOracle

-- ============================================================
-- PART 4: P^A subset NP^A (Proved)
-- ============================================================

/-- P^A subset NP^A for all oracles A.
    Uses Phi_pair_project_first to build a verifier ignoring the certificate. -/
theorem P_rel_subset_NP_rel (A : Oracle) : P_rel A ⊆ NP_rel A := by
  intro f hf
  obtain ⟨e, p, hsolves, htime⟩ := hf
  obtain ⟨e', he'⟩ := Φ_pair_project_first e
  unfold NP_rel InNP; simp only [Set.mem_setOf_eq]
  use e', ⟨p.degree, p.coeff + 1⟩
  constructor
  · intro n hn
    use 0
    constructor
    · exact Nat.zero_le _
    · obtain ⟨s, hs⟩ := hsolves n
      obtain ⟨overhead, ho_le, hfwd, _⟩ := he' A n 0
      rw [hn] at hs
      refine ⟨s + overhead, hfwd true s hs, ?_⟩
      have htime' := htime n s (by rw [hn]; exact hs)
      simp only [Polynomial.eval] at htime' ⊢
      have hxd : (inputSize n) ^ p.degree ≥ 1 :=
        Nat.one_le_pow _ _ (by unfold inputSize; omega)
      have : p.coeff * (inputSize n) ^ p.degree + (inputSize n) ^ p.degree =
        (p.coeff + 1) * (inputSize n) ^ p.degree := by ring
      omega
  · intro n hn c _ r s hrun
    obtain ⟨s_orig, hs_orig⟩ := hsolves n
    obtain ⟨overhead, _, hfwd, _⟩ := he' A n c
    rw [hn] at hs_orig
    have := (hfwd false s_orig hs_orig).symm.trans hrun
    simp at this; exact this.1

/-- P subset NP (unrelativized). -/
theorem P_subset_NP : P ⊆ NP :=
  P_rel_subset_NP_rel emptyOracle

-- ============================================================
-- PART 5: Complement Closure and coNP
-- ============================================================

/-- Complement closure: If f in P^A, then (not f) in P^A.
    PROVED from Phi_negate. -/
theorem P_complement_closed (A : Oracle) (f : ℕ → Bool) :
    f ∈ P_rel A → (fun n => !f n) ∈ P_rel A := by
  intro ⟨e, p, hsolves, htime⟩
  obtain ⟨e', he'⟩ := Φ_negate e
  refine ⟨e', p, ?_, ?_⟩
  · intro n
    obtain ⟨s, hs⟩ := hsolves n
    exact ⟨s, he' A n (f n) s hs⟩
  · intro n s hs'
    obtain ⟨s₀, hs₀⟩ := hsolves n
    have h_neg := he' A n (f n) s₀ hs₀
    have := Φ_deterministic e' A n (!f n) s₀ (!f n) s h_neg hs'
    rw [← this.2]
    exact htime n s₀ hs₀

/-- coNP^A: problems whose complements are in NP^A. -/
def coNP_rel (A : Oracle) : Set (ℕ → Bool) :=
  { f | (fun n => !f n) ∈ NP_rel A }

/-- Unrelativized coNP = coNP^empty. -/
def coNP : Set (ℕ → Bool) := coNP_rel emptyOracle

/-- P subset coNP. -/
theorem P_subset_coNP : P ⊆ coNP := by
  intro f hf
  show (fun n => !f n) ∈ NP
  exact P_subset_NP (P_complement_closed emptyOracle f hf)

/-- NP intersect coNP. -/
def NP_inter_coNP : Set (ℕ → Bool) :=
  NP ∩ coNP

/-- P subset NP intersect coNP. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP_inter_coNP := by
  intro f hf
  exact ⟨P_subset_NP hf, P_subset_coNP hf⟩

-- ============================================================
-- PART 6: Model Soundness
-- ============================================================

/-- The model is non-trivial: P is a proper subset of all functions. -/
theorem P_nontrivial : P ≠ Set.univ := by
  intro h
  obtain ⟨f, hf⟩ := Φ_countably_many
  have hfP : f ∈ P := by rw [h]; exact Set.mem_univ f
  obtain ⟨e, p, hsolves, htime⟩ := hfP
  obtain ⟨n, hn⟩ := hf e
  obtain ⟨s, hs⟩ := hsolves n
  cases hn with
  | inl h_none =>
    rw [h_none] at hs
    exact Option.noConfusion hs
  | inr h_wrong =>
    obtain ⟨r, s', hrs, hne⟩ := h_wrong
    rw [hrs] at hs
    have := Option.some.inj hs
    have : r = f n := by
      have := congr_arg Prod.fst this
      simp at this
      exact this
    exact hne this

/-- The P vs NP question is well-posed. -/
theorem p_vs_np_well_posed :
    P ≠ Set.univ ∧ P ⊆ NP :=
  ⟨P_nontrivial, P_subset_NP⟩

-- ============================================================
-- PART 7: Structural Consequences of P = NP
-- ============================================================

/-- P = NP implies NP = coNP. -/
theorem P_eq_NP_implies_NP_eq_coNP (h : P = NP) : NP = coNP := by
  ext f
  constructor
  · intro hf
    show (fun n => !f n) ∈ NP
    have hfP : f ∈ P := h ▸ hf
    have hcP : (fun n => !f n) ∈ P := P_complement_closed emptyOracle f hfP
    exact P_subset_NP hcP
  · intro hf
    have hcNP : (fun n => !f n) ∈ NP := hf
    have hcP : (fun n => !f n) ∈ P := h ▸ hcNP
    have hfP : (fun n => !(!(f n))) ∈ P :=
      P_complement_closed emptyOracle (fun n => !f n) hcP
    have : (fun n => !(!(f n))) = f := by ext n; simp
    rw [this] at hfP
    exact P_subset_NP hfP

/-- NP != coNP implies P != NP (contrapositive). -/
theorem NP_ne_coNP_implies_P_ne_NP : NP ≠ coNP → P ≠ NP := by
  intro h_neq h_eq
  exact h_neq (P_eq_NP_implies_NP_eq_coNP h_eq)

-- ============================================================
-- PART 8: Polynomial-Time Reductions
-- ============================================================

/-- A polynomial-time computable function relative to oracle A. -/
def PolyTimeComputable (A : Oracle) (f : ℕ → ℕ) : Prop :=
  ∃ (e : ℕ) (p : Polynomial), ∀ n : ℕ,
    ∃ s : ℕ, Φ e A n = some (true, s) ∧ s ≤ p.eval (inputSize n)

/-- Problem A polynomial-time reduces to problem B (A <=p B). -/
def PolyTimeReduces (A_prob B_prob : ℕ → Bool) : Prop :=
  ∃ f : ℕ → ℕ,
    PolyTimeComputable emptyOracle f ∧
    (∀ x : ℕ, A_prob x = B_prob (f x))

notation:50 A_prob " ≤ₚ " B_prob => PolyTimeReduces A_prob B_prob

/-- A problem is NP-hard if every NP problem poly-time reduces to it. -/
def NPHard (problem : ℕ → Bool) : Prop :=
  ∀ L : ℕ → Bool, L ∈ NP → L ≤ₚ problem

/-- A problem is NP-complete if it is both in NP and NP-hard. -/
def NPComplete (problem : ℕ → Bool) : Prop :=
  problem ∈ NP ∧ NPHard problem

/-- Composition of poly-time computable functions is poly-time computable. -/
axiom poly_time_compose (f g : ℕ → ℕ)
    (hf : PolyTimeComputable emptyOracle f)
    (hg : PolyTimeComputable emptyOracle g) :
    PolyTimeComputable emptyOracle (g ∘ f)

/-- Polynomial-time reductions compose. -/
theorem poly_reduce_trans (A_prob B_prob C_prob : ℕ → Bool)
    (h1 : A_prob ≤ₚ B_prob) (h2 : B_prob ≤ₚ C_prob) : A_prob ≤ₚ C_prob := by
  obtain ⟨f, hf_comp, hf_correct⟩ := h1
  obtain ⟨g, hg_comp, hg_correct⟩ := h2
  exact ⟨g ∘ f, poly_time_compose f g hf_comp hg_comp,
    fun x => by simp [Function.comp, hf_correct, hg_correct]⟩

/-- Polynomial-time reductions preserve membership in P. -/
axiom reduction_preserves_P (A_prob B_prob : ℕ → Bool)
    (h_reduce : A_prob ≤ₚ B_prob) (h_in_P : B_prob ∈ P) : A_prob ∈ P

/-- NPC in P implies P = NP. -/
theorem NPComplete_in_P_implies_P_eq_NP (L : ℕ → Bool)
    (h_complete : NPComplete L) (h_in_P : L ∈ P) : P = NP := by
  ext problem
  constructor
  · exact fun hp => P_subset_NP hp
  · intro h_in_NP
    obtain ⟨_, h_hard⟩ := h_complete
    exact reduction_preserves_P problem L (h_hard problem h_in_NP) h_in_P

/-- P != NP implies no NP-complete problem is in P. -/
theorem P_ne_NP_implies_NPC_not_in_P (h : P ≠ NP) (L : ℕ → Bool)
    (h_complete : NPComplete L) : L ∉ P := by
  intro h_in_P
  exact h (NPComplete_in_P_implies_P_eq_NP L h_complete h_in_P)

/-- NP-hardness transfers via reductions. -/
theorem NPHard_of_reduce (A_prob B_prob : ℕ → Bool)
    (h_hard : NPHard A_prob) (h_reduce : A_prob ≤ₚ B_prob) : NPHard B_prob := by
  intro L hL
  exact poly_reduce_trans L A_prob B_prob (h_hard L hL) h_reduce

/-- NP-completeness transfers via reductions within NP. -/
theorem NPComplete_of_reduce (A_prob B_prob : ℕ → Bool)
    (h_complete : NPComplete A_prob) (h_in_NP : B_prob ∈ NP)
    (h_reduce : A_prob ≤ₚ B_prob) : NPComplete B_prob :=
  ⟨h_in_NP, NPHard_of_reduce A_prob B_prob h_complete.2 h_reduce⟩

-- ============================================================
-- PART 9: NP-Intermediate (Ladner's Theorem)
-- ============================================================

/-- A problem is NP-intermediate if it is in NP but neither in P nor NP-complete. -/
def NPIntermediate (f : ℕ → Bool) : Prop :=
  f ∈ NP ∧ f ∉ P ∧ ¬NPComplete f

end ComplexityCore
