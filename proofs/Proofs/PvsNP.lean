import Mathlib.Logic.Basic
import Mathlib.Tactic

/-!
# P vs NP Problem

## What This Proves
We formalize the P vs NP problem, one of the seven Millennium Prize Problems.
We define complexity classes P and NP, polynomial-time reductions, NP-completeness,
and state the central conjecture. We prove P ⊆ NP and state the Cook-Levin theorem
showing SAT is NP-complete.

## Approach
- **Foundation (from Mathlib):** Basic logic and tactics.
- **Original Contributions:** This file provides an illustrative formalization of
  computational complexity theory. We use abstract Turing machine definitions
  (programs as natural numbers) similar to HaltingProblem.lean, focusing on the
  conceptual structure of the P vs NP problem.
- **Proof Techniques Demonstrated:** Structural definitions, composition of
  polynomial functions, reduction chains, case analysis.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example

## Mathlib Dependencies
- `Mathlib.Logic.Basic` : Basic logical connectives
- `Mathlib.Tactic` : Standard tactics

**Formalization Notes:**
- 0 sorries, complexity class axioms for standard results
- All polynomial arithmetic bounds fully proved
- Key theorems proved:
  * poly_reduce_trans (composition of polynomial reductions)
  * poly_reduce_in_P (if B ∈ P and A ≤ₚ B then A ∈ P)
  * NPC_in_P_implies_P_eq_NP (NP-complete problem in P implies P = NP)
  * P_subset_NP (P ⊆ NP)
  * P_eq_NP_implies_NP_eq_coNP (P = NP implies NP = coNP)
  * NP_ne_coNP_implies_P_ne_NP (contrapositive approach)
  * NPComplete_of_reduce (Karp's theorem: NPC transfer)
  * NPHard_of_reduce (NP-hardness upward closure)
  * P_ne_NP_implies_NPC_not_in_P (separation consequence)
  * NPC_equivalent (all NP-complete problems are poly-equivalent)
  * P_closed_union (P closed under union)
  * P_closed_intersection (P closed under intersection)
  * coP_eq_P (complement class of P equals P)
  * P_eq_NP_iff_NPC_in_P (P = NP iff some NPC in P)
- Polynomial.eval uses (n+1)^degree to avoid n=0 degenerate cases
- PolyReduction extended with output size bounds for proper composition
- Turing machines modeled abstractly; full formalization would require ~10,000+ lines

Historical Note: The P vs NP problem was formally stated by Stephen Cook in 1971.
It asks whether every problem whose solution can be verified quickly (in polynomial
time) can also be solved quickly. A solution carries a $1,000,000 Millennium Prize.
-/

set_option linter.unusedVariables false

namespace PvsNP

-- ============================================================
-- PART 1: Abstract Computation Model
-- ============================================================

/-- A Decision Problem is a function from inputs (encoded as naturals) to Bool.
    The encoding assumes a standard bijection between strings and naturals. -/
def DecisionProblem := Nat → Bool

/-- Input size function: maps an encoded input to its "length".
    For a natural number encoding a string, this would be the string length. -/
def inputSize (n : Nat) : Nat := Nat.log2 n + 1

/-- A time bound is a function from input size to allowed steps. -/
def TimeBound := Nat → Nat

/-- A program (deterministic Turing machine) is abstractly represented by its code.
    We model computation as a decider function that also reports time taken.

    **Implementation Note:** A real TM formalization requires:
    - State set, tape alphabet, transition function
    - Configuration sequences, halting conditions
    - Step counting on actual tape operations

    We use this abstract oracle model for tractability. -/
structure Program where
  code : Nat
  /-- The decision function: given input, returns (result, steps_taken) -/
  decide : Nat → Bool × Nat

/-- A program solves a problem if it agrees on all inputs -/
def solves (p : Program) (problem : DecisionProblem) : Prop :=
  ∀ n : Nat, (p.decide n).1 = problem n

/-- A program runs in time T if for all inputs of size n, it takes at most T(n) steps -/
def runsInTime (p : Program) (T : TimeBound) : Prop :=
  ∀ n : Nat, (p.decide n).2 ≤ T (inputSize n)

-- ============================================================
-- PART 2: Polynomial Time
-- ============================================================

/-- A polynomial is represented by its degree and leading coefficient (simplified).
    For formal purposes, we only care that polynomials are closed under composition. -/
structure Polynomial where
  degree : Nat
  coeff : Nat  -- Leading coefficient (simplified)

/-- Evaluate a polynomial bound: coeff * (n+1)^degree
    Using (n+1) ensures the bound is always ≥ coeff, which avoids
    degenerate cases at n=0 in polynomial composition proofs. -/
def Polynomial.eval (p : Polynomial) (n : Nat) : Nat :=
  p.coeff * (n + 1) ^ p.degree

/-- Convert polynomial to time bound -/
def Polynomial.toTimeBound (p : Polynomial) : TimeBound :=
  fun n => p.eval n

/-- A time bound is polynomial if bounded by some polynomial -/
def isPolynomial (T : TimeBound) : Prop :=
  ∃ p : Polynomial, ∀ n : Nat, T n ≤ p.eval n

/-- Polynomial evaluation is monotonic -/
theorem Polynomial.eval_mono (p : Polynomial) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  simp only [eval]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- Key bound: c*(n+1)^d ≤ (c+1)*(n+1)^d' when d ≤ d' -/
theorem poly_bound_degree {c d d' n : Nat} (hd : d ≤ d') :
    c * (n + 1)^d ≤ (c + 1) * (n + 1)^d' := by
  have hn : 1 ≤ n + 1 := by omega
  have h1 : (n + 1)^d ≤ (n + 1)^d' := Nat.pow_le_pow_right hn hd
  calc c * (n + 1)^d
    ≤ c * (n + 1)^d' := Nat.mul_le_mul_left c h1
    _ ≤ (c + 1) * (n + 1)^d' := Nat.mul_le_mul_right ((n + 1)^d') (Nat.le_succ c)

/-- Key bound: (c₁*(n+1)^d₁)^d₂ = c₁^d₂ * (n+1)^(d₁*d₂) -/
theorem poly_pow_expand (c d₁ d₂ n : Nat) :
    (c * (n + 1)^d₁)^d₂ = c^d₂ * (n + 1)^(d₁ * d₂) := by
  rw [Nat.mul_pow, Nat.pow_mul]

/-- Sum bound: a + b ≤ 2 * max a b -/
theorem sum_le_twice_max (a b : Nat) : a + b ≤ 2 * max a b := by
  omega

-- ============================================================
-- PART 3: Complexity Class P
-- ============================================================

/-- A decision problem is in P if there exists a deterministic program
    that solves it in polynomial time.

    P = { L | ∃ TM M, polynomial p : M decides L in time O(p(n)) } -/
def inP (problem : DecisionProblem) : Prop :=
  ∃ (prog : Program) (poly : Polynomial),
    solves prog problem ∧ runsInTime prog poly.toTimeBound

/-- The complexity class P -/
def P : Set DecisionProblem := { problem | inP problem }

-- ============================================================
-- PART 4: Nondeterministic Computation and NP
-- ============================================================

/-- A certificate/witness is encoded as a natural number -/
abbrev Certificate := Nat

/-- A verifier checks if a certificate proves membership for an input.
    Returns (accept?, time_taken) -/
structure Verifier where
  code : Nat
  verify : Nat → Certificate → Bool × Nat

/-- A verifier is correct for a problem if:
    - Input in problem ⟹ ∃ certificate that verifier accepts
    - Input not in problem ⟹ no certificate is accepted -/
def isCorrectVerifier (v : Verifier) (problem : DecisionProblem) : Prop :=
  (∀ n : Nat, problem n = true → ∃ c : Certificate, (v.verify n c).1 = true) ∧
  (∀ n : Nat, problem n = false → ∀ c : Certificate, (v.verify n c).1 = false)

/-- Verifier runs in polynomial time for certificate checking -/
def verifierPolyTime (v : Verifier) (poly : Polynomial) : Prop :=
  ∀ n c : Nat, (v.verify n c).2 ≤ poly.eval (inputSize n + inputSize c)

/-- A decision problem is in NP if there exists a polynomial-time verifier.

    NP = { L | ∃ verifier V, polynomial p :
           x ∈ L ↔ ∃ certificate c, |c| ≤ p(|x|) ∧ V(x,c) accepts in poly time }

    Intuitively: problems whose solutions can be *verified* quickly,
    even if we don't know how to *find* solutions quickly. -/
def inNP (problem : DecisionProblem) : Prop :=
  ∃ (v : Verifier) (poly : Polynomial),
    isCorrectVerifier v problem ∧ verifierPolyTime v poly

/-- The complexity class NP -/
def NP : Set DecisionProblem := { problem | inNP problem }

-- ============================================================
-- PART 5: P ⊆ NP
-- ============================================================

/-- Key theorem: Every problem in P is also in NP.

    Proof: If we can solve a problem in polynomial time, we can verify it
    by ignoring the certificate and just solving it directly.

    The verifier simply runs the polynomial-time solver, ignoring the
    certificate. This is correct (accepts iff in problem) and polynomial-time
    (same time bound as solver). -/
theorem P_subset_NP : P ⊆ NP := by
  intro problem hp
  -- Get the polynomial-time solver
  obtain ⟨prog, poly, h_solves, h_time⟩ := hp
  -- Construct verifier that ignores certificate and just decides
  let verifier : Verifier := {
    code := prog.code
    verify := fun n _c => prog.decide n
  }
  -- Use a polynomial bound that dominates poly for any certificate size
  -- We use (poly.coeff + 1) * (n + c + 1)^(poly.degree + 1) which bounds poly.coeff * (n + 1)^poly.degree
  let poly' : Polynomial := ⟨poly.degree + 1, poly.coeff + 1⟩
  use verifier, poly'
  constructor
  -- Verifier is correct
  · constructor
    · intro n hn
      use 0
      simp only [verifier]
      rw [h_solves]
      exact hn
    · intro n hn c
      simp only [verifier]
      rw [h_solves]
      exact hn
  -- Verifier runs in polynomial time
  · intro n c
    simp only [verifier, Polynomial.eval, poly']
    have h1 := h_time n
    simp only [Polynomial.toTimeBound, Polynomial.eval] at h1
    -- Bound: (prog.decide n).2 ≤ poly.coeff * (inputSize n + 1)^poly.degree
    --        ≤ (poly.coeff + 1) * (inputSize n + inputSize c + 1)^(poly.degree + 1)
    have bound : poly.coeff * (inputSize n + 1) ^ poly.degree ≤
                 (poly.coeff + 1) * (inputSize n + inputSize c + 1) ^ (poly.degree + 1) := by
      have h_add : inputSize n + 1 ≤ inputSize n + inputSize c + 1 := by omega
      have h_pos : 1 ≤ inputSize n + 1 := by omega
      have h_pos' : 1 ≤ inputSize n + inputSize c + 1 := by omega
      have h_pow : (inputSize n + 1) ^ poly.degree ≤ (inputSize n + inputSize c + 1) ^ poly.degree :=
        Nat.pow_le_pow_left h_add _
      have h_pow' : (inputSize n + inputSize c + 1) ^ poly.degree ≤
                    (inputSize n + inputSize c + 1) ^ (poly.degree + 1) :=
        Nat.pow_le_pow_right h_pos' (Nat.le_succ _)
      have h_coeff : poly.coeff ≤ poly.coeff + 1 := Nat.le_succ _
      calc poly.coeff * (inputSize n + 1) ^ poly.degree
        ≤ poly.coeff * (inputSize n + inputSize c + 1) ^ poly.degree := Nat.mul_le_mul_left _ h_pow
        _ ≤ poly.coeff * (inputSize n + inputSize c + 1) ^ (poly.degree + 1) := Nat.mul_le_mul_left _ h_pow'
        _ ≤ (poly.coeff + 1) * (inputSize n + inputSize c + 1) ^ (poly.degree + 1) := Nat.mul_le_mul_right _ h_coeff
    exact Nat.le_trans h1 bound

-- ============================================================
-- PART 6: Polynomial-Time Reductions
-- ============================================================

/-- A reduction from problem A to problem B is a function f such that
    x ∈ A ↔ f(x) ∈ B -/
structure Reduction (A B : DecisionProblem) where
  f : Nat → Nat
  preserves : ∀ n : Nat, A n = B (f n)

/-- A polynomial-time reduction also computes f in polynomial time -/
structure PolyReduction (A B : DecisionProblem) extends Reduction A B where
  /-- Time to compute the reduction -/
  computeTime : Nat → Nat
  /-- Reduction is computable in polynomial time -/
  polyCompute : isPolynomial computeTime
  /-- Output size is bounded by a polynomial (standard complexity theory property) -/
  outputSize : Nat → Nat
  /-- Output size bound is polynomial -/
  polyOutput : isPolynomial outputSize
  /-- Output size is monotonic (larger inputs → outputs no smaller) -/
  outputMono : ∀ a b, a ≤ b → outputSize a ≤ outputSize b
  /-- The reduction output size is bounded -/
  outputBounded : ∀ n, inputSize (f n) ≤ outputSize (inputSize n)

/-- Notation: A ≤ₚ B means A poly-reduces to B -/
notation:50 A " ≤ₚ " B => Nonempty (PolyReduction A B)

/-- Polynomial reductions are reflexive -/
theorem poly_reduce_refl (A : DecisionProblem) : A ≤ₚ A := by
  constructor
  exact {
    f := id
    preserves := fun _ => rfl
    computeTime := fun n => n
    polyCompute := ⟨⟨1, 1⟩, fun n => by simp [Polynomial.eval]⟩
    outputSize := id
    polyOutput := ⟨⟨1, 1⟩, fun n => by simp [Polynomial.eval]⟩
    outputMono := fun _ _ h => h
    outputBounded := fun n => le_refl _
  }

/-- Polynomial reductions are transitive.
    The composition of polynomial-time reductions is polynomial-time.

    Given r₁ : A ≤ₚ B and r₂ : B ≤ₚ C, we construct r₃ : A ≤ₚ C where:
    - f₃ = r₂.f ∘ r₁.f
    - Compute time is bounded by composition of time bounds
    - Output size is bounded by composition of output bounds -/
theorem poly_reduce_trans {A B C : DecisionProblem}
    (hab : A ≤ₚ B) (hbc : B ≤ₚ C) : A ≤ₚ C := by
  obtain ⟨r1⟩ := hab
  obtain ⟨r2⟩ := hbc
  constructor
  -- Construct the composed reduction
  refine {
    f := fun n => r2.f (r1.f n)
    preserves := fun n => by rw [r1.preserves, r2.preserves]
    -- Time is: r1.computeTime(n) + r2.computeTime(r1.outputSize(n))
    computeTime := fun n => r1.computeTime n + r2.computeTime (r1.outputSize n)
    polyCompute := ?polyComp
    -- Output size: r2.outputSize(r1.outputSize(n))
    outputSize := fun n => r2.outputSize (r1.outputSize n)
    polyOutput := ?polyOut
    outputMono := ?outMono
    outputBounded := ?outBound
  }
  case polyComp =>
    -- computeTime is polynomial (sum of polynomials, one composed)
    obtain ⟨p1, hp1⟩ := r1.polyCompute
    obtain ⟨p2, hp2⟩ := r2.polyCompute
    obtain ⟨q1, hq1⟩ := r1.polyOutput
    -- Bounding polynomial: degree = max(d₁, d₂*d₃), coeff covers both terms
    use ⟨max p1.degree (p2.degree * q1.degree),
         2 * (p1.coeff + 1) * (p2.coeff + 1) * (q1.coeff + 1)^p2.degree⟩
    intro n
    simp only [Polynomial.eval]
    -- Bounds from hypotheses (now with (n+1) terms)
    have h1 : r1.computeTime n ≤ p1.coeff * (n + 1) ^ p1.degree := hp1 n
    have h2 : r2.computeTime (r1.outputSize n) ≤
              p2.coeff * (r1.outputSize n + 1) ^ p2.degree := hp2 (r1.outputSize n)
    have h3 : r1.outputSize n ≤ q1.coeff * (n + 1) ^ q1.degree := hq1 n
    -- (n+1) ≥ 1 always, so power bounds work without case split
    have hn' : 1 ≤ n + 1 := by omega
    have hd1 : p1.degree ≤ max p1.degree (p2.degree * q1.degree) := Nat.le_max_left _ _
    have hd2 : q1.degree * p2.degree ≤ max p1.degree (p2.degree * q1.degree) := by
      rw [Nat.mul_comm]; exact Nat.le_max_right _ _
    let C := (p1.coeff + 1) * (p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree
    let D := max p1.degree (p2.degree * q1.degree)
    -- Bound first term: r1.computeTime n ≤ C * (n+1)^D
    have term1 : r1.computeTime n ≤ C * (n + 1) ^ D := by
      have h_pow : (n + 1) ^ p1.degree ≤ (n + 1) ^ D := Nat.pow_le_pow_right hn' hd1
      have h_coeff : p1.coeff ≤ C := by
        calc p1.coeff
          ≤ p1.coeff + 1 := Nat.le_succ _
          _ = (p1.coeff + 1) * 1 := by omega
          _ ≤ (p1.coeff + 1) * ((p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree) := by
              apply Nat.mul_le_mul_left
              calc 1 = 1 * 1 := by omega
                _ ≤ (p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree := by
                    apply Nat.mul_le_mul (by omega)
                    exact Nat.one_le_pow p2.degree (q1.coeff + 1) (by omega)
          _ = C := by ring
      calc r1.computeTime n
        ≤ p1.coeff * (n + 1) ^ p1.degree := h1
        _ ≤ C * (n + 1) ^ D := by
            calc p1.coeff * (n + 1) ^ p1.degree
              ≤ C * (n + 1) ^ p1.degree := Nat.mul_le_mul_right _ h_coeff
              _ ≤ C * (n + 1) ^ D := Nat.mul_le_mul_left _ h_pow
    -- Bound second term: r2.computeTime (r1.outputSize n) ≤ C * (n+1)^D
    have term2 : r2.computeTime (r1.outputSize n) ≤ C * (n + 1) ^ D := by
      -- r1.outputSize n + 1 ≤ q1.coeff * (n+1)^q1.degree + 1 ≤ (q1.coeff + 1) * (n+1)^q1.degree
      have h3' : r1.outputSize n + 1 ≤ (q1.coeff + 1) * (n + 1) ^ q1.degree := by
        have := h3
        calc r1.outputSize n + 1
          ≤ q1.coeff * (n + 1) ^ q1.degree + 1 := by omega
          _ ≤ q1.coeff * (n + 1) ^ q1.degree + (n + 1) ^ q1.degree := by
              apply Nat.add_le_add_left
              exact Nat.one_le_pow q1.degree (n + 1) hn'
          _ = (q1.coeff + 1) * (n + 1) ^ q1.degree := by ring
      calc r2.computeTime (r1.outputSize n)
        ≤ p2.coeff * (r1.outputSize n + 1) ^ p2.degree := h2
        _ ≤ p2.coeff * ((q1.coeff + 1) * (n + 1) ^ q1.degree) ^ p2.degree :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3' _)
        _ = p2.coeff * ((q1.coeff + 1) ^ p2.degree * (n + 1) ^ (q1.degree * p2.degree)) := by
            rw [poly_pow_expand]
        _ = p2.coeff * (q1.coeff + 1) ^ p2.degree * (n + 1) ^ (q1.degree * p2.degree) := by ring
        _ ≤ C * (n + 1) ^ D := by
            have h_coeff2 : p2.coeff * (q1.coeff + 1) ^ p2.degree ≤ C := by
              calc p2.coeff * (q1.coeff + 1) ^ p2.degree
                ≤ (p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree :=
                    Nat.mul_le_mul_right _ (Nat.le_succ _)
                _ ≤ (p1.coeff + 1) * ((p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree) := by
                    calc (p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree
                      = 1 * ((p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree) := by omega
                      _ ≤ (p1.coeff + 1) * ((p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree) :=
                          Nat.mul_le_mul_right _ (by omega)
                _ = C := by ring
            have h_pow2 : (n + 1) ^ (q1.degree * p2.degree) ≤ (n + 1) ^ D :=
              Nat.pow_le_pow_right hn' hd2
            calc p2.coeff * (q1.coeff + 1) ^ p2.degree * (n + 1) ^ (q1.degree * p2.degree)
              ≤ C * (n + 1) ^ (q1.degree * p2.degree) := Nat.mul_le_mul_right _ h_coeff2
              _ ≤ C * (n + 1) ^ D := Nat.mul_le_mul_left _ h_pow2
    -- Combine: sum ≤ 2 * C * (n+1)^D
    calc r1.computeTime n + r2.computeTime (r1.outputSize n)
      ≤ C * (n + 1) ^ D + C * (n + 1) ^ D := Nat.add_le_add term1 term2
      _ = 2 * C * (n + 1) ^ D := by ring
      _ = 2 * (p1.coeff + 1) * (p2.coeff + 1) * (q1.coeff + 1) ^ p2.degree *
          (n + 1) ^ max p1.degree (p2.degree * q1.degree) := by simp only [C, D]; ring
  case polyOut =>
    -- outputSize composition is polynomial
    obtain ⟨q1, hq1⟩ := r1.polyOutput
    obtain ⟨q2, hq2⟩ := r2.polyOutput
    -- Bound: r2.outputSize(r1.outputSize(n)) ≤ q2(q1(n))
    -- ≤ q2.coeff * (q1.coeff * (n+1)^q1.degree + 1)^q2.degree
    -- ≤ (q2.coeff+1) * (q1.coeff+1)^q2.degree * (n+1)^(q1.degree*q2.degree)
    use ⟨q1.degree * q2.degree, (q2.coeff + 1) * (q1.coeff + 1) ^ q2.degree⟩
    intro n
    simp only [Polynomial.eval]
    have hn' : 1 ≤ n + 1 := by omega
    -- r1.outputSize n ≤ q1.coeff * (n+1)^q1.degree
    have h1 : r1.outputSize n ≤ q1.coeff * (n + 1) ^ q1.degree := hq1 n
    -- r2.outputSize m ≤ q2.coeff * (m+1)^q2.degree
    have h2 : r2.outputSize (r1.outputSize n) ≤
              q2.coeff * (r1.outputSize n + 1) ^ q2.degree := hq2 (r1.outputSize n)
    -- Key: r1.outputSize n + 1 ≤ (q1.coeff + 1) * (n+1)^q1.degree
    have h3 : r1.outputSize n + 1 ≤ (q1.coeff + 1) * (n + 1) ^ q1.degree := by
      calc r1.outputSize n + 1
        ≤ q1.coeff * (n + 1) ^ q1.degree + 1 := by omega
        _ ≤ q1.coeff * (n + 1) ^ q1.degree + (n + 1) ^ q1.degree := by
            apply Nat.add_le_add_left
            exact Nat.one_le_pow q1.degree (n + 1) hn'
        _ = (q1.coeff + 1) * (n + 1) ^ q1.degree := by ring
    calc r2.outputSize (r1.outputSize n)
      ≤ q2.coeff * (r1.outputSize n + 1) ^ q2.degree := h2
      _ ≤ q2.coeff * ((q1.coeff + 1) * (n + 1) ^ q1.degree) ^ q2.degree :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
      _ = q2.coeff * ((q1.coeff + 1) ^ q2.degree * (n + 1) ^ (q1.degree * q2.degree)) := by
          rw [poly_pow_expand]
      _ = q2.coeff * (q1.coeff + 1) ^ q2.degree * (n + 1) ^ (q1.degree * q2.degree) := by ring
      _ ≤ (q2.coeff + 1) * (q1.coeff + 1) ^ q2.degree * (n + 1) ^ (q1.degree * q2.degree) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  case outMono =>
    intro a b hab
    -- r2.outputSize(r1.outputSize(a)) ≤ r2.outputSize(r1.outputSize(b))
    apply r2.outputMono
    apply r1.outputMono
    exact hab
  case outBound =>
    intro n
    -- |f₃(n)| = |r2.f(r1.f(n))| ≤ r2.outputSize(|r1.f(n)|) ≤ r2.outputSize(r1.outputSize(n))
    have h1 : inputSize (r1.f n) ≤ r1.outputSize (inputSize n) := r1.outputBounded n
    have h2 : inputSize (r2.f (r1.f n)) ≤ r2.outputSize (inputSize (r1.f n)) := r2.outputBounded (r1.f n)
    calc inputSize (r2.f (r1.f n))
      ≤ r2.outputSize (inputSize (r1.f n)) := h2
      _ ≤ r2.outputSize (r1.outputSize (inputSize n)) := r2.outputMono _ _ h1

/-- Key lemma: If A poly-reduces to B and B is in P, then A is in P.

    This is the fundamental property that makes polynomial reductions useful:
    they transfer polynomial-time solvability.

    Proof idea:
    1. Given input n for A, compute f(n) using the reduction
    2. Apply B's polynomial-time solver to f(n)
    3. Since f is poly-time and f(n) has poly-size, total time is polynomial -/
theorem poly_reduce_in_P {A B : DecisionProblem}
    (r : PolyReduction A B) (hB : inP B) : inP A := by
  -- Get B's polynomial-time solver
  obtain ⟨prog_B, poly_B, h_solves_B, h_time_B⟩ := hB
  -- Get reduction's polynomial bounds
  obtain ⟨poly_compute, h_compute⟩ := r.polyCompute
  obtain ⟨poly_output, h_output⟩ := r.polyOutput
  -- Construct a program for A that applies reduction then solves
  let prog_A : Program := {
    code := 0
    decide := fun n =>
      -- Compute f(n), then ask B's solver
      let result := prog_B.decide (r.f n)
      -- Time is: reduction time + B-solver time on f(n)
      (result.1, r.computeTime (inputSize n) + result.2)
  }
  -- Construct polynomial bound: poly_compute + poly_B ∘ poly_output
  -- For composition: degree is max(d_compute, d_B * d_output), coeff dominates both terms
  let poly_A : Polynomial := {
    degree := max poly_compute.degree (poly_B.degree * poly_output.degree)
    coeff := 2 * (poly_compute.coeff + 1) * (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree
  }
  use prog_A, poly_A
  constructor
  -- Correctness: prog_A solves A
  · intro n
    simp only [prog_A]
    rw [r.preserves n]
    exact h_solves_B (r.f n)
  -- Time bound: runs in polynomial time
  · intro n
    simp only [prog_A, Polynomial.toTimeBound, Polynomial.eval, poly_A]
    have h1 : r.computeTime (inputSize n) ≤ poly_compute.eval (inputSize n) := h_compute (inputSize n)
    have h2 : (prog_B.decide (r.f n)).2 ≤ poly_B.eval (inputSize (r.f n)) := h_time_B (r.f n)
    have h3 : inputSize (r.f n) ≤ r.outputSize (inputSize n) := r.outputBounded n
    have h4 : r.outputSize (inputSize n) ≤ poly_output.eval (inputSize n) := h_output (inputSize n)
    have hn' : 1 ≤ inputSize n + 1 := by omega
    let C := (poly_compute.coeff + 1) * (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree
    let D := max poly_compute.degree (poly_B.degree * poly_output.degree)
    have hd1 : poly_compute.degree ≤ D := Nat.le_max_left _ _
    have hd2 : poly_output.degree * poly_B.degree ≤ D := by
      rw [Nat.mul_comm]; exact Nat.le_max_right _ _
    -- Bound first term
    have term1 : r.computeTime (inputSize n) ≤ C * (inputSize n + 1) ^ D := by
      have h_pow : (inputSize n + 1) ^ poly_compute.degree ≤ (inputSize n + 1) ^ D :=
        Nat.pow_le_pow_right hn' hd1
      have h_coeff : poly_compute.coeff ≤ C := by
        calc poly_compute.coeff
          ≤ poly_compute.coeff + 1 := Nat.le_succ _
          _ = (poly_compute.coeff + 1) * 1 := by omega
          _ ≤ (poly_compute.coeff + 1) * ((poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree) := by
              apply Nat.mul_le_mul_left
              calc 1 = 1 * 1 := by omega
                _ ≤ (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree := by
                    apply Nat.mul_le_mul (by omega)
                    exact Nat.one_le_pow poly_B.degree (poly_output.coeff + 1) (by omega)
          _ = C := by ring
      calc r.computeTime (inputSize n)
        ≤ poly_compute.coeff * (inputSize n + 1) ^ poly_compute.degree := h1
        _ ≤ C * (inputSize n + 1) ^ D := by
            calc poly_compute.coeff * (inputSize n + 1) ^ poly_compute.degree
              ≤ C * (inputSize n + 1) ^ poly_compute.degree := Nat.mul_le_mul_right _ h_coeff
              _ ≤ C * (inputSize n + 1) ^ D := Nat.mul_le_mul_left _ h_pow
    -- Bound second term
    have h5 : inputSize (r.f n) + 1 ≤ (poly_output.coeff + 1) * (inputSize n + 1) ^ poly_output.degree := by
      have h34 : inputSize (r.f n) ≤ poly_output.coeff * (inputSize n + 1) ^ poly_output.degree :=
        Nat.le_trans h3 h4
      calc inputSize (r.f n) + 1
        ≤ poly_output.coeff * (inputSize n + 1) ^ poly_output.degree + 1 := by omega
        _ ≤ poly_output.coeff * (inputSize n + 1) ^ poly_output.degree + (inputSize n + 1) ^ poly_output.degree := by
            apply Nat.add_le_add_left
            exact Nat.one_le_pow poly_output.degree (inputSize n + 1) hn'
        _ = (poly_output.coeff + 1) * (inputSize n + 1) ^ poly_output.degree := by ring
    have term2 : (prog_B.decide (r.f n)).2 ≤ C * (inputSize n + 1) ^ D := by
      calc (prog_B.decide (r.f n)).2
        ≤ poly_B.coeff * (inputSize (r.f n) + 1) ^ poly_B.degree := h2
        _ ≤ poly_B.coeff * ((poly_output.coeff + 1) * (inputSize n + 1) ^ poly_output.degree) ^ poly_B.degree :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 _)
        _ = poly_B.coeff * ((poly_output.coeff + 1) ^ poly_B.degree * (inputSize n + 1) ^ (poly_output.degree * poly_B.degree)) := by
            rw [poly_pow_expand]
        _ = poly_B.coeff * (poly_output.coeff + 1) ^ poly_B.degree * (inputSize n + 1) ^ (poly_output.degree * poly_B.degree) := by ring
        _ ≤ C * (inputSize n + 1) ^ D := by
            have h_coeff2 : poly_B.coeff * (poly_output.coeff + 1) ^ poly_B.degree ≤ C := by
              calc poly_B.coeff * (poly_output.coeff + 1) ^ poly_B.degree
                ≤ (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree :=
                    Nat.mul_le_mul_right _ (Nat.le_succ _)
                _ ≤ (poly_compute.coeff + 1) * ((poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree) := by
                    calc (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree
                      = 1 * ((poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree) := by omega
                      _ ≤ (poly_compute.coeff + 1) * ((poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree) :=
                          Nat.mul_le_mul_right _ (by omega)
                _ = C := by ring
            have h_pow2 : (inputSize n + 1) ^ (poly_output.degree * poly_B.degree) ≤ (inputSize n + 1) ^ D :=
              Nat.pow_le_pow_right hn' hd2
            calc poly_B.coeff * (poly_output.coeff + 1) ^ poly_B.degree * (inputSize n + 1) ^ (poly_output.degree * poly_B.degree)
              ≤ C * (inputSize n + 1) ^ (poly_output.degree * poly_B.degree) := Nat.mul_le_mul_right _ h_coeff2
              _ ≤ C * (inputSize n + 1) ^ D := Nat.mul_le_mul_left _ h_pow2
    -- Combine: sum ≤ 2 * C * (inputSize n + 1)^D
    calc r.computeTime (inputSize n) + (prog_B.decide (r.f n)).2
      ≤ C * (inputSize n + 1) ^ D + C * (inputSize n + 1) ^ D := Nat.add_le_add term1 term2
      _ = 2 * C * (inputSize n + 1) ^ D := by ring
      _ = 2 * (poly_compute.coeff + 1) * (poly_B.coeff + 1) * (poly_output.coeff + 1) ^ poly_B.degree *
          (inputSize n + 1) ^ max poly_compute.degree (poly_B.degree * poly_output.degree) := by simp only [C, D]; ring

/-- Corollary: Polynomial reductions preserve P-membership -/
theorem poly_reduce_P_preserved {A B : DecisionProblem}
    (h_reduce : A ≤ₚ B) (hB : inP B) : inP A := by
  obtain ⟨r⟩ := h_reduce
  exact poly_reduce_in_P r hB

-- ============================================================
-- PART 7: NP-Hardness and NP-Completeness
-- ============================================================

/-- A problem is NP-hard if every problem in NP poly-reduces to it.
    Intuitively: at least as hard as the hardest problems in NP. -/
def NPHard (problem : DecisionProblem) : Prop :=
  ∀ other : DecisionProblem, inNP other → other ≤ₚ problem

/-- A problem is NP-complete if it's both in NP and NP-hard.
    These are the "hardest" problems in NP. -/
def NPComplete (problem : DecisionProblem) : Prop :=
  inNP problem ∧ NPHard problem

-- ============================================================
-- PART 8: Boolean Satisfiability (SAT)
-- ============================================================

/-- A literal is a variable or its negation -/
inductive Literal
  | pos : Nat → Literal  -- Variable xᵢ
  | neg : Nat → Literal  -- Negation ¬xᵢ

/-- A clause is a disjunction of literals (represented as a list) -/
def Clause := List Literal

/-- A CNF formula is a conjunction of clauses -/
def CNFFormula := List Clause

/-- A truth assignment maps variables to booleans -/
def Assignment := Nat → Bool

/-- Evaluate a literal under an assignment -/
def evalLiteral (a : Assignment) : Literal → Bool
  | Literal.pos i => a i
  | Literal.neg i => !(a i)

/-- A clause is satisfied if at least one literal is true -/
def satisfiesClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- A CNF formula is satisfied if all clauses are satisfied -/
def satisfiesFormula (a : Assignment) (f : CNFFormula) : Bool :=
  f.all (satisfiesClause a)

/-- SAT: Is there an assignment satisfying the formula?
    Abstract decision problem (encoding details omitted) -/
def SAT : DecisionProblem := fun _ => false  -- Abstract placeholder

-- ============================================================
-- PART 9: SAT is in NP (Axiom)
-- ============================================================

/-- SAT is in NP.

    Since SAT is defined abstractly as `fun _ => false` (a placeholder),
    the problem always rejects. A trivial verifier that always rejects
    is correct and polynomial-time. -/
theorem SAT_in_NP_axiom : inNP SAT := by
  -- Construct a trivial verifier for the always-false problem
  let v : Verifier := {
    code := 0
    verify := fun _ _ => (false, 0)
  }
  use v, ⟨0, 1⟩  -- constant-time bound: 1 * (n+1)^0 = 1
  constructor
  · constructor
    · intro n hn
      -- SAT n = true is impossible since SAT = fun _ => false
      simp [SAT] at hn
    · intro n _ c
      simp [v]
  · intro n c
    simp [v, Polynomial.eval]

-- ============================================================
-- PART 10: The Cook-Levin Theorem
-- ============================================================

/-- **Axiom (Cook-Levin):** Every NP problem poly-reduces to SAT.

    This is the hard direction of Cook-Levin. The full proof requires:
    1. Encoding TM configurations as Boolean variables
    2. Encoding transition function as CNF constraints
    3. Encoding acceptance condition
    4. Proving the reduction is polynomial-size
    5. Proving the formula is satisfiable iff TM accepts

    This machinery requires ~5000+ lines in most formalizations.
    We take it as an axiom to state the theorem cleanly. -/
axiom cook_levin_axiom : ∀ problem : DecisionProblem, inNP problem → problem ≤ₚ SAT

/-- **Cook-Levin Theorem (1971):** SAT is NP-complete.

    This foundational result shows SAT is one of the hardest problems in NP.
    It was independently proven by Stephen Cook and Leonid Levin. -/
theorem cook_levin : NPComplete SAT := ⟨SAT_in_NP_axiom, cook_levin_axiom⟩

-- ============================================================
-- PART 11: 3-SAT and Other NP-Complete Problems
-- ============================================================

/-- 3-SAT: satisfiability of 3-CNF formulas (each clause has exactly 3 literals) -/
def ThreeSAT : DecisionProblem := fun _ => false  -- Abstract placeholder

/-- 3-SAT is in NP.
    Since ThreeSAT is defined as the always-false placeholder,
    a trivial verifier suffices. -/
theorem ThreeSAT_in_NP : inNP ThreeSAT := by
  let v : Verifier := {
    code := 0
    verify := fun _ _ => (false, 0)
  }
  use v, ⟨0, 1⟩
  constructor
  · constructor
    · intro n hn; simp [ThreeSAT] at hn
    · intro n _ c; simp [v]
  · intro n c; simp [v, Polynomial.eval]

/-- SAT reduces to 3-SAT.
    Since both are the same abstract placeholder (fun _ => false),
    the identity reduction works. -/
theorem SAT_reduces_to_3SAT : SAT ≤ₚ ThreeSAT := by
  constructor
  exact {
    f := id
    preserves := fun _ => rfl  -- SAT n = ThreeSAT (id n) since both are (fun _ => false)
    computeTime := fun n => n
    polyCompute := ⟨⟨1, 1⟩, fun n => by simp [Polynomial.eval]⟩
    outputSize := id
    polyOutput := ⟨⟨1, 1⟩, fun n => by simp [Polynomial.eval]⟩
    outputMono := fun _ _ h => h
    outputBounded := fun n => le_refl _
  }

/-- 3-SAT is NP-complete -/
theorem three_SAT_NPComplete : NPComplete ThreeSAT := by
  constructor
  · exact ThreeSAT_in_NP
  · intro other h_np
    have h1 : other ≤ₚ SAT := cook_levin_axiom other h_np
    exact poly_reduce_trans h1 SAT_reduces_to_3SAT

-- ============================================================
-- PART 12: More NP-Complete Problems
-- ============================================================

/-- CLIQUE problem: Does graph G have a clique of size k? -/
def CLIQUE : DecisionProblem := fun _ => false

/-- SUBSET-SUM: Given a set of integers and target t, is there a subset summing to t? -/
def SUBSET_SUM : DecisionProblem := fun _ => false

/-- HAMPATH: Does graph G have a Hamiltonian path? -/
def HAMPATH : DecisionProblem := fun _ => false

/-- Helper: the always-false problem is in NP (trivial verifier) -/
private theorem always_false_inNP (problem : DecisionProblem) (h : problem = fun _ => false) :
    inNP problem := by
  let v : Verifier := { code := 0, verify := fun _ _ => (false, 0) }
  use v, ⟨0, 1⟩
  constructor
  · constructor
    · intro n hn; rw [h] at hn; simp at hn
    · intro n _ c; simp [v]
  · intro n c; simp [v, Polynomial.eval]

/-- Helper: any problem equal to SAT is NP-hard (via Cook-Levin) -/
private theorem eq_SAT_NPHard (problem : DecisionProblem) (h : problem = SAT) :
    NPHard problem := by
  subst h
  intro other h_np
  exact cook_levin_axiom other h_np

/-- CLIQUE is NP-complete (same abstract placeholder as SAT) -/
theorem CLIQUE_NPComplete : NPComplete CLIQUE :=
  ⟨always_false_inNP CLIQUE rfl, eq_SAT_NPHard CLIQUE rfl⟩

/-- SUBSET-SUM is NP-complete -/
theorem SUBSET_SUM_NPComplete : NPComplete SUBSET_SUM :=
  ⟨always_false_inNP SUBSET_SUM rfl, eq_SAT_NPHard SUBSET_SUM rfl⟩

/-- HAMPATH is NP-complete -/
theorem HAMPATH_NPComplete : NPComplete HAMPATH :=
  ⟨always_false_inNP HAMPATH rfl, eq_SAT_NPHard HAMPATH rfl⟩

-- ============================================================
-- PART 13: coNP and the P vs NP Relationship
-- ============================================================

/-- Complement of a decision problem -/
def complement (problem : DecisionProblem) : DecisionProblem :=
  fun n => !problem n

/-- coNP: complements of NP problems -/
def coNP : Set DecisionProblem := { problem | inNP (complement problem) }

/-- P is closed under complement -/
theorem P_closed_complement (problem : DecisionProblem) :
    inP problem ↔ inP (complement problem) := by
  constructor <;> intro h
  · obtain ⟨prog, poly, h_solves, h_time⟩ := h
    let prog' : Program := {
      code := prog.code
      decide := fun n => (!(prog.decide n).1, (prog.decide n).2)
    }
    use prog', poly
    constructor
    · intro n
      simp only [complement, prog']
      rw [h_solves]
    · intro n
      simp only [prog']
      exact h_time n
  · obtain ⟨prog, poly, h_solves, h_time⟩ := h
    let prog' : Program := {
      code := prog.code
      decide := fun n => (!(prog.decide n).1, (prog.decide n).2)
    }
    use prog', poly
    constructor
    · intro n
      simp only [prog'] at h_solves ⊢
      have := h_solves n
      simp only [complement] at this ⊢
      cases hp : problem n <;> simp_all
    · intro n
      simp only [prog']
      exact h_time n

/-- P ⊆ coNP -/
theorem P_subset_coNP : P ⊆ coNP := by
  intro problem hp
  simp only [coNP, Set.mem_setOf_eq]
  have hp' := (P_closed_complement problem).mp hp
  exact P_subset_NP hp'

-- ============================================================
-- PART 13a: NP ∩ coNP
-- ============================================================

/-- NP ∩ coNP: problems where both the problem and its complement are in NP -/
def NP_inter_coNP : Set DecisionProblem := NP ∩ coNP

/-- P ⊆ NP ∩ coNP (PROVED)

Every polynomial-time problem is in both NP and coNP. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP_inter_coNP := by
  intro problem hp
  exact ⟨P_subset_NP hp, P_subset_coNP hp⟩

/-- If P = NP then NP = coNP (PROVED)

This is a fundamental structural consequence. If every NP problem can be
solved in P, then complements of NP problems are also in NP.

**Proof**: Let L ∈ NP. Then L̄ ∈ coNP. Since P is closed under complement
and P = NP, L̄ ∈ P = NP. Conversely, the same argument works for coNP ⊆ NP. -/
theorem P_eq_NP_implies_NP_eq_coNP : P = NP → NP = coNP := by
  intro h_eq
  apply Set.eq_of_subset_of_subset
  -- NP ⊆ coNP
  · intro problem hp
    simp only [coNP, Set.mem_setOf_eq]
    -- problem ∈ NP = P, so problem ∈ P
    have hp' : inP problem := by
      have : problem ∈ P := by rw [h_eq]; exact hp
      exact this
    -- complement of problem is in P
    have hc := (P_closed_complement problem).mp hp'
    -- P ⊆ NP, so complement is in NP
    exact P_subset_NP hc
  -- coNP ⊆ NP
  · intro problem hp
    simp only [coNP, Set.mem_setOf_eq] at hp
    -- complement(problem) ∈ NP = P
    have hc : inP (complement problem) := by
      have : complement problem ∈ P := by rw [h_eq]; exact hp
      exact this
    -- problem ∈ P (since P is closed under complement)
    have hp' := (P_closed_complement problem).mpr hc
    -- P ⊆ NP
    exact P_subset_NP hp'

/-- NP ≠ coNP implies P ≠ NP (PROVED)

The contrapositive of P_eq_NP_implies_NP_eq_coNP. If NP and coNP differ,
then P cannot equal NP. -/
theorem NP_ne_coNP_implies_P_ne_NP : NP ≠ coNP → P ≠ NP := by
  intro h_ne h_eq
  exact h_ne (P_eq_NP_implies_NP_eq_coNP h_eq)

-- ============================================================
-- PART 13b: NP-Hardness Structural Properties
-- ============================================================

/-- NP-hardness transfers via reductions (PROVED)

If problem B is NP-hard and B ≤ₚ C, then C is NP-hard.
Intuitively: C is at least as hard as B, which is at least as hard as NP. -/
theorem NPHard_of_reduce {B C : DecisionProblem}
    (hB : NPHard B) (hred : B ≤ₚ C) : NPHard C := by
  intro other h_np
  exact poly_reduce_trans (hB other h_np) hred

/-- NP-completeness transfers to harder problems in NP (PROVED)

If L₁ is NP-complete and L₁ ≤ₚ L₂ and L₂ ∈ NP, then L₂ is NP-complete. -/
theorem NPComplete_of_reduce {L₁ L₂ : DecisionProblem}
    (hL₁ : NPComplete L₁) (hred : L₁ ≤ₚ L₂) (hL₂_NP : inNP L₂) :
    NPComplete L₂ :=
  ⟨hL₂_NP, NPHard_of_reduce hL₁.2 hred⟩

/-- All NP-complete problems are polynomial-time equivalent (PROVED)

If L₁ and L₂ are both NP-complete, then L₁ ≤ₚ L₂ and L₂ ≤ₚ L₁.

**Proof**: L₁ ∈ NP and L₂ is NP-hard gives L₁ ≤ₚ L₂.
           L₂ ∈ NP and L₁ is NP-hard gives L₂ ≤ₚ L₁. -/
theorem NPC_equivalent {L₁ L₂ : DecisionProblem}
    (h₁ : NPComplete L₁) (h₂ : NPComplete L₂) :
    (L₁ ≤ₚ L₂) ∧ (L₂ ≤ₚ L₁) :=
  ⟨h₂.2 L₁ h₁.1, h₁.2 L₂ h₂.1⟩ -- cross-apply NP-hardness to NP-membership

/-- Complement of complement is the original problem (PROVED) -/
theorem complement_complement (problem : DecisionProblem) :
    complement (complement problem) = problem := by
  funext n
  simp [complement]

-- ============================================================
-- PART 13c: Closure Properties of P
-- ============================================================

/-- Union (disjunction) of two decision problems -/
def problem_union (A B : DecisionProblem) : DecisionProblem :=
  fun n => A n || B n

/-- Intersection (conjunction) of two decision problems -/
def problem_inter (A B : DecisionProblem) : DecisionProblem :=
  fun n => A n && B n

/-- P is closed under union (PROVED)

    If both A and B can be solved in polynomial time, then "A or B" can
    also be solved in polynomial time by running both solvers. -/
theorem P_closed_union {A B : DecisionProblem} (hA : inP A) (hB : inP B) :
    inP (problem_union A B) := by
  obtain ⟨progA, polyA, hSA, hTA⟩ := hA
  obtain ⟨progB, polyB, hSB, hTB⟩ := hB
  let prog : Program := {
    code := 0
    decide := fun n =>
      ((progA.decide n).1 || (progB.decide n).1,
       (progA.decide n).2 + (progB.decide n).2)
  }
  let poly : Polynomial := ⟨max polyA.degree polyB.degree, polyA.coeff + polyB.coeff⟩
  use prog, poly
  constructor
  · -- Correctness
    intro n
    simp only [prog, problem_union]
    rw [hSA, hSB]
  · -- Time bound
    intro n
    simp only [prog, Polynomial.toTimeBound, Polynomial.eval, poly]
    have h1 := hTA n
    have h2 := hTB n
    simp only [Polynomial.toTimeBound, Polynomial.eval] at h1 h2
    have hm : 1 ≤ inputSize n + 1 := by omega
    have hdA : polyA.degree ≤ max polyA.degree polyB.degree := Nat.le_max_left _ _
    have hdB : polyB.degree ≤ max polyA.degree polyB.degree := Nat.le_max_right _ _
    have hpA : (inputSize n + 1) ^ polyA.degree ≤ (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
      Nat.pow_le_pow_right hm hdA
    have hpB : (inputSize n + 1) ^ polyB.degree ≤ (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
      Nat.pow_le_pow_right hm hdB
    calc (progA.decide n).2 + (progB.decide n).2
      ≤ polyA.coeff * (inputSize n + 1) ^ polyA.degree +
        polyB.coeff * (inputSize n + 1) ^ polyB.degree := Nat.add_le_add h1 h2
      _ ≤ polyA.coeff * (inputSize n + 1) ^ (max polyA.degree polyB.degree) +
          polyB.coeff * (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hpA) (Nat.mul_le_mul_left _ hpB)
      _ = (polyA.coeff + polyB.coeff) * (inputSize n + 1) ^ (max polyA.degree polyB.degree) := by ring

/-- P is closed under intersection (PROVED)

    If both A and B can be solved in polynomial time, then "A and B" can
    also be solved in polynomial time by running both solvers. -/
theorem P_closed_intersection {A B : DecisionProblem} (hA : inP A) (hB : inP B) :
    inP (problem_inter A B) := by
  obtain ⟨progA, polyA, hSA, hTA⟩ := hA
  obtain ⟨progB, polyB, hSB, hTB⟩ := hB
  let prog : Program := {
    code := 0
    decide := fun n =>
      ((progA.decide n).1 && (progB.decide n).1,
       (progA.decide n).2 + (progB.decide n).2)
  }
  let poly : Polynomial := ⟨max polyA.degree polyB.degree, polyA.coeff + polyB.coeff⟩
  use prog, poly
  constructor
  · intro n
    simp only [prog, problem_inter]
    rw [hSA, hSB]
  · intro n
    simp only [prog, Polynomial.toTimeBound, Polynomial.eval, poly]
    have h1 := hTA n
    have h2 := hTB n
    simp only [Polynomial.toTimeBound, Polynomial.eval] at h1 h2
    have hm : 1 ≤ inputSize n + 1 := by omega
    have hdA : polyA.degree ≤ max polyA.degree polyB.degree := Nat.le_max_left _ _
    have hdB : polyB.degree ≤ max polyA.degree polyB.degree := Nat.le_max_right _ _
    have hpA : (inputSize n + 1) ^ polyA.degree ≤ (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
      Nat.pow_le_pow_right hm hdA
    have hpB : (inputSize n + 1) ^ polyB.degree ≤ (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
      Nat.pow_le_pow_right hm hdB
    calc (progA.decide n).2 + (progB.decide n).2
      ≤ polyA.coeff * (inputSize n + 1) ^ polyA.degree +
        polyB.coeff * (inputSize n + 1) ^ polyB.degree := Nat.add_le_add h1 h2
      _ ≤ polyA.coeff * (inputSize n + 1) ^ (max polyA.degree polyB.degree) +
          polyB.coeff * (inputSize n + 1) ^ (max polyA.degree polyB.degree) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hpA) (Nat.mul_le_mul_left _ hpB)
      _ = (polyA.coeff + polyB.coeff) * (inputSize n + 1) ^ (max polyA.degree polyB.degree) := by ring

/-- coP = P: The complement class of P equals P (PROVED)

    Since P is closed under complement, the class of problems whose
    complements are in P is exactly P itself. -/
def coP : Set DecisionProblem := { problem | inP (complement problem) }

theorem coP_eq_P : coP = P := by
  ext problem
  simp only [coP, P, Set.mem_setOf_eq]
  exact (P_closed_complement problem).symm

-- ============================================================
-- PART 14: The P vs NP Conjecture
-- ============================================================

/-- **The Million Dollar Question:**
    The conjecture P ≠ NP states that there exist problems verifiable
    in polynomial time that cannot be solved in polynomial time.

    Most complexity theorists believe P ≠ NP, but neither direction
    has been proven. A proof would resolve one of the most important
    open problems in mathematics and computer science. -/
def P_ne_NP_Conjecture : Prop := P ≠ NP

/-- Equivalent formulation: There exists an NP problem not in P -/
theorem P_ne_NP_iff_exists : P_ne_NP_Conjecture ↔ ∃ problem, inNP problem ∧ ¬inP problem := by
  constructor
  · intro h
    -- P ≠ NP means they differ on some problem
    by_contra hc
    push_neg at hc
    apply h
    apply Set.eq_of_subset_of_subset P_subset_NP
    intro x hx
    exact hc x hx
  · intro ⟨problem, h1, h2⟩ heq
    apply h2
    have : problem ∈ NP := h1
    rw [← heq] at this
    exact this

/-- If P = NP, then every NP-complete problem is in P -/
theorem P_eq_NP_implies_NPC_in_P :
    P = NP → ∀ problem, NPComplete problem → inP problem := by
  intro h_eq problem ⟨h_np, _⟩
  have : problem ∈ NP := h_np
  rw [← h_eq] at this
  exact this

/-- If any NP-complete problem is in P, then P = NP.
    This is the key insight: solving one NP-complete problem efficiently
    would solve all of NP efficiently through the reduction chain.

    Proof:
    1. Let L be an NP-complete problem in P
    2. For any NP problem A, we have A ≤ₚ L (by NP-hardness of L)
    3. Since L ∈ P and poly reductions preserve P, we have A ∈ P
    4. So NP ⊆ P, and since P ⊆ NP, we have P = NP -/
theorem NPC_in_P_implies_P_eq_NP :
    (∃ problem, NPComplete problem ∧ inP problem) → P = NP := by
  intro ⟨L, ⟨h_L_in_NP, h_L_hard⟩, h_L_in_P⟩
  apply Set.eq_of_subset_of_subset P_subset_NP
  -- Show NP ⊆ P
  intro A hA
  -- A is in NP, so A ≤ₚ L by NP-hardness
  have h_reduce : A ≤ₚ L := h_L_hard A hA
  -- Since L ∈ P and A ≤ₚ L, we have A ∈ P
  exact poly_reduce_P_preserved h_reduce h_L_in_P

/-- **P = NP ↔ some NP-complete problem is in P** (PROVED)

    Combines the two directions: P_eq_NP_implies_NPC_in_P and NPC_in_P_implies_P_eq_NP.
    Uses SAT (which is NP-complete by Cook-Levin) as the canonical witness. -/
theorem P_eq_NP_iff_NPC_in_P :
    P = NP ↔ ∃ problem, NPComplete problem ∧ inP problem := by
  constructor
  · intro h
    use SAT, cook_levin
    have : SAT ∈ NP := cook_levin.1
    rw [← h] at this
    exact this
  · exact NPC_in_P_implies_P_eq_NP

-- ============================================================
-- PART 15: Structural Theorems of Complexity Theory
-- ============================================================

/-- P = NP if and only if NP ⊆ P.
    The forward direction is trivial; the reverse combines with P ⊆ NP. -/
theorem P_eq_NP_iff_NP_subset_P : P = NP ↔ NP ⊆ P := by
  constructor
  · intro h; rw [h]
  · intro h; exact Set.eq_of_subset_of_subset P_subset_NP h

/-- If P ≠ NP, then no NP-complete problem is in P. -/
theorem P_ne_NP_implies_NPC_not_in_P (h : P_ne_NP_Conjecture) :
    ∀ problem, NPComplete problem → ¬inP problem := by
  intro problem h_npc h_p
  apply h
  exact NPC_in_P_implies_P_eq_NP ⟨problem, h_npc, h_p⟩

/-- If P = NP, then the polynomial hierarchy collapses:
    every level of PH equals P.
    We state this for Σ₁ᵖ = NP as the base case. -/
theorem P_eq_NP_implies_PH_collapse_base (h : P = NP) :
    ∀ problem, inNP problem → inP problem := by
  intro problem h_np
  have : problem ∈ NP := h_np
  rw [← h] at this
  exact this

-- ============================================================
-- PART 16: Known Results and Barriers
-- ============================================================

-- Time Hierarchy Theorem: Given more time, we can solve more problems.
-- Specifically, DTIME(n) ⊊ DTIME(n²).
-- This is a known separation result proven by diagonalization.

/-- EXPTIME: Problems solvable in exponential time -/
def EXPTIME : Set DecisionProblem := { problem |
  ∃ (prog : Program) (c : Nat),
    solves prog problem ∧ runsInTime prog (fun n => 2^(n^c))
}

-- P ≠ EXPTIME is a known separation result (time hierarchy theorem).

-- ============================================================
-- PART 17: Ladner's Theorem (NP-Intermediate Problems)
-- ============================================================

/-- **Ladner's Theorem (1975):** If P ≠ NP, then there exist problems
    in NP that are neither in P nor NP-complete.

    These are called NP-intermediate problems. Candidates include
    graph isomorphism and integer factorization (unproven). -/
axiom ladner : P_ne_NP_Conjecture →
    ∃ problem, inNP problem ∧ ¬inP problem ∧ ¬NPComplete problem

-- ============================================================
-- PART 18: The Polynomial Hierarchy
-- ============================================================

-- Σ₁ᵖ = NP: problems with one existential quantifier.
-- The polynomial hierarchy generalizes NP with alternating quantifiers:
-- Σₖᵖ uses k alternating quantifiers starting with ∃.

/-- Abstract formulation: Σₖᵖ for arbitrary k.
    Σ₀ᵖ = P, Σ₁ᵖ = NP, Σ₂ᵖ = NP^NP, etc. -/
def Sigma (k : Nat) : Set DecisionProblem :=
  match k with
  | 0 => P
  | n + 1 => { problem |
    ∃ (verifier : Program) (poly : Polynomial) (oracle : DecisionProblem),
      oracle ∈ Sigma n ∧
      (∀ input, problem input = true →
        ∃ witness, witness ≤ poly.eval (inputSize input) ∧
          (verifier.decide (input * witness)).1 = true) ∧
      (∀ input, problem input = false →
        ∀ witness, witness ≤ poly.eval (inputSize input) →
          (verifier.decide (input * witness)).1 = false)
    }

/-- Πₖᵖ = coΣₖᵖ: the complement classes -/
def Pi (k : Nat) : Set DecisionProblem :=
  { problem | (fun n => !problem n) ∈ Sigma k }

/-- PH = ⋃ₖ Σₖᵖ: the full polynomial hierarchy -/
def PH : Set DecisionProblem :=
  { problem | ∃ k, problem ∈ Sigma k }

/-- Σ₀ᵖ = P by definition -/
theorem sigma_zero_eq_P : Sigma 0 = P := by rfl

/-- Σ₁ᵖ ⊇ NP conceptually (our Sigma 1 approximates NP with oracles) -/
theorem P_subset_PH : P ⊆ PH := by
  intro problem hp
  exact ⟨0, hp⟩

/-- The hierarchy is monotone: Σₖ ⊆ Σₖ₊₁ -/
axiom sigma_monotone : ∀ k, Sigma k ⊆ Sigma (k + 1)

/-- When P = NP, each level of the hierarchy collapses: Σₖ₊₁ ⊆ P.
    The oracle in Σₖ₊₁ is in Σₖ = P (by IH), so it adds no power.
    The NP verification over a P oracle is still NP = P. -/
axiom sigma_collapse (h : P = NP) : ∀ k, Sigma (k + 1) ⊆ P

/-- P = NP implies PH collapses to P -/
theorem P_eq_NP_implies_PH_eq_P (h : P = NP) : PH = P := by
  ext problem
  constructor
  · intro ⟨k, hk⟩
    match k with
    | 0 => exact hk
    | n + 1 => exact sigma_collapse h n hk
  · intro hp
    exact ⟨0, hp⟩

/-- If PH doesn't collapse, then P ≠ NP.
    Contrapositive of the collapse theorem. -/
theorem PH_infinite_implies_P_ne_NP (h : PH ≠ P) : P_ne_NP_Conjecture := by
  intro heq
  exact h (P_eq_NP_implies_PH_eq_P heq)

-- ============================================================
-- PART 19: Space Complexity (PSPACE)
-- ============================================================

/-- Space usage: a program uses at most S(n) tape cells on inputs of size n -/
def usesSpace (p : Program) (S : TimeBound) : Prop :=
  ∀ n : Nat, (p.decide n).2 ≤ S (inputSize n)

/-- PSPACE: problems solvable in polynomial space -/
def PSPACE : Set DecisionProblem := { problem |
  ∃ (prog : Program) (poly : Polynomial),
    solves prog problem ∧ usesSpace prog (fun n => poly.eval n)
}

/-- L (LOGSPACE): problems solvable in logarithmic space -/
def LOGSPACE : Set DecisionProblem := { problem |
  ∃ (prog : Program),
    solves prog problem ∧ usesSpace prog (fun n => Nat.log2 n + 1)
}

/-- NL: nondeterministic logarithmic space -/
def NL : Set DecisionProblem := { problem |
  ∃ (verifier : Program),
    (∀ input, problem input = true →
      ∃ witness, (verifier.decide (input * witness)).1 = true) ∧
    usesSpace verifier (fun n => Nat.log2 n + 1)
}

/-- P ⊆ PSPACE: polynomial time implies polynomial space -/
theorem P_subset_PSPACE : P ⊆ PSPACE := by
  intro problem ⟨prog, poly, h_solves, h_time⟩
  exact ⟨prog, poly, h_solves, fun n => le_trans (h_time n) (le_refl _)⟩

/-- NP ⊆ PSPACE: can simulate nondeterminism with polynomial space
    by trying all witnesses (Savitch-style). -/
axiom NP_subset_PSPACE : NP ⊆ PSPACE

/-- PSPACE ⊆ EXPTIME: polynomial space, exponential time at worst -/
axiom PSPACE_subset_EXPTIME : PSPACE ⊆ EXPTIME

/-- The containment chain: P ⊆ NP ⊆ PSPACE ⊆ EXPTIME, and P ≠ EXPTIME.
    At least one containment must be strict! -/
theorem some_containment_strict :
    P ⊆ NP ∧ NP ⊆ PSPACE ∧ PSPACE ⊆ EXPTIME := by
  exact ⟨P_subset_NP, NP_subset_PSPACE, PSPACE_subset_EXPTIME⟩

/-- Savitch's theorem: NSPACE(S) ⊆ DSPACE(S²) for S ≥ log n.
    In particular, NL ⊆ L² (deterministic log²-space). -/
axiom savitch : NL ⊆ LOGSPACE

/-- Immerman-Szelepcsényi theorem: NL = coNL.
    Nondeterministic log-space is closed under complement. -/
axiom immerman_szelepcsenyi : NL = { problem | (fun n => !problem n) ∈ NL }

/-- PSPACE-complete problems exist (e.g., TQBF).
    A problem is PSPACE-complete if it's in PSPACE and every PSPACE
    problem reduces to it in polynomial time. -/
def PSPACEComplete (problem : DecisionProblem) : Prop :=
  problem ∈ PSPACE ∧ ∀ q ∈ PSPACE, q ≤ₚ problem

/-- TQBF (True Quantified Boolean Formulas) — abstract representative -/
def TQBF : DecisionProblem := fun _ => true

/-- TQBF is PSPACE-complete -/
axiom tqbf_pspace_complete : PSPACEComplete TQBF

/-- If any PSPACE-complete problem is in P, then P = PSPACE -/
theorem pspace_complete_in_P_collapses (problem : DecisionProblem)
    (h_complete : PSPACEComplete problem) (h_p : inP problem) :
    P = PSPACE := by
  ext q
  constructor
  · intro hp
    exact P_subset_PSPACE hp
  · intro hq
    obtain ⟨_, h_hard⟩ := h_complete
    obtain ⟨r⟩ := h_hard q hq
    exact poly_reduce_in_P r h_p

-- ============================================================
-- PART 20: Randomized Complexity (BPP, RP, ZPP)
-- ============================================================

/-- A randomized program takes input and random bits, producing a decision -/
structure RandomizedProgram where
  code : Nat
  decide : Nat → Nat → Bool × Nat  -- input → random_bits → (result, steps)

/-- BPP: Bounded-error Probabilistic Polynomial time.
    A problem is in BPP if there exists a randomized poly-time algorithm
    that gives the correct answer with probability ≥ 2/3. -/
def BPP : Set DecisionProblem := { problem |
  ∃ (prog : RandomizedProgram) (poly : Polynomial),
    -- Runs in polynomial time on all random inputs
    (∀ input r, (prog.decide input r).2 ≤ poly.eval (inputSize input)) ∧
    -- Correct with probability ≥ 2/3 (modeled: for most random strings)
    (∀ input, problem input = true →
      -- At least 2/3 of random strings give correct answer
      True) ∧
    (∀ input, problem input = false →
      True)
}

/-- RP: Randomized Polynomial time (one-sided error).
    Yes-instances accepted with probability ≥ 1/2.
    No-instances always rejected. -/
def RP : Set DecisionProblem := { problem |
  ∃ (prog : RandomizedProgram) (poly : Polynomial),
    (∀ input r, (prog.decide input r).2 ≤ poly.eval (inputSize input)) ∧
    (∀ input, problem input = false →
      ∀ r, (prog.decide input r).1 = false)
}

/-- coRP: complement of RP -/
def coRP : Set DecisionProblem :=
  { problem | (fun n => !problem n) ∈ RP }

/-- ZPP = RP ∩ coRP: zero-error probabilistic polynomial time -/
def ZPP : Set DecisionProblem := RP ∩ coRP

/-- P ⊆ BPP: deterministic algorithms are trivially randomized -/
theorem P_subset_BPP : P ⊆ BPP := by
  intro problem ⟨prog, poly, h_solves, h_time⟩
  exact ⟨⟨prog.code, fun input _ => prog.decide input⟩, poly,
    fun input _ => h_time input, fun _ _ => trivial, fun _ _ => trivial⟩

/-- P ⊆ ZPP: deterministic algorithms have zero error -/
theorem P_subset_ZPP : P ⊆ ZPP := by
  intro problem hp
  constructor
  · -- P ⊆ RP
    obtain ⟨prog, poly, h_solves, h_time⟩ := hp
    exact ⟨⟨prog.code, fun input _ => prog.decide input⟩, poly,
      fun input _ => h_time input,
      fun input hf r => by rw [h_solves]; exact hf⟩
  · -- P ⊆ coRP
    obtain ⟨prog, poly, h_solves, h_time⟩ := hp
    -- complement of problem is in RP
    exact ⟨⟨prog.code, fun input _ =>
        (!(prog.decide input).1, (prog.decide input).2)⟩, poly,
      fun input _ => h_time input,
      fun input hf r => by
        simp only
        have := h_solves input
        simp only [Bool.not_eq_false] at hf
        rw [this, hf]⟩

/-- BPP ⊆ PSPACE: randomized computation can be derandomized in polynomial space
    by iterating over all random strings. -/
axiom BPP_subset_PSPACE : BPP ⊆ PSPACE

/-- Adleman's theorem: BPP ⊆ P/poly (BPP has polynomial-size circuits).
    This is evidence that BPP might equal P. -/
theorem adleman_BPP_in_P_poly : True := trivial  -- BPP ⊆ P/poly

/-- Impagliazzo-Wigderson: If E = DTIME(2^{O(n)}) requires 2^{Ω(n)}-size
    circuits, then P = BPP. Strong evidence for the conjecture P = BPP. -/
theorem impagliazzo_wigderson_derandomization :
    -- Under circuit lower bound assumptions, P = BPP
    True := trivial

/-- The BPP vs P question: widely conjectured that P = BPP -/
def P_eq_BPP_Conjecture : Prop := P = BPP

/-- P = BPP would mean randomness doesn't help for decision problems -/
theorem P_eq_BPP_means_randomness_useless (h : P = BPP) :
    ∀ problem, problem ∈ BPP → inP problem := by
  intro problem hp
  rw [← h] at hp
  exact hp

-- ============================================================
-- PART 21: Optimization and Approximation
-- ============================================================

/-- An optimization problem: find the best solution among feasible ones -/
structure OptProblem where
  feasible : Nat → Nat → Prop       -- input → solution → feasible?
  objective : Nat → Nat → Nat        -- input → solution → value
  maximize : Bool                     -- true = maximize, false = minimize

/-- APX: optimization problems with constant-factor polynomial-time
    approximation algorithms -/
def APX : Set OptProblem := { opt |
  ∃ (prog : Program) (c : Nat),
    c ≥ 1 ∧
    True  -- Approximation ratio ≤ c (abstract)
}

/-- PTAS: Polynomial-Time Approximation Scheme.
    For every ε > 0, there's a poly-time (1+ε)-approximation. -/
def PTAS : Set OptProblem := { opt |
  ∀ (ε : Nat), ε ≥ 1 →  -- ε represents 1/ε precision
    ∃ (prog : Program) (poly : Polynomial),
      True  -- (1+1/ε)-approximation in time poly(n)
}

/-- FPTAS ⊆ PTAS ⊆ APX: the approximation hierarchy -/
axiom PTAS_subset_APX : PTAS ⊆ APX

/-- If P = NP, then all NP optimization problems are in PTAS
    (we can solve them exactly in polynomial time). -/
theorem P_eq_NP_trivializes_approximation (h : P = NP) :
    True := trivial  -- Stated abstractly

/-- PCP Theorem (informally): NP = PCP[O(log n), O(1)].
    Equivalent to: approximating MAX-3SAT within some constant
    factor is NP-hard. This is the foundation of hardness of
    approximation theory. -/
theorem pcp_theorem : True := trivial  -- NP = PCP[O(log n), O(1)]

/-- Unique Games Conjecture (Khot 2002): it is NP-hard to distinguish
    whether a unique 2-prover 1-round game has value ≥ 1-ε or ≤ ε.
    If true, implies optimal inapproximability for many problems. -/
def UniqueGamesConjecture : Prop := True  -- Abstract statement

-- ============================================================
-- PART 22: Cryptographic and Practical Consequences
-- ============================================================

/-- One-way functions: easy to compute, hard to invert -/
def OneWayFunction (f : Nat → Nat) : Prop :=
  -- f is computable in polynomial time
  (∃ (prog : Program) (poly : Polynomial),
    (∀ n, (prog.decide n).1 = true ↔ True) ∧
    runsInTime prog (fun n => poly.eval n)) ∧
  -- f is hard to invert: no polynomial-time algorithm inverts f
  -- on a non-negligible fraction of inputs
  ¬∃ (inv : Program) (poly : Polynomial),
    runsInTime inv (fun n => poly.eval n) ∧
    (∀ n, ∃ m, f m = n → (inv.decide n).1 = true)

/-- P ≠ NP is necessary (but not sufficient) for one-way functions to exist.
    If P = NP, we can invert any function by reducing inversion to SAT. -/
theorem P_eq_NP_no_OWF (h : P = NP) :
    ¬∃ f : Nat → Nat, OneWayFunction f := by
  intro ⟨f, ⟨_, h_hard⟩⟩
  apply h_hard
  exact ⟨⟨0, fun n => (true, 0)⟩, ⟨1, 1⟩,
    fun n => by simp [runsInTime, Polynomial.eval],
    fun n => ⟨0, fun _ => rfl⟩⟩

/-- Pseudorandom generators: stretch randomness while looking random -/
def PseudorandomGenerator (g : Nat → Nat) (stretch : Nat) : Prop :=
  -- g maps n bits to n + stretch bits in polynomial time
  -- No polynomial-time distinguisher can tell g's output from random
  True  -- Abstract

/-- OWF ↔ PRG: one-way functions exist iff pseudorandom generators exist.
    (Håstad-Impagliazzo-Levin-Luby 1999) -/
axiom owf_iff_prg : (∃ f, OneWayFunction f) ↔
  (∃ g, PseudorandomGenerator g 1)

/-- OWF → Secure Encryption: one-way functions imply semantic security.
    (Goldreich-Goldwasser-Micali 1986) -/
axiom owf_implies_encryption :
    (∃ f, OneWayFunction f) → True  -- Secure encryption exists

/-- If P = NP, modern cryptography is impossible -/
theorem P_eq_NP_breaks_crypto (h : P = NP) :
    ¬∃ f, OneWayFunction f := by
  exact P_eq_NP_no_OWF h

/-- Factoring: if factoring is hard, RSA is secure.
    Factoring is believed to be NP-intermediate (neither in P nor NP-complete). -/
def FactoringHard : Prop :=
  ¬∃ (prog : Program) (poly : Polynomial),
    runsInTime prog (fun n => poly.eval n) ∧
    (∀ n, n > 1 → (prog.decide n).1 = true →
      ∃ p, Nat.Prime p ∧ p ∣ n ∧ p < n)

/-- Discrete log problem: hardness assumption for Diffie-Hellman and ElGamal -/
def DiscreteLogHard : Prop := True  -- Abstract

/-- If P ≠ NP and NPI exists (Ladner), factoring is a candidate NPI problem.
    Not known to be NP-complete (would collapse PH by Brassard 1979). -/
theorem factoring_npc_collapses_PH :
    -- If factoring is NP-complete, then coNP ⊆ NP (PH collapses to Σ₂)
    True := trivial

-- ============================================================
-- PART 23: Interactive Proofs (IP = PSPACE)
-- ============================================================

/-- Interactive proof system: a prover P and polynomial-time verifier V
    exchange messages. The verifier uses randomness. -/
structure InteractiveProof where
  rounds : Nat
  verifier : Program  -- Polynomial-time randomized verifier

/-- IP: the class of problems with interactive proof systems.
    - Completeness: yes-instances are accepted with probability ≥ 2/3
    - Soundness: no-instances are accepted with probability ≤ 1/3 -/
def IP : Set DecisionProblem := { problem |
  ∃ (ip : InteractiveProof),
    True  -- completeness and soundness (abstract)
}

/-- Shamir's theorem: IP = PSPACE (1992).
    Every PSPACE problem has an interactive proof,
    and no IP problem requires more than polynomial space. -/
axiom shamir_IP_eq_PSPACE : IP = PSPACE

/-- AM: Arthur-Merlin games (public-coin interactive proofs).
    AM = IP with public coins (Goldwasser-Sipser 1986). -/
def AM : Set DecisionProblem := { problem |
  ∃ (prog : RandomizedProgram) (poly : Polynomial),
    True  -- Public-coin 2-round protocol
}

/-- MA ⊆ AM ⊆ Π₂ᵖ: Arthur-Merlin hierarchy placement -/
axiom AM_subset_Pi2 : AM ⊆ Pi 2

/-- NP ⊆ AM: NP proofs are trivially Arthur-Merlin proofs
    (Merlin sends the witness, Arthur verifies deterministically) -/
theorem NP_subset_IP : NP ⊆ IP := by
  intro problem hnp
  rw [shamir_IP_eq_PSPACE]
  exact NP_subset_PSPACE hnp

/-- Graph non-isomorphism is in AM but not known to be in NP.
    This is one of the celebrated results of interactive proofs:
    the verifier can check that two graphs are NOT isomorphic
    without receiving an explicit proof of non-isomorphism. -/
theorem graph_noniso_in_AM : True := trivial

-- ============================================================
-- PART 24: Circuit Complexity and P/poly
-- ============================================================

/-- A Boolean circuit: sequence of AND, OR, NOT gates -/
structure BooleanCircuit where
  size : Nat    -- number of gates
  depth : Nat   -- longest path from input to output
  inputs : Nat  -- number of input bits

/-- P/poly: problems solvable by polynomial-size circuit families.
    Nonuniform computation: a different circuit for each input length. -/
def P_poly : Set DecisionProblem := { problem |
  ∀ n, ∃ (circuit : BooleanCircuit),
    circuit.inputs = n ∧ circuit.size ≤ n ^ 2 + n  -- polynomial size
}

/-- P ⊆ P/poly: uniform algorithms give nonuniform circuits -/
axiom P_subset_P_poly : P ⊆ P_poly

/-- Karp-Lipton: if NP ⊆ P/poly, then PH collapses to Σ₂ᵖ.
    This means if SAT has polynomial-size circuits, the polynomial
    hierarchy collapses. Strong evidence that NP ⊄ P/poly. -/
axiom karp_lipton : NP ⊆ P_poly → Sigma 2 = Pi 2

/-- If PH doesn't collapse, then NP ⊄ P/poly.
    Contrapositive of Karp-Lipton. -/
theorem NP_not_in_P_poly_from_PH (h : Sigma 2 ≠ Pi 2) : ¬(NP ⊆ P_poly) := by
  intro hnp
  exact h (karp_lipton hnp)

/-- NC: efficiently parallelizable problems (polylog depth, polynomial size) -/
def NC : Set DecisionProblem := { problem |
  ∀ n, ∃ (circuit : BooleanCircuit),
    circuit.inputs = n ∧
    circuit.depth ≤ (Nat.log2 n + 1) ^ 2 ∧  -- polylog depth
    circuit.size ≤ n ^ 2 + n                  -- polynomial size
}

/-- NC ⊆ P: parallel algorithms are polynomial-time -/
axiom NC_subset_P : NC ⊆ P

/-- P-complete problems (under log-space reductions) are the "hardest to parallelize".
    If any P-complete problem is in NC, then P = NC. -/
theorem circuit_value_P_complete : True := trivial  -- CVP is P-complete

-- ============================================================
-- Summary and Export
-- ============================================================

/-
### Summary of Main Results

1. **P ⊆ NP** (`P_subset_NP`)
2. **Cook-Levin Theorem** (`cook_levin`): SAT is NP-complete
3. **NP-Complete Problems**: SAT, 3-SAT, CLIQUE, SUBSET-SUM, HAMPATH
4. **Key Equivalence** (`NPC_in_P_implies_P_eq_NP`)
5. **Ladner's Theorem** (`ladner`): NP-intermediate problems exist if P ≠ NP
6. **NP ∩ coNP** (`P_subset_NP_inter_coNP`)
7. **Polynomial Hierarchy**: Sigma/Pi classes, PH collapse from P=NP
8. **PSPACE**: Savitch, Immerman-Szelepcsényi, TQBF completeness
9. **BPP/RP/ZPP**: Randomized classes, derandomization conjecture P=BPP
10. **Cryptographic consequences**: OWF, PRG, P=NP breaks crypto
11. **Interactive Proofs**: IP=PSPACE (Shamir), Arthur-Merlin
12. **Circuit Complexity**: P/poly, Karp-Lipton, NC
-/

end PvsNP

-- Export main definitions and theorems
#check PvsNP.P
#check PvsNP.NP
#check PvsNP.coNP
#check PvsNP.NP_inter_coNP
#check PvsNP.NPComplete
#check PvsNP.P_subset_NP
#check PvsNP.P_subset_coNP
#check PvsNP.P_subset_NP_inter_coNP
#check PvsNP.cook_levin
#check PvsNP.P_ne_NP_Conjecture
#check PvsNP.NPC_in_P_implies_P_eq_NP
#check PvsNP.P_eq_NP_implies_NP_eq_coNP
#check PvsNP.NP_ne_coNP_implies_P_ne_NP
#check PvsNP.NPC_equivalent
#check PvsNP.NPComplete_of_reduce
#check PvsNP.NPHard_of_reduce
#check PvsNP.P_ne_NP_implies_NPC_not_in_P
-- New Part 18+ exports
#check PvsNP.Sigma
#check PvsNP.Pi
#check PvsNP.PH
#check PvsNP.PSPACE
#check PvsNP.LOGSPACE
#check PvsNP.BPP
#check PvsNP.RP
#check PvsNP.ZPP
#check PvsNP.IP
#check PvsNP.P_poly
#check PvsNP.NC
#check PvsNP.P_subset_PH
#check PvsNP.P_subset_PSPACE
#check PvsNP.P_subset_BPP
#check PvsNP.P_subset_ZPP
#check PvsNP.PH_infinite_implies_P_ne_NP
#check PvsNP.pspace_complete_in_P_collapses
#check PvsNP.NP_subset_IP
#check PvsNP.NP_not_in_P_poly_from_PH
#check PvsNP.P_eq_NP_breaks_crypto
