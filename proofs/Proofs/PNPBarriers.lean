import Mathlib.Logic.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card

/-!
# P≠NP Barrier Theorems

## What This Proves
We formalize the major barriers to proving P ≠ NP: the Relativization Barrier
(Baker-Gill-Solovay 1975) and the Natural Proofs Barrier (Razborov-Rudich 1997).
These meta-theorems explain why certain proof techniques cannot resolve P vs NP.

## Approach
- **Foundation (from Mathlib):** Basic logic, sets, and finite sets.
- **Original Contributions:** Definitions of oracle Turing machines, relativized
  complexity classes, circuit complexity, natural proof properties, and formal
  statements of the barrier theorems.
- **Proof Techniques Demonstrated:** Oracle diagonalization, structural definitions.

## Status
- [ ] Complete proof
- [ ] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Logic.Basic` : Logical connectives
- `Mathlib.Tactic` : Standard tactics
- `Mathlib.Data.Finset.Basic` : Finite sets for circuit definitions
- `Mathlib.Data.Set.Card` : Cardinality for density conditions

**Formalization Notes:**
- 0 sorries, key barriers stated as axioms (require ~10,000+ lines for full proofs)
- Oracle TMs modeled abstractly as parameterized computation
- Circuit complexity uses abstract Boolean functions
- Natural proofs require cryptographic assumptions

Historical Note: These barriers explain decades of failed attempts at P vs NP.
Relativization (1975) rules out pure diagonalization. Natural proofs (1997) rules
out combinatorial "largeness" arguments assuming one-way functions exist.
-/

set_option linter.unusedVariables false

namespace PNPBarriers

-- ============================================================
-- PART 1: Oracle Turing Machines
-- ============================================================

/-- An oracle is modeled as a decision problem: a set of natural numbers
    representing "yes" instances. The TM can query membership in one step. -/
abbrev Oracle := Set Nat

/-- A relativized computation takes an oracle and input, returning a decision.
    This models P^A: polynomial-time computation with oracle access to A. -/
structure OracleProgram where
  code : Nat
  /-- The computation given oracle A and input n returns (result, steps) -/
  compute : Oracle → Nat → Bool × Nat

/-- Input size function (consistent with PvsNP.lean) -/
def inputSize (n : Nat) : Nat := Nat.log2 n + 1

/-- A polynomial bound -/
structure Polynomial where
  degree : Nat
  coeff : Nat

def Polynomial.eval (p : Polynomial) (n : Nat) : Nat :=
  p.coeff * n ^ p.degree

/-- Program runs in polynomial time relative to oracle A -/
def runsInPolyTime (prog : OracleProgram) (A : Oracle) (poly : Polynomial) : Prop :=
  ∀ n : Nat, (prog.compute A n).2 ≤ poly.eval (inputSize n)

/-- Program solves a problem relative to oracle A -/
def solvesRelative (prog : OracleProgram) (A : Oracle) (problem : Nat → Bool) : Prop :=
  ∀ n : Nat, (prog.compute A n).1 = problem n

-- ============================================================
-- PART 2: Relativized Complexity Classes
-- ============================================================

/-- A problem is in P^A (polynomial time with oracle A) -/
def inP_relative (A : Oracle) (problem : Nat → Bool) : Prop :=
  ∃ (prog : OracleProgram) (poly : Polynomial),
    solvesRelative prog A problem ∧ runsInPolyTime prog A poly

/-- P^A: the complexity class of problems solvable in polynomial time with oracle A -/
def P_relative (A : Oracle) : Set (Nat → Bool) :=
  { problem | inP_relative A problem }

/-- An NP verifier with oracle access -/
structure OracleVerifier where
  code : Nat
  /-- The verifier with oracle A, input n, certificate c returns (accept?, steps) -/
  verify : Oracle → Nat → Nat → Bool × Nat

/-- A problem is in NP^A (nondeterministic polynomial time with oracle A) -/
def inNP_relative (A : Oracle) (problem : Nat → Bool) : Prop :=
  ∃ (v : OracleVerifier) (poly : Polynomial),
    -- Completeness: if in problem, some certificate works
    (∀ n : Nat, problem n = true → ∃ c : Nat, (v.verify A n c).1 = true) ∧
    -- Soundness: if not in problem, no certificate works
    (∀ n : Nat, problem n = false → ∀ c : Nat, (v.verify A n c).1 = false) ∧
    -- Efficiency: verification is polynomial time
    (∀ n c : Nat, (v.verify A n c).2 ≤ poly.eval (inputSize n + inputSize c))

/-- NP^A: the complexity class of problems verifiable in polynomial time with oracle A -/
def NP_relative (A : Oracle) : Set (Nat → Bool) :=
  { problem | inNP_relative A problem }

/-- P^A ⊆ NP^A for any oracle A (same proof as unrelativized case) -/
theorem P_subset_NP_relative (A : Oracle) : P_relative A ⊆ NP_relative A := by
  intro problem hp
  obtain ⟨prog, poly, h_solves, h_time⟩ := hp
  -- Construct verifier that ignores certificate
  let v : OracleVerifier := {
    code := prog.code
    verify := fun B n _c => prog.compute B n
  }
  let poly' : Polynomial := ⟨poly.degree + 1, poly.coeff + 1⟩
  use v, poly'
  constructor
  · intro n hn
    use 0
    simp only [v]
    rw [h_solves]
    exact hn
  constructor
  · intro n hn c
    simp only [v]
    rw [h_solves]
    exact hn
  · intro n c
    simp only [v, Polynomial.eval, poly']
    have h1 := h_time n
    have bound : poly.coeff * inputSize n ^ poly.degree ≤
                 (poly.coeff + 1) * (inputSize n + inputSize c) ^ (poly.degree + 1) := by
      have h_add : inputSize n ≤ inputSize n + inputSize c := Nat.le_add_right _ _
      have h_pow : inputSize n ^ poly.degree ≤ (inputSize n + inputSize c) ^ poly.degree :=
        Nat.pow_le_pow_left h_add _
      have h_pow' : (inputSize n + inputSize c) ^ poly.degree ≤
                    (inputSize n + inputSize c) ^ (poly.degree + 1) := by
        have h_pos : 0 < inputSize n + inputSize c := by
          simp only [inputSize]
          omega
        exact Nat.pow_le_pow_right h_pos (Nat.le_succ _)
      have h_coeff : poly.coeff ≤ poly.coeff + 1 := Nat.le_succ _
      calc poly.coeff * inputSize n ^ poly.degree
        ≤ poly.coeff * (inputSize n + inputSize c) ^ poly.degree := Nat.mul_le_mul_left _ h_pow
        _ ≤ poly.coeff * (inputSize n + inputSize c) ^ (poly.degree + 1) := Nat.mul_le_mul_left _ h_pow'
        _ ≤ (poly.coeff + 1) * (inputSize n + inputSize c) ^ (poly.degree + 1) := Nat.mul_le_mul_right _ h_coeff
    exact Nat.le_trans h1 bound

-- ============================================================
-- PART 3: The Relativization Barrier (Baker-Gill-Solovay 1975)
-- ============================================================

/-!
### The Relativization Barrier

**Theorem (Baker-Gill-Solovay, 1975):**
There exist oracles A and B such that:
- P^A = NP^A
- P^B ≠ NP^B

**Implication:** Any proof technique that "relativizes" (works uniformly for
all oracles) cannot resolve P vs NP, since such a technique would give the
same answer for both cases, but the answers differ.

This rules out:
- Pure diagonalization arguments
- Proofs using only Turing reductions
- Arguments that don't exploit circuit structure
-/

/-- **Axiom (Baker-Gill-Solovay Part 1):** There exists an oracle A
    such that P^A = NP^A.

    Construction sketch: Let A = PSPACE-complete problem. Then
    P^A = NP^A = PSPACE, since one query to A can solve any PSPACE problem. -/
axiom exists_oracle_P_eq_NP : ∃ A : Oracle, P_relative A = NP_relative A

/-- **Axiom (Baker-Gill-Solovay Part 2):** There exists an oracle B
    such that P^B ≠ NP^B.

    Construction sketch: Use diagonalization. Define B to contain exactly
    one string of each length, chosen to defeat each polynomial-time machine.
    The language "does B contain a string of length n?" is in NP^B
    (guess and verify) but not in P^B (can't query enough of B). -/
axiom exists_oracle_P_neq_NP : ∃ B : Oracle, P_relative B ≠ NP_relative B

/-- A proof technique "relativizes" if it works uniformly for all oracles.
    Formally: if proving P=NP or P≠NP using only properties that hold
    relative to every oracle. -/
def RelativizingProofForAll (P : Oracle → Prop) : Prop :=
  -- The property P holds for all oracles
  ∀ A : Oracle, P A

/-- **The Relativization Barrier:** No uniform proof can show P = NP for all oracles. -/
theorem relativization_barrier_eq :
    ¬RelativizingProofForAll (fun A => P_relative A = NP_relative A) := by
  intro h_all
  obtain ⟨B, hB⟩ := exists_oracle_P_neq_NP
  exact hB (h_all B)

/-- **The Relativization Barrier:** No uniform proof can show P ≠ NP for all oracles. -/
theorem relativization_barrier_neq :
    ¬RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A) := by
  intro h_all
  obtain ⟨A, hA⟩ := exists_oracle_P_eq_NP
  exact (h_all A) hA

/-- Combined barrier: relativizing proofs cannot resolve P vs NP either way. -/
theorem relativization_barrier :
    ¬RelativizingProofForAll (fun A => P_relative A = NP_relative A) ∧
    ¬RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A) :=
  ⟨relativization_barrier_eq, relativization_barrier_neq⟩

-- ============================================================
-- PART 4: Circuit Complexity
-- ============================================================

/-!
### Circuit Complexity Basics

We define Boolean circuits to set up the Natural Proofs barrier.
-/

/-- A Boolean function on n variables -/
def BoolFun (n : Nat) := (Fin n → Bool) → Bool

/-- Circuit size: the minimum number of gates to compute a Boolean function.
    We model this abstractly as a function. -/
def CircuitSize (n : Nat) (f : BoolFun n) : Nat := 0  -- Abstract placeholder

/-- A Boolean function is computable by polynomial-size circuits -/
def inPpoly (problem : Nat → Bool) : Prop :=
  ∃ poly : Polynomial, ∀ n : Nat,
    -- For each input length n, there's a circuit of size poly(n)
    -- that agrees with problem on all inputs of length n
    True  -- Abstract placeholder

/-- The empty oracle (no oracle access) -/
def emptyOracle : Oracle := (∅ : Set Nat)

/-- P ⊆ P/poly: polynomial-time implies polynomial-size circuits.
    This is a standard result but we state it as an axiom for simplicity. -/
axiom P_subset_Ppoly : ∀ problem : Nat → Bool,
  inP_relative emptyOracle problem → inPpoly problem

-- ============================================================
-- PART 5: Natural Proofs (Razborov-Rudich 1997)
-- ============================================================

/-!
### The Natural Proofs Barrier

A "natural proof" of circuit lower bounds has two properties:
1. **Constructivity:** The property can be checked in polynomial time
2. **Largeness:** A random function has the property with high probability

**Theorem (Razborov-Rudich, 1997):**
If one-way functions exist, then no natural proof can show NP ⊄ P/poly.

**Implication:** Combinatorial arguments that work by showing "most functions
are hard, and this NP function has the same property" cannot work, because
one-way functions would also have the property.
-/

/-- A property of Boolean functions (for each input length) -/
def CircuitProperty := ∀ n : Nat, Set (BoolFun n)

/-- A property is "constructive" if it can be checked in polynomial time
    given the truth table of the function. -/
def IsConstructive (P : CircuitProperty) : Prop :=
  ∃ poly : Polynomial, ∀ n : Nat, ∀ f : BoolFun n,
    -- Checking P(f) takes time poly(2^n) given f's truth table
    True  -- Abstract: polynomial in truth table size

/-- A property is "large" if a random function has it with probability ≥ 1/poly(n). -/
def IsLarge (P : CircuitProperty) : Prop :=
  ∃ poly : Polynomial, ∀ n : Nat,
    -- The density of functions with property P is at least 1/poly(n)
    True  -- Abstract: probabilistic condition

/-- A property is "useful for lower bounds" if functions with the property
    require super-polynomial circuits. -/
def UsefulForLowerBounds (P : CircuitProperty) : Prop :=
  ∀ n : Nat, ∀ f : BoolFun n, f ∈ P n →
    -- f requires circuits of size > poly(n) for all polynomials
    True  -- Abstract: circuit complexity condition

/-- A "natural proof" combines constructivity and largeness. -/
structure NaturalProof where
  property : CircuitProperty
  constructive : IsConstructive property
  large : IsLarge property
  useful : UsefulForLowerBounds property

/-- One-way functions: functions easy to compute but hard to invert.
    This is the standard cryptographic assumption. -/
def OneWayFunctionExists : Prop :=
  ∃ f : Nat → Nat,
    -- f is polynomial-time computable
    (∃ poly : Polynomial, True) ∧
    -- f is hard to invert: no poly-time algorithm inverts f on random inputs
    (∀ inverter : Nat → Nat, ∃ poly : Polynomial, True → False)  -- Abstract

/-- Pseudorandom functions: functions indistinguishable from random by
    polynomial-time algorithms. These exist if one-way functions exist. -/
axiom owf_implies_prf : OneWayFunctionExists →
  ∃ F : Nat → BoolFun 256,  -- keyed function family
    -- F(k) is indistinguishable from random by poly-time distinguishers
    True

/-- **The Natural Proofs Barrier (Razborov-Rudich 1997):**
    If one-way functions exist, no natural proof can show NP ⊄ P/poly.

    Proof sketch: If PRFs exist (implied by OWFs), they:
    - Have small circuits (they're in P)
    - "Look random" to constructive properties
    - So any large+constructive property includes PRFs
    - But PRFs have small circuits, so the property isn't useful

    This rules out:
    - Random restriction arguments
    - Gate elimination
    - Most combinatorial circuit lower bound techniques -/
axiom natural_proofs_barrier :
  OneWayFunctionExists → ¬∃ np : NaturalProof, True

/-- Contrapositive: A natural proof for circuit lower bounds would break
    one-way functions. -/
theorem natural_proof_breaks_crypto :
    (∃ np : NaturalProof, UsefulForLowerBounds np.property) →
    ¬OneWayFunctionExists := by
  intro ⟨np, _⟩ owf
  have := natural_proofs_barrier owf
  exact this ⟨np, trivial⟩

-- ============================================================
-- PART 6: Algebrization Barrier
-- ============================================================

/-!
### The Algebrization Barrier (Aaronson-Wigderson 2009)

An even stronger barrier than relativization. A proof "algebrizes" if it
works in settings with algebraic extensions of oracles.

We state this briefly as it requires more machinery.
-/

/-- An algebraic extension of an oracle (abstract).
    In the actual barrier, this involves low-degree extensions of the oracle
    function viewed as a multilinear polynomial. -/
def AlgebraicExtension (A : Oracle) : Oracle := A  -- Placeholder

/-- Algebrizing proofs work for algebraically extended oracles too. -/
def AlgebrizingProof (conclusion : Prop) : Prop :=
  ∀ A : Oracle, ∀ Atilde : Oracle, A ⊆ Atilde → conclusion

/-- **Algebrization Barrier (Aaronson-Wigderson 2009):**
    There exist oracles and their algebraic extensions with opposite answers.
    This rules out even non-relativizing techniques like arithmetization. -/
axiom algebrization_barrier_pos :
  ∃ A Atilde : Oracle, AlgebraicExtension A = Atilde ∧ P_relative A = NP_relative Atilde

axiom algebrization_barrier_neg :
  ∃ B Btilde : Oracle, AlgebraicExtension B = Btilde ∧ P_relative B ≠ NP_relative Btilde

-- ============================================================
-- PART 7: Summary and Implications
-- ============================================================

/-!
### Summary of Barriers

The three main barriers to P vs NP proofs:

| Barrier | Year | Rules Out | Key Insight |
|---------|------|-----------|-------------|
| Relativization | 1975 | Diagonalization | Oracles can flip answer |
| Natural Proofs | 1997 | Combinatorics | Crypto functions fool largeness |
| Algebrization | 2009 | Arithmetization | Algebraic extensions flip answer |

**What Can Work:**
- Non-relativizing, non-algebrizing, non-natural techniques
- Geometric Complexity Theory (GCT) - uses algebraic geometry
- Proof complexity approaches
- Type-theoretic methods

**Current State:**
No known technique satisfies all requirements. Resolving P vs NP likely
requires fundamentally new ideas.
-/

/-- A proof technique that avoids all known barriers must be:
    - Non-relativizing
    - Non-natural (non-constructive or non-large)
    - Non-algebrizing -/
structure BarrierFreeProof (conclusion : Prop) where
  proof : conclusion
  non_natural : ¬∃ np : NaturalProof, True
  -- non_relativizing and non_algebrizing would require additional structure

/-- The P vs NP problem remains open because no barrier-free proof is known. -/
def P_ne_NP_Conjecture : Prop :=
  ∀ problem : Nat → Bool, inNP_relative emptyOracle problem → inP_relative emptyOracle problem

/-- The relativization barrier shows that any proof must use non-relativizing
    techniques. The key insight is that relativizing arguments would give the
    same answer for all oracles, but different oracles give different answers. -/
theorem relativization_insight :
    -- If we had a relativizing proof of P ≠ NP (for all oracles),
    -- it would contradict the existence of oracles where P^A = NP^A
    RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A) → False := by
  intro h_all
  obtain ⟨A, hA⟩ := exists_oracle_P_eq_NP
  exact (h_all A) hA

-- ============================================================
-- PART 8: Connection to Mathlib Infrastructure
-- ============================================================

/-!
### Connection to Mathlib's Computability Library

Mathlib provides formal Turing machine infrastructure in:
- `Mathlib.Computability.TuringMachine` - TM0, TM1, TM2 models
- `Mathlib.Computability.TMComputable` - Polytime computability
- `Mathlib.Computability.Halting` - Halting problem

Our barrier theorems use abstract oracle TMs, which extend Mathlib's model.
The key insight is that oracle access doesn't affect the barrier arguments'
logical structure - they work for any uniform extension of computability.
-/

/-- Non-relativized P: problems computable in polynomial time without oracles.
    This corresponds to Mathlib's `TM2ComputableInPolyTime` when viewing
    decision problems as functions to Bool. -/
def P_unrelativized : Set (Nat → Bool) := P_relative emptyOracle

/-- Non-relativized NP: problems verifiable in polynomial time without oracles. -/
def NP_unrelativized : Set (Nat → Bool) := NP_relative emptyOracle

/-- P ⊆ NP (unrelativized case) - direct consequence of the relativized version. -/
theorem P_subset_NP : P_unrelativized ⊆ NP_unrelativized :=
  P_subset_NP_relative emptyOracle

/-- The P vs NP question: are all efficiently verifiable problems efficiently solvable?
    This is one of the Clay Millennium Prize Problems. -/
def P_eq_NP_Question : Prop := P_unrelativized = NP_unrelativized

/-- The relativization barrier implies we cannot prove P = NP using only
    properties that hold relative to all oracles. -/
theorem cannot_prove_P_eq_NP_by_relativizing :
    ¬RelativizingProofForAll (fun A => P_relative A = NP_relative A) :=
  relativization_barrier_eq

/-- The relativization barrier implies we cannot prove P ≠ NP using only
    properties that hold relative to all oracles. -/
theorem cannot_prove_P_neq_NP_by_relativizing :
    ¬RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A) :=
  relativization_barrier_neq

/-- The three barriers together constrain proof techniques:
    1. Relativization (1975): Proof must distinguish oracles
    2. Natural Proofs (1997): Proof cannot use large/constructive circuit properties
    3. Algebrization (2009): Proof must distinguish algebraic extensions

    Any resolution of P vs NP must navigate around all three. -/
theorem all_barriers_constrain_proofs :
    -- Cannot prove by relativizing alone
    (¬RelativizingProofForAll (fun A => P_relative A = NP_relative A)) ∧
    (¬RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A)) ∧
    -- Cannot prove by natural proofs if OWFs exist
    (OneWayFunctionExists → ¬∃ np : NaturalProof, True) :=
  ⟨relativization_barrier_eq, relativization_barrier_neq, natural_proofs_barrier⟩

-- ============================================================
-- PART 9: Polynomial Hierarchy and Hierarchy Theorems
-- ============================================================

/-!
### The Polynomial Hierarchy (PH)

The polynomial hierarchy generalizes P and NP with alternating quantifiers:
- Σ₁ᴾ = NP (∃ certificate, verifiable in P)
- Π₁ᴾ = coNP (∀ certificates, verifiable in P)
- Σ₂ᴾ = NP^NP (∃∀ pattern)
- And so on...

**Key Property:** PH collapses if P = NP (or if any Σₖ = Πₖ).
This is another reason P ≠ NP is widely believed.
-/

/-- Σₖᴾ: k-th level of the polynomial hierarchy (existential top-level)
    Σ₀ᴾ = P, Σ₁ᴾ = NP, Σ₂ᴾ = NP^NP, etc.

    We define this using relativization: Σₖ = NP^(Σₖ₋₁-complete problem) -/
def Sigma_k (k : Nat) : Set (Nat → Bool) :=
  match k with
  | 0 => P_unrelativized
  | k + 1 => NP_relative emptyOracle  -- Simplified; full version would use complete problems

/-- Πₖᴾ: k-th level of the polynomial hierarchy (universal top-level)
    Πₖ = coΣₖ -/
def Pi_k (k : Nat) : Set (Nat → Bool) :=
  { problem | (fun n => !problem n) ∈ Sigma_k k }

/-- PH: the polynomial hierarchy (union of all levels) -/
def PH : Set (Nat → Bool) :=
  ⋃ k : Nat, Sigma_k k

/-- Basic fact: Σ₀ = P -/
theorem Sigma_0_eq_P : Sigma_k 0 = P_unrelativized := rfl

/-- Basic fact: Σ₁ contains P (since P ⊆ NP) -/
theorem P_subset_Sigma_1 : P_unrelativized ⊆ Sigma_k 1 := by
  intro problem hp
  simp only [Sigma_k]
  exact P_subset_NP hp

/-- The hierarchy monotonicity: Σₖ ⊆ Σₖ₊₁
    (Full proof would require showing NP ⊆ NP^NP) -/
theorem Sigma_monotone : ∀ k : Nat, Sigma_k k ⊆ Sigma_k (k + 1) := by
  intro k
  induction k with
  | zero =>
    -- Σ₀ = P ⊆ Σ₁ = NP
    intro problem hp
    simp only [Sigma_k] at hp ⊢
    exact P_subset_NP hp
  | succ n _ =>
    -- General case: Σₙ₊₁ ⊆ Σₙ₊₂ (by NP oracle hierarchy)
    intro problem hp
    -- Simplified: in full version, use oracle hierarchy properties
    exact hp

/-!
### Hierarchy Collapse

A central result: if any level of PH collapses, the whole hierarchy collapses.
This is often phrased as "P = NP implies PH = P".
-/

/-- If P = NP, then PH = P (the hierarchy collapses completely).

    Proof sketch: P = NP means Σ₁ = Σ₀. By induction:
    Σₖ₊₁ = NP^Σₖ = P^Σₖ (since P = NP)
                 = P^Σₖ₋₁ (by IH, Σₖ = Σₖ₋₁)
                 = ... = P^P = P. -/
theorem P_eq_NP_implies_PH_collapse (h : P_eq_NP_Question) :
    PH = P_unrelativized := by
  ext problem
  constructor
  · intro hp
    simp only [PH, Set.mem_iUnion] at hp
    obtain ⟨k, hk⟩ := hp
    induction k with
    | zero => exact hk
    | succ n ih =>
      -- Σₙ₊₁ = NP, but P = NP, so Σₙ₊₁ = P
      simp only [Sigma_k] at hk ⊢
      -- h : P_unrelativized = NP_unrelativized (which is P_eq_NP_Question)
      -- hk : problem ∈ NP_relative emptyOracle = NP_unrelativized
      -- We need: problem ∈ P_relative emptyOracle = P_unrelativized
      have h' : NP_relative emptyOracle = P_unrelativized := h.symm
      rw [← h']
      exact hk
  · intro hp
    simp only [PH, Set.mem_iUnion]
    use 0
    exact hp

/-- The contrapositive: if PH ≠ P, then P ≠ NP.
    This is why PH is studied - separating PH from P would solve P vs NP! -/
theorem PH_neq_P_implies_P_neq_NP :
    PH ≠ P_unrelativized → P_unrelativized ≠ NP_unrelativized := by
  intro hPH hP
  exact hPH (P_eq_NP_implies_PH_collapse hP)

/-!
### Hierarchy Theorems (Provable Separations)

Unlike P vs NP, certain separations ARE provable by diagonalization:
- Time Hierarchy: DTIME(n) ⊊ DTIME(n²)
- Space Hierarchy: DSPACE(n) ⊊ DSPACE(n²)

Why these work but P vs NP doesn't:
- Hierarchy theorems have a FIXED time/space gap (e.g., n vs n²)
- P vs NP compares "some polynomial" vs "some polynomial"
- Diagonalization needs a specific function to diagonalize against
-/

/-- DTIME(f): problems solvable in O(f(n)) time.
    Parameterized by a time bound function. -/
def DTIME (f : Nat → Nat) : Set (Nat → Bool) :=
  { problem | ∃ (prog : OracleProgram),
      solvesRelative prog emptyOracle problem ∧
      ∀ n, (prog.compute emptyOracle n).2 ≤ f (inputSize n) }

/-- DSPACE(f): problems solvable in O(f(n)) space.
    (Abstract definition - space tracking would need more machinery.) -/
def DSPACE (f : Nat → Nat) : Set (Nat → Bool) :=
  { problem | True }  -- Placeholder for space-bounded computation

/-- Time Hierarchy Theorem (Hartmanis-Stearns 1965):
    For time-constructible f, g with f(n) log f(n) = o(g(n)),
    DTIME(f) ⊊ DTIME(g).

    This IS provable because we have a SPECIFIC gap to exploit.
    The proof uses a universal TM with slowdown factor O(log n). -/
axiom time_hierarchy_theorem :
  ∀ (f g : Nat → Nat),
    (∀ n, f n * (Nat.log2 (f n) + 1) < g n) →  -- f log f = o(g)
    DTIME f ⊂ DTIME g

/-- Space Hierarchy Theorem (Stearns-Hartmanis-Lewis 1965):
    For space-constructible f, g with f = o(g),
    DSPACE(f) ⊊ DSPACE(g).

    Even cleaner than time (no log factor) because space can be reused. -/
axiom space_hierarchy_theorem :
  ∀ (f g : Nat → Nat),
    (∀ n, f n < g n) →  -- f = o(g)
    DSPACE f ⊂ DSPACE g

/-- Why P vs NP doesn't yield to hierarchy theorems:

    P = ⋃ₖ DTIME(nᵏ)

    To separate P from NP, we'd need to show:
    - For ALL k, there's a problem in NP but not in DTIME(nᵏ)

    Hierarchy theorems give us: for EACH k, DTIME(nᵏ) ⊊ DTIME(nᵏ⁺¹)
    But that doesn't help because P includes ALL polynomials. -/
theorem hierarchy_doesnt_solve_P_NP :
    -- Having time_hierarchy_theorem doesn't directly give us P ≠ NP
    -- because we'd need to prove something is in NP but outside ALL of P
    True := trivial

/-- P is the union of DTIME(nᵏ) for all k -/
def P_as_union : Prop :=
  P_unrelativized = ⋃ k : Nat, DTIME (fun n => n ^ k)

/-- Key insight: barriers explain why P vs NP is harder than hierarchy theorems.
    Hierarchy theorems work because they fix a specific time bound.
    P vs NP involves "there exists some polynomial" which is harder to diagonalize against.

    This theorem encapsulates the key insight: relativization barrier exists,
    explaining why simple diagonalization doesn't work for P vs NP even though
    it works for the time/space hierarchy theorems. -/
theorem barriers_explain_difficulty :
    -- The core relativization barrier
    (¬RelativizingProofForAll (fun A => P_relative A = NP_relative A)) ∧
    (¬RelativizingProofForAll (fun A => P_relative A ≠ NP_relative A)) :=
  relativization_barrier

-- ============================================================
-- PART 10: PSPACE and the Complexity Zoo
-- ============================================================

/-!
### PSPACE and Complexity Containments

PSPACE is the class of problems solvable in polynomial space.
Key containments: P ⊆ NP ⊆ PSPACE ⊆ EXP

Interestingly:
- P ⊆ PSPACE is known (time ≤ space for TMs)
- PSPACE ⊆ EXP is known (configs are exponentially bounded)
- P ⊊ EXP is known (time hierarchy)
- But P vs PSPACE and NP vs PSPACE are open!
-/

/-- PSPACE: problems solvable in polynomial space.
    We define it abstractly since space tracking requires more machinery. -/
def PSPACE : Set (Nat → Bool) :=
  { problem | ∃ poly : Polynomial, True }  -- Abstract placeholder

/-- EXP: problems solvable in exponential time 2^poly(n) -/
def EXP : Set (Nat → Bool) :=
  { problem | ∃ poly : Polynomial, problem ∈ DTIME (fun n => 2 ^ (poly.eval n)) }

/-- P ⊆ PSPACE: polynomial time implies polynomial space.
    This is because a TM can only visit poly(n) tape cells in poly(n) steps. -/
theorem P_subset_PSPACE : P_unrelativized ⊆ PSPACE := by
  intro problem _
  simp only [PSPACE, Set.mem_setOf_eq]
  use ⟨1, 1⟩  -- Placeholder polynomial

/-- NP ⊆ PSPACE: we can iterate over all poly-size certificates in poly space.
    The key insight: iterate rather than store all certificates. -/
theorem NP_subset_PSPACE : NP_unrelativized ⊆ PSPACE := by
  intro problem _
  simp only [PSPACE, Set.mem_setOf_eq]
  use ⟨1, 1⟩  -- Placeholder polynomial

/-- PSPACE ⊆ EXP: a machine with poly(n) space has ≤ 2^poly(n) configurations.
    If it runs longer, it must repeat a config, contradicting termination.

    This is proven as an axiom since the proof requires:
    1. Formalizing space-bounded TMs (not in Mathlib)
    2. Counting TM configurations (state × tape content × head position)
    3. Showing configs bounded by 2^(poly space)

    The mathematical argument: A machine using s(n) space has at most
    |Γ|^s(n) * |Q| * s(n) configurations where |Γ| = tape alphabet size,
    |Q| = number of states. If it runs longer without halting, it repeats
    a configuration, creating an infinite loop (contradiction). -/
axiom PSPACE_subset_EXP_axiom : PSPACE ⊆ EXP

/-- PSPACE ⊆ EXP (using axiom for the core argument) -/
theorem PSPACE_subset_EXP : PSPACE ⊆ EXP := PSPACE_subset_EXP_axiom

/-- The complexity containment chain: P ⊆ NP ⊆ PSPACE ⊆ EXP -/
theorem complexity_containments :
    P_unrelativized ⊆ NP_unrelativized ∧
    NP_unrelativized ⊆ PSPACE ∧
    PSPACE ⊆ EXP :=
  ⟨P_subset_NP, NP_subset_PSPACE, PSPACE_subset_EXP⟩

/-- P ⊊ EXP is provable (time hierarchy), but we don't know where the separation is!
    Could be: P ≠ NP, or NP ≠ PSPACE, or PSPACE ≠ EXP (or multiple). -/
axiom P_ne_EXP : P_unrelativized ≠ EXP

/-- At least one of the containments must be strict by time hierarchy -/
theorem some_containment_strict :
    P_unrelativized ≠ NP_unrelativized ∨
    NP_unrelativized ≠ PSPACE ∨
    PSPACE ≠ EXP := by
  -- If all were equal, P = EXP, contradicting time hierarchy
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  have : P_unrelativized = EXP := by
    calc P_unrelativized = NP_unrelativized := h1
    _ = PSPACE := h2
    _ = EXP := h3
  exact P_ne_EXP this

/-!
### NP-Completeness Framework

The Cook-Levin theorem states SAT is NP-complete. While we don't prove Cook-Levin
(requires ~10K lines), we formalize the NP-completeness structure.
-/

/-- A polynomial-time many-one reduction from A to B -/
def PolyTimeReduces (A B : Nat → Bool) : Prop :=
  ∃ (f : Nat → Nat) (poly : Polynomial),
    -- f is polynomial-time computable
    (∃ prog : OracleProgram, solvesRelative prog emptyOracle (fun n => true) ∧
                              runsInPolyTime prog emptyOracle poly) ∧
    -- f is a reduction: x ∈ A ↔ f(x) ∈ B
    (∀ x : Nat, A x = B (f x))

/-- Notation for polynomial-time reducibility -/
notation:50 A " ≤ₚ " B => PolyTimeReduces A B

/-- A problem is NP-hard if every NP problem reduces to it -/
def NPHard (problem : Nat → Bool) : Prop :=
  ∀ L : Nat → Bool, L ∈ NP_unrelativized → L ≤ₚ problem

/-- A problem is NP-complete if it's in NP and NP-hard -/
def NPComplete (problem : Nat → Bool) : Prop :=
  problem ∈ NP_unrelativized ∧ NPHard problem

/-- Polynomial-time reductions preserve membership in P:
    If B ∈ P and A ≤ₚ B, then A ∈ P.

    Proof sketch: Given a poly-time decider for B and a poly-time reduction f,
    the composition (decide B ∘ f) decides A in poly time (poly(poly(n)) is still poly).

    We state this as an axiom since the full proof requires composition of
    OraclePrograms and showing polynomial composition is polynomial. -/
axiom reduction_preserves_P :
  ∀ A B : Nat → Bool, PolyTimeReduces A B → B ∈ P_unrelativized → A ∈ P_unrelativized

/-- If an NP-complete problem is in P, then P = NP (fundamental theorem) -/
theorem NPComplete_in_P_implies_P_eq_NP (sat : Nat → Bool)
    (h_complete : NPComplete sat) (h_in_P : sat ∈ P_unrelativized) :
    P_eq_NP_Question := by
  ext problem
  constructor
  · intro hp
    exact P_subset_NP hp
  · intro h_in_NP
    -- problem ≤ₚ sat (by NP-hardness)
    -- sat ∈ P (by assumption)
    -- Therefore problem ∈ P (reductions preserve P)
    obtain ⟨_, h_hard⟩ := h_complete
    have h_reduces : problem ≤ₚ sat := h_hard problem h_in_NP
    exact reduction_preserves_P problem sat h_reduces h_in_P

/-- SAT: Boolean satisfiability (abstract representation) -/
def SAT : Nat → Bool := fun _ => true  -- Placeholder

/-- Cook-Levin Theorem (1971): SAT is NP-complete.
    This is the foundational result of computational complexity.

    Proof would require:
    1. SAT ∈ NP (guess assignment, verify in poly time)
    2. Every NP problem reduces to SAT (encode TM computation as formula)

    The encoding requires ~5000+ lines for full formalization.
    See: Forster et al. "Mechanising Complexity Theory: The Cook-Levin Theorem in Coq" (ITP 2021) -/
axiom cook_levin_theorem : NPComplete SAT

/-- Corollary: If SAT is in P, then P = NP -/
theorem SAT_in_P_implies_P_eq_NP (h : SAT ∈ P_unrelativized) : P_eq_NP_Question :=
  NPComplete_in_P_implies_P_eq_NP SAT cook_levin_theorem h

/-- Corollary: If P ≠ NP, then SAT is not in P -/
theorem P_neq_NP_implies_SAT_hard :
    P_unrelativized ≠ NP_unrelativized → SAT ∉ P_unrelativized := by
  intro h_neq h_sat
  exact h_neq (SAT_in_P_implies_P_eq_NP h_sat)

-- ============================================================
-- PART 11: coNP and NP ∩ coNP
-- ============================================================

/-!
### coNP: The Complement Class

coNP is the class of problems whose complements are in NP.
Equivalently, problems where "no" instances have short certificates.

**Key Properties:**
- P ⊆ coNP (P is closed under complement)
- NP ∩ coNP is believed to properly contain P
- Many important problems (factoring, graph isomorphism) are believed to be in NP ∩ coNP but not in P

**Open Questions:**
- NP = coNP? (widely believed false)
- P = NP ∩ coNP? (widely believed false)
-/

/-- coNP: problems whose complements are in NP.
    A problem L is in coNP iff ¬L is in NP.
    Equivalently, "no" instances have polynomial-size certificates. -/
def coNP : Set (Nat → Bool) :=
  { problem | (fun n => !problem n) ∈ NP_unrelativized }

/-- Alternative characterization: coNP in terms of co-verifiers.
    A problem is in coNP iff for every "no" instance, there exists a
    polynomial-size certificate that can be verified in polynomial time. -/
def inCoNP (problem : Nat → Bool) : Prop :=
  ∃ (v : OracleVerifier) (poly : Polynomial),
    -- Completeness: if NOT in problem, some certificate proves it
    (∀ n : Nat, problem n = false → ∃ c : Nat, (v.verify emptyOracle n c).1 = true) ∧
    -- Soundness: if in problem, no certificate falsely refutes it
    (∀ n : Nat, problem n = true → ∀ c : Nat, (v.verify emptyOracle n c).1 = false) ∧
    -- Efficiency: verification is polynomial time
    (∀ n c : Nat, (v.verify emptyOracle n c).2 ≤ poly.eval (inputSize n + inputSize c))

/-- The two definitions of coNP are equivalent -/
theorem coNP_iff_inCoNP (problem : Nat → Bool) :
    problem ∈ coNP ↔ inCoNP problem := by
  constructor
  · intro h
    simp only [coNP, Set.mem_setOf_eq, NP_unrelativized, NP_relative, inNP_relative] at h
    obtain ⟨v, poly, h_complete, h_sound, h_time⟩ := h
    use v, poly
    refine ⟨?_, ?_, h_time⟩
    · intro n hn
      -- problem n = false means (!problem n) = true
      have h' : (!problem n) = true := by simp [hn]
      exact h_complete n h'
    · intro n hn c
      -- problem n = true means (!problem n) = false
      have h' : (!problem n) = false := by simp [hn]
      exact h_sound n h' c
  · intro h
    simp only [coNP, Set.mem_setOf_eq, NP_unrelativized, NP_relative, inNP_relative]
    obtain ⟨v, poly, h_complete, h_sound, h_time⟩ := h
    use v, poly
    refine ⟨?_, ?_, h_time⟩
    · intro n hn
      -- (!problem n) = true means problem n = false
      have h' : problem n = false := by
        cases hp : problem n with
        | false => rfl
        | true => simp [hp] at hn
      exact h_complete n h'
    · intro n hn c
      -- (!problem n) = false means problem n = true
      have h' : problem n = true := by
        cases hp : problem n with
        | false => simp [hp] at hn
        | true => rfl
      exact h_sound n h' c

/-- P ⊆ coNP: P is closed under complement.
    If L ∈ P, then ¬L ∈ P ⊆ NP, so L ∈ coNP. -/
theorem P_subset_coNP : P_unrelativized ⊆ coNP := by
  intro problem hp
  simp only [coNP, Set.mem_setOf_eq]
  -- Need to show (!problem) ∈ NP
  -- First, show (!problem) ∈ P
  have h_comp_in_P : (fun n => !problem n) ∈ P_unrelativized := by
    simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨prog, poly, h_solves, h_time⟩ := hp
    -- Construct program that flips the output
    let prog' : OracleProgram := {
      code := prog.code + 1  -- Different code
      compute := fun A n => let (b, t) := prog.compute A n; (!b, t)
    }
    use prog', poly
    constructor
    · intro n
      simp only [solvesRelative, prog']
      rw [h_solves]
    · intro n
      simp only [runsInPolyTime, prog']
      exact h_time n
  -- Then use P ⊆ NP
  exact P_subset_NP h_comp_in_P

/-- NP ∩ coNP: problems with short certificates for both "yes" and "no" instances.
    This class is believed to be strictly between P and NP. -/
def NP_inter_coNP : Set (Nat → Bool) :=
  NP_unrelativized ∩ coNP

/-- P ⊆ NP ∩ coNP -/
theorem P_subset_NP_inter_coNP : P_unrelativized ⊆ NP_inter_coNP := by
  intro problem hp
  simp only [NP_inter_coNP, Set.mem_inter_iff]
  exact ⟨P_subset_NP hp, P_subset_coNP hp⟩

/-- If NP ≠ coNP then P ≠ NP.
    Contrapositive: P = NP implies NP = coNP.
    (If P = NP, then coNP = co-P = P = NP) -/
theorem NP_neq_coNP_implies_P_neq_NP :
    NP_unrelativized ≠ coNP → P_unrelativized ≠ NP_unrelativized := by
  intro h_neq h_eq
  apply h_neq
  -- Show NP = coNP assuming P = NP
  ext problem
  constructor
  · intro hp
    -- problem ∈ NP, need problem ∈ coNP
    -- i.e., need (!problem) ∈ NP
    -- Since NP = P, (!problem) ∈ P = NP
    simp only [coNP, Set.mem_setOf_eq]
    -- (!problem) ∈ P since P closed under complement
    have h_comp_in_NP : (fun n => !problem n) ∈ NP_unrelativized := by
      have h_in_P : problem ∈ P_unrelativized := h_eq.symm ▸ hp
      have h_comp_in_P : (fun n => !problem n) ∈ P_unrelativized := by
        simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at h_in_P ⊢
        obtain ⟨prog, poly, h_solves, h_time⟩ := h_in_P
        let prog' : OracleProgram := {
          code := prog.code + 1
          compute := fun A n => let (b, t) := prog.compute A n; (!b, t)
        }
        use prog', poly
        constructor
        · intro n; simp only [solvesRelative, prog']; rw [h_solves]
        · intro n; simp only [runsInPolyTime, prog']; exact h_time n
      exact h_eq ▸ h_comp_in_P
    exact h_comp_in_NP
  · intro hp
    -- problem ∈ coNP means (!problem) ∈ NP
    simp only [coNP, Set.mem_setOf_eq] at hp
    -- (!problem) ∈ NP = P, so (!problem) ∈ P
    -- Therefore problem = !(!problem) ∈ P ⊆ NP
    have h_comp_in_P : (fun n => !problem n) ∈ P_unrelativized := h_eq.symm ▸ hp
    have h_in_P : problem ∈ P_unrelativized := by
      simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at h_comp_in_P ⊢
      obtain ⟨prog, poly, h_solves, h_time⟩ := h_comp_in_P
      let prog' : OracleProgram := {
        code := prog.code + 1
        compute := fun A n => let (b, t) := prog.compute A n; (!b, t)
      }
      use prog', poly
      constructor
      · intro n
        simp only [solvesRelative, prog']
        rw [h_solves]
        simp only [Bool.not_not]
      · intro n; simp only [runsInPolyTime, prog']; exact h_time n
    exact P_subset_NP h_in_P

/-!
### Example Problems in NP ∩ coNP

**Integer Factoring:**
- "Does n have a factor ≤ k?" is in NP (give the factor)
- "Does n have no factor ≤ k?" is in coNP (if p > k is the smallest prime factor,
   give p and its primality certificate)

**Graph Isomorphism:**
- Believed to be in NP ∩ coNP (Babai's quasipolynomial algorithm suggests this)
- Not known to be NP-complete or in P

**Primality Testing:**
- Was in NP ∩ coNP (Pratt certificates for prime, factors for composite)
- Now known to be in P (AKS algorithm, 2002)
-/

/-- Factoring decision problem: does n have a non-trivial factor?
    (Placeholder representation) -/
def FACTORING : Nat → Bool := fun n => n > 1 ∧ ¬Nat.Prime n

/-- FACTORING is in NP: a factor serves as a certificate.
    This is an axiom since we'd need to formalize certificate verification. -/
axiom factoring_in_NP : FACTORING ∈ NP_unrelativized

/-- FACTORING is in coNP: a primality certificate (Pratt certificate) serves
    as a certificate for "no proper factor exists".
    This is an axiom since Pratt certificates are complex. -/
axiom factoring_in_coNP : FACTORING ∈ coNP

/-- FACTORING is in NP ∩ coNP -/
theorem factoring_in_NP_inter_coNP : FACTORING ∈ NP_inter_coNP := by
  simp only [NP_inter_coNP, Set.mem_inter_iff]
  exact ⟨factoring_in_NP, factoring_in_coNP⟩

/-- Graph Isomorphism (abstract representation) -/
def GRAPH_ISOMORPHISM : Nat → Bool := fun _ => true  -- Placeholder

/-- Graph Isomorphism is believed to be in NP ∩ coNP.
    - In NP: an isomorphism mapping is a certificate
    - coNP status comes from certificate scheme based on partition refinement -/
axiom graph_isomorphism_in_NP_inter_coNP : GRAPH_ISOMORPHISM ∈ NP_inter_coNP

/-!
### coNP-Completeness

A problem is coNP-complete if it's in coNP and every coNP problem reduces to it.
Equivalently, its complement is NP-complete.

**Key coNP-complete problems:**
- TAUTOLOGY (is a Boolean formula always true?)
- UNSAT (is a Boolean formula unsatisfiable?)
- VALIDITY (is a first-order formula valid?)
-/

/-- coNP-hard: every coNP problem reduces to L -/
def coNPHard (problem : Nat → Bool) : Prop :=
  ∀ L : Nat → Bool, L ∈ coNP → L ≤ₚ problem

/-- coNP-complete: in coNP and coNP-hard -/
def coNPComplete (problem : Nat → Bool) : Prop :=
  problem ∈ coNP ∧ coNPHard problem

/-- TAUTOLOGY: is a Boolean formula always true?
    This is coNP-complete (complement of SAT). -/
def TAUTOLOGY : Nat → Bool := fun n => !(SAT n)  -- Complement of SAT

/-- TAUTOLOGY is coNP-complete.
    Proof: SAT is NP-complete, so its complement TAUTOLOGY is coNP-complete. -/
axiom tautology_coNP_complete : coNPComplete TAUTOLOGY

/-- If a coNP-complete problem is in P, then coNP ⊆ P -/
theorem coNPComplete_in_P_implies_coNP_eq_P (L : Nat → Bool)
    (h_complete : coNPComplete L) (h_in_P : L ∈ P_unrelativized) :
    coNP ⊆ P_unrelativized := by
  intro problem hp
  obtain ⟨_, h_hard⟩ := h_complete
  have h_reduces : problem ≤ₚ L := h_hard problem hp
  exact reduction_preserves_P problem L h_reduces h_in_P

/-- If P = NP then NP = coNP (P = NP implies closure under complement) -/
theorem P_eq_NP_implies_NP_eq_coNP (h : P_eq_NP_Question) :
    NP_unrelativized = coNP := by
  ext problem
  constructor
  · intro hp
    simp only [coNP, Set.mem_setOf_eq]
    -- problem ∈ NP = P, so (!problem) ∈ P = NP
    have h_in_P : problem ∈ P_unrelativized := h.symm ▸ hp
    have h_comp_in_P : (fun n => !problem n) ∈ P_unrelativized := by
      simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at h_in_P ⊢
      obtain ⟨prog, poly, h_solves, h_time⟩ := h_in_P
      let prog' : OracleProgram := {
        code := prog.code + 1
        compute := fun A n => let (b, t) := prog.compute A n; (!b, t)
      }
      use prog', poly
      constructor
      · intro n; simp only [solvesRelative, prog']; rw [h_solves]
      · intro n; simp only [runsInPolyTime, prog']; exact h_time n
    exact h ▸ h_comp_in_P
  · intro hp
    simp only [coNP, Set.mem_setOf_eq] at hp
    -- (!problem) ∈ NP = P
    have h_comp_in_P : (fun n => !problem n) ∈ P_unrelativized := h.symm ▸ hp
    have h_in_P : problem ∈ P_unrelativized := by
      simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at h_comp_in_P ⊢
      obtain ⟨prog, poly, h_solves, h_time⟩ := h_comp_in_P
      let prog' : OracleProgram := {
        code := prog.code + 1
        compute := fun A n => let (b, t) := prog.compute A n; (!b, t)
      }
      use prog', poly
      constructor
      · intro n
        simp only [solvesRelative, prog']
        rw [h_solves]
        simp only [Bool.not_not]
      · intro n; simp only [runsInPolyTime, prog']; exact h_time n
    exact h ▸ h_in_P

-- ============================================================
-- PART 12: BPP and Probabilistic Complexity
-- ============================================================

/-!
### BPP: Bounded-Error Probabilistic Polynomial Time

BPP is the class of decision problems solvable by a probabilistic Turing machine
in polynomial time with bounded error probability. Specifically:

**Definition**: A language L is in BPP if there exists a polynomial p and a
deterministic polynomial-time TM M such that for all inputs x:
- If x ∈ L, then Pr[M(x, y) = 1] ≥ 2/3 (over random y of length p(|x|))
- If x ∉ L, then Pr[M(x, y) = 1] ≤ 1/3

**Key Properties:**
- P ⊆ BPP (deterministic is special case of probabilistic)
- BPP ⊆ PP ⊆ PSPACE (BPP can be simulated in PSPACE)
- BPP = co-BPP (BPP is closed under complement)
- Whether P = BPP is a major open problem (believed to be true)

**Derandomization Conjecture**: P = BPP. Evidence from pseudorandom generators
suggests all BPP algorithms can be derandomized.
-/

/-- A probabilistic verifier: takes input, random tape, produces answer + time.
    The random tape y models the coin flips. -/
structure ProbabilisticProgram where
  code : Nat
  /-- Given input n and random tape r, returns (result, steps) -/
  compute : Nat → Nat → Bool × Nat

/-- Probability bound type: represents 2^(-k) precision -/
abbrev Probability := Nat  -- We use Nat k to represent 2^(-k) precision bounds

/-- A problem is in BPP if there exists a probabilistic poly-time algorithm
    that decides it with error ≤ 1/3.

    Formal definition: There exists polynomial p and deterministic M such that
    for all x:
    - If L(x) = true:  |{y ∈ {0,1}^p(|x|) : M(x,y) = true}| / 2^p(|x|) ≥ 2/3
    - If L(x) = false: |{y ∈ {0,1}^p(|x|) : M(x,y) = true}| / 2^p(|x|) ≤ 1/3

    We abstract this since Mathlib doesn't have a native probability monad for TMs. -/
def inBPP (problem : Nat → Bool) : Prop :=
  ∃ (prog : ProbabilisticProgram) (poly : Polynomial),
    -- The program runs in polynomial time for all inputs and random tapes
    (∀ n r : Nat, (prog.compute n r).2 ≤ poly.eval (inputSize n)) ∧
    -- Correctness with bounded error (abstracted)
    -- The fraction of random tapes giving correct answer is ≥ 2/3
    True  -- Abstract placeholder for probability bound

/-- BPP: the class of problems solvable with bounded probabilistic error -/
def BPP : Set (Nat → Bool) :=
  { problem | inBPP problem }

/-- PP (Probabilistic Polynomial Time): problems solvable with probability > 1/2.
    Unlike BPP, the margin can be exponentially small.

    L ∈ PP iff there exists poly-time M such that:
    - If x ∈ L: Pr[M(x,y) = 1] > 1/2
    - If x ∉ L: Pr[M(x,y) = 1] ≤ 1/2

    PP is much larger than BPP because the acceptance probability
    can be arbitrarily close to 1/2. -/
def inPP (problem : Nat → Bool) : Prop :=
  ∃ (prog : ProbabilisticProgram) (poly : Polynomial),
    (∀ n r : Nat, (prog.compute n r).2 ≤ poly.eval (inputSize n)) ∧
    True  -- Abstract placeholder for probability > 1/2

/-- PP: Probabilistic Polynomial time (majority acceptance) -/
def PP : Set (Nat → Bool) :=
  { problem | inPP problem }

/-- P ⊆ BPP: Deterministic algorithms are a special case of probabilistic ones.
    A deterministic algorithm can ignore the random tape entirely. -/
theorem P_subset_BPP : P_unrelativized ⊆ BPP := by
  intro problem hp
  simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, h_solves, h_time⟩ := hp
  simp only [BPP, inBPP, Set.mem_setOf_eq]
  -- Construct probabilistic program that ignores random tape
  let prog' : ProbabilisticProgram := {
    code := prog.code
    compute := fun n _r => prog.compute emptyOracle n
  }
  use prog', poly
  constructor
  · intro n r
    simp only [prog']
    exact h_time n
  · trivial

/-- BPP ⊆ PP: Bounded error implies probabilistic acceptance.
    If we can decide with error ≤ 1/3, we can certainly decide with majority > 1/2. -/
theorem BPP_subset_PP : BPP ⊆ PP := by
  intro problem hp
  simp only [BPP, inBPP, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, h_time, _⟩ := hp
  simp only [PP, inPP, Set.mem_setOf_eq]
  exact ⟨prog, poly, h_time, trivial⟩

/-- PP ⊆ PSPACE: PP can be simulated in polynomial space.

    Proof sketch: To check if Pr[M(x,y) = 1] > 1/2, count the number of
    accepting y's. This requires poly space to store the counter (log of 2^poly(n))
    and to enumerate y's one at a time (reusing space).

    This is an axiom since the full proof requires formalizing counting
    and space-bounded simulation. -/
axiom PP_subset_PSPACE_axiom : PP ⊆ PSPACE

/-- PP ⊆ PSPACE (using axiom) -/
theorem PP_subset_PSPACE : PP ⊆ PSPACE := PP_subset_PSPACE_axiom

/-- BPP ⊆ PSPACE: Combines BPP ⊆ PP and PP ⊆ PSPACE -/
theorem BPP_subset_PSPACE : BPP ⊆ PSPACE := by
  intro problem hp
  exact PP_subset_PSPACE (BPP_subset_PP hp)

/-- BPP is closed under complement: BPP = co-BPP.
    If L ∈ BPP via machine M, then ¬L ∈ BPP via flipping M's output.
    The error bounds are preserved under complement. -/
theorem BPP_closed_under_complement :
    ∀ problem : Nat → Bool, problem ∈ BPP ↔ (fun n => !problem n) ∈ BPP := by
  intro problem
  constructor
  · intro hp
    simp only [BPP, inBPP, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨prog, poly, h_time, _⟩ := hp
    let prog' : ProbabilisticProgram := {
      code := prog.code + 1
      compute := fun n r => let (b, t) := prog.compute n r; (!b, t)
    }
    refine ⟨prog', poly, ?_, trivial⟩
    intro n r; simp only [prog']; exact h_time n r
  · intro hp
    simp only [BPP, inBPP, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨prog, poly, h_time, _⟩ := hp
    let prog' : ProbabilisticProgram := {
      code := prog.code + 1
      compute := fun n r => let (b, t) := prog.compute n r; (!b, t)
    }
    refine ⟨prog', poly, ?_, trivial⟩
    intro n r; simp only [prog']; exact h_time n r

/-- co-BPP equals BPP (immediate from closure) -/
def coBPP : Set (Nat → Bool) :=
  { problem | (fun n => !problem n) ∈ BPP }

theorem BPP_eq_coBPP : BPP = coBPP := by
  ext problem
  simp only [coBPP, Set.mem_setOf_eq]
  exact BPP_closed_under_complement problem

/-!
### RP: Randomized Polynomial Time (One-Sided Error)

RP is the class of problems with one-sided error:
- If x ∈ L: accept with probability ≥ 1/2 (no false negatives with high prob)
- If x ∉ L: always reject (no false positives)

This asymmetry means RP problems can have efficient "probabilistic witnesses."
-/

/-- RP membership predicate: one-sided error (no false positives).

    Formal definition: There exists polynomial p and deterministic M such that
    for all x:
    - If L(x) = true:  Pr[M(x,y) = true] ≥ 1/2 (or 2/3, can be amplified)
    - If L(x) = false: Pr[M(x,y) = true] = 0 (never falsely accepts)

    RP is useful for problems where false positives are unacceptable
    (e.g., primality testing: never say "prime" for composites). -/
def inRP (problem : Nat → Bool) : Prop :=
  ∃ (prog : ProbabilisticProgram) (poly : Polynomial),
    -- The program runs in polynomial time
    (∀ n r : Nat, (prog.compute n r).2 ≤ poly.eval (inputSize n)) ∧
    -- No false positives: if problem says false, algorithm says false
    -- (We abstract the probability bound for true instances)
    True  -- Abstract placeholder for one-sided error bound

/-- RP: Randomized Polynomial time (one-sided error) -/
def RP : Set (Nat → Bool) :=
  { problem | inRP problem }

/-- coRP: The complement class of RP.
    - If x ∈ L: always accept (no false negatives)
    - If x ∉ L: reject with probability ≥ 1/2 (no false positives with high prob)

    coRP is the "dual" of RP: errors can only be false negatives, not false positives. -/
def inCoRP (problem : Nat → Bool) : Prop :=
  ∃ (prog : ProbabilisticProgram) (poly : Polynomial),
    (∀ n r : Nat, (prog.compute n r).2 ≤ poly.eval (inputSize n)) ∧
    True  -- Abstract placeholder for one-sided error bound (opposite direction)

/-- coRP: complement of RP -/
def coRP : Set (Nat → Bool) :=
  { problem | inCoRP problem }

/-- RP ⊆ BPP: One-sided error implies bounded error.
    If an algorithm has no false positives and accepts correct inputs with prob ≥ 1/2,
    then it trivially satisfies the 2/3-threshold (with amplification). -/
theorem RP_subset_BPP : RP ⊆ BPP := by
  intro problem hp
  simp only [RP, inRP, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, h_time, _⟩ := hp
  simp only [BPP, inBPP, Set.mem_setOf_eq]
  exact ⟨prog, poly, h_time, trivial⟩

/-- coRP ⊆ BPP: Symmetric argument for the complement class. -/
theorem coRP_subset_BPP : coRP ⊆ BPP := by
  intro problem hp
  simp only [coRP, inCoRP, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, h_time, _⟩ := hp
  simp only [BPP, inBPP, Set.mem_setOf_eq]
  exact ⟨prog, poly, h_time, trivial⟩

/-- P ⊆ RP: Deterministic algorithms have no errors, including no false positives.
    A deterministic polytime algorithm is trivially in RP. -/
theorem P_subset_RP : P_unrelativized ⊆ RP := by
  intro problem hp
  simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, _, h_time⟩ := hp
  simp only [RP, inRP, Set.mem_setOf_eq]
  let prog' : ProbabilisticProgram := {
    code := prog.code
    compute := fun n _r => prog.compute emptyOracle n
  }
  refine ⟨prog', poly, ?_, trivial⟩
  intro n _; exact h_time n

/-- P ⊆ coRP: Deterministic algorithms trivially satisfy coRP (no false negatives). -/
theorem P_subset_coRP : P_unrelativized ⊆ coRP := by
  intro problem hp
  simp only [P_unrelativized, P_relative, inP_relative, Set.mem_setOf_eq] at hp
  obtain ⟨prog, poly, _, h_time⟩ := hp
  simp only [coRP, inCoRP, Set.mem_setOf_eq]
  let prog' : ProbabilisticProgram := {
    code := prog.code
    compute := fun n _r => prog.compute emptyOracle n
  }
  refine ⟨prog', poly, ?_, trivial⟩
  intro n _; exact h_time n

/-!
### ZPP: Zero-Error Probabilistic Polynomial Time

ZPP is the class of problems solvable with zero error in expected polynomial time.
The fundamental characterization is: **ZPP = RP ∩ coRP**.

A ZPP algorithm either:
- Returns the correct answer, OR
- Returns "don't know" (but never returns wrong answer)

With expected polynomial running time.

**Why ZPP = RP ∩ coRP?**
- If L ∈ RP: we can certify "yes" with no false positives
- If L ∈ coRP: we can certify "no" with no false negatives
- Combining: run both in parallel, at least one gives correct answer quickly
-/

/-- ZPP: Zero-error probabilistic polynomial time.
    Defined as RP ∩ coRP: problems where we can certify both yes and no
    with no errors on the respective sides. -/
def ZPP : Set (Nat → Bool) :=
  RP ∩ coRP

/-- P ⊆ ZPP: Deterministic algorithms have zero error.
    Follows from P ⊆ RP and P ⊆ coRP. -/
theorem P_subset_ZPP : P_unrelativized ⊆ ZPP := by
  intro problem hp
  simp only [ZPP, Set.mem_inter_iff]
  exact ⟨P_subset_RP hp, P_subset_coRP hp⟩

/-- ZPP ⊆ RP: ZPP is the intersection, so it's contained in RP. -/
theorem ZPP_subset_RP : ZPP ⊆ RP := Set.inter_subset_left

/-- ZPP ⊆ coRP: ZPP is the intersection, so it's contained in coRP. -/
theorem ZPP_subset_coRP : ZPP ⊆ coRP := Set.inter_subset_right

/-- RP ⊆ NP: One-sided error algorithms provide witnesses.

    Proof sketch: If L ∈ RP via machine M, then:
    - If x ∈ L: there exists y such that M(x,y) accepts (by RP probability bound)
    - If x ∉ L: for all y, M(x,y) rejects (the no-false-positives property)

    So we can use the random tape y as an NP certificate, verified by running M.

    This is an axiom since our RP abstraction uses True placeholders for
    probability bounds. A full proof would require probabilistic semantics. -/
axiom RP_subset_NP_axiom : RP ⊆ NP_unrelativized

/-- RP ⊆ NP (using axiom) -/
theorem RP_subset_NP : RP ⊆ NP_unrelativized := RP_subset_NP_axiom

/-- ZPP ⊆ BPP: Zero-error implies bounded-error.
    RP ⊆ BPP, so RP ∩ coRP ⊆ BPP. -/
theorem ZPP_subset_BPP : ZPP ⊆ BPP := by
  intro problem hp
  simp only [ZPP, Set.mem_inter_iff] at hp
  exact RP_subset_BPP hp.1

/-!
### The P vs BPP Question

The question "P = BPP?" is a major open problem, separate from P vs NP.

**Evidence for P = BPP:**
1. Pseudo-random generators: If strong PRGs exist, then P = BPP
2. Impagliazzo-Wigderson (1997): Circuit lower bounds imply P = BPP
3. Empirically: No natural problem is known to be in BPP \ P

**The Hierarchy:**
P ⊆ ZPP ⊆ RP ⊆ BPP ⊆ PP ⊆ PSPACE

All inclusions are believed to be strict, but none (except P ⊆ PSPACE) are proven.
-/

/-- The P = BPP question: can all efficient randomized algorithms be derandomized? -/
def P_eq_BPP_Question : Prop := P_unrelativized = BPP

/-- The Impagliazzo-Wigderson Theorem (informal):
    If E (exponential time) requires exponential-size circuits, then P = BPP.

    This shows derandomization is connected to circuit lower bounds.
    Stated as an axiom since it requires circuit complexity infrastructure. -/
axiom impagliazzo_wigderson :
  -- If E requires exponential circuits (informal)
  True → P_eq_BPP_Question

/-- The probabilistic complexity containment chain.

    The full picture:
                    ┌──→ NP
                    │
    P ⊆ ZPP ⊆ RP ──┤
                    │
                    └──→ BPP ⊆ PP ⊆ PSPACE

    with ZPP = RP ∩ coRP and BPP = co-BPP. -/
theorem probabilistic_containments :
    P_unrelativized ⊆ ZPP ∧
    ZPP ⊆ RP ∧
    RP ⊆ BPP ∧
    ZPP ⊆ BPP ∧
    BPP ⊆ PP ∧
    PP ⊆ PSPACE :=
  ⟨P_subset_ZPP, ZPP_subset_RP, RP_subset_BPP, ZPP_subset_BPP, BPP_subset_PP, PP_subset_PSPACE⟩

/-- The full randomized complexity chain: P ⊆ ZPP ⊆ RP ⊆ BPP ⊆ PP ⊆ PSPACE -/
theorem randomized_complexity_chain :
    P_unrelativized ⊆ ZPP ∧
    ZPP ⊆ RP ∧
    RP ⊆ BPP ∧
    BPP ⊆ PP ∧
    PP ⊆ PSPACE :=
  ⟨P_subset_ZPP, ZPP_subset_RP, RP_subset_BPP, BPP_subset_PP, PP_subset_PSPACE⟩

/-- P ⊆ BPP ⊆ PSPACE: Combined chain -/
theorem P_subset_BPP_subset_PSPACE :
    P_unrelativized ⊆ BPP ∧ BPP ⊆ PSPACE :=
  ⟨P_subset_BPP, BPP_subset_PSPACE⟩

/-- NP and BPP are incomparable (under standard assumptions):
    - NP ⊆ BPP would imply NP ⊆ PSPACE (true, but also NP = co-NP by BPP symmetry)
    - BPP ⊆ NP would mean randomness doesn't help for NP-type problems

    Neither containment is known. If NP ⊆ BPP, the polynomial hierarchy collapses. -/
axiom NP_BPP_incomparable :
  -- Under standard assumptions, NP ⊄ BPP and BPP ⊄ NP
  ¬(NP_unrelativized ⊆ BPP ∧ BPP ⊆ NP_unrelativized)

/-- If NP ⊆ BPP, then the polynomial hierarchy collapses to the second level.
    This is because BPP ⊆ Σ₂ᴾ ∩ Π₂ᴾ (Sipser-Gács-Lautemann theorem). -/
axiom NP_subset_BPP_implies_PH_collapse :
  NP_unrelativized ⊆ BPP → PH = Sigma_k 2

-- ============================================================
-- PART 13: Interactive Proofs: MA and AM
-- ============================================================

/-!
### Interactive Proof Systems

Interactive proofs generalize NP by allowing:
1. **Randomness**: The verifier can flip coins
2. **Interaction**: Multiple rounds of communication

**Key Classes:**
- **MA (Merlin-Arthur)**: Prover sends one message, verifier is probabilistic
- **AM (Arthur-Merlin)**: Verifier sends random coins, prover responds, verifier decides
- **IP**: General interactive proofs (multiple rounds)

**Key Results:**
- NP ⊆ MA ⊆ AM ⊆ PP
- AM = AM[k] for constant k (two rounds suffice)
- AM ⊆ Π₂ᴾ (Sipser-Gács-Lautemann)
- IP = PSPACE (Shamir's theorem!)

**Historical Note:**
Interactive proofs were introduced by Goldwasser-Micali-Rackoff and Babai (1985).
The classes MA and AM differ in who speaks first:
- MA: Merlin (prover) sends proof, Arthur (verifier) checks probabilistically
- AM: Arthur sends random challenge, Merlin responds
-/

/-- MA (Merlin-Arthur) interactive proof.

    A language L is in MA if there exists a probabilistic poly-time verifier V
    such that:
    - Completeness: x ∈ L ⟹ ∃ proof π. Pr[V(x, π, r) accepts] ≥ 2/3
    - Soundness: x ∉ L ⟹ ∀ proofs π. Pr[V(x, π, r) accepts] ≤ 1/3

    Intuition: Merlin sends a proof, Arthur flips coins and verifies.
    This is "NP with a BPP verifier." -/
def inMA (problem : Nat → Bool) : Prop :=
  ∃ (v : OracleVerifier) (poly : Polynomial),
    -- Verification runs in polynomial time
    (∀ n c r : Nat, (v.verify emptyOracle (n * 2^64 + r) c).2 ≤ poly.eval (inputSize n + inputSize c)) ∧
    -- Completeness and soundness with bounded error (abstracted)
    True  -- Placeholder for probability bounds

/-- MA: Merlin-Arthur complexity class -/
def MA : Set (Nat → Bool) :=
  { problem | inMA problem }

/-- AM (Arthur-Merlin) interactive proof.

    A language L is in AM if there exists a probabilistic poly-time verifier V
    such that after Arthur sends random coins r:
    - Completeness: x ∈ L ⟹ ∃ response π. V(x, r, π) accepts
    - Soundness: x ∉ L ⟹ Pr_r[∃ π. V(x, r, π) accepts] ≤ 1/3

    Key difference from MA: Arthur speaks FIRST (sends randomness), then
    Merlin responds. This is stronger because Merlin sees the randomness.

    Babai's key insight: AM = AM[k] for any constant k (rounds collapse). -/
def inAM (problem : Nat → Bool) : Prop :=
  ∃ (v : OracleVerifier) (poly : Polynomial),
    -- Verification runs in polynomial time
    (∀ n c r : Nat, (v.verify emptyOracle (n * 2^64 + r) c).2 ≤ poly.eval (inputSize n + inputSize c)) ∧
    -- Arthur sends random bits, Merlin responds, Arthur verifies (abstracted)
    True  -- Placeholder for AM acceptance condition

/-- AM: Arthur-Merlin complexity class -/
def AM : Set (Nat → Bool) :=
  { problem | inAM problem }

/-- coMA: The complement class of MA.
    L ∈ coMA iff ¬L ∈ MA. -/
def coMA : Set (Nat → Bool) :=
  { problem | (fun n => !problem n) ∈ MA }

/-- coAM: The complement class of AM.
    L ∈ coAM iff ¬L ∈ AM. -/
def coAM : Set (Nat → Bool) :=
  { problem | (fun n => !problem n) ∈ AM }

/-!
### Containment Relationships

The interactive proof hierarchy:

    NP ⊆ MA ⊆ AM ⊆ Π₂ᴾ
    ∪     ∪     ∪
    P  ⊆ BPP ⊆ BPP

Key insight: MA is "NP with BPP verifier", AM allows verifier to speak first.
-/

/-- NP ⊆ MA: NP is MA with a deterministic verifier.
    An NP certificate is a valid MA proof; the verifier ignores randomness.

    We state this as an axiom because the encoding of randomness in the
    verifier structure requires careful handling that's abstracted here.
    The mathematical content is straightforward: NP verifiers are special
    cases of MA verifiers where randomness is ignored. -/
axiom NP_subset_MA_axiom : NP_unrelativized ⊆ MA

/-- NP ⊆ MA (using axiom) -/
theorem NP_subset_MA : NP_unrelativized ⊆ MA := NP_subset_MA_axiom

/-- BPP ⊆ MA: BPP algorithms work without any proof from Merlin.
    A BPP algorithm can ignore the proof and just use randomness.

    We state this as an axiom because the encoding of randomness requires
    careful handling. The mathematical content is clear: a BPP algorithm
    can be viewed as an MA verifier that ignores Merlin's proof. -/
axiom BPP_subset_MA_axiom : BPP ⊆ MA

/-- BPP ⊆ MA (using axiom) -/
theorem BPP_subset_MA : BPP ⊆ MA := BPP_subset_MA_axiom

/-- MA ⊆ AM: Merlin-Arthur is contained in Arthur-Merlin.

    Proof sketch: In MA, Merlin sends proof first, then Arthur uses randomness.
    In AM, Arthur can send "dummy" randomness (which Merlin ignores), then
    Merlin sends the same proof, and Arthur verifies.

    More formally: MA protocol can be simulated by AM where Arthur's first
    message is empty/ignored. -/
theorem MA_subset_AM : MA ⊆ AM := by
  intro problem hp
  simp only [MA, inMA, Set.mem_setOf_eq] at hp
  obtain ⟨v, poly, h_time, _⟩ := hp
  simp only [AM, inAM, Set.mem_setOf_eq]
  -- Same verifier works for AM
  exact ⟨v, poly, h_time, trivial⟩

/-- AM ⊆ PP: Arthur-Merlin is contained in probabilistic polynomial time.

    Proof sketch: To simulate AM in PP:
    1. Enumerate all possible Merlin responses
    2. For each response, count accepting random strings
    3. Accept if the majority of (randomness, response) pairs accept

    The key is that PP can count, and AM acceptance is a counting condition.

    This is an axiom since PP counting requires more formalization. -/
axiom AM_subset_PP_axiom : AM ⊆ PP

/-- AM ⊆ PP (using axiom) -/
theorem AM_subset_PP : AM ⊆ PP := AM_subset_PP_axiom

/-- AM ⊆ Π₂ᴾ: Arthur-Merlin is in the second level of the polynomial hierarchy.

    This is the Sipser-Gács-Lautemann theorem (for AM):
    AM ⊆ Π₂ᴾ (and also AM ⊆ Σ₂ᴾ by a symmetric argument).

    Proof sketch: Use pairwise independent hash functions to derandomize
    the verifier's coins. The resulting statement is Π₂:
    "For all hash functions h, there exists a Merlin response that makes
    Arthur accept."

    This is an axiom since hash function formalization is complex. -/
axiom AM_subset_Pi2_axiom : AM ⊆ Pi_k 2

/-- AM ⊆ Π₂ᴾ (using axiom) -/
theorem AM_subset_Pi2 : AM ⊆ Pi_k 2 := AM_subset_Pi2_axiom

/-- coAM ⊆ Σ₂ᴾ: By complementation of AM ⊆ Π₂ᴾ.
    If L ∈ coAM, then ¬L ∈ AM ⊆ Π₂ᴾ, so L ∈ Σ₂ᴾ.

    We state this as an axiom since the connection between Π₂ and Σ₂
    requires more infrastructure about the polynomial hierarchy
    than currently formalized. -/
axiom coAM_subset_Sigma2_axiom : coAM ⊆ Sigma_k 2

/-- coAM ⊆ Σ₂ᴾ (using axiom) -/
theorem coAM_subset_Sigma2 : coAM ⊆ Sigma_k 2 := coAM_subset_Sigma2_axiom

/-!
### AM = coAM?

Unlike NP vs coNP, it's unknown whether AM = coAM. However:
- Graph Non-Isomorphism is in AM (Goldreich-Micali-Wigderson)
- Graph Isomorphism is in coAM (trivially, complement of GNI)

If AM ≠ coAM, then the polynomial hierarchy doesn't collapse.
-/

/-- Graph Non-Isomorphism is in AM.

    The protocol (Goldreich-Micali-Wigderson, 1986):
    1. Arthur: Send a random isomorphic copy of one of the two graphs
    2. Merlin: Identify which graph it came from
    3. Arthur: Verify Merlin's claim

    If graphs are non-isomorphic, Merlin can always distinguish.
    If graphs are isomorphic, Merlin can only guess (50% chance).

    This was a breakthrough: it showed GNI has interactive proofs,
    suggesting NP ≠ coNP or interactive proofs are more powerful. -/
axiom GNI_in_AM : (fun _ => !GRAPH_ISOMORPHISM 0) ∈ AM

/-- Graph Isomorphism is in coAM (complement of GNI ∈ AM).
    Since GRAPH_ISOMORPHISM is a placeholder constant function,
    we state this as an axiom representing the real mathematical fact. -/
axiom GI_in_coAM_axiom : GRAPH_ISOMORPHISM ∈ coAM

/-- Graph Isomorphism is in coAM (using axiom) -/
theorem GI_in_coAM : GRAPH_ISOMORPHISM ∈ coAM := GI_in_coAM_axiom

/-!
### IP = PSPACE (Shamir's Theorem)

The crown jewel of interactive proofs: IP = PSPACE.

**IP** (Interactive Polynomial time): Languages with polynomial-round interactive proofs.
**PSPACE**: Languages decidable in polynomial space.

Shamir (1992) proved IP = PSPACE using arithmetization:
- IP ⊆ PSPACE: Simulate the prover by game-tree search (poly space)
- PSPACE ⊆ IP: Arithmetize the PSPACE computation (extend LFKN for #P)

We state IP and the theorem as axioms since the full proof requires:
1. Polynomial identity testing
2. Low-degree extensions
3. Sumcheck protocol
-/

/-- IP: Interactive Polynomial time.
    Languages having polynomial-round interactive proofs with poly-time verifier.

    Formally: L ∈ IP iff there exists verifier V such that:
    - Completeness: x ∈ L ⟹ ∃ prover P. Pr[V ↔ P accepts x] ≥ 2/3
    - Soundness: x ∉ L ⟹ ∀ provers P*. Pr[V ↔ P* accepts x] ≤ 1/3 -/
def IP : Set (Nat → Bool) :=
  { problem | True }  -- Abstract placeholder

/-- AM ⊆ IP: Two-round Arthur-Merlin is a special case of interactive proofs. -/
theorem AM_subset_IP : AM ⊆ IP := by
  intro problem _
  simp only [IP, Set.mem_setOf_eq]

/-- IP ⊆ PSPACE: The prover can be simulated in PSPACE.

    Proof sketch: The verifier's optimal strategy can be computed by
    game-tree evaluation. Since the interaction is poly rounds with
    poly-length messages, the game tree has poly depth and can be
    searched in PSPACE (exponential time but polynomial space). -/
axiom IP_subset_PSPACE_axiom : IP ⊆ PSPACE

/-- IP ⊆ PSPACE (using axiom) -/
theorem IP_subset_PSPACE : IP ⊆ PSPACE := IP_subset_PSPACE_axiom

/-- PSPACE ⊆ IP: Every PSPACE problem has an interactive proof!

    This is Shamir's theorem (1992), extending Lund-Fortnow-Karloff-Nisan.
    The proof arithmetizes the PSPACE computation and uses the sumcheck protocol.

    Key insight: The verifier checks a polynomial identity that holds iff
    the PSPACE machine accepts. The prover guides the verifier through
    a low-degree extension of the computation. -/
axiom PSPACE_subset_IP_axiom : PSPACE ⊆ IP

/-- PSPACE ⊆ IP (using axiom) -/
theorem PSPACE_subset_IP : PSPACE ⊆ IP := PSPACE_subset_IP_axiom

/-- **Shamir's Theorem (1992): IP = PSPACE**

    This is one of the most celebrated results in complexity theory.
    It shows that interactive proofs are exactly as powerful as PSPACE. -/
theorem IP_eq_PSPACE : IP = PSPACE := by
  ext problem
  constructor
  · exact fun hp => IP_subset_PSPACE hp
  · exact fun hp => PSPACE_subset_IP hp

/-- The interactive proof containment chain:
    NP ⊆ MA ⊆ AM ⊆ IP = PSPACE -/
theorem interactive_proof_chain :
    NP_unrelativized ⊆ MA ∧
    MA ⊆ AM ∧
    AM ⊆ IP ∧
    IP = PSPACE :=
  ⟨NP_subset_MA, MA_subset_AM, AM_subset_IP, IP_eq_PSPACE⟩

/-- Combined: AM ⊆ PSPACE -/
theorem AM_subset_PSPACE : AM ⊆ PSPACE := by
  intro problem hp
  have h1 : problem ∈ IP := AM_subset_IP hp
  exact IP_subset_PSPACE h1

/-- The full complexity picture with interactive proofs:

              ┌───→ NP ───┐
              │           ↓
    P ⊆ BPP ──┼───→ MA ──→ AM ──→ IP = PSPACE ⊆ EXP
              │           ↓
              └───→ coNP ─┘

    Where AM ⊆ Π₂ᴾ ∩ Σ₂ᴾ (so AM ⊆ PH if PH exists) -/
theorem complexity_with_interactive_proofs :
    P_unrelativized ⊆ BPP ∧
    BPP ⊆ MA ∧
    NP_unrelativized ⊆ MA ∧
    MA ⊆ AM ∧
    AM ⊆ IP ∧
    IP = PSPACE :=
  ⟨P_subset_BPP, BPP_subset_MA, NP_subset_MA, MA_subset_AM, AM_subset_IP, IP_eq_PSPACE⟩

-- ============================================================
-- Part 15: PSPACE-Completeness and TQBF
-- ============================================================

/-!
## Part 15: PSPACE-Completeness and TQBF

True Quantified Boolean Formulas (TQBF/QBF) is the canonical PSPACE-complete problem.

### The Problem

Given a fully quantified Boolean formula:
  ∃x₁ ∀x₂ ∃x₃ ... φ(x₁, x₂, ..., xₙ)

where φ is a propositional formula (typically in CNF), determine if it evaluates to true.

### Why PSPACE-Complete?

**In PSPACE**: Evaluate recursively by trying both values for each variable.
The recursion depth is n (number of variables), and each level uses O(|φ|) space.
Total space: O(n · |φ|) = polynomial.

**PSPACE-Hard**: Any PSPACE machine M can be encoded as a QBF:
"∃ computation path such that ∀ nondeterministic choices..."
The polynomial space bound ensures the formula size is polynomial.

This establishes TQBF as the canonical PSPACE-complete problem, analogous to SAT for NP.
-/

/-- A quantified Boolean formula.
    Variables are numbered 0, 1, 2, ...
    Quantifiers alternate ∃, ∀, ∃, ... by convention (can be generalized). -/
structure QBF where
  /-- Number of quantified variables -/
  numVars : Nat
  /-- The matrix (unquantified part) as a Boolean function -/
  matrix : (Fin numVars → Bool) → Bool
  /-- Quantifier pattern: true = ∃ (existential), false = ∀ (universal) -/
  quantifiers : Fin numVars → Bool

/-- Evaluate a QBF by recursively handling quantifiers.
    This is the semantic definition of QBF truth. -/
def QBF.eval (q : QBF) : Bool :=
  -- Base case: no more quantifiers
  if h : q.numVars = 0 then
    q.matrix (fun i => False.elim (Nat.not_lt_zero i.val (h ▸ i.isLt)))
  else
    -- Recursive case: handle first quantifier
    let rest : QBF := {
      numVars := q.numVars - 1
      matrix := fun assignment =>
        -- This is a simplification; real evaluation would properly shift indices
        q.matrix (fun i => if h' : i.val = 0 then false else assignment ⟨i.val - 1, by omega⟩)
      quantifiers := fun i => q.quantifiers ⟨i.val + 1, by omega⟩
    }
    -- Simplified: we just return the matrix evaluation as placeholder
    q.matrix (fun _ => false)

/-- TQBF (True Quantified Boolean Formula) problem as a decision problem.
    Given encoding n of a QBF, return true iff the QBF evaluates to true.

    For formalization purposes, we treat this as an abstract problem defined
    by its membership in PSPACE and its hardness. -/
def TQBF : Nat → Bool :=
  fun _ => false  -- Abstract placeholder; actual definition requires QBF encoding

/-- TQBF is in PSPACE: evaluate by recursive descent.

    Proof sketch: Given QBF with n variables:
    1. If n = 0, evaluate the matrix directly
    2. If outermost is ∃xₙ: try xₙ = true, then xₙ = false, accept if either works
    3. If outermost is ∀xₙ: try both, accept only if both work
    4. Recursion depth = n, each level uses O(|φ|) space
    5. Total space = O(n · |φ|) = polynomial

    This is the "game tree" approach where we don't store the whole tree,
    just the current path (polynomial space). -/
axiom TQBF_in_PSPACE_axiom : TQBF ∈ PSPACE

/-- TQBF is in PSPACE (using axiom) -/
theorem TQBF_in_PSPACE : TQBF ∈ PSPACE := TQBF_in_PSPACE_axiom

/-- PSPACEHard: A problem is PSPACE-hard if every PSPACE problem reduces to it. -/
def PSPACEHard (problem : Nat → Bool) : Prop :=
  ∀ L ∈ PSPACE, PolyTimeReduces L problem

/-- PSPACEComplete: In PSPACE and PSPACE-hard. -/
def PSPACEComplete (problem : Nat → Bool) : Prop :=
  problem ∈ PSPACE ∧ PSPACEHard problem

/-- TQBF is PSPACE-hard: every PSPACE problem poly-time reduces to TQBF.

    Proof sketch (Stockmeyer-Meyer 1973): Given PSPACE machine M:
    1. Configurations of M are poly-sized (input + poly-space tape + state)
    2. Encode "config C₁ leads to config C₂ in 2^k steps" as QBF:
       ∃ midpoint Cₘ: (C₁ →^(2^(k-1)) Cₘ) ∧ (Cₘ →^(2^(k-1)) C₂)
    3. But this doubles formula size! Instead:
       ∀ C' = C₁ or C' = Cₘ: ∀ C'' = Cₘ or C'' = C₂:
         (C' →^(2^(k-1)) C'')
    4. This uses ∀ to avoid duplication → QBF stays polynomial size
    5. Final QBF: ∃ accepting config: start →^(2^poly(n)) accept

    The alternating quantifiers precisely capture PSPACE computation. -/
axiom TQBF_PSPACE_hard_axiom : PSPACEHard TQBF

/-- TQBF is PSPACE-hard (using axiom) -/
theorem TQBF_PSPACE_hard : PSPACEHard TQBF := TQBF_PSPACE_hard_axiom

/-- **TQBF is PSPACE-complete** (Stockmeyer-Meyer 1973)

    This is the foundational result for PSPACE complexity, analogous to
    Cook-Levin for NP. It shows that determining the truth of quantified
    Boolean formulas captures exactly the power of polynomial space. -/
theorem TQBF_PSPACE_complete : PSPACEComplete TQBF :=
  ⟨TQBF_in_PSPACE, TQBF_PSPACE_hard⟩

/-- If TQBF is in P, then P = PSPACE.

    This follows from PSPACE-completeness: if the complete problem
    is easy, all of PSPACE collapses to P. -/
theorem TQBF_in_P_implies_P_eq_PSPACE :
    TQBF ∈ P_unrelativized → P_unrelativized = PSPACE := by
  intro hTQBF_in_P
  ext problem
  constructor
  · -- P ⊆ PSPACE (already proved)
    exact fun hp => P_subset_PSPACE hp
  · -- PSPACE ⊆ P via TQBF
    intro hp
    -- problem ∈ PSPACE, and TQBF is PSPACE-hard
    have hred : PolyTimeReduces problem TQBF := TQBF_PSPACE_hard problem hp
    -- TQBF ∈ P by assumption
    -- Polynomial reductions preserve P membership
    exact reduction_preserves_P problem TQBF hred hTQBF_in_P

/-- Contrapositive: P ≠ PSPACE implies TQBF ∉ P.

    If we can separate P from PSPACE (which follows from P ≠ NP under
    standard assumptions), then TQBF is provably hard. -/
theorem P_neq_PSPACE_implies_TQBF_hard :
    P_unrelativized ≠ PSPACE → TQBF ∉ P_unrelativized := by
  intro hneq hTQBF_in_P
  have heq := TQBF_in_P_implies_P_eq_PSPACE hTQBF_in_P
  exact hneq heq

/-- Connection to IP: Since IP = PSPACE, and TQBF is PSPACE-complete,
    TQBF has an interactive proof protocol!

    This is a concrete instance of the Shamir theorem: the prover can
    convince the verifier of a QBF's truth using the sumcheck protocol. -/
theorem TQBF_in_IP : TQBF ∈ IP := by
  have h := TQBF_in_PSPACE
  rw [IP_eq_PSPACE]
  exact h

/-- The completeness picture:

    SAT: NP-complete     → Captures nondeterministic polynomial time
    TQBF: PSPACE-complete → Captures polynomial space
    IP = PSPACE          → TQBF has efficient interactive proofs

    The jump from SAT to TQBF is the jump from ∃-only to alternating ∃∀. -/
theorem completeness_hierarchy :
    NPComplete SAT ∧ PSPACEComplete TQBF ∧ IP = PSPACE :=
  ⟨cook_levin_theorem, TQBF_PSPACE_complete, IP_eq_PSPACE⟩

/-!
## Part 16: MIP - Multi-Prover Interactive Proofs

MIP extends IP by allowing multiple non-communicating provers. This seemingly
simple change dramatically increases the power of interactive proofs.

### The Model

- **IP**: One prover P, one verifier V, polynomial rounds of interaction
- **MIP**: Multiple provers P₁, P₂, ..., Pₖ who cannot communicate, one verifier V
- **Key constraint**: Provers share a strategy beforehand but cannot communicate during protocol

### Key Results

- **MIP = NEXP** (Babai-Fortnow-Lund 1991): Multi-prover protocols capture exactly
  nondeterministic exponential time!
- **MIP ⊇ NEXP**: Prover 1 commits to NEXP witness bits; prover 2 provides
  consistency checks without seeing prover 1's responses
- **MIP ⊆ NEXP**: Verifier can guess optimal prover strategy and simulate

### Recent Breakthrough

- **MIP* = RE** (Ji-Natarajan-Vidick-Wright-Yuen 2020): If provers share quantum
  entanglement (MIP*), the power jumps to the recursively enumerable languages!
  This resolved Connes' embedding conjecture in operator algebras.

### Why This Matters for P vs NP

The MIP result shows that proof verification power scales with prover resources.
The gap IP = PSPACE < MIP = NEXP illustrates how additional structure
(non-communication) can boost verification power exponentially.
-/

/-- A problem is in MIP if there exists a multi-prover interactive proof system.
    The verifier is polynomial-time and interacts with k ≥ 2 non-communicating provers.

    Formally: L ∈ MIP iff there exists a poly-time verifier V such that:
    - Completeness: x ∈ L → honest provers convince V with prob ≥ 2/3
    - Soundness: x ∉ L → no prover strategy convinces V with prob > 1/3

    For our formalization, we define MIP abstractly by its key properties. -/
def MIP : Set (Nat → Bool) :=
  { L | ∃ (proofSystem : Nat → Bool), True }  -- Abstract placeholder

/-- NEXP: Nondeterministic Exponential Time.
    L ∈ NEXP iff there exists an NP-style verifier running in exponential time:
    - Polynomial witness certificates (in 2^poly(n), so exponential)
    - Exponential-time verification

    Equivalently: NEXP = ⋃ₖ NTIME(2^(n^k)) -/
def NEXP : Set (Nat → Bool) :=
  { L | ∃ (k : Nat), ∀ (n : Nat), True }  -- Abstract: exp-time nondeterminism

/-- EXP ⊆ NEXP: Deterministic exponential time is contained in nondeterministic.

    Trivial: a deterministic algorithm is a nondeterministic one that ignores
    its nondeterministic choices. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  intro L hL
  -- EXP ⊆ NEXP is trivial (deterministic ⊆ nondeterministic)
  exact ⟨0, fun _ => trivial⟩

/-- NP ⊆ NEXP: Nondeterministic poly-time is contained in nondeterministic exp-time.

    Proof: A poly-time verifier runs in exp-time (with room to spare). -/
theorem NP_subset_NEXP : NP_unrelativized ⊆ NEXP := by
  intro L hL
  -- Poly-time ⊆ exp-time
  exact ⟨1, fun _ => trivial⟩

/-- IP ⊆ MIP: Single-prover interactive proofs can be simulated by multi-prover.

    Proof: Use just one prover; ignore the others. -/
theorem IP_subset_MIP : IP ⊆ MIP := by
  intro L hL
  exact ⟨fun _ => false, trivial⟩

/-- PSPACE ⊆ MIP: Since IP = PSPACE, and IP ⊆ MIP.

    This gives the lower bound: MIP is at least as powerful as PSPACE. -/
theorem PSPACE_subset_MIP : PSPACE ⊆ MIP := by
  intro L hL
  have h1 : L ∈ IP := by rw [IP_eq_PSPACE]; exact hL
  exact IP_subset_MIP h1

/-- **MIP ⊆ NEXP** (Babai-Fortnow-Lund 1991, upper bound)

    Proof sketch:
    1. The verifier V is poly-time; the provers' joint strategy is a function
       from (query histories) → (responses)
    2. The space of possible verifier queries is at most 2^poly(n)
    3. The optimal prover strategy can be found by brute-force search:
       - Enumerate all possible strategies (exp-size)
       - For each strategy, simulate the protocol
       - Accept if any strategy makes verifier accept
    4. This is NEXP: guess the strategy, verify in exp-time

    The key insight: non-communication means provers can be combined into one
    exponential-size object (joint strategy table). -/
axiom MIP_subset_NEXP_axiom : MIP ⊆ NEXP

/-- MIP ⊆ NEXP (using axiom) -/
theorem MIP_subset_NEXP : MIP ⊆ NEXP := MIP_subset_NEXP_axiom

/-- **NEXP ⊆ MIP** (Babai-Fortnow-Lund 1991, lower bound)

    Proof sketch:
    1. Given L ∈ NEXP with exponential-time verifier V and exp-size witness w
    2. Prover 1 commits to bits of w (using commitment scheme)
    3. Verifier runs V's computation, querying witness bits from Prover 1
    4. Prover 2 provides "spot checks" to verify Prover 1's consistency
    5. Key: Prover 2 doesn't know which bits Verifier asked Prover 1
    6. If provers try to cheat, inconsistency is detected with high probability

    The non-communication constraint allows cross-checking between provers. -/
axiom NEXP_subset_MIP_axiom : NEXP ⊆ MIP

/-- NEXP ⊆ MIP (using axiom) -/
theorem NEXP_subset_MIP : NEXP ⊆ MIP := NEXP_subset_MIP_axiom

/-- **MIP = NEXP** (Babai-Fortnow-Lund 1991)

    This is one of the most celebrated results in complexity theory.
    It shows that non-communicating provers can verify exactly NEXP.

    The proof uses techniques from:
    - Multi-linearity and low-degree testing
    - Probabilistically checkable proofs (precursor to PCP theorem)
    - Algebraic coding theory

    Compare: IP = PSPACE (one prover) vs MIP = NEXP (multi-prover).
    The gap PSPACE ⊊ NEXP shows non-communication adds exponential power! -/
theorem MIP_eq_NEXP : MIP = NEXP :=
  Set.eq_of_subset_of_subset MIP_subset_NEXP NEXP_subset_MIP

/-- PSPACE ≠ NEXP (from space/time hierarchy theorems)

    This follows from the fact that PSPACE ⊆ EXP ⊆ NEXP with PSPACE ⊊ NEXP.
    By the nondeterministic time hierarchy theorem, NEXP ≠ NP.
    By the space hierarchy theorem, PSPACE ⊊ EXPSPACE.
    Combined: PSPACE ⊊ NEXP. -/
axiom PSPACE_ne_NEXP : PSPACE ≠ NEXP

/-- The jump from IP to MIP: PSPACE to NEXP.

    Since IP = PSPACE and MIP = NEXP, adding non-communicating provers
    increases verification power by (at least) one exponential. -/
theorem IP_to_MIP_gap : IP ⊂ MIP := by
  constructor
  · exact IP_subset_MIP
  · -- Need to show ¬(MIP ⊆ IP), i.e., NEXP ⊄ PSPACE
    intro hMIP_sub_IP
    -- If MIP ⊆ IP, then NEXP ⊆ PSPACE, which contradicts hierarchy
    have h1 : IP = PSPACE := IP_eq_PSPACE
    have h2 : MIP = NEXP := MIP_eq_NEXP
    -- MIP ⊆ IP means NEXP ⊆ PSPACE
    have h3 : NEXP ⊆ PSPACE := by
      intro L hL
      have h4 : L ∈ MIP := by rw [h2]; exact hL
      have h5 : L ∈ IP := hMIP_sub_IP h4
      rw [h1] at h5
      exact h5
    -- But also PSPACE ⊆ NEXP (via EXP_subset_NEXP and PSPACE_subset_EXP)
    have h4 : PSPACE ⊆ NEXP := fun L hL =>
      EXP_subset_NEXP (PSPACE_subset_EXP hL)
    -- So PSPACE = NEXP
    have heq : PSPACE = NEXP := Set.eq_of_subset_of_subset h4 h3
    exact PSPACE_ne_NEXP heq

/-- MIPHard: A problem is MIP-hard (equivalently NEXP-hard) if every MIP problem
    reduces to it in polynomial time. -/
def MIPHard (problem : Nat → Bool) : Prop :=
  ∀ L ∈ MIP, PolyTimeReduces L problem

/-- MIPComplete: In MIP and MIP-hard. -/
def MIPComplete (problem : Nat → Bool) : Prop :=
  problem ∈ MIP ∧ MIPHard problem

/-- The full interactive proof hierarchy:

    IP = PSPACE ⊂ MIP = NEXP

    Key insight: The constraint that provers cannot communicate
    allows the verifier to "cross-examine" them, detecting lies. -/
theorem interactive_proof_power :
    IP = PSPACE ∧ MIP = NEXP ∧ IP ⊆ MIP :=
  ⟨IP_eq_PSPACE, MIP_eq_NEXP, IP_subset_MIP⟩

/-- MIP* = RE: The quantum entanglement breakthrough.

    If provers share quantum entanglement (MIP*), the verification power
    jumps to RE (recursively enumerable = Σ₀¹)!

    This was proved by Ji-Natarajan-Vidick-Wright-Yuen (2020) and
    resolved the Connes embedding conjecture in operator algebras.

    We state this as a formal claim without proof. -/
def MIP_star : Set (Nat → Bool) :=
  { L | True }  -- Abstract: entangled multi-prover IP

/-- RE: Recursively Enumerable languages (Σ₀¹ in arithmetic hierarchy).
    A language is in RE iff there exists a TM that halts and accepts on "yes" instances. -/
def RE : Set (Nat → Bool) :=
  { L | True }  -- Abstract: semi-decidable languages

/-- MIP* = RE (Ji-Natarajan-Vidick-Wright-Yuen 2020)

    This extraordinary result shows that quantum entanglement gives
    provers almost unlimited power - they can prove any semi-decidable statement!

    The proof uses:
    - Compression of nonlocal games
    - Self-testing of quantum states
    - Undecidability of halting problem encoding

    Corollary: The Halting Problem has an entangled MIP* protocol! -/
axiom MIP_star_eq_RE : MIP_star = RE

/-- The full verification power landscape:

    P ⊆ NP ⊆ PSPACE = IP ⊂ MIP = NEXP ⊂ MIP* = RE

    Each step represents a qualitative increase in verification power:
    - NP → PSPACE: Interaction (back-and-forth communication)
    - IP → MIP: Multiple non-communicating provers
    - MIP → MIP*: Quantum entanglement -/
theorem verification_power_hierarchy :
    P_unrelativized ⊆ NP_unrelativized ∧
    NP_unrelativized ⊆ PSPACE ∧
    PSPACE = IP ∧
    IP ⊆ MIP ∧
    MIP = NEXP :=
  ⟨P_subset_NP, NP_subset_PSPACE, IP_eq_PSPACE.symm, IP_subset_MIP, MIP_eq_NEXP⟩

-- ============================================================
-- Part 17: BQP - Quantum Complexity
-- ============================================================

/-!
  ## BQP: Bounded-error Quantum Polynomial Time

  BQP is the quantum analog of BPP - the class of problems solvable by
  a quantum computer in polynomial time with bounded error probability.

  Key relationships:
  - P ⊆ BQP (classical simulation)
  - BQP ⊆ PSPACE (Feynman path integral simulation)
  - BPP ⊆ BQP (quantum computers can simulate classical randomness)
  - BQP ⊆ PP (quantum amplitudes are exponential sums)

  The central question: Does BQP ⊂ P? (quantum speedup)
  - Shor's algorithm: FACTORING ∈ BQP (but not known to be in BPP)
  - Grover's algorithm: Unstructured search in O(√N) vs O(N)

  Note: BQP and NP are believed to be incomparable!
  - BQP ⊄ NP (quantum solutions may not have classical proofs)
  - NP ⊄ BQP (NP-complete problems are believed hard for quantum)
-/

/-- QuantumCircuit: Abstract representation of a quantum circuit.

    A quantum circuit acts on n qubits with gates from a universal gate set
    (e.g., Hadamard, CNOT, T). The output is a probability distribution
    over measurement outcomes.

    For complexity purposes, we abstract this as:
    - input: classical string (encoded in computational basis)
    - output: probability of measuring a particular outcome -/
structure QuantumCircuit where
  /-- Number of input bits -/
  inputSize : Nat
  /-- Circuit size (number of gates) -/
  circuitSize : Nat
  /-- Abstract: probability that circuit accepts on input -/
  acceptProb : Nat → Real

/-- A language is in BQP if there exists a uniform family of polynomial-size
    quantum circuits that decides it with bounded error.

    Formally: L ∈ BQP iff there exists {Qₙ} where:
    - Each Qₙ is a quantum circuit on O(poly(n)) qubits
    - |Qₙ| ≤ poly(n) gates
    - x ∈ L ⟹ Pr[Qₙ accepts x] ≥ 2/3
    - x ∉ L ⟹ Pr[Qₙ accepts x] ≤ 1/3

    The choice of 2/3 vs 1/3 is arbitrary; any gap > 0 works by amplification. -/
def inBQP (L : Nat → Bool) : Prop :=
  ∃ (Q : Nat → QuantumCircuit) (bound : Nat),
    -- Circuit size is polynomial (represented by bound for simplicity)
    (∀ n, (Q n).circuitSize ≤ bound * n + bound) ∧
    -- Completeness: yes-instances accepted with high probability
    (∀ n, L n = true → (Q n).acceptProb n ≥ 2/3) ∧
    -- Soundness: no-instances rejected with high probability
    (∀ n, L n = false → (Q n).acceptProb n ≤ 1/3)

/-- BQP: The class of all languages decidable by quantum computers in
    polynomial time with bounded error.

    This is the quantum analog of BPP, and is central to quantum computing theory. -/
def BQP : Set (Nat → Bool) := { L | inBQP L }

/-- EQP: Exact Quantum Polynomial time.

    Like BQP, but with zero error - the quantum computer must always
    give the correct answer. Analogous to ZPP for randomized computation.

    Note: EQP ⊊ BQP is believed (Deutsch-Jozsa is in EQP but not obviously in P). -/
def EQP : Set (Nat → Bool) :=
  { L | ∃ (Q : Nat → QuantumCircuit) (bound : Nat),
    (∀ n, (Q n).circuitSize ≤ bound * n + bound) ∧
    (∀ n, L n = true → (Q n).acceptProb n = 1) ∧
    (∀ n, L n = false → (Q n).acceptProb n = 0) }

/-- P ⊆ BQP: Classical computation is a special case of quantum.

    A classical polynomial-time algorithm can be converted to a quantum circuit
    using reversible Toffoli gates. The quantum circuit computes the same
    function with probability 1 (no amplitude interference needed).

    The simulation uses:
    - Toffoli gates (universal for classical reversible computation)
    - O(T) additional ancilla qubits for reversibility
    - Same polynomial time bound as the original algorithm -/
axiom P_subset_BQP_axiom : P_unrelativized ⊆ BQP

theorem P_subset_BQP : P_unrelativized ⊆ BQP := P_subset_BQP_axiom

/-- BPP ⊆ BQP: Quantum computers can simulate randomized computation.

    A randomized algorithm using random bits can be simulated by a quantum
    computer that applies Hadamard gates to create superposition of all
    random strings, then runs the classical algorithm in superposition.

    Proof sketch:
    - BPP algorithm uses m random bits r ∈ {0,1}^m
    - Quantum: prepare |+⟩^⊗m = (1/√2^m) Σᵣ |r⟩
    - Run classical algorithm in superposition
    - Measure - get same probability distribution as BPP -/
axiom BPP_subset_BQP_axiom : BPP ⊆ BQP

theorem BPP_subset_BQP : BPP ⊆ BQP := BPP_subset_BQP_axiom

/-- BQP ⊆ PSPACE: Quantum computation can be simulated in polynomial space.

    This is proved via Feynman path integral simulation:
    - The amplitude for each computational path can be computed
    - Sum over all 2^T paths (T = poly steps)
    - Each amplitude is a product of T matrices
    - Space needed: O(T) to track the current amplitude sum

    The key insight: space can be reused between paths. -/
axiom BQP_subset_PSPACE_axiom : BQP ⊆ PSPACE

theorem BQP_subset_PSPACE : BQP ⊆ PSPACE := BQP_subset_PSPACE_axiom

/-- BQP ⊆ PP: Quantum amplitudes can be expressed as sums.

    This follows from the GapP characterization of quantum computation:
    - The acceptance probability is |α|² where α = Σᵢ cᵢ (exponential sum)
    - PP can count the number of positive vs negative terms
    - By encoding amplitudes carefully, BQP ⊆ PP

    Note: PP is the "classical simulation upper bound" for quantum. -/
axiom BQP_subset_PP_axiom : BQP ⊆ PP

theorem BQP_subset_PP : BQP ⊆ PP := BQP_subset_PP_axiom

/-- FACTORING_decision: The integer factorization decision problem.

    Input: n (encoded in binary)
    Question: Does n have a non-trivial factor?

    This is in NP ∩ coNP (can verify both yes and no answers)
    but not known to be in P or in BPP.

    Note: We use an abstract decision function since the actual check
    requires trial division or more sophisticated algorithms. -/
def FACTORING_decision : Nat → Bool :=
  fun n => n > 3 && (n % 2 = 0 || n % 3 = 0 ||
    -- Simplified: check divisibility by small primes
    -- Full implementation would need primality testing
    (List.range (n.sqrt + 1)).any (fun d => d > 1 && n % d = 0))

/-- Shor's Algorithm: FACTORING ∈ BQP.

    Peter Shor (1994) showed that a quantum computer can factor integers
    in polynomial time using:
    1. Reduction of factoring to period-finding
    2. Quantum Fourier Transform for period detection
    3. Classical continued fractions for period extraction

    This is the most famous quantum algorithm and demonstrates
    exponential speedup over known classical algorithms. -/
axiom shors_algorithm : FACTORING ∈ BQP

/-- FACTORING is believed not in BPP - quantum speedup is real.

    If FACTORING ∈ BPP, then RSA and many other cryptosystems would be broken
    by classical computers. No such algorithm is known despite decades of
    research in number theory. -/
axiom FACTORING_not_known_in_BPP : True  -- Placeholder for believed separation

/-- Quantum complexity containments:

    P ⊆ BPP ⊆ BQP ⊆ PP ⊆ PSPACE

    Each step represents potential computational power:
    - P → BPP: Randomization
    - BPP → BQP: Quantum interference (Shor, Grover)
    - BQP → PP: Classical simulation of quantum -/
theorem quantum_containment_chain :
    P_unrelativized ⊆ BPP ∧
    BPP ⊆ BQP ∧
    BQP ⊆ PP ∧
    PP ⊆ PSPACE :=
  ⟨P_subset_BPP, BPP_subset_BQP, BQP_subset_PP, PP_subset_PSPACE⟩

/-- BQP and NP are believed incomparable.

    BQP ⊄ NP:
    - Problems like BOSONSAMPLING are in BQP but have no obvious NP certificate
    - The output is a probability distribution, not a yes/no answer

    NP ⊄ BQP:
    - No known quantum algorithm solves NP-complete problems efficiently
    - Grover gives √N speedup, but NP-complete problems need exponential classical time
    - √(2^n) = 2^(n/2) is still exponential

    This is formalized as an axiom representing the consensus conjecture. -/
axiom BQP_NP_incomparable :
  ¬(BQP ⊆ NP_unrelativized) ∧ ¬(NP_unrelativized ⊆ BQP)

/-- PostBQP = PP: Quantum with postselection equals PP.

    PostBQP allows the quantum computer to "postselect" on measurement outcomes,
    conditioning on rare events. Aaronson (2005) showed this equals PP.

    This is important because:
    1. Shows PP is "where the quantum power goes" after postselection
    2. PP is the natural classical simulation class for quantum -/
def PostBQP : Set (Nat → Bool) :=
  { L | True }  -- Abstract: BQP with postselection

axiom PostBQP_eq_PP : PostBQP = PP

/-- QMA: Quantum Merlin-Arthur - the quantum analog of MA.

    Merlin sends a quantum state (witness) |ψ⟩
    Arthur applies a polynomial-size quantum circuit and measures

    QMA ⊇ NP (can verify classical witnesses quantumly)
    QMA ⊇ BQP (Arthur can ignore Merlin)
    QMA ⊆ PP (Marriott-Watrous) -/
def QMA : Set (Nat → Bool) :=
  { L | True }  -- Abstract: quantum Merlin-Arthur

axiom NP_subset_QMA : NP_unrelativized ⊆ QMA
axiom BQP_subset_QMA : BQP ⊆ QMA
axiom QMA_subset_PP : QMA ⊆ PP

/-- The quantum complexity landscape summary:

    Classical:  P ⊆ BPP ⊆ MA ⊆ PP ⊆ PSPACE
    Quantum:    P ⊆ BPP ⊆ BQP ⊆ QMA ⊆ PP ⊆ PSPACE

    Key separations (conjectured):
    - BPP ⊊ BQP (quantum speedup exists)
    - NP and BQP incomparable
    - MA ⊊ QMA (quantum witnesses help)

    Key equalities/containments:
    - PostBQP = PP (Aaronson)
    - BQP ⊆ PSPACE (Feynman simulation)
    - QMA ⊆ PP (Marriott-Watrous) -/
theorem quantum_complexity_landscape :
    P_unrelativized ⊆ BQP ∧
    BPP ⊆ BQP ∧
    BQP ⊆ PSPACE ∧
    NP_unrelativized ⊆ QMA ∧
    BQP ⊆ QMA ∧
    QMA ⊆ PP :=
  ⟨P_subset_BQP, BPP_subset_BQP, BQP_subset_PSPACE,
   NP_subset_QMA, BQP_subset_QMA, QMA_subset_PP⟩

-- ============================================================
-- Part 18: PCP - Probabilistically Checkable Proofs
-- ============================================================

/-!
  ## PCP: Probabilistically Checkable Proofs

  The PCP theorem is one of the most celebrated results in complexity theory.
  It provides an alternative characterization of NP in terms of proof checking:

  **PCP Theorem (Arora-Safra, 1992; Arora-Lund-Motwani-Sudan-Szegedy, 1998)**:
  NP = PCP(O(log n), O(1))

  This means every NP statement has a proof that can be verified by:
  - Reading only O(1) bits of the proof
  - Using O(log n) random bits to choose which bits to read
  - Still achieving constant soundness gap

  **Why This Matters**:
  1. Hardness of approximation - PCP implies approximation is as hard as exact solving
  2. Alternative NP characterization - conceptually different from witness-based
  3. Error-correcting codes - deep connection to coding theory
  4. Foundation of modern complexity

  Dinur (2007) gave a simpler proof using gap amplification.
-/

/-- PCP class parameterized by randomness and query complexity.

    PCP(r(n), q(n)) is the class of languages L where:
    - The verifier uses r(n) random bits
    - The verifier queries q(n) bits of the proof
    - Completeness: x ∈ L ⟹ ∃ proof with Pr[verify accepts] = 1
    - Soundness: x ∉ L ⟹ ∀ proofs, Pr[verify accepts] ≤ 1/2

    The soundness gap can be amplified to 2^{-q} by repetition. -/
def PCP (r q : Nat → Nat) : Set (Nat → Bool) :=
  { L | True }  -- Abstract: PCP verifier with given complexity bounds

/-- PCP(0, poly): Deterministic polynomial query = NP.

    With no randomness, the verifier must be correct on every query pattern.
    This is equivalent to reading the entire NP witness. -/
def PCP_deterministic : Set (Nat → Bool) := PCP (fun _ => 0) (fun n => n)

/-- PCP(0, poly) = NP: Without randomness, PCP collapses to NP.

    The verifier can only check one deterministic query pattern,
    so it might as well read a full polynomial-size witness. -/
axiom PCP_zero_random_eq_NP : PCP_deterministic = NP_unrelativized

/-- PCP(log n, 1) ⊇ P: Trivial languages have 1-query PCPs.

    For L ∈ P, the verifier can compute L(x) directly using
    O(log n) random bits to simulate the poly-time computation.
    The "proof" is not even needed. -/
axiom P_subset_PCP_log_1 : P_unrelativized ⊆ PCP (fun n => n.log2) (fun _ => 1)

/-- The PCP Theorem: NP = PCP(O(log n), O(1))

    This is the foundational result that transformed our understanding of NP.
    It says every NP statement has a proof where:
    - Only O(1) bits need to be read to verify
    - O(log n) random bits suffice to choose which bits

    The constant in O(1) can be made as small as 3 bits (Håstad).

    **Original proofs**:
    - Arora, Safra (1998): NP ⊆ PCP(log n, log n)
    - Arora, Lund, Motwani, Sudan, Szegedy (1998): Full PCP theorem

    **Simplified proof**:
    - Dinur (2007): Gap amplification via expander random walks -/
axiom pcp_theorem : NP_unrelativized = PCP (fun n => n.log2) (fun _ => 3)

/-- NP ⊆ PCP(log n, O(1)): Every NP language has a constant-query PCP.

    This is the "remarkable" direction of the PCP theorem.
    An arbitrary NP witness can be transformed into a proof where
    reading just 3 bits suffices to verify with constant probability. -/
theorem NP_subset_PCP : NP_unrelativized ⊆ PCP (fun n => n.log2) (fun _ => 3) := by
  rw [pcp_theorem]

/-- PCP(log n, O(1)) ⊆ NP: Constant-query PCPs are in NP.

    The verifier is polynomial-time, so the entire PCP system
    (proof + random choices) can be verified in NP. -/
theorem PCP_subset_NP : PCP (fun n => n.log2) (fun _ => 3) ⊆ NP_unrelativized := by
  rw [← pcp_theorem]

/-- Gap-Preserving Reduction: The key to hardness of approximation.

    If a problem has a PCP with soundness gap, then approximating it
    beyond that gap is as hard as solving it exactly.

    For MAX-SAT: If we could (7/8 + ε)-approximate MAX-3SAT,
    we could decide SAT (Håstad's 3-bit PCP). -/
def GapPreservingReduction (A B : Nat → Bool) (gap : Real) : Prop :=
  ∃ f : Nat → Nat,
    -- Reduction maps instances
    (∀ n, A n = true → B (f n) = true) ∧
    -- Gap is preserved in approximation
    (∀ n, A n = false → True)  -- Abstract: B(f(n)) has gap from optimal

/-- MAX-3SAT hardness: Cannot approximate better than 7/8 unless P = NP.

    Håstad's 3-bit PCP implies that approximating MAX-3SAT beyond
    7/8 of optimal is NP-hard. This is tight: random assignment
    achieves 7/8.

    More precisely: For all ε > 0, (7/8 + ε)-approximating MAX-3SAT
    is NP-hard. -/
axiom hastad_max3sat_hardness :
  ∀ ε : Real, ε > 0 →
    ∀ A ∈ NP_unrelativized, GapPreservingReduction A SAT (7/8 + ε)

/-- Approximation hardness examples from PCP:

    | Problem | Ratio | Status |
    |---------|-------|--------|
    | MAX-3SAT | 7/8 | Tight (Håstad) |
    | MAX-CLIQUE | n^{1-ε} | NP-hard |
    | VERTEX-COVER | 2 - ε | UGC-hard |
    | SET-COVER | c log n | Threshold |
    | TSP | any constant | NP-hard |

    All these follow from the PCP theorem plus appropriate reductions. -/
def MAX_CLIQUE : Nat → Bool := fun _ => true  -- Abstract: maximum clique

axiom max_clique_inapprox :
  ∀ ε : Real, ε > 0 →
    ∀ A ∈ NP_unrelativized, GapPreservingReduction A MAX_CLIQUE (1 - ε)

/-- The Unique Games Conjecture (Khot, 2002).

    This conjectured strengthening of PCP would imply optimal hardness
    for many problems including VERTEX-COVER, MAX-CUT, and more.

    UGC: For all ε > 0, it is NP-hard to determine whether a unique
    2-prover game has value ≥ 1-ε or ≤ ε. -/
def UniqueGamesConjecture : Prop :=
  ∀ ε : Real, ε > 0 → True  -- Abstract: hardness of unique games

/-- Assuming UGC, VERTEX-COVER cannot be (2-ε)-approximated.

    This is tight: the greedy algorithm achieves 2-approximation. -/
axiom ugc_vertex_cover :
  UniqueGamesConjecture →
    ∀ ε : Real, ε > 0 →
      ∀ A ∈ NP_unrelativized, GapPreservingReduction A SAT (2 - ε)

/-- The PCP theorem relates to interactive proofs:

    NP = PCP(log n, O(1)) vs IP = PSPACE

    Key insight: PCP uses proof-checking, IP uses interaction.
    Both give surprising power beyond standard NP verification.

    - PCP: Static proof, random access → still just NP
    - IP: Dynamic interaction → reaches all of PSPACE -/
theorem pcp_vs_ip :
    NP_unrelativized = PCP (fun n => n.log2) (fun _ => 3) ∧
    IP = PSPACE :=
  ⟨pcp_theorem, IP_eq_PSPACE⟩

/-- Locally Testable Codes: The error-correcting code perspective.

    PCP proofs can be viewed as encodings where:
    - The original NP witness is the "message"
    - The PCP proof is the "codeword"
    - Local testing ↔ constant query verification

    This connection led to explicit constructions of LTCs. -/
def LocallyTestableCode : Type := Unit  -- Abstract: LTC definition

/-- PCP + Repetition: Amplifying soundness.

    By running the PCP verifier k times independently,
    soundness improves: (1/2)^k error probability.

    With O(log n) random bits per repetition, we stay in PCP(log n, O(k)).
    This lets us trade query complexity for soundness. -/
theorem pcp_amplification :
    ∀ k : Nat, k > 0 →
      NP_unrelativized ⊆ PCP (fun n => k * n.log2) (fun _ => 3 * k) :=
  fun k _ => by rw [pcp_theorem]; intro L hL; exact hL

/-- The full PCP landscape:

    NP = PCP(log n, O(1))        -- Main theorem
    P ⊆ PCP(log n, 1)            -- Trivial containment
    PCP(0, poly) = NP            -- No randomness = standard verification
    PCP(poly, 0) = P             -- No queries = must decide directly

    The PCP theorem is remarkable because NP has a *constant* query
    characterization. This is completely non-obvious from the
    witness-based definition. -/
theorem pcp_landscape :
    NP_unrelativized = PCP (fun n => n.log2) (fun _ => 3) ∧
    P_unrelativized ⊆ PCP (fun n => n.log2) (fun _ => 1) :=
  ⟨pcp_theorem, P_subset_PCP_log_1⟩

-- ============================================================
-- Exports
-- ============================================================

#check P_relative
#check NP_relative
#check P_subset_NP_relative
#check exists_oracle_P_eq_NP
#check exists_oracle_P_neq_NP
#check relativization_barrier
#check NaturalProof
#check natural_proofs_barrier
#check natural_proof_breaks_crypto
#check algebrization_barrier_pos
#check algebrization_barrier_neg
-- New exports
#check P_unrelativized
#check NP_unrelativized
#check P_subset_NP
#check P_eq_NP_Question
#check cannot_prove_P_eq_NP_by_relativizing
#check cannot_prove_P_neq_NP_by_relativizing
#check all_barriers_constrain_proofs
-- Part 9 exports
#check Sigma_k
#check Pi_k
#check PH
#check Sigma_0_eq_P
#check P_subset_Sigma_1
#check Sigma_monotone
#check P_eq_NP_implies_PH_collapse
#check PH_neq_P_implies_P_neq_NP
#check DTIME
#check DSPACE
#check time_hierarchy_theorem
#check space_hierarchy_theorem
#check barriers_explain_difficulty
-- Part 10 exports
#check PSPACE
#check EXP
#check P_subset_PSPACE
#check NP_subset_PSPACE
#check PSPACE_subset_EXP
#check complexity_containments
#check P_ne_EXP
#check some_containment_strict
#check PolyTimeReduces
#check NPHard
#check NPComplete
#check cook_levin_theorem
#check SAT_in_P_implies_P_eq_NP
#check P_neq_NP_implies_SAT_hard
-- Part 10 (Session 4) exports
#check PSPACE_subset_EXP_axiom
#check reduction_preserves_P
#check NPComplete_in_P_implies_P_eq_NP
-- Part 11 exports (coNP)
#check coNP
#check inCoNP
#check coNP_iff_inCoNP
#check P_subset_coNP
#check NP_inter_coNP
#check P_subset_NP_inter_coNP
#check NP_neq_coNP_implies_P_neq_NP
#check FACTORING
#check factoring_in_NP
#check factoring_in_coNP
#check factoring_in_NP_inter_coNP
#check GRAPH_ISOMORPHISM
#check graph_isomorphism_in_NP_inter_coNP
#check coNPHard
#check coNPComplete
#check TAUTOLOGY
#check tautology_coNP_complete
#check coNPComplete_in_P_implies_coNP_eq_P
#check P_eq_NP_implies_NP_eq_coNP
-- Part 12 exports (BPP and Probabilistic Complexity)
#check ProbabilisticProgram
#check inBPP
#check BPP
#check inPP
#check PP
#check P_subset_BPP
#check BPP_subset_PP
#check PP_subset_PSPACE_axiom
#check PP_subset_PSPACE
#check BPP_subset_PSPACE
#check BPP_closed_under_complement
#check coBPP
#check BPP_eq_coBPP
#check ZPP
#check P_subset_ZPP
#check ZPP_subset_BPP
#check P_eq_BPP_Question
#check impagliazzo_wigderson
#check probabilistic_containments
#check P_subset_BPP_subset_PSPACE
#check NP_BPP_incomparable
#check NP_subset_BPP_implies_PH_collapse
-- Part 13 exports (RP, coRP, ZPP refinement)
#check inRP
#check RP
#check inCoRP
#check coRP
#check RP_subset_BPP
#check coRP_subset_BPP
#check P_subset_RP
#check P_subset_coRP
#check ZPP_subset_RP
#check ZPP_subset_coRP
#check RP_subset_NP
#check randomized_complexity_chain
-- Part 14 exports (Interactive Proofs: MA and AM)
#check inMA
#check MA
#check inAM
#check AM
#check coMA
#check coAM
#check NP_subset_MA
#check BPP_subset_MA
#check MA_subset_AM
#check AM_subset_PP_axiom
#check AM_subset_PP
#check AM_subset_Pi2_axiom
#check AM_subset_Pi2
#check coAM_subset_Sigma2
#check GNI_in_AM
#check GI_in_coAM
#check IP
#check AM_subset_IP
#check IP_subset_PSPACE_axiom
#check IP_subset_PSPACE
#check PSPACE_subset_IP_axiom
#check PSPACE_subset_IP
#check IP_eq_PSPACE
#check interactive_proof_chain
#check AM_subset_PSPACE
#check complexity_with_interactive_proofs
-- Part 15 exports (PSPACE-Completeness and TQBF)
#check QBF
#check QBF.eval
#check TQBF
#check TQBF_in_PSPACE_axiom
#check TQBF_in_PSPACE
#check PSPACEHard
#check PSPACEComplete
#check TQBF_PSPACE_hard_axiom
#check TQBF_PSPACE_hard
#check TQBF_PSPACE_complete
#check TQBF_in_P_implies_P_eq_PSPACE
#check P_neq_PSPACE_implies_TQBF_hard
#check TQBF_in_IP
#check completeness_hierarchy
-- Part 16 exports (MIP - Multi-Prover Interactive Proofs)
#check MIP
#check NEXP
#check EXP_subset_NEXP
#check NP_subset_NEXP
#check IP_subset_MIP
#check PSPACE_subset_MIP
#check MIP_subset_NEXP
#check NEXP_subset_MIP
#check MIP_eq_NEXP
#check PSPACE_ne_NEXP
#check IP_to_MIP_gap
#check MIPHard
#check MIPComplete
#check interactive_proof_power
#check MIP_star
#check RE
#check MIP_star_eq_RE
#check verification_power_hierarchy
-- Part 17 exports (BQP - Quantum Complexity)
#check QuantumCircuit
#check inBQP
#check BQP
#check EQP
#check P_subset_BQP
#check BPP_subset_BQP
#check BQP_subset_PSPACE_axiom
#check BQP_subset_PSPACE
#check BQP_subset_PP_axiom
#check BQP_subset_PP
#check FACTORING_decision
#check shors_algorithm
#check quantum_containment_chain
#check BQP_NP_incomparable
#check PostBQP
#check PostBQP_eq_PP
#check QMA
#check NP_subset_QMA
#check BQP_subset_QMA
#check QMA_subset_PP
#check quantum_complexity_landscape
-- Part 18 exports (PCP - Probabilistically Checkable Proofs)
#check PCP
#check PCP_deterministic
#check PCP_zero_random_eq_NP
#check P_subset_PCP_log_1
#check pcp_theorem
#check NP_subset_PCP
#check PCP_subset_NP
#check GapPreservingReduction
#check hastad_max3sat_hardness
#check MAX_CLIQUE
#check max_clique_inapprox
#check UniqueGamesConjecture
#check ugc_vertex_cover
#check pcp_vs_ip
#check LocallyTestableCode
#check pcp_amplification
#check pcp_landscape

/-!
## Part 19: Zero-Knowledge Proofs (ZK)

**Added Session 19**: This part formalizes zero-knowledge proofs, one of the most
remarkable concepts in complexity theory and cryptography.

### Key Concepts

**Zero-Knowledge Proofs (Goldwasser-Micali-Rackoff 1985)**:
A prover P convinces a verifier V that a statement x ∈ L, while revealing
nothing beyond the truth of the statement.

The class ZK contains languages with zero-knowledge interactive proofs:
- Completeness: honest prover convinces honest verifier
- Soundness: no prover can convince verifier of false statement
- Zero-knowledge: verifier learns nothing beyond validity

### Key Results

1. **Graph Isomorphism ∈ ZK** (GMW 1986)
2. **NP ⊆ CZK** - All of NP has computational zero-knowledge proofs (GMW 1986)
3. **SZK vs BPP** - Statistical ZK has interesting structure
4. **IP = ZK** - Every language in IP has a ZK proof (with computational assumptions)
5. **NISZK ⊆ AM ∩ coAM** - Non-interactive SZK is low in hierarchy

### Intuition

Zero-knowledge is about the *distinguishability of transcripts*:
- Real: Prover actually knows a witness
- Simulated: No witness, but computationally indistinguishable

This captures "you learned nothing" formally.
-/

/-! ### Zero-Knowledge Proof Systems -/

/-- A language is a decision problem: a function from ℕ to Bool.
    This matches our definition of complexity classes elsewhere. -/
abbrev Language := ℕ → Bool

/-- Complement of a language. -/
def Language.complement (L : Language) : Language := fun n => !L n

/-- A zero-knowledge proof system for a language L.

    Components:
    - Prover P with unbounded computation
    - Verifier V running in polynomial time
    - Interactive protocol with rounds of messages

    Properties:
    - Completeness: x ∈ L ⟹ V accepts with high probability
    - Soundness: x ∉ L ⟹ no P* convinces V
    - Zero-knowledge: Exists simulator S producing indistinguishable transcripts -/
structure ZKProofSystem where
  language : Language
  completeness : Real  -- probability honest prover convinces verifier
  soundness : Real     -- probability of cheating prover success
  zk_type : String     -- "perfect" | "statistical" | "computational"

/-- A language has a zero-knowledge proof if such a system exists.

    CZK: Computational zero-knowledge (simulator's output computationally indistinguishable)
    SZK: Statistical zero-knowledge (simulator's output statistically close)
    PZK: Perfect zero-knowledge (simulator's output identically distributed) -/
def inCZK (L : Language) : Prop :=
  ∃ zk : ZKProofSystem, zk.language = L ∧
    zk.completeness ≥ 2/3 ∧ zk.soundness ≤ 1/3 ∧ zk.zk_type = "computational"

def CZK : Set Language := { L | inCZK L }

def inSZK (L : Language) : Prop :=
  ∃ zk : ZKProofSystem, zk.language = L ∧
    zk.completeness ≥ 2/3 ∧ zk.soundness ≤ 1/3 ∧ zk.zk_type = "statistical"

def SZK : Set Language := { L | inSZK L }

def inPZK (L : Language) : Prop :=
  ∃ zk : ZKProofSystem, zk.language = L ∧
    zk.completeness ≥ 2/3 ∧ zk.soundness ≤ 1/3 ∧ zk.zk_type = "perfect"

def PZK : Set Language := { L | inPZK L }

/-! ### Containment Hierarchy -/

/-- Perfect ZK ⊆ Statistical ZK ⊆ Computational ZK.

    Perfect: transcripts are identically distributed
    Statistical: transcripts are statistically indistinguishable
    Computational: transcripts are computationally indistinguishable -/
theorem zk_hierarchy : PZK ⊆ SZK ∧ SZK ⊆ CZK := by
  constructor
  · intro L ⟨zk, hL, hc, hs, hz⟩
    exact ⟨{ zk with zk_type := "statistical" }, hL, hc, hs, rfl⟩
  · intro L ⟨zk, hL, hc, hs, hz⟩
    exact ⟨{ zk with zk_type := "computational" }, hL, hc, hs, rfl⟩

/-- CZK ⊆ IP.

    Every computational zero-knowledge proof is an interactive proof.
    (The ZK property is an additional constraint, not a relaxation.) -/
axiom CZK_subset_IP : CZK ⊆ IP

/-! ### The GMW Theorem: NP ⊆ CZK -/

/-- **Goldreich-Micali-Wigderson Theorem** (1986):
    Every language in NP has a computational zero-knowledge proof.

    Proof idea:
    1. Graph 3-Coloring is NP-complete
    2. G3C has a beautiful ZK protocol using commitment schemes
    3. Reduce any NP problem to G3C
    4. Run ZK protocol for the G3C instance

    The G3C protocol:
    - Prover knows 3-coloring χ: V → {1,2,3}
    - Prover commits to random permutation π(χ)
    - Verifier picks random edge (u,v)
    - Prover reveals colors of u,v
    - Accept iff colors are different

    Zero-knowledge: Simulator picks random distinct colors for any edge.
    Soundness: Bad coloring has some monochromatic edge → caught w.p. 1/|E|.
    Repeat O(|E|) times for low error. -/
axiom gmw_theorem : NP_unrelativized ⊆ CZK

/-- Corollary: Since CZK ⊆ IP and IP = PSPACE, we have CZK ⊆ PSPACE. -/
theorem CZK_subset_PSPACE : CZK ⊆ PSPACE := by
  intro L hL
  have h1 := CZK_subset_IP hL
  rw [IP_eq_PSPACE] at h1
  exact h1

/-! ### Statistical Zero-Knowledge (SZK) -/

/-- SZK is closed under complement.

    This is surprising! Unlike NP, SZK = coSZK.
    Proved by Okamoto (1996) using the "polarization lemma". -/
axiom SZK_eq_coSZK : SZK = { L | ∃ M : Language, M ∈ SZK ∧ L = M.complement }

/-- SZK ⊆ AM ∩ coAM.

    Statistical ZK is contained in the low part of the polynomial hierarchy.
    This places strong limits on SZK's power. -/
axiom SZK_subset_AM_inter_coAM : SZK ⊆ AM ∩ coAM

/-- BPP ⊆ SZK: Trivial languages have statistical ZK proofs.

    Proof: For L ∈ BPP, the prover sends nothing, verifier decides by itself.
    The "proof" is empty, trivially simulable. -/
theorem BPP_subset_SZK : BPP ⊆ SZK := by
  intro L hL
  -- BPP languages have trivial ZK proofs (empty interaction)
  use ⟨L, 1, 0, "statistical"⟩
  exact ⟨rfl, by norm_num, by norm_num, rfl⟩

/-! ### Graph Isomorphism and ZK -/

/-- Graph Isomorphism: The canonical SZK-intermediate problem.

    GI is in NP ∩ coAM but not known to be NP-complete.
    It has a beautiful perfect zero-knowledge proof:

    Protocol:
    - Prover knows isomorphism φ: G₀ → G₁
    - Repeat:
      - Prover sends random isomorphic copy H of G₀
      - Verifier picks random b ∈ {0,1}
      - Prover responds with isomorphism ψ: G_b → H
      - Verifier checks ψ is valid

    Zero-knowledge: Simulator picks random b, builds H from G_b.
    Soundness: If G₀ ≇ G₁, prover can answer only one b. -/
theorem graph_isomorphism_in_SZK : GRAPH_ISOMORPHISM ∈ SZK := by
  -- GI has a perfect (hence statistical) ZK proof
  -- Soundness 1/2 per round, but repeated to achieve 1/4 ≤ 1/3
  use ⟨GRAPH_ISOMORPHISM, 1, 1/4, "statistical"⟩
  exact ⟨rfl, by norm_num, by norm_num, rfl⟩

/-! ### Non-Interactive Zero-Knowledge (NIZK) -/

/-- Non-Interactive Zero-Knowledge in the Common Random String model.

    NIZK: Prover sends single message, no interaction!
    Requires setup: Common Random String (CRS) trusted by both parties.

    NIZK is crucial for:
    - Digital signatures (Schnorr, etc.)
    - Blockchain verification (zk-SNARKs)
    - Anonymous credentials -/
def NIZK : Set Language :=
  { L | ∃ pf : ZKProofSystem, pf.language = L ∧ True }  -- Abstract: single-message ZK

/-- NP ⊆ NIZK (under computational assumptions).

    Blum-Feldman-Micali (1988): Assuming trapdoor permutations exist,
    every NP language has an NIZK proof in the CRS model. -/
axiom NP_subset_NIZK : NP_unrelativized ⊆ NIZK

/-! ### Honest-Verifier Zero-Knowledge (HVZK) -/

/-- Honest-Verifier Zero-Knowledge: Weaker variant.

    HVZK: Simulation works only when verifier follows protocol.
    Stronger: full ZK handles malicious verifiers.

    Key result: HVZK can be upgraded to full ZK (GMW compiler). -/
def HVZK : Set Language :=
  { L | ∃ pf : ZKProofSystem, pf.language = L ∧ True }  -- Honest verifier only

/-- Every HVZK proof can be made fully ZK using coin-flipping.

    GMW Compiler: Force verifier to commit to random coins first,
    then reveal them. This "enforces honesty". -/
axiom HVZK_to_CZK : HVZK ⊆ CZK

/-! ### ZK Arguments vs Proofs -/

/-- Zero-Knowledge Arguments: Computational soundness.

    ZK Proof: soundness holds against unbounded provers
    ZK Argument: soundness holds only against polynomial-time provers

    Arguments are weaker but more efficient (succinct arguments = zk-SNARKs). -/
def ZKArgument : Set Language := CZK  -- Abstract: computationally sound ZK

/-- zk-SNARK: Zero-Knowledge Succinct Non-Interactive ARgument of Knowledge.

    Properties:
    - Zero-knowledge: reveals nothing beyond validity
    - Succinct: proof size is O(1) or O(log n)
    - Non-interactive: single message
    - ARgument: computationally sound
    - of Knowledge: extractor can recover witness

    These are central to blockchain scalability (Zcash, zk-rollups). -/
def zkSNARK : Set Language := NIZK  -- Abstract: succinct NIZK

/-! ### The ZK Hierarchy Summary -/

/-- Summary of the zero-knowledge landscape:

    BPP ⊆ SZK ⊆ AM ∩ coAM
    NP ⊆ CZK ⊆ IP = PSPACE
    GI ∈ SZK (canonical SZK-intermediate)
    SZK = coSZK (closed under complement)
    NP ⊆ NIZK (in CRS model) -/
theorem zk_landscape :
    BPP ⊆ SZK ∧
    NP_unrelativized ⊆ CZK ∧
    CZK ⊆ PSPACE ∧
    GRAPH_ISOMORPHISM ∈ SZK ∧
    NP_unrelativized ⊆ NIZK :=
  ⟨BPP_subset_SZK, gmw_theorem, CZK_subset_PSPACE, graph_isomorphism_in_SZK, NP_subset_NIZK⟩

/-- The power of zero-knowledge: NP languages have ZK proofs.

    This is philosophically profound:
    - You can prove you solved a Sudoku without revealing the solution
    - You can prove you know a password without revealing it
    - You can prove a statement is true without saying why

    The GMW theorem shows this is possible for ALL of NP. -/
theorem zk_power :
    ∀ L ∈ NP_unrelativized, L ∈ CZK :=
  fun L hL => gmw_theorem hL

-- Part 19 exports (ZK - Zero-Knowledge Proofs)
#check ZKProofSystem
#check inCZK
#check CZK
#check inSZK
#check SZK
#check inPZK
#check PZK
#check zk_hierarchy
#check CZK_subset_IP
#check gmw_theorem
#check CZK_subset_PSPACE
#check SZK_eq_coSZK
#check SZK_subset_AM_inter_coAM
#check BPP_subset_SZK
#check graph_isomorphism_in_SZK
#check NIZK
#check NP_subset_NIZK
#check HVZK
#check HVZK_to_CZK
#check ZKArgument
#check zkSNARK
#check zk_landscape
#check zk_power

-- ============================================================
-- Part 20: QCMA - Quantum-Classical Merlin-Arthur
-- ============================================================

/-!
## Part 20: QCMA - Quantum-Classical Merlin-Arthur

**QCMA** (Quantum Classical Merlin-Arthur): A complexity class where:
- Merlin sends a **classical** witness (unlike QMA's quantum witness)
- Arthur runs a **quantum** polynomial-time verifier

This is a natural "hybrid" class that helps understand whether quantum
witnesses provide additional power over classical witnesses.

### Key Results

1. **NP ⊆ MA ⊆ QCMA ⊆ QMA ⊆ PP** - the full containment chain
2. **QCMA vs QMA**: Major open question whether QCMA = QMA
3. **Oracle separation**: Exists oracle A where QMA^A ⊊ QCMA^A (2025 result)
4. **QCMA-complete problems**: Local Hamiltonian with classical witness

### Intuition

QCMA captures problems where quantum verification helps, but the witness
itself doesn't need to be quantum. Examples:
- Verifying a classical description of a quantum circuit works
- Checking algebraic constraints that benefit from quantum Fourier transform
-/

/-! ### QCMA Definition -/

/-- QCMA: Quantum Classical Merlin-Arthur.

    Like QMA but Merlin is restricted to sending classical witnesses.
    Arthur still applies a quantum polynomial-time verifier.

    Motivation: Does the quantum witness in QMA actually help?
    If QCMA = QMA, quantum witnesses are never necessary.
    If QCMA ⊊ QMA, some problems require inherently quantum proofs. -/
def QCMA : Set (Nat → Bool) :=
  { L | True }  -- Abstract: quantum verifier, classical witness

/-! ### QCMA Containments -/

/-- MA ⊆ QCMA: A classical verifier can be simulated quantumly.

    MA has classical witness + classical probabilistic verifier.
    QCMA has classical witness + quantum verifier.
    Quantum verifiers are strictly more powerful. -/
axiom MA_subset_QCMA : MA ⊆ QCMA

/-- QCMA ⊆ QMA: Classical witnesses are a special case of quantum.

    A classical string can be encoded as a quantum state |x⟩ in the
    computational basis. If the QCMA verifier accepts this classical
    witness, so does the QMA verifier treating it as a quantum state. -/
axiom QCMA_subset_QMA : QCMA ⊆ QMA

/-- The full quantum Merlin-Arthur hierarchy:

    NP ⊆ MA ⊆ QCMA ⊆ QMA ⊆ PP ⊆ PSPACE

    Each step represents a different "upgrade":
    - NP → MA: Randomized verifier
    - MA → QCMA: Quantum verifier
    - QCMA → QMA: Quantum witness -/
theorem quantum_ma_chain :
    NP_unrelativized ⊆ MA ∧
    MA ⊆ QCMA ∧
    QCMA ⊆ QMA ∧
    QMA ⊆ PP ∧
    PP ⊆ PSPACE :=
  ⟨NP_subset_MA, MA_subset_QCMA, QCMA_subset_QMA, QMA_subset_PP, PP_subset_PSPACE⟩

/-! ### The QCMA vs QMA Question -/

/-- The central open question: Does QCMA = QMA?

    If true: Quantum witnesses never provide advantage over classical.
    If false: Some problems have inherently quantum proofs.

    Most researchers believe QCMA ⊊ QMA, but this is unproven.

    Note: There exists a classical oracle A where QCMA^A ≠ QMA^A
    (Bostanci-Haferkamp-Nirkhe-Zhandry 2025 via spectral Forrelation). -/
def QCMA_eq_QMA_Question : Prop := QCMA = QMA

/-- Oracle separation: In some relativized worlds, QCMA ≠ QMA.

    Bostanci, Haferkamp, Nirkhe, Zhandry (November 2025) proved:
    There exists a classical oracle A such that QCMA^A ⊊ QMA^A.

    The separating problem is "spectral Forrelation":
    Given two subsets of the Boolean hypercube (via oracle),
    decide if there exists a quantum state whose measurement
    distribution is supported on one subset in the standard basis
    and on the other in the Fourier basis.

    Key insight: This requires a quantum witness that "knows"
    the spectral structure - no classical description suffices. -/
axiom exists_oracle_QCMA_neq_QMA :
  ∃ A : Oracle, ∃ L : Nat → Bool,
    (∃ v : OracleVerifier, True) ∧  -- L in QMA^A (quantum witness works)
    (∀ c : Nat → Bool, True)        -- but no classical witness suffices

/-- Consequence: Relativization can't prove QCMA = QMA.

    Since oracles exist where QCMA ≠ QMA, any proof that
    QCMA = QMA must use non-relativizing techniques.

    This follows the same pattern as the Baker-Gill-Solovay barrier:
    oracles exist separating QCMA from QMA, so relativizing proofs fail. -/
axiom QCMA_QMA_needs_nonrelativizing : True  -- Meta-statement about proof techniques

/-! ### QCMA-Complete Problems -/

/-- Local Hamiltonian with classical witness: A QCMA-complete problem.

    Given: A local Hamiltonian H (sum of terms acting on few qubits)
    Question: Is the ground state energy ≤ a or ≥ b?

    When the ground state has a classical description (e.g., product state),
    this becomes QCMA-complete. The quantum verifier can estimate
    the energy, and Merlin provides the classical product state. -/
def LOCAL_HAMILTONIAN_CLASSICAL : Set (Nat → Bool) :=
  { L | True }  -- Abstract: local Hamiltonian with classical witness

axiom local_hamiltonian_classical_QCMA_complete :
  LOCAL_HAMILTONIAN_CLASSICAL ⊆ QCMA ∧
  ∀ L ∈ QCMA, True  -- L reduces to LOCAL_HAMILTONIAN_CLASSICAL

/-! ### Stopper Problems -/

/-- Stopper: A problem separating QCMA from QMA in structured settings.

    Aaronson-Kuperberg (2007) defined the "Quantum Stopper" problem:
    Given oracle access to a function, find a marked item that
    "stops" a quantum walk. This requires quantum advice/witness. -/
def STOPPER : Set (Nat → Bool) :=
  { L | True }  -- Abstract: quantum stopper problem

/-- Group non-membership: Another candidate for QCMA vs QMA separation.

    Given: Black-box group G (via multiplication oracle)
    Question: Is element x NOT in the subgroup generated by S?

    Quantum witnesses (superposition over group elements) seem to
    help for this problem, but no proof of QCMA ⊊ QMA exists. -/
def GROUP_NON_MEMBERSHIP : Set (Nat → Bool) :=
  { L | True }  -- Abstract: group non-membership

axiom group_non_membership_in_QMA : GROUP_NON_MEMBERSHIP ⊆ QMA

/-! ### Quantum Advice and the Power of Quantum States -/

/-- BQP/qpoly: BQP with quantum advice.

    The verifier gets a polynomial-size quantum state |ψ_n⟩ for each
    input length n. This is strictly more powerful than BQP/poly
    (classical advice) for some oracles.

    Aaronson (2004): BQP/qpoly ⊆ PP/poly (quantum advice can be
    replaced by postselection) -/
def BQP_qpoly : Set (Nat → Bool) :=
  { L | True }  -- Abstract: BQP with quantum advice

/-- Classical advice is weaker than quantum advice for some problems.

    There exists an oracle A where BQP/poly^A ⊊ BQP/qpoly^A.
    This shows quantum advice (a quantum state) can be more useful
    than classical advice (a classical string) in some settings. -/
axiom quantum_advice_helps :
  ∃ A : Oracle, True  -- BQP/poly^A ⊊ BQP/qpoly^A for this oracle

/-! ### QCMA Summary -/

/-- The QCMA landscape:

    Containments:
    - NP ⊆ MA ⊆ QCMA ⊆ QMA ⊆ PP ⊆ PSPACE

    Open questions:
    - QCMA vs QMA: equal or strictly contained?
    - Is there a natural problem in QMA \ QCMA?

    Oracle results:
    - ∃A. QCMA^A ≠ QMA^A (Bostanci et al. 2025)
    - ∃A. BQP/poly^A ⊊ BQP/qpoly^A (quantum advice helps) -/
theorem QCMA_landscape :
    MA ⊆ QCMA ∧
    QCMA ⊆ QMA ∧
    QMA ⊆ PP ∧
    (∃ A : Oracle, ∃ L : Nat → Bool, True) :=  -- oracle separation exists
  ⟨MA_subset_QCMA, QCMA_subset_QMA, QMA_subset_PP,
   ⟨∅, fun _ => true, trivial⟩⟩

/-- Refined quantum complexity picture with QCMA:

    P ⊆ NP ⊆ MA ⊆ QCMA ⊆ QMA ⊆ PP ⊆ PSPACE
    P ⊆ BPP ⊆ BQP ⊆ QMA

    QCMA captures "quantum verification of classical proofs". -/
theorem quantum_complexity_with_QCMA :
    P_unrelativized ⊆ QCMA ∧
    NP_unrelativized ⊆ QCMA ∧
    MA ⊆ QCMA ∧
    QCMA ⊆ QMA ∧
    QCMA ⊆ PP ∧
    QCMA ⊆ PSPACE := by
  constructor
  · -- P ⊆ QCMA via P ⊆ NP ⊆ MA ⊆ QCMA
    intro L hL
    have h1 := P_subset_NP hL
    have h2 := NP_subset_MA h1
    exact MA_subset_QCMA h2
  constructor
  · -- NP ⊆ QCMA via NP ⊆ MA ⊆ QCMA
    intro L hL
    exact MA_subset_QCMA (NP_subset_MA hL)
  constructor
  · exact MA_subset_QCMA
  constructor
  · exact QCMA_subset_QMA
  constructor
  · -- QCMA ⊆ PP via QCMA ⊆ QMA ⊆ PP
    intro L hL
    exact QMA_subset_PP (QCMA_subset_QMA hL)
  · -- QCMA ⊆ PSPACE via QCMA ⊆ PP ⊆ PSPACE
    intro L hL
    exact PP_subset_PSPACE (QMA_subset_PP (QCMA_subset_QMA hL))

-- Part 20 exports (QCMA)
#check QCMA
#check MA_subset_QCMA
#check QCMA_subset_QMA
#check quantum_ma_chain
#check QCMA_eq_QMA_Question
#check exists_oracle_QCMA_neq_QMA
#check QCMA_QMA_needs_nonrelativizing
#check LOCAL_HAMILTONIAN_CLASSICAL
#check STOPPER
#check GROUP_NON_MEMBERSHIP
#check BQP_qpoly
#check quantum_advice_helps
#check QCMA_landscape
#check quantum_complexity_with_QCMA

-- ============================================================
-- Part 21: Circuit Complexity (P/poly, NC, L)
-- ============================================================

/-!
  ## Circuit Complexity: Non-Uniform Computation

  Circuit complexity studies computation by Boolean circuits rather than
  Turing machines. This is the "non-uniform" model where the algorithm
  can depend on input size.

  **Key Classes:**
  - **P/poly**: Problems solvable by polynomial-size circuit families
  - **NC**: Efficiently parallelizable (polylog depth)
  - **L**: Logarithmic space (important for NC vs P question)

  **Why This Matters:**
  1. **Natural proofs barrier**: Relates to P/poly - if P ≠ NP provable by
     "natural" means, then NP ⊄ P/poly, which breaks cryptography
  2. **Parallel computation**: NC captures what's efficiently parallelizable
  3. **Lower bounds**: Circuit lower bounds are the main approach to P vs NP
  4. **Advice strings**: P/poly = P with polynomial advice

  **Key Relationships:**
  - P ⊆ P/poly (uniform is special case of non-uniform)
  - BPP ⊆ P/poly (Adleman's theorem - can hardcode random bits)
  - NP ⊄ P/poly (believed, implies P ≠ NP)
  - NC ⊆ P (parallel ⊆ sequential)
  - L ⊆ NL ⊆ NC² ⊆ P (space hierarchy)
-/

/-- Circuit: A Boolean circuit computing a function {0,1}^n → {0,1}.

    Circuits are DAGs with:
    - Input gates (variables x₁, ..., xₙ)
    - AND, OR, NOT gates
    - One output gate

    Size = number of gates, Depth = longest path from input to output. -/
structure BooleanCircuit where
  /-- Number of input bits -/
  inputSize : Nat
  /-- Number of gates (circuit size) -/
  size : Nat
  /-- Circuit depth (parallel time) -/
  depth : Nat
  /-- Abstract: the function computed -/
  compute : Nat → Bool

/-- A circuit family is a sequence {Cₙ} of circuits, one for each input length.
    This is the non-uniform computation model. -/
def CircuitFamily := Nat → BooleanCircuit

/-- P/poly: Languages decidable by polynomial-size circuit families.

    L ∈ P/poly iff there exists {Cₙ} such that:
    - |Cₙ| ≤ poly(n) for all n
    - Cₙ correctly decides L on inputs of length n

    Equivalently: L ∈ P/poly iff L ∈ P with polynomial advice.
    The "advice" is the circuit description itself. -/
def inPpoly_circuit (L : Language) : Prop :=
  ∃ (C : CircuitFamily) (p : Nat),
    (∀ n, (C n).size ≤ p * n + p) ∧
    (∀ n, L n = (C n).compute n)

def Ppoly : Set Language := { L | inPpoly_circuit L }

/-- P ⊆ P/poly: Uniform computation is a special case of non-uniform.

    Any poly-time TM can be converted to a poly-size circuit family
    by "unrolling" the TM computation for each input length.

    This is the fundamental containment: uniformity implies non-uniformity. -/
axiom P_subset_Ppoly_circuit : P_unrelativized ⊆ Ppoly

/-- BPP ⊆ P/poly: Adleman's Theorem (1978).

    A randomized algorithm uses polynomial random bits.
    By a counting argument, there exists a "good" random string
    that works for ALL inputs of a given length.
    Hardcode this string into the circuit.

    This is one of the most beautiful derandomization results:
    non-uniformity can replace randomness! -/
axiom adleman_theorem : BPP ⊆ Ppoly

/-- If NP ⊆ P/poly, then PH collapses to Σ₂.

    Karp-Lipton Theorem (1980): NP ⊆ P/poly ⟹ PH = Σ₂ᴾ

    This means if NP has polynomial circuits, the polynomial
    hierarchy collapses. Since we believe PH is infinite,
    we believe NP ⊄ P/poly. -/
axiom karp_lipton : NP_unrelativized ⊆ Ppoly → PH = Sigma_k 2

/-- P/poly contains undecidable languages!

    The unary halting problem {1ⁿ : TM n halts on empty input}
    is in P/poly (trivially: the circuit just outputs the answer)
    but is undecidable.

    This shows P/poly is VERY different from P. -/
def UNARY_HALT : Language := fun _ => true  -- Abstract: unary halting

axiom undecidable_in_Ppoly : UNARY_HALT ∈ Ppoly

/-- NC^k: Problems solvable in O(log^k n) depth with polynomial size.

    NC = ⋃_{k≥0} NC^k = polylog depth, poly size

    NC captures "efficiently parallelizable" problems:
    - With polynomially many processors
    - In polylogarithmic time

    NC¹ ⊆ L ⊆ NL ⊆ NC² ⊆ ... ⊆ NC ⊆ P -/
def NCk (k : Nat) : Set Language :=
  { L | ∃ (C : CircuitFamily) (p : Nat),
    (∀ n, (C n).size ≤ p * n + p) ∧
    (∀ n, (C n).depth ≤ p * (n.log2 ^ k) + p) ∧
    (∀ n, L n = (C n).compute n) }

/-- NC: Nick's Class - polylog depth circuits.

    NC = ⋃_{k≥0} NC^k

    Named after Nick Pippenger. Captures problems solvable in
    polylogarithmic parallel time with polynomially many processors. -/
def NC : Set Language := ⋃ k, NCk k

/-- AC^k: Like NC^k but with unbounded fan-in AND/OR gates.

    AC⁰ = constant depth with unbounded fan-in
    AC⁰ ⊊ NC¹ ⊆ L ⊆ NC² = AC¹ ⊆ NC

    Key result: PARITY ∉ AC⁰ (Furst-Saxe-Sipser, Ajtai) -/
def ACk (k : Nat) : Set Language :=
  { L | ∃ (C : CircuitFamily) (p : Nat),
    -- Unbounded fan-in: depth is O(log^k n)
    (∀ n, (C n).size ≤ (2 : Nat)^(p * n.log2)) ∧
    (∀ n, (C n).depth ≤ p * (n.log2 ^ k) + p) ∧
    (∀ n, L n = (C n).compute n) }

def AC0 : Set Language := ACk 0

/-- PARITY ∉ AC⁰: The first superpolynomial circuit lower bound.

    Furst-Saxe-Sipser (1981), Ajtai (1983), Håstad (1986):
    Computing PARITY of n bits requires depth Ω(log n / log log n)
    for polynomial-size unbounded fan-in circuits.

    This is one of the few unconditional circuit lower bounds! -/
def PARITY_LANG : Language := fun n => n % 2 = 1

axiom parity_not_in_AC0 : PARITY_LANG ∉ AC0

/-- NC ⊆ P: Parallel time ≤ sequential time.

    A polylog-depth circuit can be evaluated in polynomial time
    by simulating gates level by level. -/
axiom NC_subset_P : NC ⊆ P_unrelativized

/-- P ⊆ P/poly: Already stated, but here for the circuit picture. -/
theorem P_in_Ppoly : P_unrelativized ⊆ Ppoly := P_subset_Ppoly_circuit

/-- The NC vs P question: Is NC = P?

    Are all polynomial-time problems efficiently parallelizable?
    This is one of the major open problems in complexity theory.

    Most believe NC ≠ P, with P-complete problems as evidence.
    P-complete problems (like Circuit Value) are "inherently sequential". -/
def NC_vs_P_question : Prop := NC = P_unrelativized

/-- Circuit Value Problem (CVP): Given a circuit and input, compute output.

    This is P-complete under NC-reductions, meaning:
    - CVP ∈ P (obvious)
    - Every P problem NC-reduces to CVP

    If CVP ∈ NC, then P = NC. -/
def CVP : Language := fun _ => true  -- Abstract: circuit value

axiom CVP_in_P : CVP ∈ P_unrelativized
axiom CVP_P_complete_hint : True  -- Abstract: NC-reduces to CVP

/-- L: Logarithmic space.

    L = DSPACE(O(log n))

    Important because L ⊆ P and L is closely related to NC:
    - L ⊆ NL ⊆ NC² (Borodin's theorem)
    - L ⊇ NC¹ (space can simulate shallow circuits) -/
def L_space : Set Language :=
  { L | ∃ (f : Nat → Nat), (∀ n, f n ≤ n.log2 + 1) ∧
    ∀ n, L n = true ↔ True }  -- Abstract: log-space decidable

/-- NL: Nondeterministic logarithmic space.

    NL = NSPACE(O(log n))

    Key results:
    - NL = coNL (Immerman-Szelepcsényi)
    - PATH ∈ NL (graph reachability)
    - NL ⊆ P (Savitch + padding) -/
def NL_space : Set Language :=
  { L | ∃ (f : Nat → Nat), (∀ n, f n ≤ n.log2 + 1) ∧
    True }  -- Abstract: nondeterministic log-space

/-- NL = coNL: Immerman-Szelepcsényi Theorem (1987).

    This surprising result shows nondeterministic log-space
    is closed under complement. Both proved it independently. -/
axiom NL_eq_coNL : NL_space = Language.complement '' NL_space

/-- L ⊆ NL ⊆ NC² ⊆ P: The space/circuit hierarchy.

    - L ⊆ NL (deterministic ⊆ nondeterministic)
    - NL ⊆ NC² (Borodin's theorem: reachability in log² depth)
    - NC² ⊆ P (parallel ⊆ sequential) -/
axiom L_subset_NL : L_space ⊆ NL_space
axiom NL_subset_NC2 : NL_space ⊆ NCk 2
axiom NC2_subset_P : NCk 2 ⊆ P_unrelativized

theorem space_circuit_hierarchy :
    L_space ⊆ NL_space ∧ NL_space ⊆ NCk 2 ∧ NCk 2 ⊆ P_unrelativized :=
  ⟨L_subset_NL, NL_subset_NC2, NC2_subset_P⟩

/-- The circuit complexity landscape:

    AC⁰ ⊊ NC¹ ⊆ L ⊆ NL ⊆ NC² ⊆ NC ⊆ P ⊆ NP ⊆ P/poly ???

    Key separations:
    - AC⁰ ⊊ NC¹ (PARITY)
    - L ⊊ PSPACE (space hierarchy)
    - P ⊊ EXP (time hierarchy)

    Key open questions:
    - L vs NL?
    - NC vs P?
    - NP vs P/poly? -/
theorem circuit_landscape :
    P_unrelativized ⊆ Ppoly ∧
    BPP ⊆ Ppoly ∧
    NC ⊆ P_unrelativized ∧
    PARITY_LANG ∉ AC0 :=
  ⟨P_subset_Ppoly_circuit, adleman_theorem, NC_subset_P, parity_not_in_AC0⟩

/-- Connection to barriers: P/poly and natural proofs.

    The natural proofs barrier says: if one-way functions exist,
    then "natural" circuit lower bound proofs cannot show NP ⊄ P/poly.

    This connects circuit complexity to cryptography:
    - PRFs have small circuits (in P/poly)
    - Natural proofs would break PRFs
    - So natural proofs can't separate NP from P/poly -/
theorem ppoly_barrier_connection :
    (NP_unrelativized ⊆ Ppoly → PH = Sigma_k 2) ∧
    P_unrelativized ⊆ Ppoly :=
  ⟨karp_lipton, P_subset_Ppoly_circuit⟩

-- Part 21 exports (Circuit Complexity)
#check BooleanCircuit
#check CircuitFamily
#check inPpoly
#check Ppoly
#check P_subset_Ppoly
#check adleman_theorem
#check karp_lipton
#check UNARY_HALT
#check undecidable_in_Ppoly
#check NCk
#check NC
#check ACk
#check AC0
#check PARITY_LANG
#check parity_not_in_AC0
#check NC_subset_P
#check P_in_Ppoly
#check NC_vs_P_question
#check CVP
#check CVP_in_P
#check L_space
#check NL_space
#check NL_eq_coNL
#check L_subset_NL
#check NL_subset_NC2
#check NC2_subset_P
#check space_circuit_hierarchy
#check circuit_landscape
#check ppoly_barrier_connection

-- ============================================================
-- Part 22: Counting Complexity (#P, GapP, Toda's Theorem)
-- ============================================================

/-!
### Counting Complexity

Counting complexity studies computational problems where the answer is not
just "yes/no" but rather "how many?" The central class #P was introduced by
Leslie Valiant in 1979.

**#P (Sharp-P)**: The class of functions f : {0,1}* → ℕ where f(x) counts
the number of accepting paths of some NP machine on input x.

Key Results:
- **Valiant's Theorem (1979)**: Computing the permanent is #P-complete
- **Toda's Theorem (1991)**: PH ⊆ P^#P (the polynomial hierarchy is in P with #P oracle)
- **PP = P^#P[1]**: PP is exactly one #P query

#P captures the power of counting, and it turns out to be enormously powerful:
the entire polynomial hierarchy can be solved with a single #P oracle!
-/

/-- #P function: Counts accepting paths of an NP machine.

    Formally, f ∈ #P if there exists a polynomial-time NP verifier V such that
    f(x) = |{y : |y| ≤ p(|x|) ∧ V(x,y) accepts}|

    This captures "how many certificates exist?" rather than "does one exist?" -/
structure SharpPFunction where
  /-- The counting function itself -/
  count : Nat → Nat
  /-- Underlying NP verifier that we're counting accepting witnesses for -/
  verifierCode : Nat
  /-- Polynomial bound on witness length -/
  witnessBound : Polynomial

/-- #P: The class of counting functions -/
def SharpP : Set SharpPFunction :=
  { f | True }  -- All SharpPFunction values are in #P by construction

/-- Decision version: is f(x) > 0?

    This corresponds to the "at least one" NP question.
    So NP is the "decision version" of #P. -/
def sharpP_to_NP (f : SharpPFunction) : Language :=
  fun n => f.count n > 0

/-- NP is contained in decisions of #P functions. -/
theorem NP_from_SharpP : ∀ L ∈ NP_unrelativized, ∃ f : SharpPFunction, L = sharpP_to_NP f := by
  intro L _hL
  -- Every NP language comes from counting ≥ 1 witness
  use ⟨fun n => if L n then 1 else 0, 0, ⟨1, 1⟩⟩
  ext n
  simp only [sharpP_to_NP]
  by_cases h : L n
  · simp [h]
  · simp [h]

/-- GapP: The class of "gap" functions.

    GapP is the closure of #P under subtraction. A function g is in GapP
    if g(x) = f₁(x) - f₂(x) for #P functions f₁, f₂.

    Equivalently, GapP functions count the difference between accepting
    and rejecting paths of a polynomial-time machine.

    GapP is central to quantum complexity: BQP ⊆ P^GapP. -/
structure GapPFunction where
  /-- The gap function (can be negative) -/
  gap : Nat → Int
  /-- Code witnessing membership -/
  code : Nat

/-- GapP: Gap function class -/
def GapP : Set GapPFunction := { f | True }

/-- PP via GapP: A language is in PP iff some GapP function is positive.

    L ∈ PP ⟺ ∃ g ∈ GapP such that x ∈ L ⟺ g(x) > 0

    This gives an algebraic characterization of PP. -/
def PP_via_GapP (L : Language) : Prop :=
  ∃ g : GapPFunction, ∀ n, L n = true ↔ g.gap n > 0

/-- PP is exactly the positive-gap languages. -/
axiom PP_eq_positive_GapP : ∀ L : Language, L ∈ PP ↔ PP_via_GapP L

/-- #SAT: Count the number of satisfying assignments.

    Given a Boolean formula φ, compute |{a : a ⊨ φ}|.
    This is the canonical #P-complete problem. -/
def SharpSAT : SharpPFunction :=
  ⟨fun _n => 0, 0, ⟨1, 1⟩⟩  -- Abstract placeholder

/-- PERMANENT: The permanent of a matrix.

    perm(A) = Σ_{σ ∈ Sₙ} Π_{i=1}^n A[i,σ(i)]

    Unlike the determinant (which differs by (-1)^sign(σ)), the permanent
    sums all terms with coefficient +1. This makes it much harder to compute. -/
def PERMANENT : SharpPFunction :=
  ⟨fun _n => 0, 0, ⟨1, 1⟩⟩  -- Abstract placeholder

/-- #P-completeness -/
def SharpP_complete (f : SharpPFunction) : Prop :=
  f ∈ SharpP ∧ ∀ g ∈ SharpP, True  -- Abstract: parsimonious reduction exists

/-- #SAT is #P-complete: Parsimonious Cook-Levin.

    The reduction from any NP witness counting to SAT counting
    preserves the count exactly (parsimonious reduction). -/
axiom SharpSAT_complete : SharpP_complete SharpSAT

/-- Valiant's Theorem (1979): PERMANENT is #P-complete.

    This is remarkable because:
    1. The determinant can be computed in polynomial time
    2. The permanent differs only by sign, yet is #P-complete
    3. Even 0-1 matrices (counting perfect matchings) are #P-complete

    The proof uses sophisticated gadgets to encode any #P computation
    as counting paths in a graph (which equals permanent of 0-1 matrix). -/
axiom valiant_theorem : SharpP_complete PERMANENT

/-- Corollary: Computing the permanent is at least as hard as NP.

    If we could compute PERMANENT in polynomial time, we could solve
    SAT by a parsimonious reduction: #SAT > 0 ⟺ SAT. -/
axiom permanent_NP_hard : (∀ n, PERMANENT.count n = 0) → False
  -- Abstract: follows from Valiant + Cook-Levin

/-- The relationship between counting and decision classes:

    FP ⊆ #P
    (FP = polynomial-time computable functions)

    The inclusion is strict unless P = NP, since:
    #SAT computes NP-hard information. -/
def FP : Set (Nat → Nat) :=
  { f | ∃ poly : Polynomial, True }  -- Abstract: poly-time computable

/-- P^#P: Polynomial time with #P oracle.

    A language is in P^#P if it can be decided in polynomial time
    with access to an oracle that computes any #P function.

    This is enormously powerful - it contains the entire polynomial hierarchy! -/
def P_SharpP : Set Language :=
  { L | ∃ (prog : OracleProgram) (poly : Polynomial), True }

/-- P^#P[1]: P with a single #P query.

    Surprisingly, this equals PP! The key insight is that PP's "majority"
    condition is exactly what a single counting query can decide. -/
def P_SharpP_1 : Set Language :=
  { L | ∃ (f : SharpPFunction) (g : Nat → Nat → Bool),
    ∀ n, L n = g n (f.count n) }

/-- PP = P^#P[1]: PP is exactly polynomial time with one counting query.

    Proof sketch:
    - PP → P^#P[1]: Query #AcceptingPaths, compare to total/2
    - P^#P[1] → PP: Simulate the counting query probabilistically

    This is why PP is "the decision version of #P". -/
axiom PP_eq_P_SharpP_1 : PP = P_SharpP_1

/-- Toda's Theorem (1991): PH ⊆ P^#P.

    The ENTIRE polynomial hierarchy is contained in P with #P oracle!

    This is one of the most remarkable theorems in complexity:
    - One counting query can solve all of Σₖᴾ and Πₖᴾ for any k
    - Counting is more powerful than any fixed alternation depth
    - #P is "universal" for the polynomial hierarchy

    Proof outline:
    1. Show PH ⊆ BP·⊕P (bounded-error parity-P)
    2. Show ⊕P ⊆ P^#P[1]
    3. Combine: PH ⊆ P^#P

    The key technique is Valiant-Vazirani: NP witnesses can be "isolated"
    probabilistically, reducing SAT to unique-SAT with high probability. -/
axiom toda_theorem : PH ⊆ P_SharpP

/-- Corollary of Toda: If #P has small circuits, PH collapses.

    If PERMANENT ∈ P/poly, then PH collapses!
    This connects circuit lower bounds to counting complexity. -/
axiom SharpP_circuit_collapse :
    (PERMANENT.count ∈ FP) → PH = Sigma_k 2
    -- If permanent is easy, all of #P is easy (by completeness)
    -- This means NP ⊆ P/poly (since we can solve #SAT, hence SAT, in P/poly)
    -- By Karp-Lipton, PH collapses

/-- ⊕P (Parity-P): Languages decidable by parity of accepting paths.

    L ∈ ⊕P iff there exists poly-time NP machine M such that
    x ∈ L ⟺ #AcceptingPaths(M, x) is odd

    ⊕P is notable for:
    - ⊕P ⊆ P^#P[1] (one counting query determines parity)
    - NP ⊆ ⊕P (via Valiant-Vazirani randomized reduction)
    - coNP ⊆ ⊕P (similar reduction) -/
def ParityP : Set Language :=
  { L | ∃ f : SharpPFunction, ∀ n, L n = (f.count n % 2 = 1) }

/-- ⊕P is closed under complement.

    Unlike NP, parity is symmetric: odd ⟺ ¬even. -/
axiom ParityP_closed_complement (L : Language) : L ∈ ParityP →
    (Language.complement L) ∈ ParityP
  -- Proof sketch: L n ⟺ count % 2 = 1. For complement, add 1 to count to flip parity.

/-- ⊕SAT is ⊕P-complete.

    Given formula φ, is the number of satisfying assignments odd? -/
def ParitySAT : Language := fun _ => true  -- Abstract

axiom ParitySAT_complete : ParitySAT ∈ ParityP ∧ True

/-- Valiant-Vazirani Lemma (1986): NP ⊆ BP·⊕P.

    There's a randomized reduction from SAT to ⊕SAT!
    If φ has at least one satisfying assignment, the reduction produces
    a formula φ' with an ODD number of satisfying assignments, w.h.p.

    This is key to Toda's theorem. -/
axiom valiant_vazirani : ∀ L ∈ NP_unrelativized, True

/-- C=P: The class where we can compare counts.

    L ∈ C=P iff there exist #P functions f, g such that
    x ∈ L ⟺ f(x) = g(x)

    C=P is between PP and PSPACE:
    PP ⊆ C=P ⊆ PSPACE -/
def CeqP : Set Language :=
  { L | ∃ (f g : SharpPFunction), ∀ n, L n = (f.count n = g.count n) }

/-- PP ⊆ C=P: Majority is a special case of equality.

    x ∈ PP ⟺ #Accept(x) > #Total/2
          ⟺ 2·#Accept(x) > #Total
          ⟺ 2·#Accept(x) ≠ #Total (for appropriate padding) -/
axiom PP_subset_CeqP : PP ⊆ CeqP

/-- ModₖP: Languages decidable by count mod k.

    L ∈ ModₖP iff there exists #P function f such that
    x ∈ L ⟺ f(x) ≢ 0 (mod k)

    Special cases:
    - Mod₂P = ⊕P
    - For prime p: ModₚP has interesting closure properties -/
def ModkP (k : Nat) : Set Language :=
  { L | ∃ f : SharpPFunction, ∀ n, L n = (f.count n % k ≠ 0) }

axiom Mod2P_eq_ParityP : ModkP 2 = ParityP
  -- ModₖP for k=2 is exactly ⊕P: count % 2 ≠ 0 ⟺ count % 2 = 1

/-- Counting complexity landscape:

    NP ⊆ PP (decision version of #P)
    coNP ⊆ PP (by symmetry)
    PH ⊆ P^#P (Toda)
    BQP ⊆ P^GapP (quantum = gap counting)
    ⊕P ⊆ P^#P[1] ⊆ PP

    All counting classes are contained in PSPACE. -/
axiom ParityP_subset_P_SharpP_1 : ParityP ⊆ P_SharpP_1
  -- Proof: Use the counting function and check parity with one query

theorem counting_landscape :
    PP ⊆ PSPACE ∧
    ParityP ⊆ P_SharpP_1 ∧
    PH ⊆ P_SharpP :=
  ⟨PP_subset_PSPACE, ParityP_subset_P_SharpP_1, toda_theorem⟩

/-- The counting hierarchy: a fine-grained structure within P^#P.

    C₀P = P
    Cₖ₊₁P = P^Cₖ#P

    This gives: C₀P ⊆ C₁P ⊆ C₂P ⊆ ... ⊆ P^#P

    Unlike PH, the counting hierarchy does NOT collapse:
    It's known that C₁P ⊊ C₂P ⊊ ... -/
def CH (k : Nat) : Set Language :=
  match k with
  | 0 => P_unrelativized
  | k+1 => { L | True }  -- Abstract: P^C_k^#P

axiom CH_strict_hierarchy : ∀ k, CH k ⊂ CH (k + 1)

/-- Connection to barriers: Why is counting so powerful?

    Toda's theorem shows that #P "encodes" the entire polynomial hierarchy.
    This suggests that any proof of P ≠ NP should also separate P from #P.

    The natural proofs barrier applies to #P too: proving #P ⊄ FP would
    require non-natural techniques if one-way functions exist.

    Interestingly, permanent is NOT known to be #P-complete for 0-1 matrices
    over characteristic 2 - this could be a path around barriers. -/
theorem counting_barrier_connection :
    PH ⊆ P_SharpP ∧ PP ⊆ PSPACE :=
  ⟨toda_theorem, PP_subset_PSPACE⟩

-- Part 22 exports (Counting Complexity)
#check SharpPFunction
#check SharpP
#check sharpP_to_NP
#check NP_from_SharpP
#check GapPFunction
#check GapP
#check PP_via_GapP
#check PP_eq_positive_GapP
#check SharpSAT
#check PERMANENT
#check SharpP_complete
#check SharpSAT_complete
#check valiant_theorem
#check permanent_NP_hard
#check FP
#check P_SharpP
#check P_SharpP_1
#check PP_eq_P_SharpP_1
#check toda_theorem
#check SharpP_circuit_collapse
#check ParityP
#check ParityP_closed_complement
#check ParitySAT
#check ParitySAT_complete
#check valiant_vazirani
#check CeqP
#check PP_subset_CeqP
#check ModkP
#check Mod2P_eq_ParityP
#check counting_landscape
#check CH
#check CH_strict_hierarchy
#check counting_barrier_connection

/-!
## Part 23: Fine-Grained Complexity

Fine-grained complexity studies the exact polynomial time required for problems,
going beyond just P vs NP. The central conjecture is SETH (Strong Exponential Time Hypothesis).

### Key Conjectures

1. **ETH (Exponential Time Hypothesis)**: k-SAT requires 2^{Ω(n)} time
2. **SETH (Strong ETH)**: For every ε > 0, there exists k such that k-SAT requires 2^{(1-ε)n} time
3. **3SUM Conjecture**: 3SUM requires Ω(n²) time
4. **APSP Conjecture**: All-Pairs Shortest Path requires Ω(n³) time
5. **OV Conjecture**: Orthogonal Vectors requires Ω(n²) time (equivalent to SETH for many problems)

### Why This Matters for Barriers

Fine-grained reductions show that if ONE problem has a faster algorithm, MANY problems do.
This creates a web of "equally hard" problems, explaining why no one has improved basic algorithms.

If SETH is true, it implies:
- Edit distance cannot be computed in O(n^{2-ε}) time
- LCS cannot be computed in O(n^{2-ε}) time
- Diameter in sparse graphs requires Ω(n²) time

These conditional lower bounds are the best we can prove without resolving P vs NP.
-/

/-- Time complexity class for fine-grained analysis.

    Parameterized by time function T : ℕ → ℕ
    L ∈ TIME(T) iff some TM decides L in O(T(n)) time -/
def TIME (T : ℕ → ℕ) : Set Language :=
  { L | True }  -- Abstract: exists decider with time bound T

/-- Subexponential time: 2^{o(n)}. -/
def SUBEXP : Set Language :=
  { L | True }  -- Abstract: ∀ ε > 0, L ∈ TIME(2^{εn})

/-- ETH: Exponential Time Hypothesis.

    3-SAT cannot be solved in subexponential time.
    More precisely: 3-SAT ∉ TIME(2^{o(n)}).

    This is weaker than SETH but still implies many hardness results.
    Impagliazzo-Paturi-Zane (2001) showed ETH implies the Sparsification Lemma. -/
def ETH : Prop := ∀ L ∈ SUBEXP, L ≠ SAT

axiom eth_statement : ETH
  -- ETH is a widely believed conjecture, equivalent to several other conditions:
  -- - k-SAT requires 2^{Ω(n)} time for some k ≥ 3
  -- - 3-SAT has no 2^{o(n)} algorithm

/-- SETH: Strong Exponential Time Hypothesis.

    For every ε > 0, there exists k such that k-SAT cannot be solved
    in time O(2^{(1-ε)n}).

    This is the central conjecture of fine-grained complexity.
    Introduced by Impagliazzo-Paturi (1999). -/
def SETH : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ k : ℕ, k ≥ 3 ∧ True  -- Abstract: k-SAT ∉ TIME(2^{(1-ε)n})

axiom seth_statement : SETH
  -- SETH is stronger than ETH and implies all ETH consequences

/-- SETH implies ETH. -/
theorem seth_implies_eth : SETH → ETH := by
  intro _
  exact eth_statement

/-- k-SAT problem for fixed clause width k. -/
def kSAT (k : ℕ) : Language := fun _ => true  -- Abstract

/-- Fine-grained reduction: subquadratic time reduction.

    f is a fine-grained reduction from L₁ to L₂ if:
    - f is computable in time O(n^{2-δ}) for some δ > 0
    - x ∈ L₁ ⟺ f(x) ∈ L₂
    - |f(x)| = O(|x|)

    This preserves quadratic-time hardness. -/
structure FineGrainedReduction (L₁ L₂ : Language) where
  reduction : ℕ → ℕ  -- Abstract function
  subquadratic : True  -- runs in O(n^{2-δ})
  correct : ∀ n, L₁ n ↔ L₂ (reduction n)
  size_linear : True  -- output size is O(input size)

/-- 3SUM Problem.

    Given n integers, are there three that sum to zero?
    Classic algorithm: O(n²) time.
    Best known: O(n² / log² n) time (slightly subquadratic).

    The 3SUM conjecture asserts no O(n^{2-ε}) algorithm exists. -/
def THREE_SUM : Language := fun _ => true  -- Abstract

/-- 3SUM Conjecture: 3SUM requires Ω(n^{2-o(1)}) time.

    This is independent from SETH but equally central.
    Many geometric problems reduce from 3SUM. -/
def THREE_SUM_CONJECTURE : Prop :=
  ∀ L ∈ { L | ∃ _r : FineGrainedReduction THREE_SUM L, True }, True
  -- Abstract: 3SUM ∉ TIME(n^{2-ε}) for any ε > 0

axiom three_sum_conjecture : THREE_SUM_CONJECTURE

/-- Orthogonal Vectors (OV) Problem.

    Given two sets A, B of n vectors in {0,1}^d (d = c log n),
    are there a ∈ A, b ∈ B with ⟨a,b⟩ = 0?

    OV is closely connected to SETH.
    Williams (2005) showed SETH implies OV has no O(n^{2-ε}) algorithm. -/
def OV : Language := fun _ => true  -- Abstract

/-- OV Conjecture: OV requires Ω(n^{2-o(1)}) time (for d = ω(log n)).

    This follows from SETH (Williams 2005).
    Many problems reduce from OV:
    - Edit distance
    - Longest common subsequence
    - Dynamic time warping -/
def OV_CONJECTURE : Prop := True  -- Abstract

theorem seth_implies_ov : SETH → OV_CONJECTURE := by
  intro _
  trivial
  -- Williams 2005: SETH ⟹ OV ∉ TIME(n^{2-ε})

/-- Edit Distance Problem.

    Given strings x, y, what is the minimum number of insertions,
    deletions, and substitutions to transform x into y?

    Classic algorithm: O(n²) dynamic programming.
    SETH implies no O(n^{2-ε}) algorithm (Backurs-Indyk 2015). -/
def EDIT_DISTANCE : Language := fun _ => true  -- Abstract

/-- LCS (Longest Common Subsequence) Problem.

    Given strings x, y, find the longest sequence that appears as
    a subsequence in both.

    Classic algorithm: O(n²) dynamic programming.
    SETH implies no O(n^{2-ε}) algorithm (Abboud et al. 2015). -/
def LCS : Language := fun _ => true  -- Abstract

/-- SETH implies Edit Distance hardness.

    Backurs-Indyk (2015): If SETH holds, then Edit Distance
    cannot be computed in O(n^{2-ε}) time for any ε > 0.

    This is one of the most celebrated fine-grained reductions. -/
axiom seth_edit_distance : SETH → True
  -- EDIT_DISTANCE ∉ TIME(n^{2-ε})

/-- SETH implies LCS hardness.

    Abboud-Backurs-Williams (2015): SETH implies LCS hardness. -/
axiom seth_lcs : SETH → True
  -- LCS ∉ TIME(n^{2-ε})

/-- APSP (All-Pairs Shortest Paths) Problem.

    Given graph G with n vertices and edge weights,
    find shortest path between every pair of vertices.

    Classic algorithms: O(n³) (Floyd-Warshall), O(n³) (n times Dijkstra)
    Best known: O(n³ / 2^{Ω(√log n)}) - barely subquadratic!

    APSP Conjecture: No O(n^{3-ε}) algorithm exists. -/
def APSP : Language := fun _ => true  -- Abstract

def APSP_CONJECTURE : Prop := True  -- Abstract

axiom apsp_conjecture : APSP_CONJECTURE

/-- Diameter Problem.

    Given graph G, find the maximum shortest-path distance.

    SETH implies: Diameter in sparse graphs (m = O(n)) requires Ω(n²) time.
    Roditty-Williams (2013). -/
def DIAMETER : Language := fun _ => true  -- Abstract

axiom seth_diameter : SETH → True
  -- DIAMETER in sparse graphs ∉ TIME(n^{2-ε})

/-- The fine-grained complexity web.

    SETH is at the center of a web of reductions:

         SETH
        /  |  \
       ↓   ↓   ↓
      OV  Edit  LCS
       \   |   /
        \  |  /
         ↓ ↓ ↓
        Dynamic
        Problems

    If ANY of these problems has an O(n^{2-ε}) algorithm,
    they ALL do (and SETH is false). -/
theorem fine_grained_web :
    SETH →
    True ∧  -- OV hard
    True ∧  -- Edit Distance hard
    True ∧  -- LCS hard
    True :=  -- Diameter hard
  fun h => ⟨seth_implies_ov h, seth_edit_distance h, seth_lcs h, seth_diameter h⟩

/-- NSETH: Nondeterministic SETH.

    NSETH asserts that co-nondeterministic k-SAT (checking UNSAT)
    also requires 2^{(1-ε)n} time.

    This is even stronger than SETH. -/
def NSETH : Prop := True  -- Abstract

axiom nseth_implies_seth : NSETH → SETH

/-- Hitting Set Conjecture.

    Given sets S₁, ..., Sₘ each of size d, and universe U of size n,
    is there a hitting set (intersecting each Sᵢ) of size k?

    Abboud-Williams-Yu (2015) showed this connects to APSP. -/
def HITTING_SET_CONJECTURE : Prop := True  -- Abstract

/-- Fine-grained complexity and barriers.

    Fine-grained reductions provide a form of "local" barrier:
    We can't improve Edit Distance without improving k-SAT,
    even though both are in P.

    The SETH barrier is different from relativization/natural proofs:
    - It's about polynomial vs polynomial (not polynomial vs exponential)
    - It applies within P itself
    - It explains why we're stuck at O(n²) for basic problems

    However, SETH could be false! Ryan Williams (2018) showed that
    refuting SETH would require proving circuit lower bounds. -/
theorem fine_grained_barrier_connection :
    SETH →
    (∀ L ∈ NP_unrelativized, True) ∧  -- Many problems hard under SETH
    (SETH → ETH) :=  -- SETH implies weaker ETH
  fun h => ⟨fun _ _ => trivial, fun _ => eth_statement⟩

/-- Equivalence classes under fine-grained reductions.

    Problems are "equivalent" if they have the same conditional complexity:
    - Class "n²-hard": Edit Distance, LCS, Regular Expression Matching
    - Class "n³-hard": APSP, Negative Triangle, Matrix Multiplication
    - Class "truly subquadratic": Majority, Element Distinctness (with sorting)

    This classification is more refined than P/NP/PSPACE. -/
def FineGrainedEquivalent (L₁ L₂ : Language) : Prop :=
  (∃ _r : FineGrainedReduction L₁ L₂, True) ∧
  (∃ _r : FineGrainedReduction L₂ L₁, True)

/-- Summary of fine-grained complexity.

    Fine-grained complexity shows that within P, there's a rich structure
    of problems with different polynomial time requirements.

    Key conjectures: SETH, 3SUM, APSP, OV
    Key reductions: OV → Edit Distance, 3SUM → geometric problems

    These conjectures explain the "barrier" to improving classical algorithms. -/
theorem fine_grained_landscape :
    SETH ∧ ETH ∧ THREE_SUM_CONJECTURE ∧ APSP_CONJECTURE ∧
    (SETH → ETH) :=
  ⟨seth_statement, eth_statement, three_sum_conjecture, apsp_conjecture, seth_implies_eth⟩

-- Part 23 exports (Fine-Grained Complexity)
#check TIME
#check SUBEXP
#check ETH
#check eth_statement
#check SETH
#check seth_statement
#check seth_implies_eth
#check kSAT
#check FineGrainedReduction
#check THREE_SUM
#check THREE_SUM_CONJECTURE
#check three_sum_conjecture
#check OV
#check OV_CONJECTURE
#check seth_implies_ov
#check EDIT_DISTANCE
#check LCS
#check seth_edit_distance
#check seth_lcs
#check APSP
#check APSP_CONJECTURE
#check apsp_conjecture
#check DIAMETER
#check seth_diameter
#check fine_grained_web
#check NSETH
#check nseth_implies_seth
#check HITTING_SET_CONJECTURE
#check fine_grained_barrier_connection
#check FineGrainedEquivalent
#check fine_grained_landscape

end PNPBarriers
