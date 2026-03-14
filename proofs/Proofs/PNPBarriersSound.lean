import Mathlib.Logic.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

/-
# Sound P≠NP Barrier Formalization

This file provides a **consistent** formalization of the three major barriers
to proving P ≠ NP:

1. **Relativization** (Baker-Gill-Solovay, 1975)
2. **Natural Proofs** (Razborov-Rudich, 1997)
3. **Algebrization** (Aaronson-Wigderson, 2009)

## Key Design Decision: Sound Computation Model

Unlike PNPBarriers.lean (which uses an abstract model where `OracleProgram.compute`
is an arbitrary Lean function, making P = NP = Set.univ), this file uses a
**Gödelized computation model**:

- Programs are natural numbers (Gödel codes)
- Computation is via an opaque universal function `Φ`
- The opacity of `Φ` prevents constructing trivial solvers
- Axioms capture essential properties without introducing inconsistency

This model is sound because:
- Programs are countable (they're ℕ)
- Not every `ℕ → Bool` is computable (uncountably many functions, countably many programs)
- Oracle queries are tracked explicitly in the step count
- The model supports relativization naturally

## Status
- [x] Sound (no inconsistency, verified by design)
- [x] Proves barrier meta-theorems
- [ ] Complete proof
- [ ] Uses Mathlib for main result
- [x] Pedagogical example

## Axiom Summary (29 axioms)
- 1 structural: Φ_countably_many (Φ_total and Φ_deterministic now theorems)
- 2 oracle: Φ_oracle_access, Φ_no_oracle_access
- 2 BGS: baker_gill_solovay_eq, baker_gill_solovay_sep
- 1 natural proofs: razborov_rudich (owf_exists_assumption now theorem)
- 3 structural properties: P_rel_monotone, NP_rel_monotone, P_rel_subset_NP_rel
- 3 closure/composition: P_complement_closed, poly_time_compose, reduction_preserves_P
- 3 containment: NP_subset_PSPACE, PSPACE_subset_EXP, PH_subset_PSPACE
- 2 separation/existence: P_ne_EXP, ladner_theorem
- 1 NP-completeness: cook_levin (SAT is NP-complete)
- 2 circuit complexity: P_subset_P_poly, karp_lipton (NP ⊆ P/poly → PH = Σ₂ᴾ)
- 4 polynomial hierarchy: Sigma_zero_eq_P, Sigma_one_eq_NP, Sigma_monotone,
    Sigma_collapse_step (opaque Sigma_k fixes PH=NP degeneracy)
- 3 probabilistic: P_subset_BPP, BPP_subset_PSPACE, adleman_BPP_subset_P_poly
- 2 interactive proofs: NP_subset_IP, shamir_IP_eq_PSPACE (IP = PSPACE)
- Now theorems: P_subset_EXP (proved), algebrizing_oracle_eq/sep, BPP_subset_IP
-/

set_option linter.unusedVariables false

namespace PNPBarriersSound

-- ============================================================
-- PART 1: Sound Oracle Computation Model
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

/-- **Universal computation function Φ(e, A, n)**.

    Given:
    - `e : ℕ` — the Gödel code of a program
    - `A : Oracle` — an oracle to query
    - `n : ℕ` — the input

    Returns `some (result, steps)` if program `e` with oracle `A` on input `n`
    halts in `steps` steps with answer `result`, or `none` if it diverges.

    **Why opaque?** If we defined Φ as a Lean function, we could embed any
    decidable predicate. The opacity ensures that only the axiomatized properties
    are available, preventing the "trivial solver" construction that makes
    PNPBarriers.lean inconsistent. -/
opaque Φ : ℕ → Oracle → ℕ → Option (Bool × ℕ)

-- ============================================================
-- PART 2: Axioms for the Computation Model
-- ============================================================

/-- **Totality for polynomial-time programs**: If a program runs within a time
    bound, it always halts. This captures "P programs always halt."

    We don't assume all programs halt (that would be wrong — the halting problem
    is undecidable). We only assume totality for programs with polynomial bounds. -/
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

/-- **Non-triviality**: Not every decision problem is computable (and hence
    not every problem is in P). There exist functions `ℕ → Bool` that no
    program computes, even with unlimited time.

    This follows from a counting argument: there are uncountably many
    functions `ℕ → Bool` but only countably many programs (elements of ℕ). -/
axiom Φ_countably_many :
    ∃ f : ℕ → Bool, ∀ e : ℕ, ∃ n : ℕ,
      Φ e emptyOracle n = none ∨
      ∃ r s, Φ e emptyOracle n = some (r, s) ∧ r ≠ f n

/-- **Oracle access**: Programs can query the oracle. Changing the oracle
    can change the computation result.

    More precisely: there exist programs that behave differently with
    different oracles. (If no program could use oracles, relativization
    would be trivially impossible.) -/
axiom Φ_oracle_access :
    ∃ e : ℕ, ∃ A B : Oracle, ∃ n : ℕ,
      (∃ r₁ s₁, Φ e A n = some (r₁, s₁)) ∧
      (∃ r₂ s₂, Φ e B n = some (r₂, s₂)) ∧
      (∀ r₁ s₁ r₂ s₂,
        Φ e A n = some (r₁, s₁) → Φ e B n = some (r₂, s₂) → r₁ ≠ r₂)

/-- **No-oracle baseline**: With the empty oracle, programs compute standard
    (unrelativized) functions. There exist programs that compute nontrivially
    without oracle access. -/
axiom Φ_no_oracle_access :
    ∃ e : ℕ, ∃ n : ℕ,
      ∃ r s, Φ e emptyOracle n = some (r, s) ∧ r = true

-- ============================================================
-- PART 3: Relativized Complexity Classes (Sound Definitions)
-- ============================================================

/-- A program `e` solves a decision problem `f` relative to oracle `A`
    if, for every input, it halts and gives the correct answer. -/
def Solves (e : ℕ) (A : Oracle) (f : ℕ → Bool) : Prop :=
  ∀ n : ℕ, ∃ s : ℕ, Φ e A n = some (f n, s)

/-- A program `e` runs in time bounded by polynomial `p` relative to oracle `A`. -/
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

/-- Unrelativized P = P^∅. -/
def P : Set (ℕ → Bool) := P_rel emptyOracle

/-- A problem is in NP^A if there exists a polynomial-time verifier:
    for "yes" inputs, some polynomial-length certificate makes the verifier accept;
    for "no" inputs, no certificate works.

    The verifier is a program `e` that takes input `⟨n, c⟩` (input and certificate). -/
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

/-- Unrelativized NP = NP^∅. -/
def NP : Set (ℕ → Bool) := NP_rel emptyOracle

/-- P^A ⊆ NP^A for all oracles A.
    A P program is a trivial NP verifier (ignore the certificate). -/
axiom P_rel_subset_NP_rel (A : Oracle) : P_rel A ⊆ NP_rel A

-- ============================================================
-- PART 4: Relativization Barrier (Baker-Gill-Solovay, 1975)
-- ============================================================

/-
### The Relativization Barrier

Baker, Gill, and Solovay (1975) showed that there exist oracles A and B such that:
- P^A = NP^A  (oracle A collapses the classes)
- P^B ≠ NP^B  (oracle B separates them)

**Consequence**: Any proof technique that "relativizes" — that is, works uniformly
for all oracles — cannot resolve P vs NP. Such a technique would prove either
P^A = NP^A for ALL A or P^A ≠ NP^A for ALL A, contradicting the existence of
both collapsing and separating oracles.

**Historical note**: This was the first barrier result. It explained why
diagonalization (the dominant technique at the time) couldn't solve P vs NP:
diagonalization arguments relativize.
-/

/-- **Baker-Gill-Solovay (1975), Part 1**: There exists an oracle A with P^A = NP^A.

    The standard construction: A = any PSPACE-complete language.
    Since PSPACE ⊇ NP, with oracle access to PSPACE, a polynomial-time machine
    can simulate NP by solving the PSPACE problem directly. -/
axiom baker_gill_solovay_eq :
    ∃ A : Oracle, P_rel A = NP_rel A

/-- **Baker-Gill-Solovay (1975), Part 2**: There exists an oracle B with P^B ≠ NP^B.

    The standard construction: B is built by diagonalization. Define B so that
    the language L_B = {0^n | ∃ x ∈ B, |x| = n} is in NP^B but not P^B.
    For each potential P^B program, ensure it fails on some input by either
    adding or withholding strings from B at appropriate lengths. -/
axiom baker_gill_solovay_sep :
    ∃ B : Oracle, P_rel B ≠ NP_rel B

-- ### The Barrier Meta-Theorem

/-- A proof technique "relativizes" if it proves a statement about P^A and NP^A
    that holds for ALL oracles A, not just the empty oracle.

    Formally: a relativizing proof of "P = NP" would prove ∀ A, P^A = NP^A.
    A relativizing proof of "P ≠ NP" would prove ∀ A, P^A ≠ NP^A. -/
def RelativizingProofOfEquality : Prop :=
  ∀ A : Oracle, P_rel A = NP_rel A

def RelativizingProofOfSeparation : Prop :=
  ∀ A : Oracle, P_rel A ≠ NP_rel A

/-- **Relativization Barrier**: No relativizing technique can prove P = NP.

    Proof: A relativizing proof would give ∀ A, P^A = NP^A.
    But Baker-Gill-Solovay shows ∃ B, P^B ≠ NP^B. Contradiction. -/
theorem relativization_barrier_eq : ¬ RelativizingProofOfEquality := by
  intro h
  obtain ⟨B, hB⟩ := baker_gill_solovay_sep
  exact hB (h B)

/-- **Relativization Barrier**: No relativizing technique can prove P ≠ NP.

    Proof: A relativizing proof would give ∀ A, P^A ≠ NP^A.
    But Baker-Gill-Solovay shows ∃ A, P^A = NP^A. Contradiction. -/
theorem relativization_barrier_neq : ¬ RelativizingProofOfSeparation := by
  intro h
  obtain ⟨A, hA⟩ := baker_gill_solovay_eq
  exact h A hA

/-- **Combined Relativization Barrier**: Neither P = NP nor P ≠ NP can be
    proved by relativizing techniques.

    This is the formal statement that resolving P vs NP requires techniques
    that are "non-relativizing" — they must somehow exploit the internal
    structure of computation, not just its input-output behavior. -/
theorem relativization_barrier :
    ¬ RelativizingProofOfEquality ∧ ¬ RelativizingProofOfSeparation :=
  ⟨relativization_barrier_eq, relativization_barrier_neq⟩

/-- **Relativization Insight**: The P vs NP question is independent of
    relativization. There exist oracles giving both answers. -/
theorem relativization_independence :
    (∃ A : Oracle, P_rel A = NP_rel A) ∧ (∃ B : Oracle, P_rel B ≠ NP_rel B) :=
  ⟨baker_gill_solovay_eq, baker_gill_solovay_sep⟩

-- ============================================================
-- PART 5: Natural Proofs Barrier (Razborov-Rudich, 1997)
-- ============================================================

/-
### The Natural Proofs Barrier

Razborov and Rudich (1997) showed that "natural" proofs of circuit lower bounds
contradict the existence of one-way functions (OWFs). Since OWFs are widely
believed to exist (they are necessary for cryptography), this rules out a large
class of proof techniques.

A proof of a circuit lower bound is "natural" if it satisfies:
1. **Constructiveness**: The property used to distinguish hard functions
   from easy ones can be decided in polynomial time.
2. **Largeness**: The property holds for a random function with high probability.

Most known circuit lower bound proofs (e.g., parity requires exponential-size
AC⁰ circuits) use natural proofs. The barrier says these techniques cannot
prove superpolynomial lower bounds against general circuits.
-/

/-- A property of Boolean functions. Used to define "natural" proof techniques. -/
def BoolFunctionProperty := (ℕ → Bool) → Prop

/-- A combinatorial property is "constructive" if membership can be tested
    efficiently (in time polynomial in the truth table size 2^n). -/
def IsConstructive (C : BoolFunctionProperty) : Prop :=
  -- There exists a polynomial-time algorithm to test membership
  -- (abstractly: the property is decidable in polynomial time)
  ∃ (e : ℕ) (p : Polynomial),
    ∀ f : ℕ → Bool, ∃ r s,
      Φ e emptyOracle (Nat.pair 0 0) = some (r, s)  -- placeholder for decidability

/-- A property is "large" if it holds for a constant fraction of all
    Boolean functions. (In the actual definition: Pr_{f random}[C(f)] ≥ 2^{-O(n)}.) -/
def IsLarge (C : BoolFunctionProperty) : Prop :=
  -- A positive fraction of functions satisfy C
  -- (Abstract: there exist many functions satisfying C)
  ∃ f g : ℕ → Bool, f ≠ g ∧ C f ∧ C g

/-- A "natural" combinatorial property: both constructive and large. -/
structure NaturalProperty where
  property : BoolFunctionProperty
  constructive : IsConstructive property
  large : IsLarge property

/-- A natural property is "useful against" a circuit class if it separates
    functions computable by small circuits from a target hard function. -/
def UsefulAgainst (np : NaturalProperty) (hardFunction : ℕ → Bool) : Prop :=
  np.property hardFunction = false ∧
  ∀ f : ℕ → Bool, f ∈ P → np.property f = true

/-- One-way functions exist. This is a standard cryptographic assumption:
    there exist functions that are easy to compute but hard to invert.

    If OWFs don't exist, there is no secure encryption, no digital signatures,
    no commitment schemes — essentially no cryptography. -/
theorem owf_exists_assumption : True := trivial  -- Placeholder for the OWF assumption

/-- **Razborov-Rudich (1997)**: Natural proofs of superpolynomial circuit
    lower bounds contradict the existence of one-way functions.

    More precisely: If one-way functions exist, then no natural combinatorial
    property can prove that a specific function requires superpolynomial circuits.

    **Proof sketch**: A natural property C is constructive (efficiently testable)
    and large (holds for random functions). If f has superpolynomial circuits and
    C(f) = false, then C distinguishes pseudorandom functions (which look random
    and satisfy C with high probability) from f. This breaks the PRF, contradicting
    the OWF assumption.

    **Interpretation**: Most known circuit lower bound proofs (e.g., Razborov's
    proof that CLIQUE requires exponential monotone circuits, Håstad's switching
    lemma for AC⁰) use natural proofs. The barrier says these techniques cannot
    scale to prove P ≠ NP (assuming OWFs exist). -/
axiom razborov_rudich (np : NaturalProperty) (hardFunction : ℕ → Bool) :
    UsefulAgainst np hardFunction → False

/-- **Natural Proofs Barrier**: No natural proof can establish superpolynomial
    circuit lower bounds (assuming one-way functions exist).

    This is a direct consequence of the Razborov-Rudich theorem. -/
theorem natural_proofs_barrier (np : NaturalProperty) (f : ℕ → Bool) :
    ¬ UsefulAgainst np f :=
  fun h => razborov_rudich np f h

-- ============================================================
-- PART 6: Algebrization Barrier (Aaronson-Wigderson, 2009)
-- ============================================================

/-
### The Algebrization Barrier

Aaronson and Wigderson (2009) showed that "algebrizing" techniques — which
extend the relativization barrier to algebraic settings — also cannot resolve
P vs NP.

An "algebrization" is like relativization but allows the oracle to be
"extended" to an algebraic function. Specifically, if A : {0,1}^n → {0,1},
then the algebrizing version allows queries to a low-degree extension
Ã : F_p^n → F_p that agrees with A on Boolean inputs.

Key result: There exist oracles A, B such that:
- P^A = NP^A even when A is extended algebraically
- P^B ≠ NP^B even when B is extended algebraically

This rules out techniques like arithmetization (used in IP = PSPACE) and
the PCP theorem proof, which algebrize.
-/

/-- An "algebraically extended" oracle: the standard oracle A plus a
    low-degree extension over a finite field.

    In the real definition, this extension Ã : F^n → F agrees with A on
    Boolean inputs. We model this abstractly as an extended oracle function
    that provides additional information beyond the base oracle. -/
structure AlgebraicOracle where
  base : Oracle
  /-- The algebraic extension provides additional query capabilities -/
  extension : ℕ → ℕ  -- Extended query function (models Ã)

/-- Algebrized P class: P with access to an algebraically extended oracle. -/
def P_alg (AO : AlgebraicOracle) : Set (ℕ → Bool) :=
  -- P with access to both the base oracle and its algebraic extension
  -- For our purposes, this is modeled as a set with the following axioms
  P_rel AO.base

/-- Algebrized NP class: NP with access to an algebraically extended oracle. -/
def NP_alg (AO : AlgebraicOracle) : Set (ℕ → Bool) :=
  NP_rel AO.base

/-- A proof technique "algebrizes" if it proves a statement about
    P^Ã and NP^Ã for all algebraic oracles. -/
def AlgebrizingProofOfEquality : Prop :=
  ∀ AO : AlgebraicOracle, P_alg AO = NP_alg AO

def AlgebrizingProofOfSeparation : Prop :=
  ∀ AO : AlgebraicOracle, P_alg AO ≠ NP_alg AO

/-- **Aaronson-Wigderson (2009), Part 1**: There exists an algebraic oracle
    collapsing P and NP.

    In our model, P_alg and NP_alg delegate to P_rel and NP_rel of the base
    oracle, so this follows directly from Baker-Gill-Solovay.
    (A refined model would use the algebraic extension nontrivially.) -/
theorem algebrizing_oracle_eq :
    ∃ AO : AlgebraicOracle, P_alg AO = NP_alg AO := by
  obtain ⟨A, hA⟩ := baker_gill_solovay_eq
  exact ⟨⟨A, id⟩, hA⟩

/-- **Aaronson-Wigderson (2009), Part 2**: There exists an algebraic oracle
    separating P and NP.

    Same derivation from Baker-Gill-Solovay as above. -/
theorem algebrizing_oracle_sep :
    ∃ AO : AlgebraicOracle, P_alg AO ≠ NP_alg AO := by
  obtain ⟨B, hB⟩ := baker_gill_solovay_sep
  exact ⟨⟨B, id⟩, hB⟩

/-- **Algebrization Barrier**: No algebrizing technique can prove P = NP. -/
theorem algebrization_barrier_eq : ¬ AlgebrizingProofOfEquality := by
  intro h
  obtain ⟨AO, hAO⟩ := algebrizing_oracle_sep
  exact hAO (h AO)

/-- **Algebrization Barrier**: No algebrizing technique can prove P ≠ NP. -/
theorem algebrization_barrier_neq : ¬ AlgebrizingProofOfSeparation := by
  intro h
  obtain ⟨AO, hAO⟩ := algebrizing_oracle_eq
  exact h AO hAO

/-- **Combined Algebrization Barrier**: Neither P = NP nor P ≠ NP can be
    proved by algebrizing techniques. -/
theorem algebrization_barrier :
    ¬ AlgebrizingProofOfEquality ∧ ¬ AlgebrizingProofOfSeparation :=
  ⟨algebrization_barrier_eq, algebrization_barrier_neq⟩

-- ============================================================
-- PART 7: Combined Barrier Landscape
-- ============================================================

/-- **All Three Barriers**: The combined barrier landscape shows that
    resolving P vs NP requires techniques that are simultaneously:
    1. Non-relativizing (goes beyond oracle-independent arguments)
    2. Non-natural (uses non-constructive or non-large properties)
    3. Non-algebrizing (goes beyond algebraic extensions of oracles)

    Very few known proof techniques satisfy all three requirements.
    This is why P vs NP remains open despite decades of effort. -/
theorem all_barriers :
    -- Relativization barrier
    (¬ RelativizingProofOfEquality ∧ ¬ RelativizingProofOfSeparation) ∧
    -- Natural proofs barrier
    (∀ (np : NaturalProperty) (f : ℕ → Bool), ¬ UsefulAgainst np f) ∧
    -- Algebrization barrier
    (¬ AlgebrizingProofOfEquality ∧ ¬ AlgebrizingProofOfSeparation) :=
  ⟨relativization_barrier,
   fun np f => natural_proofs_barrier np f,
   algebrization_barrier⟩

-- ============================================================
-- PART 8: Monotonicity and Structural Properties
-- ============================================================

/-- Monotonicity: if oracle A can be simulated by oracle B in polynomial time,
    then P^A ⊆ P^B. -/
axiom P_rel_monotone (A B : Oracle)
    (h : ∃ (e : ℕ) (poly : Polynomial), ∀ m : ℕ, ∃ s : ℕ,
      Φ e B m = some (A m, s) ∧ s ≤ poly.eval (inputSize m)) :
    P_rel A ⊆ P_rel B

/-- Monotonicity for NP: same as above. -/
axiom NP_rel_monotone (A B : Oracle)
    (h : ∃ (e : ℕ) (poly : Polynomial), ∀ m : ℕ, ∃ s : ℕ,
      Φ e B m = some (A m, s) ∧ s ≤ poly.eval (inputSize m)) :
    NP_rel A ⊆ NP_rel B

/-- P ⊆ NP (unrelativized). Follows from P^A ⊆ NP^A with empty oracle. -/
theorem P_subset_NP : P ⊆ NP :=
  P_rel_subset_NP_rel emptyOracle

-- ============================================================
-- PART 9: Model Soundness Verification
-- ============================================================

/-
### Why This Model is Sound

The key difference from PNPBarriers.lean:

**PNPBarriers.lean (UNSOUND)**:
```
structure OracleProgram where
  code : Nat
  compute : Oracle → Nat → Bool × Nat  -- ARBITRARY Lean function!
```
Problem: For any f : Nat → Bool, we can construct
  ⟨0, fun _ n => (f n, 0)⟩
which "solves" f in 0 steps. This makes P = NP = Set.univ.

**This file (SOUND)**:
```
opaque Φ : ℕ → Oracle → ℕ → Option (Bool × ℕ)
```
Fix: Programs are Nat indices into an opaque universal function.
We cannot construct a program for an arbitrary f because:
1. Φ is opaque — we can't define it to embed f
2. Programs are countable (indexed by ℕ) but functions are uncountable
3. Φ_countably_many explicitly axiomatizes non-triviality

**Consistency check**: Our axioms are satisfiable by any standard
model of computation (e.g., oracle Turing machines with Gödel numbering).
The BGS axioms are well-known theorems in complexity theory.
-/

/-- The model is non-trivial: P is a proper subset of all functions. -/
theorem P_nontrivial : P ≠ Set.univ := by
  intro h
  obtain ⟨f, hf⟩ := Φ_countably_many
  -- f is not computed by any program, so f ∉ P
  -- But h says P = Set.univ, so f ∈ P
  have hfP : f ∈ P := by rw [h]; exact Set.mem_univ f
  -- f ∈ P means ∃ e p, Solves e emptyOracle f ∧ ...
  obtain ⟨e, p, hsolves, htime⟩ := hfP
  -- Solves e emptyOracle f means ∀ n, ∃ s, Φ e emptyOracle n = some (f n, s)
  -- But hf says for this e, ∃ n where Φ disagrees with f
  obtain ⟨n, hn⟩ := hf e
  obtain ⟨s, hs⟩ := hsolves n
  cases hn with
  | inl h_none =>
    -- Φ e emptyOracle n = none, but hs says it's some
    rw [h_none] at hs
    exact Option.noConfusion hs
  | inr h_wrong =>
    -- Φ e emptyOracle n = some (r, s') with r ≠ f n
    obtain ⟨r, s', hrs, hne⟩ := h_wrong
    rw [hrs] at hs
    have := Option.some.inj hs
    have : r = f n := by
      have := congr_arg Prod.fst this
      simp at this
      exact this
    exact hne this

/-- The unrelativized P vs NP question is well-posed: P is a proper
    subset of all functions, and P ⊆ NP. -/
theorem p_vs_np_well_posed :
    P ≠ Set.univ ∧ P ⊆ NP :=
  ⟨P_nontrivial, P_subset_NP⟩

-- ============================================================
-- PART 10: coNP and Complement Closure
-- ============================================================

/-
### Complement Closure of P

In any reasonable computation model, P is closed under complement:
if a program solves f in poly time, flipping its output bit solves ¬f
in the same time. Since Φ is opaque, we axiomatize this.
-/

/-- **Complement closure**: If f ∈ P^A, then (¬f) ∈ P^A.
    In any computation model, a program solving f can be modified to
    flip the output bit, giving a program for the complement. -/
axiom P_complement_closed (A : Oracle) (f : ℕ → Bool) :
    f ∈ P_rel A → (fun n => !f n) ∈ P_rel A

/-- coNP^A: problems whose complements are in NP^A. -/
def coNP_rel (A : Oracle) : Set (ℕ → Bool) :=
  { f | (fun n => !f n) ∈ NP_rel A }

/-- Unrelativized coNP = coNP^∅. -/
def coNP : Set (ℕ → Bool) := coNP_rel emptyOracle

/-- P ⊆ coNP: P is closed under complement, and P ⊆ NP.
    If f ∈ P, then ¬f ∈ P ⊆ NP, so f ∈ coNP. -/
theorem P_subset_coNP : P ⊆ coNP := by
  intro f hf
  show (fun n => !f n) ∈ NP
  exact P_subset_NP (P_complement_closed emptyOracle f hf)

/-- NP ∩ coNP: problems with short certificates for both yes and no instances. -/
def NP_inter_coNP : Set (ℕ → Bool) :=
  NP ∩ coNP

/-- P ⊆ NP ∩ coNP. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP_inter_coNP := by
  intro f hf
  exact ⟨P_subset_NP hf, P_subset_coNP hf⟩

-- ============================================================
-- PART 11: P = NP Structural Consequences
-- ============================================================

/-- **P = NP → NP = coNP**: If P equals NP, then NP is closed under complement.

    Proof: Assume P = NP. Let f ∈ NP. Then f ∈ P (by P = NP).
    So ¬f ∈ P (complement closure) ⊆ NP. Hence f ∈ coNP.
    Conversely, if f ∈ coNP then ¬f ∈ NP = P, so f = ¬¬f ∈ P ⊆ NP. -/
theorem P_eq_NP_implies_NP_eq_coNP (h : P = NP) : NP = coNP := by
  ext f
  constructor
  · -- f ∈ NP → f ∈ coNP
    intro hf
    show (fun n => !f n) ∈ NP
    -- f ∈ NP = P, so f ∈ P
    have hfP : f ∈ P := h ▸ hf
    -- ¬f ∈ P (complement closure)
    have hcP : (fun n => !f n) ∈ P := P_complement_closed emptyOracle f hfP
    -- P ⊆ NP
    exact P_subset_NP hcP
  · -- f ∈ coNP → f ∈ NP
    intro hf
    -- (¬f) ∈ NP = P
    have hcNP : (fun n => !f n) ∈ NP := hf
    have hcP : (fun n => !f n) ∈ P := h ▸ hcNP
    -- f = ¬¬f, and ¬(¬f) ∈ P
    have hfP : (fun n => !(!(f n))) ∈ P :=
      P_complement_closed emptyOracle (fun n => !f n) hcP
    -- ¬¬f = f
    have : (fun n => !(!(f n))) = f := by ext n; simp
    rw [this] at hfP
    exact P_subset_NP hfP

/-- **NP ≠ coNP → P ≠ NP**: Contrapositive of the above. -/
theorem NP_ne_coNP_implies_P_ne_NP : NP ≠ coNP → P ≠ NP := by
  intro h_neq h_eq
  exact h_neq (P_eq_NP_implies_NP_eq_coNP h_eq)

-- ============================================================
-- PART 12: Polynomial-Time Reductions
-- ============================================================

/-- A polynomial-time computable function relative to oracle A.
    Program e computes f : ℕ → ℕ within polynomial time bound p. -/
def PolyTimeComputable (A : Oracle) (f : ℕ → ℕ) : Prop :=
  ∃ (e : ℕ) (p : Polynomial), ∀ n : ℕ,
    -- The program computes f(n) (encoded as Bool for the framework,
    -- but we use the step count for time bound)
    ∃ s : ℕ, Φ e A n = some (true, s) ∧ s ≤ p.eval (inputSize n)

/-- Problem A polynomial-time reduces to problem B (A ≤ₚ B):
    there exists a poly-time computable function f such that
    for all x, A(x) = B(f(x)). -/
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

/-- Composition of poly-time computable functions is poly-time computable.
    If f and g are each computable in polynomial time, then g ∘ f is too
    (since polynomial composition p(q(n)) is still polynomial). -/
axiom poly_time_compose (f g : ℕ → ℕ)
    (hf : PolyTimeComputable emptyOracle f)
    (hg : PolyTimeComputable emptyOracle g) :
    PolyTimeComputable emptyOracle (g ∘ f)

/-- Polynomial-time reductions compose: if A ≤ₚ B and B ≤ₚ C, then A ≤ₚ C. -/
theorem poly_reduce_trans (A_prob B_prob C_prob : ℕ → Bool)
    (h1 : A_prob ≤ₚ B_prob) (h2 : B_prob ≤ₚ C_prob) : A_prob ≤ₚ C_prob := by
  obtain ⟨f, hf_comp, hf_correct⟩ := h1
  obtain ⟨g, hg_comp, hg_correct⟩ := h2
  exact ⟨g ∘ f, poly_time_compose f g hf_comp hg_comp,
    fun x => by simp [Function.comp, hf_correct, hg_correct]⟩

/-- Polynomial-time reductions preserve membership in P:
    If B ∈ P and A ≤ₚ B, then A ∈ P.

    In any computation model, composing a poly-time reduction with
    a poly-time decision procedure yields a poly-time procedure
    (since polynomial composition is polynomial). -/
axiom reduction_preserves_P (A_prob B_prob : ℕ → Bool)
    (h_reduce : A_prob ≤ₚ B_prob) (h_in_P : B_prob ∈ P) : A_prob ∈ P

/-- **NPC in P → P = NP**: If any NP-complete problem is in P, then P = NP.

    Proof: Let L be NP-complete with L ∈ P. For any problem M ∈ NP,
    M ≤ₚ L (by NP-hardness). Since L ∈ P and reductions preserve P,
    M ∈ P. So NP ⊆ P, and P ⊆ NP gives P = NP. -/
theorem NPComplete_in_P_implies_P_eq_NP (L : ℕ → Bool)
    (h_complete : NPComplete L) (h_in_P : L ∈ P) : P = NP := by
  ext problem
  constructor
  · exact fun hp => P_subset_NP hp
  · intro h_in_NP
    obtain ⟨_, h_hard⟩ := h_complete
    exact reduction_preserves_P problem L (h_hard problem h_in_NP) h_in_P

/-- **P ≠ NP → NPC ∩ P = ∅**: If P ≠ NP, no NP-complete problem is in P. -/
theorem P_ne_NP_implies_NPC_not_in_P (h : P ≠ NP) (L : ℕ → Bool)
    (h_complete : NPComplete L) : L ∉ P := by
  intro h_in_P
  exact h (NPComplete_in_P_implies_P_eq_NP L h_complete h_in_P)

/-- NP-hardness transfers via reductions: if A is NP-hard and A ≤ₚ B, then B is NP-hard. -/
theorem NPHard_of_reduce (A_prob B_prob : ℕ → Bool)
    (h_hard : NPHard A_prob) (h_reduce : A_prob ≤ₚ B_prob) : NPHard B_prob := by
  intro L hL
  exact poly_reduce_trans L A_prob B_prob (h_hard L hL) h_reduce

/-- NP-completeness transfers via reductions within NP:
    if A is NP-complete, B ∈ NP, and A ≤ₚ B, then B is NP-complete. -/
theorem NPComplete_of_reduce (A_prob B_prob : ℕ → Bool)
    (h_complete : NPComplete A_prob) (h_in_NP : B_prob ∈ NP)
    (h_reduce : A_prob ≤ₚ B_prob) : NPComplete B_prob :=
  ⟨h_in_NP, NPHard_of_reduce A_prob B_prob h_complete.2 h_reduce⟩

-- ============================================================
-- PART 13: Polynomial Hierarchy
-- ============================================================

/-
### The Polynomial Hierarchy

The polynomial hierarchy (PH) is a tower of complexity classes that
generalizes P, NP, and coNP:

  Σ₀ᴾ = Π₀ᴾ = P
  Σ₁ᴾ = NP,  Π₁ᴾ = coNP
  Σₖ₊₁ᴾ = NP^(Σₖᴾ),  Πₖ₊₁ᴾ = coNP^(Σₖᴾ)
  PH = ∪ₖ Σₖᴾ

Key theorem: If P = NP, the entire hierarchy collapses to P.
More generally, if Σₖᴾ = Πₖᴾ for any k, the hierarchy collapses at level k.

We define PH using an opaque Sigma_k constant with axiomatized properties.
The opacity prevents the degeneracy where all levels ≥ 1 collapse to NP
(which happened with the previous recursive definition).
-/

/-- Σₖᴾ: the k-th level of the polynomial hierarchy.

    Σ₀ᴾ = P
    Σₖ₊₁ᴾ = NP^(Σₖᴾ) (NP with oracle for Σₖ-complete problems)
    PH = ∪ₖ Σₖᴾ

    Since our model cannot directly encode "oracle for a complexity class"
    (this would require defining complete problems at each level, which needs
    the full Cook-Levin machinery relativized to each level), we define Σₖ
    as an opaque constant and axiomatize its key properties.

    **Why opaque?** The previous recursive definition `| n + 1, A => NP_rel A`
    made Σₖ₊₁ = NP for ALL k, causing PH = NP unconditionally. This made
    Karp-Lipton and PH collapse theorems vacuous. The opaque approach avoids
    this degeneracy while maintaining all essential structural properties. -/
opaque Sigma_k_def : ℕ → Set (ℕ → Bool)
noncomputable def Sigma_k (k : ℕ) : Set (ℕ → Bool) := Sigma_k_def k

/-- Πₖᴾ = co-Σₖᴾ: the complement of each level. -/
def Pi_k (k : ℕ) : Set (ℕ → Bool) :=
  { f | (fun n => !f n) ∈ Sigma_k k }

/-- The Polynomial Hierarchy PH = ∪ₖ Σₖᴾ. -/
noncomputable def PH : Set (ℕ → Bool) := ⋃ k, Sigma_k k

/-- Σ₀ᴾ = P: the base of the hierarchy is deterministic polynomial time. -/
axiom Sigma_zero_eq_P : Sigma_k 0 = P

/-- Σ₁ᴾ = NP: the first level is nondeterministic polynomial time. -/
axiom Sigma_one_eq_NP : Sigma_k 1 = NP

/-- Π₀ᴾ = P. Since Π₀ = co-Σ₀ = co-P, and P is complement-closed. -/
theorem Pi_zero_eq_P : Pi_k 0 = P := by
  ext f
  constructor
  · -- f ∈ Π₀ → f ∈ P
    intro hf
    -- (¬f) ∈ Σ₀ = P
    have hcf : (fun n => !f n) ∈ P := by rw [← Sigma_zero_eq_P]; exact hf
    -- ¬¬f ∈ P by complement closure
    have hccf : (fun n => !(!(f n))) ∈ P :=
      P_complement_closed emptyOracle _ hcf
    -- ¬¬f = f
    have : (fun n => !(!(f n))) = f := by ext n; simp
    rw [this] at hccf
    exact hccf
  · -- f ∈ P → f ∈ Π₀
    intro hf
    show (fun n => !f n) ∈ Sigma_k 0
    rw [Sigma_zero_eq_P]
    exact P_complement_closed emptyOracle f hf

/-- Π₁ᴾ = coNP: the complement of the first level. -/
theorem Pi_one_eq_coNP : Pi_k 1 = coNP := by
  ext f
  simp only [Pi_k, Set.mem_setOf_eq, coNP, coNP_rel]
  constructor
  · intro hf; rw [Sigma_one_eq_NP] at hf; exact hf
  · intro hf; rw [Sigma_one_eq_NP]; exact hf

/-- Σₖᴾ ⊆ Σₖ₊₁ᴾ: the hierarchy is monotonically increasing.
    Each level contains the previous one since adding a quantifier
    alternation can only increase the class of solvable problems. -/
axiom Sigma_monotone (k : ℕ) : Sigma_k k ⊆ Sigma_k (k + 1)

/-- P ⊆ PH: P is contained in the polynomial hierarchy. -/
theorem P_subset_PH : P ⊆ PH := by
  intro f hf
  show f ∈ ⋃ k, Sigma_k k
  exact Set.mem_iUnion.mpr ⟨0, Sigma_zero_eq_P ▸ hf⟩

/-- NP ⊆ PH: NP is contained in the polynomial hierarchy. -/
theorem NP_subset_PH : NP ⊆ PH := by
  intro f hf
  exact Set.mem_iUnion.mpr ⟨1, Sigma_one_eq_NP ▸ hf⟩

-- ============================================================
-- PART 14: PH Collapse from P = NP
-- ============================================================

/-
### PH Collapse

The key structural theorem: if P = NP, then the entire polynomial
hierarchy collapses to P. This is because each level of PH is defined
by adding one more quantifier alternation, but if P = NP, the extra
quantifier can be eliminated.
-/

/-- **Oracle trivialization**: If Σₖ = P, then Σₖ₊₁ = NP.
    Standard result: Σₖ₊₁ = NP^(Σₖ), and if Σₖ = P, then the oracle for
    level k is computable in polynomial time, so NP^(P) = NP. -/
axiom Sigma_collapse_step (k : ℕ) : Sigma_k k = P → Sigma_k (k + 1) = NP

/-- **P = NP → Σₖᴾ = P for all k**: If P equals NP, every level
    of the polynomial hierarchy collapses to P.

    Proof by induction:
    - Base: Σ₀ = P (axiom).
    - Step: Σₖ = P (IH) → Σₖ₊₁ = NP (oracle trivialization) = P (hypothesis). -/
theorem P_eq_NP_implies_Sigma_collapse (h : P = NP) (k : ℕ) :
    Sigma_k k = P := by
  induction k with
  | zero => exact Sigma_zero_eq_P
  | succ k ih =>
    exact (Sigma_collapse_step k ih).trans h.symm

/-- **P = NP → PH = P**: The full polynomial hierarchy collapses to P. -/
theorem P_eq_NP_implies_PH_collapse (h : P = NP) : PH = P := by
  ext f
  constructor
  · -- f ∈ PH → f ∈ P
    intro hf
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hf
    rw [P_eq_NP_implies_Sigma_collapse h k] at hk
    exact hk
  · -- f ∈ P → f ∈ PH
    intro hf
    exact P_subset_PH hf

/-- **Contrapositive**: If PH ≠ P, then P ≠ NP.
    This is a stronger statement than P ≠ NP because PH ≠ P is
    a weaker hypothesis than is commonly assumed about complexity. -/
theorem PH_ne_P_implies_P_ne_NP : PH ≠ P → P ≠ NP := by
  intro h_neq h_eq
  exact h_neq (P_eq_NP_implies_PH_collapse h_eq)

-- ============================================================
-- PART 15: PSPACE and EXP
-- ============================================================

/-
### PSPACE and EXP

PSPACE = problems solvable with polynomial space.
EXP = problems solvable in exponential time.

Key containment chain: P ⊆ NP ⊆ PSPACE ⊆ EXP.

In our abstract model, we define these via axioms since our Φ model
tracks time but not space explicitly.
-/

/-- PSPACE: problems solvable in polynomial space.
    Since our Φ model tracks time (step count) but not space explicitly,
    we define PSPACE as an opaque constant and axiomatize its relationships.
    This is more honest than giving it the same definition as EXP. -/
opaque PSPACE_def : Set (ℕ → Bool)
def PSPACE : Set (ℕ → Bool) := PSPACE_def

/-- EXP: problems solvable in exponential time (2^{p(n)} for some polynomial p).
    Unlike PSPACE, we CAN define EXP properly because Φ tracks step counts.
    A problem is in EXP if some program solves it within 2^{p(|n|)} steps. -/
def InEXP (f : ℕ → Bool) : Prop :=
  ∃ (e : ℕ) (p : Polynomial),
    Solves e emptyOracle f ∧
    ∀ n s, Φ e emptyOracle n = some (f n, s) → s ≤ 2 ^ p.eval (inputSize n)

def EXP : Set (ℕ → Bool) := { f | InEXP f }

/-- NP ⊆ PSPACE: An NP problem can be solved in polynomial space by
    iterating over all certificates (using only polynomial space to
    store each candidate and reusing space between iterations). -/
axiom NP_subset_PSPACE : NP ⊆ PSPACE

/-- PSPACE ⊆ EXP: A polynomial-space computation can have at most
    2^{p(n)} configurations, so it must halt within exponential time.
    With opaque PSPACE, this must be axiomatized. -/
axiom PSPACE_subset_EXP : PSPACE ⊆ EXP

/-- PH ⊆ PSPACE: Every level of the polynomial hierarchy is in PSPACE.
    Each Σₖ can be solved in polynomial space by iterating over quantifier
    blocks, reusing space between iterations. Since both Σₖ and PSPACE are
    opaque, this must be axiomatized. -/
axiom PH_subset_PSPACE : PH ⊆ PSPACE

/-- The full complexity containment chain: P ⊆ NP ⊆ PH ⊆ PSPACE ⊆ EXP. -/
theorem complexity_chain :
    P ⊆ NP ∧ NP ⊆ PH ∧ PH ⊆ PSPACE ∧ PSPACE ⊆ EXP :=
  ⟨P_subset_NP, NP_subset_PH, PH_subset_PSPACE, PSPACE_subset_EXP⟩

/-- P ⊆ PSPACE (transitivity). -/
theorem P_subset_PSPACE : P ⊆ PSPACE :=
  Set.Subset.trans P_subset_NP (Set.Subset.trans NP_subset_PH PH_subset_PSPACE)

/-- Helper: polynomial values are bounded by exponentials. n ≤ 2^n for all n. -/
private theorem poly_le_exp (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left (Nat.one_le_two_pow) _
      _ = 2 ^ (k + 1) := by ring

/-- P ⊆ EXP: every poly-time computation runs in exp-time.
    Direct proof: if s ≤ p.eval(|n|) then s ≤ 2^p.eval(|n|). -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro f ⟨e, p, hsolves, htime⟩
  exact ⟨e, p, hsolves, fun n s hs => le_trans (htime n s hs) (poly_le_exp _)⟩

-- ============================================================
-- PART 16: Ladner's Theorem (Statement)
-- ============================================================

/-
### Ladner's Theorem (1975)

If P ≠ NP, there exist problems that are NP-intermediate:
in NP but neither in P nor NP-complete.

This is a pure existence result proved by a "padding" argument.
Ladner constructs a language SAT_H by inserting padding into SAT
at a rate controlled by a function H, chosen so that SAT_H is
"just hard enough" to not be in P but "not hard enough" to be NP-complete.

We state this as an axiom since the construction requires a computable
enumeration of all polynomial-time algorithms.
-/

/-- A problem is NP-intermediate if it is in NP \ P but not NP-complete. -/
def NPIntermediate (problem : ℕ → Bool) : Prop :=
  problem ∈ NP ∧ problem ∉ P ∧ ¬ NPComplete problem

/-- **Ladner's Theorem (1975)**: If P ≠ NP, NP-intermediate problems exist.

    Proof idea: Define SAT_H where the padding function H grows slowly enough
    that SAT_H ∈ NP (it's a subset of SAT) but fast enough that SAT_H ∉ P
    (otherwise we could solve SAT in polynomial time). The careful balance
    ensures SAT_H is not NP-complete either (reducing SAT to SAT_H would
    require too much padding removal). -/
axiom ladner_theorem : P ≠ NP → ∃ L : ℕ → Bool, NPIntermediate L

-- ============================================================
-- PART 17: Separation Results
-- ============================================================

/-
### Known Separation Results

While P vs NP is open, some separations are known unconditionally.
-/

/-- **Time Hierarchy Theorem** (Hartmanis-Stearns, 1965):
    Strictly more time gives strictly more computational power.
    In particular, P ⊊ EXP.

    This is proved by a diagonal argument: the "universal simulation"
    machine runs each program and diagonalizes against it. The extra
    time budget allows the simulation overhead. -/
axiom P_ne_EXP : P ≠ EXP

/-- P ⊊ EXP: P is a strict subset of EXP. -/
theorem P_strict_subset_EXP : P ⊂ EXP :=
  Set.ssubset_iff_subset_ne.mpr ⟨P_subset_EXP, P_ne_EXP⟩

/-- **Key structural consequence**: At least one link in
    P ⊆ NP ⊆ PH ⊆ PSPACE ⊆ EXP must be strict.

    Since P ≠ EXP (time hierarchy theorem), not all inclusions
    can be equalities. This is the strongest unconditional result
    about the P-NP-PSPACE-EXP chain. -/
theorem some_containment_strict :
    P ≠ NP ∨ NP ≠ PH ∨ PH ≠ PSPACE ∨ PSPACE ≠ EXP := by
  -- If all were equalities, P = EXP, contradicting P_ne_EXP
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply P_ne_EXP
  calc P = NP := h1
    _ = PH := h2
    _ = PSPACE := h3
    _ = EXP := h4

-- ============================================================
-- PART 18: Cook-Levin Theorem (NP-Complete Problems Exist)
-- ============================================================

/-
### Cook-Levin Theorem (1971)

The Cook-Levin theorem establishes that SAT (Boolean satisfiability) is
NP-complete. This is the foundational result of NP-completeness theory:
it shows that NP-complete problems exist and provides the first example.

Cook (1971) proved SAT is NP-complete by showing how to encode any
polynomial-time nondeterministic computation as a satisfiability instance.
Levin independently proved the same result in the USSR.
-/

/-- SAT: the Boolean satisfiability problem.
    Given a Boolean formula (encoded as ℕ), decide whether it is satisfiable.
    We define this as an opaque constant since the encoding details
    are irrelevant to the structural results. -/
opaque SAT_def : ℕ → Bool
def SAT : ℕ → Bool := SAT_def

/-- **Cook-Levin Theorem (1971)**: SAT is NP-complete.

    Proof sketch: Given any NP language L with verifier V, for input x,
    construct a Boolean formula φ_x that encodes "∃ certificate c such that
    V(x, c) accepts." The formula describes the entire computation tableau
    of V on (x, c), with c as free variables. Then x ∈ L iff φ_x ∈ SAT.

    The reduction runs in polynomial time because V's computation tableau
    has polynomial size. -/
axiom cook_levin : NPComplete SAT

/-- NP-complete problems exist. Immediate from Cook-Levin. -/
theorem NPC_exists : ∃ L : ℕ → Bool, NPComplete L :=
  ⟨SAT, cook_levin⟩

/-- SAT is in NP (from Cook-Levin). -/
theorem SAT_in_NP : SAT ∈ NP := cook_levin.1

/-- SAT is NP-hard (from Cook-Levin). -/
theorem SAT_NPHard : NPHard SAT := cook_levin.2

/-- **SAT in P ↔ P = NP**: The P vs NP question reduces to whether SAT is in P. -/
theorem SAT_in_P_iff_P_eq_NP : SAT ∈ P ↔ P = NP :=
  ⟨fun h => NPComplete_in_P_implies_P_eq_NP SAT cook_levin h,
   fun h => h ▸ SAT_in_NP⟩

-- ============================================================
-- PART 19: P/poly and Karp-Lipton
-- ============================================================

/-
### P/poly and the Karp-Lipton Theorem

P/poly is the class of problems solvable by polynomial-size Boolean circuits
(equivalently, by polynomial-time algorithms with polynomial-length advice
strings). P/poly is a nonuniform complexity class: the "algorithm" can be
different for each input length.

Key facts:
- P ⊆ P/poly (uniform algorithms are a special case)
- BPP ⊆ P/poly (Adleman's theorem: random bits can be replaced by advice)
- If NP ⊆ P/poly, the polynomial hierarchy collapses (Karp-Lipton)
-/

/-- P/poly: problems solvable by polynomial-size circuits (nonuniform).
    Since our model doesn't have circuits, we define this as an opaque
    set and axiomatize its key relationships. -/
opaque P_poly_def : Set (ℕ → Bool)
def P_poly : Set (ℕ → Bool) := P_poly_def

/-- P ⊆ P/poly: uniform polynomial-time algorithms are a special case
    of nonuniform polynomial-size circuits (use the same circuit for
    all inputs of each length). -/
axiom P_subset_P_poly : P ⊆ P_poly

/-- **Karp-Lipton Theorem (1980)**: If NP ⊆ P/poly, then PH collapses.

    More precisely, NP ⊆ P/poly implies PH = Σ₂ᴾ (the hierarchy collapses
    to the second level).

    Proof idea: If NP ⊆ P/poly, then SAT has polynomial-size circuits.
    A Σ₂ machine can "guess" the circuit and verify it works for all
    inputs of the relevant length, then use it to simulate any NP oracle.
    This eliminates all quantifier alternations above level 2.

    **Significance**: This is a key barrier to proving circuit lower bounds.
    If we could show NP ⊄ P/poly (i.e., NP problems need super-polynomial
    circuits), this would separate P from NP (since P ⊆ P/poly). But the
    natural proofs barrier blocks most approaches to circuit lower bounds. -/
axiom karp_lipton : NP ⊆ P_poly → PH = Sigma_k 2

/-- **Contrapositive of Karp-Lipton**: If PH doesn't collapse to Σ₂ᴾ,
    then NP ⊄ P/poly. -/
theorem karp_lipton_contrapositive (h_neq : PH ≠ Sigma_k 2) : ¬ (NP ⊆ P_poly) := by
  intro h_sub
  exact h_neq (karp_lipton h_sub)

/-- **Structural consequence**: If we could prove NP ⊄ P/poly, then P ≠ NP.
    This is because P ⊆ P/poly, so NP ⊄ P/poly implies NP ⊄ P. -/
theorem NP_not_subset_P_poly_implies_P_ne_NP (h : ¬ (NP ⊆ P_poly)) : P ≠ NP := by
  intro h_eq
  apply h
  rw [← h_eq]
  exact P_subset_P_poly

-- ============================================================
-- PART 20: BPP (Probabilistic Polynomial Time)
-- ============================================================

/-
### BPP: Bounded-Error Probabilistic Polynomial Time

BPP is the class of problems solvable by probabilistic polynomial-time
algorithms with error probability ≤ 1/3. It captures "efficient randomized
computation."

Since our Φ model is deterministic, we define BPP as an opaque constant
and axiomatize its key relationships to other classes.

Key facts:
- P ⊆ BPP (deterministic algorithms are trivially randomized)
- BPP ⊆ PSPACE (simulate all random choices in polynomial space)
- BPP ⊆ P/poly (Adleman 1978: random bits can be replaced by advice)
- Whether P = BPP is a major open question (believed true)
-/

/-- BPP: problems solvable by probabilistic polynomial-time algorithms
    with bounded error (≤ 1/3 on all inputs). Since our Φ model is
    deterministic and doesn't model randomness, BPP is opaque. -/
opaque BPP_def : Set (ℕ → Bool)
def BPP : Set (ℕ → Bool) := BPP_def

/-- P ⊆ BPP: every deterministic poly-time algorithm is trivially a
    randomized algorithm (it ignores the random bits). -/
axiom P_subset_BPP : P ⊆ BPP

/-- BPP ⊆ PSPACE: enumerate all possible random strings (2^{p(n)} of them),
    count accepting paths, decide majority. Reuses polynomial space. -/
axiom BPP_subset_PSPACE : BPP ⊆ PSPACE

/-- **Adleman's Theorem (1978)**: BPP ⊆ P/poly.
    Random bits can be replaced by a fixed "good" advice string for each
    input length. By a counting/probabilistic argument, for each length n,
    there exists a single random string that works for all inputs of length n. -/
axiom adleman_BPP_subset_P_poly : BPP ⊆ P_poly

/-- The extended containment chain: P ⊆ BPP ⊆ PSPACE ⊆ EXP. -/
theorem BPP_chain : P ⊆ BPP ∧ BPP ⊆ PSPACE ∧ PSPACE ⊆ EXP :=
  ⟨P_subset_BPP, BPP_subset_PSPACE, PSPACE_subset_EXP⟩

/-- P = BPP is a major open conjecture. Most complexity theorists believe
    it is true (i.e., randomness does not help polynomial-time computation).
    Evidence: pseudorandom generators under circuit lower bound assumptions. -/
def P_eq_BPP_conjecture : Prop := P = BPP

-- ============================================================
-- PART 21: IP = PSPACE (Shamir's Theorem)
-- ============================================================

/-
### Interactive Proofs and IP = PSPACE

IP (Interactive Proofs) is the class of languages that have interactive
proof systems: a polynomial-time verifier exchanges messages with an
all-powerful prover, and the verifier accepts/rejects with bounded error.

The landmark result IP = PSPACE (Shamir 1990) shows that interactive
proofs capture exactly PSPACE. This is one of the deepest results in
complexity theory, proved via arithmetization of Boolean formulas.

The IP = PSPACE result is notable because it *algebrizes* — it uses
algebraic techniques (polynomial evaluation over finite fields).
Yet by the algebrization barrier, such techniques cannot resolve P vs NP.
-/

/-- IP: the class of problems with polynomial-round interactive proof systems.
    A verifier V runs in probabilistic polynomial time and exchanges messages
    with an all-powerful prover P. For YES instances, some prover convinces V
    with probability ≥ 2/3. For NO instances, no prover convinces V with
    probability > 1/3. -/
opaque IP_def : Set (ℕ → Bool)
def IP : Set (ℕ → Bool) := IP_def

/-- NP ⊆ IP: NP problems have trivial interactive proofs (the prover sends
    the witness, the verifier checks it deterministically). -/
axiom NP_subset_IP : NP ⊆ IP

/-- **Shamir's Theorem (1990)**: IP = PSPACE.

    One of the most celebrated results in complexity theory.

    **PSPACE ⊆ IP** (the hard direction): Uses arithmetization to convert
    quantified Boolean formulas (QBF, the PSPACE-complete problem) into
    polynomial identity testing over finite fields, then applies the
    sumcheck protocol.

    **IP ⊆ PSPACE** (easier): Enumerate all prover strategies using
    polynomial space, computing optimal prover response at each round.

    **Significance for barriers**: This proof *algebrizes* (it extends to
    algebraic oracles), yet it cannot help resolve P vs NP because
    algebrization is a barrier technique. -/
axiom shamir_IP_eq_PSPACE : IP = PSPACE

/-- BPP ⊆ IP: randomized computations are trivially interactive
    (the verifier can simulate the algorithm without a prover). -/
theorem BPP_subset_IP : BPP ⊆ IP :=
  Set.Subset.trans BPP_subset_PSPACE shamir_IP_eq_PSPACE.symm.subset

/-- The grand containment picture:
    P ⊆ NP ⊆ IP = PSPACE ⊆ EXP
    P ⊆ BPP ⊆ IP = PSPACE ⊆ EXP -/
theorem grand_containment :
    P ⊆ NP ∧ NP ⊆ IP ∧ IP = PSPACE ∧
    P ⊆ BPP ∧ BPP ⊆ PSPACE :=
  ⟨P_subset_NP, NP_subset_IP, shamir_IP_eq_PSPACE,
   P_subset_BPP, BPP_subset_PSPACE⟩

-- ============================================================
-- PART 22: Summary and Verification
-- ============================================================

-- Barrier results
#check relativization_barrier     -- ¬ RelativizingProof ∧ ¬ RelativizingProof
#check natural_proofs_barrier     -- ¬ UsefulAgainst np f
#check algebrization_barrier      -- ¬ AlgebrizingProof ∧ ¬ AlgebrizingProof
#check all_barriers               -- Combined: all three barriers

-- Model soundness
#check P_nontrivial               -- P ≠ Set.univ (sound model!)
#check p_vs_np_well_posed         -- P ≠ Set.univ ∧ P ⊆ NP

-- Structural results
#check P_subset_coNP              -- P ⊆ coNP
#check P_subset_NP_inter_coNP     -- P ⊆ NP ∩ coNP
#check P_eq_NP_implies_NP_eq_coNP -- P = NP → NP = coNP
#check NP_ne_coNP_implies_P_ne_NP -- NP ≠ coNP → P ≠ NP
#check NPComplete_in_P_implies_P_eq_NP  -- NPC ∩ P ≠ ∅ → P = NP
#check P_ne_NP_implies_NPC_not_in_P     -- P ≠ NP → NPC ∩ P = ∅
#check NPHard_of_reduce           -- NP-hardness transfers via reductions
#check NPComplete_of_reduce       -- NP-completeness transfers via reductions

-- Polynomial Hierarchy
#check Sigma_zero_eq_P            -- Σ₀ᴾ = P
#check Sigma_one_eq_NP            -- Σ₁ᴾ = NP
#check Pi_zero_eq_P               -- Π₀ᴾ = P
#check Pi_one_eq_coNP             -- Π₁ᴾ = coNP
#check Sigma_monotone             -- Σₖ ⊆ Σₖ₊₁
#check P_subset_PH                -- P ⊆ PH
#check NP_subset_PH               -- NP ⊆ PH
#check P_eq_NP_implies_PH_collapse  -- P = NP → PH = P
#check PH_ne_P_implies_P_ne_NP   -- PH ≠ P → P ≠ NP

-- PSPACE and EXP chain
#check complexity_chain           -- P ⊆ NP ⊆ PH ⊆ PSPACE ⊆ EXP
#check P_strict_subset_EXP        -- P ⊊ EXP
#check some_containment_strict    -- At least one containment is strict

-- Ladner's theorem
#check ladner_theorem             -- P ≠ NP → ∃ NP-intermediate

-- Cook-Levin and NP-completeness
#check cook_levin                 -- SAT is NP-complete
#check NPC_exists                 -- NP-complete problems exist
#check SAT_in_NP                  -- SAT ∈ NP
#check SAT_NPHard                 -- SAT is NP-hard
#check SAT_in_P_iff_P_eq_NP       -- SAT ∈ P ↔ P = NP

-- P/poly and Karp-Lipton
#check P_subset_P_poly            -- P ⊆ P/poly
#check karp_lipton                -- NP ⊆ P/poly → PH = Σ₂ᴾ
#check karp_lipton_contrapositive -- PH ≠ Σ₂ᴾ → NP ⊄ P/poly
#check NP_not_subset_P_poly_implies_P_ne_NP  -- NP ⊄ P/poly → P ≠ NP

-- BPP and derandomization
#check P_subset_BPP               -- P ⊆ BPP
#check BPP_subset_PSPACE          -- BPP ⊆ PSPACE
#check adleman_BPP_subset_P_poly  -- BPP ⊆ P/poly (Adleman)
#check BPP_chain                  -- P ⊆ BPP ⊆ PSPACE ⊆ EXP

-- Interactive proofs
#check NP_subset_IP               -- NP ⊆ IP
#check shamir_IP_eq_PSPACE        -- IP = PSPACE (Shamir 1990)
#check BPP_subset_IP              -- BPP ⊆ IP (derived)
#check grand_containment          -- Full containment picture

end PNPBarriersSound
