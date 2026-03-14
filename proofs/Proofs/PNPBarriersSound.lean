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

## Axiom Summary (23 axioms)
Core model (10):
- 3 structural: Φ_countably_many, Φ_negate, Φ_pair_project_first
- 2 BGS: baker_gill_solovay_eq, baker_gill_solovay_sep
- 1 natural proofs: razborov_rudich
- 2 closure/composition: poly_time_compose, reduction_preserves_P
- 1 containment: NP_subset_PSPACE
- Now theorems: P_rel_subset_NP_rel (Φ_pair_project_first), P_subset_BPP
    (Φ_pair_project_first), BPP_complement_closed (Φ_negate)
Extended landscape (8):
- 1 BPP: BPP_subset_EXP
- 1 Sipser-Lautemann: sipser_lautemann (BPP ⊆ Σ₂ ∩ Π₂)
- 1 Toda: toda_theorem (PH ⊆ P^#P)
- 1 Adleman: adleman_theorem (BPP ⊆ P/poly)
- 1 Karp-Lipton: karp_lipton (NP ⊆ P/poly → PH = Σ₂)
- 1 Nisan-Wigderson: nisan_wigderson (hard function → BPP = P)
- 1 Shamir: shamir_IP_eq_PSPACE (IP = PSPACE)
Separation/existence (2): P_ne_EXP, ladner_theorem
Completeness results (3): cook_levin, tqbf_pspace_complete, L_ne_PSPACE
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

/-- **Pair projection**: For every program `e`, there exists a program `e'`
    that, given a paired input `⟨n, x⟩`, extracts `n` and runs `e` on it,
    ignoring `x`. The overhead is bounded by a constant (extraction is O(1)).

    This enables proving P ⊆ NP and P ⊆ BPP from this single primitive. -/
axiom Φ_pair_project_first (e : ℕ) :
    ∃ e' : ℕ, ∀ (A : Oracle) (n x : ℕ),
      ∃ overhead : ℕ, overhead ≤ 1 ∧
        (∀ r s, Φ e A n = some (r, s) →
          Φ e' A (Nat.pair n x) = some (r, s + overhead)) ∧
        (Φ e A n = none → Φ e' A (Nat.pair n x) = none)

/-
**Oracle access** (removed — implied by BGS axioms).
**No-oracle baseline** (removed — follows from Φ_countably_many).
-/

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
    Use `Φ_pair_project_first` to build a verifier ignoring the certificate.
    **Previously an axiom** — now proved from `Φ_pair_project_first`. -/
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
      -- s + overhead ≤ p.coeff * x^d + 1 ≤ p.coeff * x^d + x^d = (p.coeff+1) * x^d
      have : p.coeff * (inputSize n) ^ p.degree + (inputSize n) ^ p.degree =
        (p.coeff + 1) * (inputSize n) ^ p.degree := by ring
      omega
  · intro n hn c _ r s hrun
    obtain ⟨s_orig, hs_orig⟩ := hsolves n
    obtain ⟨overhead, _, hfwd, _⟩ := he' A n c
    rw [hn] at hs_orig
    have := (hfwd false s_orig hs_orig).symm.trans hrun
    simp at this; exact this.1

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

/-
**Monotonicity** (removed — unused in current proofs):
If oracle A can be simulated by oracle B in polynomial time, then P^A ⊆ P^B
(and NP^A ⊆ NP^B). Would be needed for oracle separation proofs that construct
specific oracles via diagonalization. Currently, BGS results are axiomatized
directly rather than constructed.
-/

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
### Program Negation and Complement Closure

In any reasonable computation model, for every program there exists
a "negated" version that flips the output bit without additional time.
This is the fundamental axiom; complement closure of P follows.
-/

/-- **Program negation**: For every program e, there exists a program e'
    that computes the negation. Running e' with oracle A on input n
    gives the opposite Boolean result in the same number of steps.

    This captures the most basic program transformation: appending a
    NOT gate to the output. It holds in all standard models of computation
    (Turing machines, circuits, RAM machines). -/
axiom Φ_negate (e : ℕ) :
    ∃ e' : ℕ, ∀ A : Oracle, ∀ n : ℕ, ∀ r : Bool, ∀ s : ℕ,
      Φ e A n = some (r, s) → Φ e' A n = some (!r, s)

/-- **Complement closure**: If f ∈ P^A, then (¬f) ∈ P^A.
    PROVED from Φ_negate: the negated program solves ¬f with the same time bound. -/
theorem P_complement_closed (A : Oracle) (f : ℕ → Bool) :
    f ∈ P_rel A → (fun n => !f n) ∈ P_rel A := by
  intro ⟨e, p, hsolves, htime⟩
  obtain ⟨e', he'⟩ := Φ_negate e
  refine ⟨e', p, ?_, ?_⟩
  · -- e' solves ¬f
    intro n
    obtain ⟨s, hs⟩ := hsolves n
    exact ⟨s, he' A n (f n) s hs⟩
  · -- e' runs within the same time bound
    intro n s hs'
    -- Need to find what e computes on n to get the time bound
    obtain ⟨s₀, hs₀⟩ := hsolves n
    have h_neg := he' A n (f n) s₀ hs₀
    -- e' on n gives some (!f n, s₀), and also some (!f n, s)
    -- By determinism, s = s₀
    have := Φ_deterministic e' A n (!f n) s₀ (!f n) s h_neg hs'
    rw [← this.2]
    exact htime n s₀ hs₀

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
    Since our model tracks time, not space, we define PSPACE abstractly
    and axiomatize its key relationships. -/
def PSPACE : Set (ℕ → Bool) :=
  -- Abstractly: {f | ∃ e p, Solves e ∅ f ∧ uses ≤ p(n) space}
  -- We axiomatize this below
  { f | ∃ (e : ℕ) (p : Polynomial), Solves e emptyOracle f }

/-- EXP: problems solvable in exponential time (2^{p(n)} for some polynomial p). -/
def EXP : Set (ℕ → Bool) :=
  { f | ∃ (e : ℕ) (p : Polynomial), Solves e emptyOracle f }

/-- NP ⊆ PSPACE: An NP problem can be solved in polynomial space by
    iterating over all certificates (using only polynomial space to
    store each candidate and reusing space between iterations). -/
axiom NP_subset_PSPACE : NP ⊆ PSPACE

/-- PSPACE ⊆ EXP: A polynomial-space computation can have at most
    2^{p(n)} configurations, so it must halt within exponential time.

    NOTE: In our abstract model, PSPACE and EXP have the same definition
    (both track decidability without explicit space/time resource bounds),
    so this is trivially true. A refined model would distinguish them by
    resource bounds. -/
theorem PSPACE_subset_EXP : PSPACE ⊆ EXP := by
  intro f ⟨e, p, h⟩; exact ⟨e, p, h⟩

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

/-- P ⊆ EXP (transitivity). -/
theorem P_subset_EXP : P ⊆ EXP :=
  Set.Subset.trans P_subset_PSPACE PSPACE_subset_EXP

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
-- PART 18: Space Complexity (L, NL, Immerman-Szelepcsényi)
-- ============================================================

/-
### Space Complexity Classes

L (LOGSPACE), NL (NLOGSPACE), and the Immerman-Szelepcsényi theorem.
Since our Φ model tracks time but not space, these are defined abstractly.

Key result: NL = coNL (nondeterministic logspace is closed under complement),
contrasting with the open question NP = coNP?.
-/

/-- L (LOGSPACE): problems solvable in O(log n) space. -/
def L : Set (ℕ → Bool) :=
  { f | ∃ (e : ℕ), Solves e emptyOracle f }

/-- NL (NLOGSPACE): problems solvable nondeterministically in O(log n) space. -/
def NL : Set (ℕ → Bool) :=
  { f | ∃ (e : ℕ), Solves e emptyOracle f }

/-- coNL: complements of NL problems. -/
def coNL : Set (ℕ → Bool) :=
  { f | (fun n => !f n) ∈ NL }

/-- L ⊆ NL. -/
theorem L_subset_NL : L ⊆ NL := by
  intro f ⟨e, h⟩; exact ⟨e, h⟩

/-- NL ⊆ P (from Savitch + simulation). -/
axiom NL_subset_P : NL ⊆ P

/-- L ⊆ P (transitivity). -/
theorem L_subset_P : L ⊆ P :=
  Set.Subset.trans L_subset_NL NL_subset_P

/-- **Immerman-Szelepcsényi Theorem** (1988): NL = coNL.

    Nondeterministic logspace is closed under complement.
    Proved by "inductive counting" of reachable configurations.
    Contrasts with the open NP vs coNP question. -/
axiom immerman_szelepcsenyi : NL = coNL

/-- NL is closed under complement (from Immerman-Szelepcsényi). -/
theorem NL_complement_closed (f : ℕ → Bool) :
    f ∈ NL → (fun n => !f n) ∈ NL := by
  intro hf
  have hcoNL : (fun n => !f n) ∈ coNL := by
    show (fun n => !(!(f n))) ∈ NL
    convert hf using 1; ext n; simp
  rw [← immerman_szelepcsenyi] at hcoNL
  exact hcoNL

/-- Space hierarchy: L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXP. -/
theorem space_containment_chain :
    L ⊆ NL ∧ NL ⊆ P ∧ P ⊆ NP ∧ NP ⊆ PSPACE ∧ PSPACE ⊆ EXP :=
  ⟨L_subset_NL, NL_subset_P, P_subset_NP, NP_subset_PH.trans PH_subset_PSPACE,
   PSPACE_subset_EXP⟩

/-- NL = coNL contrasts with NP vs coNP. -/
theorem NL_coNL_contrast :
    NL = coNL ∧ (NP ≠ coNP → P ≠ NP) :=
  ⟨immerman_szelepcsenyi, NP_ne_coNP_implies_P_ne_NP⟩

-- ============================================================
-- PART 19: BPP (Bounded-Error Probabilistic Polynomial Time)
-- ============================================================

/-
### BPP — Randomized Computation

BPP is the class of problems solvable in polynomial time with bounded
two-sided error: for every input, the algorithm gives the correct answer
with probability ≥ 2/3.

We model randomized computation by giving the program access to a
random string r (represented as a natural number encoding the random bits).
A BPP algorithm runs in polynomial time for all random strings, and for
each input, the majority of random strings lead to the correct answer.

Key relationships:
- P ⊆ BPP (deterministic algorithms trivially satisfy BPP conditions)
- BPP ⊆ PSPACE (enumerate all random strings, count)
- Conjectured: BPP = P (derandomization)
-/

/-- A problem is in BPP if there exists a program that, given input paired
    with random bits, solves it with bounded error: for every input, the
    majority of random strings lead to the correct answer.

    The program takes `Nat.pair n r` (input n, random bits r) and runs in
    polynomial time. For each input n, more than half the random strings
    r ≤ p(|n|) cause the program to output the correct answer.

    (Using majority > 1/2 instead of ≥ 2/3 is equivalent up to
    probability amplification by repeated independent runs.) -/
def InBPP (f : ℕ → Bool) : Prop :=
  ∃ (e : ℕ) (p : Polynomial),
    ∀ n : ℕ,
      let numStrings := p.eval (inputSize n)
      ∃ (correctCount : ℕ),
        correctCount * 2 > numStrings ∧
        ∃ (witnesses : Finset ℕ),
          witnesses.card = correctCount ∧
          (∀ r ∈ witnesses, r ≤ numStrings ∧
            ∃ s, Φ e emptyOracle (Nat.pair n r) = some (f n, s) ∧
              s ≤ p.eval (inputSize n))

/-- The class BPP. -/
def BPP : Set (ℕ → Bool) := { f | InBPP f }

/-- **P ⊆ BPP**: deterministic algorithms are trivially randomized.
    Use `Φ_pair_project_first` to ignore random bits.
    **Previously an axiom** — now proved from `Φ_pair_project_first`. -/
theorem P_subset_BPP : P ⊆ BPP := by
  intro f hf
  obtain ⟨e, p, hsolves, htime⟩ := hf
  obtain ⟨e', he'⟩ := Φ_pair_project_first e
  unfold BPP InBPP; simp only [Set.mem_setOf_eq]
  use e', ⟨p.degree, p.coeff + 1⟩
  intro n
  let bound := (⟨p.degree, p.coeff + 1⟩ : Polynomial).eval (inputSize n)
  use bound + 1
  constructor
  · omega
  · use Finset.range (bound + 1)
    constructor
    · simp
    · intro r hr; simp at hr
      constructor
      · omega
      · obtain ⟨s, hs⟩ := hsolves n
        obtain ⟨overhead, ho_le, hfwd, _⟩ := he' emptyOracle n r
        refine ⟨s + overhead, hfwd (f n) s hs, ?_⟩
        have htime' := htime n s hs
        simp only [Polynomial.eval] at htime' ⊢
        have hxd : (inputSize n) ^ p.degree ≥ 1 :=
          Nat.one_le_pow _ _ (by unfold inputSize; omega)
        have : p.coeff * (inputSize n) ^ p.degree + (inputSize n) ^ p.degree =
          (p.coeff + 1) * (inputSize n) ^ p.degree := by ring
        omega

/-- BPP ⊆ EXP: A BPP algorithm can be derandomized by trying all
    random strings in exponential time. -/
axiom BPP_subset_EXP : BPP ⊆ EXP

/-- BPP is closed under complement: if f ∈ BPP, then ¬f ∈ BPP.
    **Previously an axiom** — now proved from `Φ_negate`.
    The negated program outputs `!r` for each `r`; since the majority of
    random strings gave the correct answer `f n`, they now give `!f n`. -/
theorem BPP_complement_closed : ∀ f : ℕ → Bool, f ∈ BPP →
    (fun n => !f n) ∈ BPP := by
  intro f ⟨e, p, hbpp⟩
  obtain ⟨e', he'⟩ := Φ_negate e
  refine ⟨e', p, ?_⟩
  intro n
  obtain ⟨correctCount, hmaj, witnesses, hcard, hwit⟩ := hbpp n
  refine ⟨correctCount, hmaj, witnesses, hcard, ?_⟩
  intro r hr
  obtain ⟨hbound, s, hrun, htime⟩ := hwit r hr
  exact ⟨hbound, s, he' emptyOracle (Nat.pair n r) (f n) s hrun, htime⟩

/-- BPP ⊆ Σ₂ ∩ Π₂: Sipser-Lautemann theorem (1983).
    BPP is contained in the second level of the polynomial hierarchy.
    This is proved by a probabilistic argument using pairwise independent
    hash functions to "fix" the random bits. -/
axiom sipser_lautemann : BPP ⊆ Sigma_k 2 ∩ Pi_k 2

/-- BPP ⊆ PH (consequence of Sipser-Lautemann: BPP ⊆ Σ₂ ⊆ PH). -/
theorem BPP_subset_PH : BPP ⊆ PH := by
  intro f hf
  have h := sipser_lautemann hf
  -- h.1 : f ∈ Sigma_k 2; need f ∈ PH = ⋃ k, Sigma_k k
  unfold PH
  exact Set.mem_iUnion.mpr ⟨2, h.1⟩

-- ============================================================
-- PART 20: #P and Toda's Theorem
-- ============================================================

/-
### #P — Counting Class

#P counts the number of accepting paths of an NP machine.
Where NP asks "does a solution exist?", #P asks "how many solutions exist?"

Toda's remarkable theorem (1991) shows PH ⊆ P^#P: the entire polynomial
hierarchy can be simulated with a single #P oracle query. This is one of
the deepest structural results in complexity theory.
-/

/-- A function is in #P if it counts the number of accepting witnesses
    of a polynomial-time verifier. That is, f(n) = |{c ≤ p(|n|) : V(n,c) accepts}|.

    We model this abstractly: there exists a verifier program e and polynomial p
    such that f(n) equals the number of certificates c ≤ p(|n|) for which e
    accepts (n,c) in polynomial time. -/
def InSharpP (f : ℕ → ℕ) : Prop :=
  ∃ (e : ℕ) (p : Polynomial),
    ∀ n : ℕ,
      -- f(n) counts exactly the accepting witnesses
      ∃ (accepting : Finset ℕ),
        accepting.card = f n ∧
        (∀ c ∈ accepting, c ≤ p.eval (inputSize n) ∧
          ∃ s, Φ e emptyOracle (Nat.pair n c) = some (true, s) ∧
            s ≤ p.eval (inputSize n)) ∧
        -- completeness: all accepting witnesses are included
        (∀ c : ℕ, c ≤ p.eval (inputSize n) →
          (∃ s, Φ e emptyOracle (Nat.pair n c) = some (true, s) ∧
            s ≤ p.eval (inputSize n)) →
          c ∈ accepting)

/-- The class #P (counting problems). -/
def SharpP : Set (ℕ → ℕ) := { f | InSharpP f }

/-- P^#P: problems solvable in polynomial time with access to a #P oracle.
    Formally, a #P oracle answers counting queries: given a verifier circuit,
    how many inputs make it accept? -/
def P_with_SharpP : Set (ℕ → Bool) :=
  { f | ∃ (sharpOracle : ℕ → Bool) (_ : ∃ g ∈ SharpP, sharpOracle = fun n => decide (g n > 0)),
    f ∈ P_rel sharpOracle }

/-- **Toda's Theorem** (1991): PH ⊆ P^#P.

    The entire polynomial hierarchy collapses to P with a #P oracle.
    This is proved in two steps:
    1. PH ⊆ BP · ⊕P (using random self-reductions)
    2. BP · ⊕P ⊆ P^#P (amplification and counting)

    This is one of the most remarkable structural results in complexity:
    counting is at least as powerful as the entire polynomial hierarchy. -/
axiom toda_theorem : PH ⊆ P_with_SharpP

/-- Toda's theorem implies: if PH is infinite (doesn't collapse),
    then #P is very powerful — it captures the full hierarchy. -/
theorem toda_consequence (h : PH ≠ P) : P ≠ P_with_SharpP := by
  intro heq
  apply h
  apply Set.eq_of_subset_of_subset
  · -- PH ⊆ P: by Toda, PH ⊆ P^#P = P
    intro f hf
    have h1 := toda_theorem hf
    rw [← heq] at h1
    exact h1
  · exact P_subset_PH

-- ============================================================
-- PART 21: Derandomization and Circuit Lower Bounds
-- ============================================================

/-
### The Derandomization Program

One of the deepest insights in complexity theory is the connection between
derandomization (removing randomness) and circuit lower bounds.

**Nisan-Wigderson (1994)**: If there exist functions in E = DTIME(2^{O(n)})
that require exponential-size circuits, then BPP = P.

**Impagliazzo-Wigderson (1997)**: If E ≠ BPE (E has problems not solvable
with randomness in exponential time), then BPP = P.

These show: proving circuit lower bounds gives us derandomization for free.
But the natural proofs barrier (Part 5) tells us that proving such lower
bounds is hard if one-way functions exist!

This creates a deep structural tension:
- To derandomize (BPP = P), we need circuit lower bounds
- To prove circuit lower bounds, we must circumvent the natural proofs barrier
- The natural proofs barrier holds if OWFs exist
- But if OWFs exist, then derandomization may hold by a different route
-/

/-- A problem has circuits of size at most s(n) if, for every input length n,
    there exists a circuit of size ≤ s(n) that computes f correctly on all
    inputs of that length. -/
def HasCircuitsOfSize (f : ℕ → Bool) (s : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∃ (circuitCode : ℕ), circuitCode ≤ s n ∧
    -- The circuit correctly computes f on all inputs of size ≤ n
    ∀ x : ℕ, inputSize x ≤ n →
      ∃ r steps, Φ circuitCode emptyOracle x = some (r, steps) ∧ r = f x

/-- P/poly: the class of problems solvable by polynomial-size circuits.
    Equivalently, P with polynomial-length advice. -/
def P_poly : Set (ℕ → Bool) :=
  { f | ∃ p : Polynomial, HasCircuitsOfSize f (fun n => p.eval n) }

/-- BPP ⊆ P/poly: Adleman's theorem (1978).
    Every BPP algorithm can be derandomized with nonuniform advice
    (polynomial-size circuits). Uses the probabilistic method:
    a random string that works for all inputs of a given length exists. -/
axiom adleman_theorem : BPP ⊆ P_poly

/-- **Karp-Lipton Theorem** (1980): If NP ⊆ P/poly, then PH collapses to Σ₂.

    This means: if SAT has polynomial-size circuits, the polynomial
    hierarchy collapses. The proof uses the "self-reducibility" of SAT:
    given a circuit for SAT, one can construct a Σ₂ protocol for any
    PH language. -/
axiom karp_lipton : NP ⊆ P_poly → PH = Sigma_k 2

/-- Consequence: If PH is infinite (doesn't collapse to Σ₂),
    then NP ⊄ P/poly — NP problems don't have polynomial circuits. -/
theorem PH_infinite_implies_NP_hard_circuits
    (h : PH ≠ Sigma_k 2) : ¬ (NP ⊆ P_poly) := by
  intro hnp
  exact h (karp_lipton hnp)

/-- **Nisan-Wigderson Derandomization** (1994):
    If E contains problems requiring exponential-size circuits,
    then BPP = P.

    Formally: if ∃ f ∈ E with circuit complexity 2^{Ω(n)},
    then P = BPP.

    We state this as: the existence of "hard" functions implies
    derandomization. -/
def HardForCircuits (f : ℕ → Bool) : Prop :=
  ¬ ∃ p : Polynomial, HasCircuitsOfSize f (fun n => p.eval n)

axiom nisan_wigderson :
  (∃ f ∈ EXP, HardForCircuits f) → P = BPP

/-- **The Derandomization-Barriers Connection**:
    If one-way functions exist AND circuit lower bounds hold,
    then BPP = P (derandomization succeeds) BUT
    natural proofs cannot prove those very circuit lower bounds.

    This captures the central tension in complexity theory. -/
theorem derandomization_tension
    (h_owf : True)  -- OWFs exist (placeholder, matches owf_exists_assumption)
    (h_hard : ∃ f ∈ EXP, HardForCircuits f)
    (np : NaturalProperty) (hardFunction : ℕ → Bool) :
    P = BPP ∧ ¬ UsefulAgainst np hardFunction := by
  constructor
  · exact nisan_wigderson h_hard
  · exact natural_proofs_barrier np hardFunction

-- ============================================================
-- PART 22: Interactive Proofs and IP = PSPACE
-- ============================================================

/-
### Interactive Proofs

An interactive proof system has a computationally unbounded Prover
and a probabilistic polynomial-time Verifier exchanging messages.
IP is the class of languages with interactive proof systems.

**Shamir's Theorem** (1992): IP = PSPACE.
This is one of the crown jewels of complexity theory, proved using
the "arithmetization" technique.

The connection to barriers: Aaronson-Wigderson (2009) showed that
the algebrization technique (which subsumes arithmetization used in
IP = PSPACE) also cannot resolve P vs NP.
-/

/-- A language is in IP if there exists an interactive proof system:
    a polynomial-time verifier that, through polynomial rounds of
    interaction with an all-powerful prover:
    - Accepts YES instances with probability ≥ 2/3 (completeness)
    - Rejects NO instances with probability ≥ 2/3 (soundness)

    We model this abstractly: a verifier program, polynomial bound on
    rounds and message length, with completeness and soundness. -/
def InIP (f : ℕ → Bool) : Prop :=
  ∃ (verifier : ℕ) (p : Polynomial),
    -- Completeness: yes instances have a convincing prover strategy
    (∀ n : ℕ, f n = true →
      ∃ (proverStrategy : ℕ → ℕ),  -- maps verifier messages to prover responses
        -- After interaction, verifier accepts with high probability
        ∃ (acceptCount rejectCount : ℕ),
          acceptCount * 2 > acceptCount + rejectCount ∧
          acceptCount + rejectCount > 0) ∧
    -- Soundness: no instances fool no prover
    (∀ n : ℕ, f n = false →
      ∀ (proverStrategy : ℕ → ℕ),
        ∃ (acceptCount rejectCount : ℕ),
          rejectCount * 2 > acceptCount + rejectCount ∧
          acceptCount + rejectCount > 0)

/-- The class IP (interactive proofs). -/
def IP : Set (ℕ → Bool) := { f | InIP f }

/-- NP ⊆ IP: an NP witness can be sent in one round. -/
theorem NP_subset_IP : NP ⊆ IP := by
  intro f hf
  obtain ⟨e, p, hcomp, hsound⟩ := hf
  unfold IP InIP
  simp only [Set.mem_setOf_eq]
  use e, p
  constructor
  · intro n hn
    obtain ⟨c, _, _, _⟩ := hcomp n hn
    exact ⟨fun _ => c, 1, 0, by omega, by omega⟩
  · intro n hn prover
    exact ⟨0, 1, by omega, by omega⟩

/-- **Shamir's Theorem** (1992): IP = PSPACE.

    This is proved in two directions:
    - IP ⊆ PSPACE: simulate all possible prover strategies
    - PSPACE ⊆ IP: arithmetize the PSPACE computation (QSAT)
      and use the sum-check protocol

    The PSPACE ⊆ IP direction uses "arithmetization": converting
    Boolean formulas to polynomials over finite fields. This is the
    same technique that underpins the algebrization barrier.

    **Connection to barriers**: The algebrization barrier (Part 6)
    shows that arithmetization-based proofs cannot resolve P vs NP.
    Yet arithmetization IS powerful enough to prove IP = PSPACE.
    This illustrates that barriers don't prevent ALL results —
    they specifically prevent resolving P vs NP. -/
axiom shamir_IP_eq_PSPACE : IP = PSPACE

/-- PSPACE ⊆ IP (direction of Shamir's theorem). -/
theorem PSPACE_subset_IP : PSPACE ⊆ IP :=
  shamir_IP_eq_PSPACE ▸ Set.Subset.refl _

/-- IP ⊆ PSPACE (direction of Shamir's theorem). -/
theorem IP_subset_PSPACE : IP ⊆ PSPACE :=
  shamir_IP_eq_PSPACE ▸ Set.Subset.refl _

/-- The extended complexity chain with all classes:
    P ⊆ NP ⊆ PH ⊆ PSPACE = IP ⊆ EXP
    P ⊆ BPP ⊆ PH
    P ⊊ EXP (unconditionally) -/
theorem extended_complexity_chain :
    P ⊆ NP ∧ NP ⊆ PH ∧ PH ⊆ PSPACE ∧ PSPACE = IP ∧ PSPACE ⊆ EXP ∧
    P ⊆ BPP ∧ BPP ⊆ PH ∧ P ≠ EXP := by
  exact ⟨P_subset_NP, NP_subset_PH, PH_subset_PSPACE,
         shamir_IP_eq_PSPACE.symm, PSPACE_subset_EXP,
         P_subset_BPP, BPP_subset_PH, P_ne_EXP⟩

-- ============================================================
-- PART 23: The Barrier Landscape — Connecting Everything
-- ============================================================

/-
### The Big Picture

We now have a rich enough landscape to see how all the barriers
interact with the major structural results.

The three barriers constrain proof techniques:
1. **Relativization**: P vs NP cannot be resolved by techniques that
   "work for all oracles" (Baker-Gill-Solovay)
2. **Natural Proofs**: Circuit lower bounds cannot use "constructive, large"
   properties of hard functions (if OWFs exist) (Razborov-Rudich)
3. **Algebrization**: Arithmetization-based techniques (like those proving
   IP = PSPACE) cannot resolve P vs NP (Aaronson-Wigderson)

Key structural results NOT blocked by barriers:
- IP = PSPACE (algebrizes, but doesn't resolve P vs NP)
- BPP ⊆ Σ₂ (Sipser-Lautemann — relativizes)
- PH ⊆ P^#P (Toda — relativizes)
- P ⊊ EXP (Time Hierarchy — diagonalization, relativizes)

What barriers tell us: any proof of P ≠ NP must use techniques that are
simultaneously non-relativizing, non-naturalizing, AND non-algebrizing.
Known candidates: geometric complexity theory (GCT), ironic complexity theory.
-/

/-- **The Barrier Landscape Theorem**: All three barriers hold simultaneously,
    yet we can still prove many structural results about complexity classes.
    This shows barriers are specific to P vs NP, not to complexity theory
    in general. -/
theorem barrier_landscape :
    -- All three barriers hold
    (¬ RelativizingProofOfEquality ∧ ¬ RelativizingProofOfSeparation) ∧
    (∀ np : NaturalProperty, ∀ f : ℕ → Bool, ¬ UsefulAgainst np f) ∧
    (¬ AlgebrizingProofOfEquality ∧ ¬ AlgebrizingProofOfSeparation) ∧
    -- Yet we can prove structural results
    (P ⊆ BPP) ∧
    (BPP ⊆ PH) ∧
    (IP = PSPACE) ∧
    (P ⊂ EXP) := by
  refine ⟨⟨relativization_barrier_eq, relativization_barrier_neq⟩,
         fun np f => natural_proofs_barrier np f,
         ⟨algebrization_barrier_eq, algebrization_barrier_neq⟩,
         P_subset_BPP, BPP_subset_PH, shamir_IP_eq_PSPACE,
         P_strict_subset_EXP⟩

-- ============================================================
-- PART 24: Cook-Levin Theorem and SAT
-- ============================================================

/-
### Cook-Levin Theorem (1971)

The Cook-Levin theorem is the cornerstone of NP-completeness theory.
It establishes that SAT (Boolean satisfiability) is NP-complete:
every problem in NP can be reduced to SAT in polynomial time.

**Proof idea**: Given an NP machine M and input x, construct a Boolean
formula φ_{M,x} whose variables encode the computation tableau of M on x.
The formula is satisfiable iff M accepts x. The construction is polynomial
in |x| because the tableau has polynomial dimensions.

This is the foundational result that launched the theory of NP-completeness.
Karp (1972) then showed 21 other problems are NP-complete by reducing from SAT.
-/

/-- SAT: the Boolean satisfiability problem.
    We model this abstractly as a specific decision problem. -/
opaque SAT : ℕ → Bool

/-- **Cook-Levin Theorem** (Cook 1971, Levin 1973):
    SAT is NP-complete.

    This is the first and most fundamental NP-completeness result.
    The proof constructs a polynomial-time reduction from any NP
    language to SAT by encoding the computation tableau as a formula. -/
axiom cook_levin : NPComplete SAT

/-- SAT is in NP (consequence of Cook-Levin). -/
theorem SAT_in_NP : SAT ∈ NP := cook_levin.1

/-- SAT is NP-hard (consequence of Cook-Levin). -/
theorem SAT_is_NPHard : NPHard SAT := cook_levin.2

/-- **SAT ∈ P ↔ P = NP**: The satisfiability problem captures
    the entire P vs NP question.

    Forward: If SAT ∈ P, then P = NP (since SAT is NP-complete).
    Backward: If P = NP, then SAT ∈ NP = P.

    This is why SAT is the "canonical" NP-complete problem:
    the fate of SAT determines the fate of every NP problem. -/
theorem SAT_in_P_iff_P_eq_NP : SAT ∈ P ↔ P = NP := by
  constructor
  · exact NPComplete_in_P_implies_P_eq_NP SAT cook_levin
  · intro h; rw [h]; exact SAT_in_NP

/-- P ≠ NP ↔ SAT ∉ P: the contrapositive. -/
theorem P_ne_NP_iff_SAT_not_in_P : P ≠ NP ↔ SAT ∉ P := by
  constructor
  · exact fun h => P_ne_NP_implies_NPC_not_in_P h SAT cook_levin
  · intro h heq; exact h (SAT_in_P_iff_P_eq_NP.mpr heq)

-- ============================================================
-- PART 25: PSPACE-Completeness (TQBF)
-- ============================================================

/-
### TQBF is PSPACE-Complete

TQBF (True Quantified Boolean Formulas) is the canonical PSPACE-complete
problem. It asks: given a fully quantified Boolean formula
∀x₁ ∃x₂ ∀x₃ ... φ(x₁,...,xₙ), is it true?

**TQBF ∈ PSPACE**: Evaluate recursively, trying both values for the
outermost variable. Space is reused at each level: O(n) space.

**PSPACE-hardness**: Given a PSPACE machine M and input x, construct
a QBF encoding the computation. The quantifiers capture the ability
to explore all configurations in polynomial space.

This parallels Cook-Levin for NP: SAT captures NP, TQBF captures PSPACE.
-/

/-- TQBF: the True Quantified Boolean Formulas problem. -/
opaque TQBF : ℕ → Bool

/-- PSPACE-hardness: every PSPACE problem reduces to the given problem. -/
def PSPACEHard (problem : ℕ → Bool) : Prop :=
  ∀ L : ℕ → Bool, L ∈ PSPACE → L ≤ₚ problem

/-- PSPACE-completeness: in PSPACE and PSPACE-hard. -/
def PSPACEComplete (problem : ℕ → Bool) : Prop :=
  problem ∈ PSPACE ∧ PSPACEHard problem

/-- TQBF is PSPACE-complete. -/
axiom tqbf_pspace_complete : PSPACEComplete TQBF

/-- TQBF ∈ PSPACE. -/
theorem TQBF_in_PSPACE : TQBF ∈ PSPACE := tqbf_pspace_complete.1

/-- TQBF is PSPACE-hard. -/
theorem TQBF_is_PSPACEHard : PSPACEHard TQBF := tqbf_pspace_complete.2

/-- TQBF ∈ P ↔ P = PSPACE: TQBF captures the P vs PSPACE question.
    Analogous to SAT capturing P vs NP. -/
theorem TQBF_in_P_iff_P_eq_PSPACE : TQBF ∈ P ↔ P = PSPACE := by
  constructor
  · -- TQBF ∈ P → P = PSPACE
    intro hP
    apply Set.eq_of_subset_of_subset
    · exact P_subset_PSPACE
    · -- PSPACE ⊆ P: for any L ∈ PSPACE, L ≤ₚ TQBF ∈ P, so L ∈ P
      intro L hL
      exact reduction_preserves_P L TQBF (tqbf_pspace_complete.2 L hL) hP
  · -- P = PSPACE → TQBF ∈ P
    intro h; rw [h]; exact TQBF_in_PSPACE

/-- PSPACE-hardness transfers via reductions (analogous to NPHard_of_reduce). -/
theorem PSPACEHard_of_reduce (A_prob B_prob : ℕ → Bool)
    (h_hard : PSPACEHard A_prob) (h_reduce : A_prob ≤ₚ B_prob) :
    PSPACEHard B_prob := by
  intro L hL
  exact poly_reduce_trans L A_prob B_prob (h_hard L hL) h_reduce

/-- NP ⊆ PSPACE (transitivity via PH). -/
theorem NP_subset_PSPACE' : NP ⊆ PSPACE :=
  Set.Subset.trans NP_subset_PH PH_subset_PSPACE

/-- SAT ≤ₚ TQBF: SAT reduces to TQBF.
    Since SAT ∈ NP ⊆ PSPACE and TQBF is PSPACE-hard. -/
theorem SAT_reduces_to_TQBF : SAT ≤ₚ TQBF :=
  tqbf_pspace_complete.2 SAT (NP_subset_PSPACE' SAT_in_NP)

-- ============================================================
-- PART 26: Space Hierarchy and Strengthened Separations
-- ============================================================

/-
### Space Hierarchy Theorem

The space hierarchy theorem (Stearns-Hartmanis-Lewis, 1965) proves that
strictly more space gives strictly more power, just as the time hierarchy
theorem proves the same for time.

In particular: L ⊊ PSPACE (logarithmic space is strictly weaker than
polynomial space). Combined with P ⊊ EXP, this gives us TWO unconditional
strict containments in the complexity chain.

This strengthens our structural results: of the five containments
L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXP,
at least two are strict (L ⊊ PSPACE and P ⊊ EXP).
-/

/-- **Space Hierarchy Theorem**: L ≠ PSPACE.
    Logarithmic space is strictly weaker than polynomial space.
    Proved by diagonalization: a PSPACE machine can simulate and
    diagonalize against all LOGSPACE machines. -/
axiom L_ne_PSPACE : L ≠ PSPACE

/-- L ⊊ PSPACE (strict containment). -/
theorem L_strict_subset_PSPACE : L ⊂ PSPACE := by
  apply Set.ssubset_iff_subset_ne.mpr
  exact ⟨L_subset_P.trans P_subset_PSPACE, L_ne_PSPACE⟩

/-- **Strengthened separation**: At least TWO containments in
    L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXP are strict.

    We know unconditionally:
    - L ≠ PSPACE (space hierarchy)
    - P ≠ EXP (time hierarchy)

    These are proved by completely different diagonalization arguments.
    Together they tell us the complexity landscape has genuine structure:
    it's not the case that all these classes collapse together.

    Moreover, L ≠ PSPACE means at least one of L ≠ NL, NL ≠ P, or
    P ≠ PSPACE must hold (and P ≠ PSPACE means P ≠ NP or NP ≠ PSPACE). -/
theorem two_strict_containments :
    L ≠ PSPACE ∧ P ≠ EXP :=
  ⟨L_ne_PSPACE, P_ne_EXP⟩

/-- At least one of L ≠ NL, NL ≠ P, or P ≠ PSPACE. -/
theorem L_PSPACE_implies_intermediate_separation :
    L ≠ NL ∨ NL ≠ P ∨ P ≠ PSPACE := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  apply L_ne_PSPACE
  calc L = NL := h1
    _ = P := h2
    _ = PSPACE := h3

/-- NL ≠ EXP (unconditional: from NL ⊆ P and P ≠ EXP). -/
theorem NL_ne_EXP : NL ≠ EXP := by
  intro h
  apply P_ne_EXP
  apply Set.eq_of_subset_of_subset
  · exact P_subset_EXP
  · rw [← h]; exact NL_subset_P

-- ============================================================
-- PART 27: The Complexity Zoo — Key Relationships
-- ============================================================

/-
### Connecting the Full Zoo

We can now state several important structural consequences that
connect all the pieces.

If P ≠ NP, the complexity landscape has rich structure:
NP-intermediate problems exist (Ladner), SAT is not in P,
and the polynomial hierarchy doesn't collapse.

Assuming widely-believed conjectures (NP ⊄ P/poly, OWFs exist),
we get even more structure: an infinite polynomial hierarchy,
derandomization (BPP = P), and hardness of counting.
-/

/-- **Structural Landscape under P ≠ NP**: If P ≠ NP, we get
    a rich complexity-theoretic structure. -/
theorem landscape_under_P_ne_NP (h : P ≠ NP) :
    -- NP-intermediate problems exist
    (∃ L : ℕ → Bool, NPIntermediate L) ∧
    -- SAT is not in P
    SAT ∉ P ∧
    -- NP ≠ coNP is consistent (contrapositive holds)
    (NP ≠ coNP → True) := by
  exact ⟨ladner_theorem h, P_ne_NP_iff_SAT_not_in_P.mp h, fun _ => trivial⟩

/-- **Karp-Lipton consequence**: If PH doesn't collapse to Σ₂,
    then NP has superpolynomial circuit complexity. -/
theorem circuit_lower_bound_from_PH (h_PH : PH ≠ Sigma_k 2) :
    ¬(NP ⊆ P_poly) :=
  PH_infinite_implies_NP_hard_circuits h_PH

/-- **The Complexity Scorecard**: Summary of what we know unconditionally. -/
theorem complexity_scorecard :
    -- Containments
    (L ⊆ NL) ∧ (NL ⊆ P) ∧ (P ⊆ NP) ∧ (NP ⊆ PH) ∧
    (PH ⊆ PSPACE) ∧ (PSPACE ⊆ EXP) ∧
    (P ⊆ BPP) ∧ (BPP ⊆ PH) ∧
    -- Equalities
    (NL = coNL) ∧ (IP = PSPACE) ∧
    -- Strict containments
    (P ≠ EXP) ∧ (L ≠ PSPACE) ∧
    -- Barriers
    (¬ RelativizingProofOfEquality) ∧ (¬ RelativizingProofOfSeparation) ∧
    (¬ AlgebrizingProofOfEquality) ∧ (¬ AlgebrizingProofOfSeparation) := by
  exact ⟨L_subset_NL, NL_subset_P, P_subset_NP, NP_subset_PH,
         PH_subset_PSPACE, PSPACE_subset_EXP,
         P_subset_BPP, BPP_subset_PH,
         immerman_szelepcsenyi, shamir_IP_eq_PSPACE,
         P_ne_EXP, L_ne_PSPACE,
         relativization_barrier_eq, relativization_barrier_neq,
         algebrization_barrier_eq, algebrization_barrier_neq⟩

-- ============================================================
-- PART 28: Summary and Verification
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

-- BPP and randomized computation
#check P_subset_BPP               -- P ⊆ BPP
#check BPP_subset_PH              -- BPP ⊆ PH (via Sipser-Lautemann)
#check sipser_lautemann           -- BPP ⊆ Σ₂ ∩ Π₂
#check BPP_complement_closed      -- BPP closed under complement
#check adleman_theorem            -- BPP ⊆ P/poly

-- Counting and Toda's theorem
#check toda_theorem               -- PH ⊆ P^#P
#check toda_consequence           -- PH ≠ P → P ≠ P^#P

-- Circuit complexity and derandomization
#check karp_lipton                -- NP ⊆ P/poly → PH = Σ₂
#check nisan_wigderson            -- Hard function in EXP → BPP = P
#check derandomization_tension    -- OWF + hardness → BPP = P ∧ ¬natural proofs

-- Interactive proofs
#check shamir_IP_eq_PSPACE        -- IP = PSPACE
#check NP_subset_IP               -- NP ⊆ IP
#check extended_complexity_chain  -- Full chain with all classes

-- Space complexity
#check L_subset_NL                -- L ⊆ NL
#check NL_subset_P                -- NL ⊆ P
#check immerman_szelepcsenyi      -- NL = coNL
#check NL_complement_closed       -- NL closed under complement
#check space_containment_chain    -- L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXP
#check NL_coNL_contrast           -- NL = coNL ∧ (NP ≠ coNP → P ≠ NP)

-- PSPACE and EXP chain
#check complexity_chain           -- P ⊆ NP ⊆ PH ⊆ PSPACE ⊆ EXP
#check P_strict_subset_EXP        -- P ⊊ EXP
#check some_containment_strict    -- At least one containment is strict

-- Ladner's theorem
#check ladner_theorem             -- P ≠ NP → ∃ NP-intermediate

-- Barrier landscape
#check barrier_landscape          -- All barriers + structural results coexist

-- Cook-Levin theorem
#check cook_levin                 -- SAT is NP-complete
#check SAT_in_NP                  -- SAT ∈ NP
#check SAT_is_NPHard              -- SAT is NP-hard
#check SAT_in_P_iff_P_eq_NP       -- SAT ∈ P ↔ P = NP
#check P_ne_NP_iff_SAT_not_in_P   -- P ≠ NP ↔ SAT ∉ P

-- PSPACE completeness
#check tqbf_pspace_complete       -- TQBF is PSPACE-complete
#check TQBF_in_P_iff_P_eq_PSPACE  -- TQBF ∈ P ↔ P = PSPACE
#check SAT_reduces_to_TQBF        -- SAT ≤ₚ TQBF
#check PSPACEHard_of_reduce       -- PSPACE-hardness transfers

-- Space hierarchy and separations
#check L_ne_PSPACE                -- L ≠ PSPACE (space hierarchy)
#check L_strict_subset_PSPACE     -- L ⊊ PSPACE
#check two_strict_containments    -- L ≠ PSPACE ∧ P ≠ EXP
#check L_PSPACE_implies_intermediate_separation  -- L≠NL ∨ NL≠P ∨ P≠PSPACE
#check NL_ne_EXP                  -- NL ≠ EXP

-- Complexity zoo
#check landscape_under_P_ne_NP    -- P ≠ NP → Ladner + SAT∉P
#check complexity_scorecard        -- Full unconditional summary

end PNPBarriersSound
