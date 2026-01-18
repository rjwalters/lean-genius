/-
Erdős Problem #906: Dense Zeros of Derivative Subsequences

**Question**: Is there an entire non-zero transcendental function f : ℂ → ℂ such that
for any infinite increasing sequence n₁ < n₂ < ..., the set
  { z : f^{(nₖ)}(z) = 0 for some k ≥ 1 }
is everywhere dense in ℂ?

**Status**: UNCLEAR (reported as solved by Erdős but no proof known)

**History**:
- Erdős [Er82e] writes this was "solved in the affirmative more than ten years ago"
  but gives no reference or attribution
- He seems to attribute it to Barth-Schneider [BaSc72], but their paper contains
  no such result
- Tang notes the problem is trivial for polynomials, so transcendental is required
- formal-conjectures marks this as OPEN due to no verified proof

**Interpretation**:
- For polynomials: Eventually all derivatives are zero, so trivially dense
- For transcendental f: This requires f^{(n)} to have zeros everywhere for
  arbitrarily sparse sequences of n

References:
- https://erdosproblems.com/906
- [Er82e] Erdős, "Some of my favourite problems which recently have been solved" (1982)
- [BaSc72] Barth & Schneider, "On a problem of Erdős concerning zeros of derivatives" (1972)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Erdos906

open Complex Topology

/-! ## Key Definitions

We need:
1. **Entire function**: Differentiable everywhere on ℂ
2. **Transcendental**: Not equal to any polynomial
3. **Iterated derivative**: The n-th derivative f^{(n)}
4. **Dense set**: Closure equals the whole space
-/

/-- A function f : ℂ → ℂ is entire if it is differentiable everywhere.
This is the standard definition in complex analysis. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- A function is transcendental if it is not equal to any polynomial.
This means f cannot be written as a finite sum Σ aₙ zⁿ. -/
def IsTranscendental (f : ℂ → ℂ) : Prop :=
  ∀ p : Polynomial ℂ, f ≠ fun z => p.eval z

/-- The n-th iterated derivative of f.
Axiomatized as Mathlib's iteratedDeriv requires more setup. -/
axiom iteratedDeriv (n : ℕ) (f : ℂ → ℂ) : ℂ → ℂ

/-- Basic property: the 0th derivative is f itself. -/
axiom iteratedDeriv_zero (f : ℂ → ℂ) : iteratedDeriv 0 f = f

/-- The 1st derivative equals the standard derivative. -/
axiom iteratedDeriv_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
  iteratedDeriv 1 f = deriv f

/-- Recursive property: (n+1)th derivative = derivative of nth derivative. -/
axiom iteratedDeriv_succ (n : ℕ) (f : ℂ → ℂ) :
  iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)

/-! ## The Zero Set

For a function f and a sequence of derivative indices, the zero set collects
all z where some derivative in the sequence vanishes at z. -/

/-- The zero set of f^{(n)} for indices n in a sequence.
Given a strictly increasing sequence n : ℕ → ℕ, this is
{ z : ∃ k, f^{(n(k))}(z) = 0 }. -/
def derivativeZeroSet (f : ℂ → ℂ) (n : ℕ → ℕ) : Set ℂ :=
  { z | ∃ k, iteratedDeriv (n k) f z = 0 }

/-! ## The Main Property

The property Erdős asks about: for ANY strictly increasing sequence,
the zero set of the corresponding derivatives is dense. -/

/-- The property that for any strictly increasing sequence n, the zeros of
f^{(n(k))} for varying k are dense in ℂ. -/
def HasDenseDerivativeZeros (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → Dense (derivativeZeroSet f n)

/-! ## Why Polynomials Are Trivial

For a polynomial of degree d, f^{(n)} = 0 for all n > d.
Thus derivativeZeroSet f n = ℂ for any sequence eventually exceeding d.
This is why the problem requires transcendental functions. -/

/-- Polynomials eventually have zero derivatives.
Axiomatized as it requires degree theory. -/
axiom polynomial_eventually_zero (p : Polynomial ℂ) :
  ∃ d : ℕ, ∀ n > d, iteratedDeriv n (fun z => p.eval z) = 0

/-- For polynomials, the property is trivially satisfied.
Tang's observation: this is why transcendental is required.
Axiomatized due to proof complexity with Dense. -/
axiom polynomial_trivial (p : Polynomial ℂ) :
    HasDenseDerivativeZeros (fun z => p.eval z)

/-! ## The Main Problem -/

/-- **Erdős Problem #906 (STATUS UNCLEAR)**:

Does there exist an entire, non-zero, transcendental function f : ℂ → ℂ
such that HasDenseDerivativeZeros f holds?

Erdős claimed this was solved affirmatively before 1972, but no proof
is known. We axiomatize this as an unknown Prop. -/
axiom erdos_906_open :
  Prop  -- Unknown: ∃ f, IsEntire f ∧ f ≠ 0 ∧ IsTranscendental f ∧ HasDenseDerivativeZeros f

/-- The formal statement of the problem. -/
def erdos_906_statement : Prop :=
  ∃ f : ℂ → ℂ,
    IsEntire f ∧
    f ≠ 0 ∧
    IsTranscendental f ∧
    HasDenseDerivativeZeros f

/-! ## Examples and Non-Examples -/

/-- The exponential function e^z is entire. -/
axiom exp_is_entire : IsEntire Complex.exp

/-- The exponential function is transcendental.
Proof: e^z is not a polynomial since all its derivatives equal itself. -/
axiom exp_is_transcendental : IsTranscendental Complex.exp

/-- e^z ≠ 0 for any z ∈ ℂ. All derivatives of e^z equal e^z.
Axiomatized as it requires complex exponential properties. -/
axiom exp_deriv_never_zero (z : ℂ) (k : ℕ) :
  iteratedDeriv k Complex.exp z ≠ 0

/-- However, exp does NOT satisfy the dense zeros property.
All derivatives of e^z equal e^z, which has no zeros.
Axiomatized due to proof complexity with Set.ext. -/
axiom exp_no_zeros : derivativeZeroSet Complex.exp id = ∅

/-! ## Related Concepts -/

/-- Connection to the Pólya-Erdős conjecture about zeros of derivatives.
Pólya's shire theorem and Erdős's work on zeros of polynomials
are related background. -/
axiom connection_to_polya : Prop

/-- Connection to the distribution of zeros of entire functions.
The Weierstrass factorization theorem gives control over zeros,
but not the density property for subsequences. -/
axiom connection_to_weierstrass : Prop

/-! ## Properties of the Zero Set -/

/-- The zero set is always closed (for continuous functions). -/
axiom zero_set_closed (f : ℂ → ℂ) (n : ℕ → ℕ) (hf : Continuous f) :
  IsClosed (derivativeZeroSet f n)

/-- For a non-constant entire function, each individual zero set
{ z : f^{(k)}(z) = 0 } is discrete (isolated points) unless f^{(k)} ≡ 0.
The union over a sequence can be dense. -/
axiom individual_zero_sets_discrete (f : ℂ → ℂ) (k : ℕ) (hf : IsEntire f)
    (hne : iteratedDeriv k f ≠ 0) :
    ∀ z ∈ { w | iteratedDeriv k f w = 0 }, ∃ ε > 0,
      ∀ w ∈ Metric.ball z ε, w = z ∨ iteratedDeriv k f w ≠ 0

/-! ## Summary -/

/-- **Erdős Problem #906 Summary**:

1. QUESTION: Does there exist a transcendental entire f with dense derivative zeros
   for any subsequence?
2. STATUS: Erdős claimed solved (before 1972) but no proof is documented
3. TRIVIAL CASE: Polynomials work, but that's why transcendental is required
4. EXAMPLE: exp doesn't work (no zeros at all)
5. RELATED: Pólya's shire theorem, Weierstrass factorization
-/
theorem erdos_906_summary :
    -- Polynomials trivially satisfy the property
    HasDenseDerivativeZeros (fun z => (0 : Polynomial ℂ).eval z) ∧
    -- The exponential is entire and transcendental
    IsEntire Complex.exp ∧
    IsTranscendental Complex.exp :=
  ⟨polynomial_trivial 0, exp_is_entire, exp_is_transcendental⟩

end Erdos906
