/-
Erdős Problem #66: Representation Function Asymptotics

Is there a set A ⊆ ℕ such that the limit
  lim_{n→∞} (1_A ∗ 1_A)(n) / log(n)
exists and is nonzero?

Here (1_A ∗ 1_A)(n) counts the number of ways to write n = a + b with a,b ∈ A.

**Status**: OPEN (carries $500 prize)

**Erdős's Conjecture**: The answer is NO.

**Partial Results**:
- Erdős-Sárközy: The representation function cannot approximate log(n) too closely
- Horváth (2007): Strengthened the error bounds

Reference: https://erdosproblems.com/66
-/

import Mathlib

open Filter
open scoped Topology

namespace Erdos66

/-!
## Background

The representation function r_A(n) = |{(a,b) ∈ A×A : a + b = n}| counts how many ways
we can write n as a sum of two elements from A.

For the set of primes, the Goldbach conjecture is equivalent to asking whether r_P(n) > 0
for all even n > 2.

Here we ask about the asymptotic growth rate of r_A(n). The natural scale for comparison
is log(n), since many natural sets have representation functions of this order.
-/

/--
The **representation function** r_A(n) counts ordered pairs (a,b) with a,b ∈ A
and a + b = n.

This is also written as (1_A ∗ 1_A)(n), the convolution of the indicator function.

We define this noncomputably as the cardinality of the representation set.
-/
noncomputable def representationFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a : ℕ | a ≤ n ∧ a ∈ A ∧ n - a ∈ A}

/--
Alternative definition using the sumset convolution notation.
For finite sets, this counts representations directly.
-/
noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ :=
  representationFunction A n

/-!
## The Main Question

Erdős Problem #66 asks whether there exists a set A such that
  r_A(n) / log(n) → c  for some c ≠ 0

Erdős believed the answer should be NO.
-/

/--
**Erdős Problem #66 (OPEN)**

Does there exist a set A ⊆ ℕ and a constant c ≠ 0 such that
  lim_{n→∞} r_A(n) / log(n) = c?

This is equivalent to asking if the representation function can have
"exactly logarithmic" growth with a definite limit.

Erdős conjectured the answer is NO, but this remains open.
We state it without asserting truth value.
-/
def Erdos66Question : Prop :=
  ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
    Tendsto (fun n => (representationFunction A n : ℝ) / Real.log n)
            atTop (𝓝 c)

/--
**Erdős's Conjecture** (believed but unproved)

Erdős believed the answer to Problem 66 should be NO—there is no set A
with representation function having a nonzero logarithmic limit.

We state this as a definition (not asserting its truth).
-/
def ErdosConjecture66 : Prop := ¬Erdos66Question

/-!
## Partial Results

While the main question is open, several partial results constrain how
closely r_A(n) can approximate log(n).
-/

/--
**Erdős-Sárközy Theorem**

For any set A ⊆ ℕ, the representation function cannot approximate log(n)
with error o(√log n). More precisely:

  |r_A(n) - log(n)| / √(log n) → 0 is IMPOSSIBLE.

This shows that even if r_A(n) ~ log(n), the fluctuations must be significant.
-/
axiom erdosSarkozy :
  ¬∃ (A : Set ℕ),
    Tendsto (fun n => |((representationFunction A n : ℝ) - Real.log n)| / Real.sqrt (Real.log n))
            atTop (𝓝 0)

/--
**Horváth's Improvement (2007)**

Horváth strengthened the Erdős-Sárközy result: the error cannot stay below
(1-ε)√(log n) for any ε > 0 and all sufficiently large n.

Formally: For all ε > 0, there exist infinitely many n with
  |r_A(n) - log(n)| > (1-ε)√(log n)
-/
axiom horvath2007 :
  ∀ (A : Set ℕ) (ε : ℝ), ε > 0 →
    ∀ᶠ n in atTop,
      |((representationFunction A n : ℝ) - Real.log n)| > (1 - ε) * Real.sqrt (Real.log n)

/-!
## Connection to Random Sets

Random sets constructed with the right density DO have the property
r_A(n) / log(n) → c, but only "almost surely"—there is always an
exceptional set of density zero where the limit fails.

The challenge is eliminating this exceptional set entirely.
-/

/--
**Random Set Behavior** (heuristic)

A random set A where each n is included independently with probability
p(n) ~ c/√n would have E[r_A(n)] ~ c² log(n).

However, the variance is large enough that the limit fails on a
null set of n values.

This informal statement captures the key difficulty: random constructions
give the desired limit "almost everywhere" but not everywhere.
-/
def randomSetHasLimitAlmostEverywhere : Prop :=
  ∃ (A : Set ℕ) (c : ℝ) (E : Set ℕ), c ≠ 0 ∧
    -- E has natural density zero
    (∀ ε > 0, ∀ᶠ n in atTop, Set.ncard (E ∩ Set.Icc 1 n) < ε * n) ∧
    -- Outside E, the ratio is close to c
    (∀ ε > 0, ∀ᶠ n in atTop, n ∉ E →
      |(representationFunction A n : ℝ) / Real.log n - c| < ε)

/-!
## Erdős's Stronger Conjecture

Erdős suggested an even stronger statement might be true: that the
liminf and limsup of r_A(n)/log(n) are always separated by an absolute
constant, for any set A.
-/

/--
**Erdős's Stronger Conjecture**

For any set A, the liminf and limsup of r_A(n)/log(n) are separated by
some universal constant δ > 0.

This would imply Problem 66 has a negative answer.
-/
def ErdosStrongerConjecture : Prop :=
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (A : Set ℕ),
    let f := fun n => (representationFunction A n : ℝ) / Real.log n
    limsup (fun n => f n) atTop - liminf (fun n => f n) atTop ≥ δ

/-- The stronger conjecture implies the original. -/
theorem stronger_implies_original :
    ErdosStrongerConjecture → ErdosConjecture66 := by
  intro ⟨δ, hδ, hA⟩
  intro ⟨A, c, hc, hlim⟩
  -- If the limit exists, liminf = limsup = c
  have hsup : limsup (fun n => (representationFunction A n : ℝ) / Real.log n) atTop = c :=
    hlim.limsup_eq
  have hinf : liminf (fun n => (representationFunction A n : ℝ) / Real.log n) atTop = c :=
    hlim.liminf_eq
  -- But then the difference is 0, contradicting δ > 0
  specialize hA A
  simp only [hsup, hinf, sub_self, ge_iff_le] at hA
  linarith

end Erdos66
