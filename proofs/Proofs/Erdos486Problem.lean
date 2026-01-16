/-
Erdős Problem #486: Logarithmic Density for Modular Avoidance Sets

For each n ∈ ℕ, choose some Xₙ ⊆ ℤ/nℤ. Let
  B = {m ∈ ℕ : m ∉ Xₙ (mod n) for all n with m > n}
Must B have a logarithmic density?

**Status**: OPEN

**Partial Results**:
- Davenport-Erdős (1936): YES when Xₙ = {0} for all n
- Besicovitch (1934): Natural density may not exist even in the {0} case

**Generalizes**: Problem #25 (the case |Xₙ| = 1 for all n)

Reference: https://erdosproblems.com/486
-/

import Mathlib

namespace Erdos486

open scoped Classical

/-!
## Logarithmic Density

The logarithmic density of a set A ⊆ ℕ is defined as:
  δ_log(A) = lim_{x→∞} (1/log x) · Σ_{n ∈ A, n ≤ x} 1/n

This is a weaker notion than natural density. Some sets have logarithmic
density but not natural density (Besicovitch 1934).
-/

/-- The logarithmic sum of a set A up to bound x:
    Σ_{n ∈ A, 1 ≤ n ≤ x} 1/n -/
noncomputable def logSum (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.filter (fun n => n ∈ A ∧ 0 < n) (Finset.range (x + 1)), (1 : ℝ) / n

/-- A set A ⊆ ℕ has logarithmic density d if:
    lim_{x→∞} (1/log x) · Σ_{n ∈ A, n ≤ x} 1/n = d -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun x => logSum A x / Real.log x) Filter.atTop (nhds d)

/-!
## The Modular Avoidance Set

Given a family of "forbidden" residue classes Xₙ ⊆ ℤ/nℤ for each n,
the avoidance set B consists of all m that avoid every forbidden class.
-/

/-- The modular avoidance set: all m ∈ ℕ that avoid every forbidden residue class.
    B = {m ∈ ℕ : ∀ n, (m : ℤ/nℤ) ∉ Xₙ} -/
def avoidanceSet (X : (n : ℕ) → Set (ZMod n)) : Set ℕ :=
  {m : ℕ | ∀ n : ℕ, (m : ZMod n) ∉ X n}

/-!
## Erdős Conjecture #486

The conjecture asks: for ANY choice of forbidden sets Xₙ, must the
resulting avoidance set B have a logarithmic density?

This generalizes the Davenport-Erdős theorem (1936) which proved the
case Xₙ = {0} for all n (i.e., avoiding multiples of all n ∈ A).
-/

/-- **Erdős Problem #486** (OPEN)

For any choice of forbidden residue classes Xₙ ⊆ ℤ/nℤ, the modular
avoidance set B = {m : ∀n, m ∉ Xₙ (mod n)} has a logarithmic density.

This is a significant generalization of the Davenport-Erdős theorem. -/
axiom erdos486_conjecture :
    ∀ X : (n : ℕ) → Set (ZMod n),
    ∃ d : ℝ, HasLogDensity (avoidanceSet X) d

/-!
## Special Case: Davenport-Erdős Theorem (1936)

When Xₙ = {0} for all n in some set A, the avoidance set consists of
numbers not divisible by any element of A. Davenport and Erdős proved
this set always has logarithmic density.
-/

/-- The zero-avoidance set for A: numbers not divisible by any n ∈ A -/
def zeroAvoidanceSet (A : Set ℕ) : Set ℕ :=
  {m : ℕ | ∀ n ∈ A, ¬(n ∣ m) ∨ n = 0}

/-- **Davenport-Erdős Theorem** (1936)

For any A ⊆ ℕ, the set of numbers not divisible by any element of A
has a logarithmic density. This is the Xₙ = {0} case of Problem #486.

Note: This is a known theorem, stated as an axiom pending Mathlib formalization. -/
axiom davenport_erdos_theorem :
    ∀ A : Set ℕ, ∃ d : ℝ, HasLogDensity (zeroAvoidanceSet A) d

/-!
## Related Results

Besicovitch (1934) showed that natural density may fail to exist for
zero-avoidance sets, which is why logarithmic density is the right notion.
-/

/-- Natural density of a set A ⊆ ℕ -/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun n => (Finset.filter (· ∈ A) (Finset.range (n + 1))).card / ((n : ℝ) + 1))
    Filter.atTop (nhds d)

/-- **Besicovitch Counterexample** (1934)

There exists A ⊆ ℕ such that the zero-avoidance set has logarithmic density
but NOT natural density. This justifies studying logarithmic density. -/
axiom besicovitch_counterexample :
    ∃ A : Set ℕ, (∃ d : ℝ, HasLogDensity (zeroAvoidanceSet A) d) ∧
                 (¬ ∃ d : ℝ, HasNaturalDensity (zeroAvoidanceSet A) d)

end Erdos486
