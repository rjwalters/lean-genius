/-
  Erdős Problem #1205: Maximum Multi-Covering by Congruence Classes

  Let F(x) be maximal such that there exist congruence classes a_n (mod n)
  (one for each n ≤ x) such that every m ≤ x satisfies at least F(x) of
  the congruences m ≡ a_n (mod n).

  **Answer**: F(x) = Θ(log x).

  The key tool is the harmonic sum: ∑_{n ≤ x} 1/n ≈ ln(x).
  - Upper bound: F(x) ≤ ∑_{n ≤ x} 1/n ≈ ln(x), since the average coverage is ln(x)
  - Lower bound: Random assignment achieves F(x) ≥ Ω(ln(x)) with positive probability

  Status: Solved (probabilistic method). Lean formalization axiomatized.
  Reference: https://erdosproblems.com/1205
-/

import Mathlib

/-! ## Coverage Functions

A **covering assignment** chooses a residue class a_n ∈ {0,...,n-1} for each n.
The **coverage count** C_a(m) of an integer m counts how many n ≤ x have m ≡ a_n (mod n).
The function F(x) is the maximum, over all assignments, of the minimum coverage over m ≤ x.
-/

/-- A covering assignment maps each modulus n to a residue class a_n ∈ Fin n. -/
def CoveringAssignment (x : ℕ) : Type :=
  (n : Fin x) → Fin n.val.succ

/-- The coverage count of m under assignment a at scale x:
    the number of n ≤ x such that m ≡ a(n) (mod n). -/
def coverageCount (x m : ℕ) (a : (n : Fin x) → Fin n.val.succ) : ℕ :=
  (Finset.univ.filter (fun n : Fin x => m % n.val.succ = a n)).card

/-! ## The Function F(x)

F(x) is the maximum guaranteed multi-coverage: the largest k such that
there exists an assignment where every m ≤ x is covered at least k times.
-/

/-- The harmonic sum H(x) = ∑_{n=1}^{x} 1/n ≈ ln(x).
    This is the theoretical maximum coverage per integer. -/
noncomputable def harmonicSum (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range x, (1 : ℝ) / (n + 1)

/-! ## Known Bounds (Axiomatized)

The exact asymptotics F(x) = Θ(log x) require the probabilistic method
(specifically: concentration inequalities for sums of independent Bernoulli
random variables, applied with a union bound over m ≤ x). These are not
yet formalized in Lean's Mathlib.
-/

/-- **Upper bound**: F(x) ≤ C · ln(x) for all x ≥ 2.
    Proof: by averaging — the total coverage ∑_m C_a(m) = ∑_n ⌊x/n⌋ ≈ x·ln(x),
    so the average coverage per m ≈ ln(x); the minimum cannot exceed the average. -/
axiom fx_upper_bound : ∃ C : ℝ, C > 0 ∧
  ∀ x : ℕ, 2 ≤ x →
  ∀ a : (n : Fin x) → Fin n.val.succ,
  ∃ m : Fin x, (coverageCount x m.val a : ℝ) ≤ C * Real.log x

/-- **Lower bound**: F(x) ≥ c · ln(x) for all x ≥ 2.
    Proof: random assignment — choosing each a_n uniformly gives E[C(m)] = H(x) ≈ ln(x),
    and concentration (Chernoff bound / Lovász Local Lemma) ensures a good assignment exists. -/
axiom fx_lower_bound : ∃ c : ℝ, c > 0 ∧
  ∀ x : ℕ, 2 ≤ x →
  ∃ a : (n : Fin x) → Fin n.val.succ,
  ∀ m : Fin x, c * Real.log x ≤ coverageCount x m.val a

/-- **Erdős Problem #1205** (main result):
    F(x) = Θ(log x) — the maximum guaranteed multi-coverage grows logarithmically.

    The lower bound is given by `fx_lower_bound` and the upper bound by `fx_upper_bound`.
    Together they characterize F(x) up to a constant factor. -/
theorem erdos_1205 :
    (∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, 2 ≤ x →
      ∃ a : (n : Fin x) → Fin n.val.succ,
      ∀ m : Fin x, c * Real.log x ≤ coverageCount x m.val a) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, 2 ≤ x →
      ∀ a : (n : Fin x) → Fin n.val.succ,
      ∃ m : Fin x, (coverageCount x m.val a : ℝ) ≤ C * Real.log x) :=
  ⟨fx_lower_bound, fx_upper_bound⟩

#check erdos_1205
#check harmonicSum
#check coverageCount
