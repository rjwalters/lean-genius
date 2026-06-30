/-
  Erdős Problem #1047 — Main Results (axiom-free)

  These four headline theorems were relocated here from `Erdos1047Problem.lean` so
  that they can consume the machine-checked geometric certificate
  `Erdos1047OQ02Cert.goodman_counterexample_proof` (0 sorry / 0 axiom) instead of the
  former `goodman_counterexample` *axiom*.

  The parent file `Erdos1047Problem.lean` cannot itself import the certificate: the
  certificate (`Erdos1047OQ02Certificate.lean`) imports the reduction bridge
  (`Erdos1047OQ02Reduction.lean`), which imports the parent — so the dependency runs
  parent → reduction → certificate, and the four theorems that rest on the
  counterexample must live *downstream* of the certificate.  Reopening
  `namespace Erdos1047` keeps every public name unchanged
  (`Erdos1047.erdos_1047`, `Erdos1047.grunskyConjecture_false`, …).

  Net effect: Erdős #1047 now has **no problem-specific axiom** — `goodman_counterexample`
  is a theorem, and the whole development is verified modulo Mathlib's foundational axioms.

  See `Erdos1047Problem.lean` for the definitions (`grunskyConjecture`,
  `goodmanPolynomial`, `lemniscate`, `componentContaining`, `IsConvexComplex`, …).
-/
import Proofs.Erdos1047OQ02Certificate

open Polynomial Set

namespace Erdos1047

/-- Grunsky's conjecture is FALSE — there exist non-convex lemniscate components.

    Formerly rested on the `goodman_counterexample` *axiom*.  With the faithful
    `∀ c > 0` statement of `grunskyConjecture` (Parent, Part V), the negation is a
    genuine **theorem**: it follows from the discharged counterexample
    `Erdos1047OQ02Cert.goodman_counterexample_proof`.  The counterexample
    `f = (z²+1)(z−2)²` at `c = 5^{3/2}/4` exhibits a non-convex component,
    contradicting universal convexity. -/
theorem grunskyConjecture_false : ¬grunskyConjecture := by
  intro h
  obtain ⟨z₀, hz₀, hnc⟩ := Erdos1047OQ02Cert.goodman_counterexample_proof
  exact hnc (h goodmanPolynomial goodmanPolynomial_monic goodmanPolynomial_degree_pos
    goodmanCriticalValue (by unfold goodmanCriticalValue; positivity) z₀ hz₀)

/-- Erdős Problem #1047: SOLVED (Answer: NO)
    Not all lemniscate components need be convex. -/
theorem erdos_1047 : ¬grunskyConjecture := grunskyConjecture_false

/-- Existence of non-convex lemniscate components via Goodman's example -/
theorem erdos_1047_counterexample :
    ∃ f : ℂ[X], f.Monic ∧ f.natDegree > 0 ∧
      ∃ c > 0, ∃ z₀ ∈ lemniscate f c,
        ¬IsConvexComplex (componentContaining (lemniscate f c) z₀) :=
  ⟨goodmanPolynomial, goodmanPolynomial_monic, goodmanPolynomial_degree_pos,
   goodmanCriticalValue, by unfold goodmanCriticalValue; positivity,
   Erdos1047OQ02Cert.goodman_counterexample_proof⟩

/-- The answer to Erdős Problem #1047 is NO -/
theorem erdos_1047_answer : ∃ f : ℂ[X], ∃ c > 0, ∃ z₀ ∈ lemniscate f c,
    ¬IsConvexComplex (componentContaining (lemniscate f c) z₀) := by
  obtain ⟨f, _, _, c, hc, z₀, hz₀, hconv⟩ := erdos_1047_counterexample
  exact ⟨f, c, hc, z₀, hz₀, hconv⟩

end Erdos1047

/- Axiom audit (Docker-verified, 3061 jobs, 2026-06-18): `#print axioms` for each of
   `Erdos1047.erdos_1047`, `Erdos1047.grunskyConjecture_false`, and
   `Erdos1047.erdos_1047_answer` reports exactly
   `[propext, Classical.choice, Quot.sound]` — Mathlib's standard foundational
   axioms.  No problem-specific axiom (the former `goodman_counterexample` is now the
   machine-checked theorem `Erdos1047OQ02Cert.goodman_counterexample_proof`), no
   `sorry`, no `Lean.ofReduceBool`. -/
