/-
  Erdős #1047 — OQ-02: soundness of the Grunsky-conjecture axiom
  (erdos-1047-oq-02)

  ── The integrity problem ─────────────────────────────────────────────────────

  The registered flagship `Proofs/Erdos1047Problem.lean` defines Grunsky's question
  with a spurious **small-`c`** restriction:

      def grunskyConjecture : Prop :=
        ∀ f : ℂ[X], f.Monic → f.natDegree > 0 →
          ∃ c₀ > 0, ∀ c, 0 < c → c < c₀ → ∀ z₀ ∈ lemniscate f c,
            IsConvexComplex (componentContaining (lemniscate f c) z₀)

  and then *posits* its negation as an axiom:

      axiom grunskyConjecture_false : ¬grunskyConjecture          -- Erdos1047Problem:124

  But the small-`c` statement is **true**: for a *fixed* monic `f`, as `c → 0` the
  sublevel set `{|f| ≤ c}` breaks into one tiny component around each distinct root
  `r`, and near `r` (multiplicity `k`) it is `{ |z − r|ᵏ ≲ c' } = { |z − r| ≤ c'^{1/k} }`,
  a disk — hence convex.  So for every `f` there is a threshold `c₀` below which all
  components are convex, i.e. `grunskyConjecture` holds.  Its negation
  `grunskyConjecture_false` is therefore a **false axiom**, and the headline
  `erdos_1047 : ¬grunskyConjecture := grunskyConjecture_false` "solves" Erdős #1047
  through an unsound assumption that also does not match the real question (the
  Pommerenke/Goodman counterexamples live at specific, *non-small* critical `c`).

  ── The faithful statement, and why it needs no standalone axiom ───────────────

  Grunsky actually asked (Erdos1047Problem docstring): *must all lemniscate
  components be convex?* — with **no** small-`c` restriction.  The faithful
  formalization is `grunskyConjectureFaithful` below (`∀ c > 0`).  It is genuinely
  FALSE, and — crucially — its negation is a **theorem**, not an axiom: it follows
  directly from the file's existing `goodman_counterexample` (the only genuine
  analytic input).  `grunsky_false_faithful` proves it here.

  `faithful_imp_grunsky` records the logical relationship: the faithful (∀ c)
  statement is strictly stronger than the parent's small-`c` one, so the parent's
  axiom (negating the *weaker* statement) over-claims — which is exactly why it is
  unsound.

  ── Parent patch: APPLIED ─────────────────────────────────────────────────────

  The patch this file proposed has now been applied in `Proofs/Erdos1047Problem.lean`
  (Docker-verified):
    1. `grunskyConjecture` was redefined to the `∀ c > 0` faithful form (= this
       file's `grunskyConjectureFaithful`).
    2. `axiom grunskyConjecture_false` was converted to a `theorem`, proved from
       `goodman_counterexample`.

  ── This entry is now axiom-free ──────────────────────────────────────────────

  The last analytic assumption has been discharged.  The Goodman counterexample is
  proved with no `sorry` and no axiom in `Proofs/Erdos1047OQ02Certificate.lean`
  (`goodman_counterexample_proof`), so `grunsky_false_faithful` below now derives the
  Erdős #1047 answer from that machine-checked certificate instead of the parent's
  `goodman_counterexample` *axiom*.  Its `#print axioms` shows only Mathlib's
  standard `propext`/`Classical.choice`/`Quot.sound`.  `meta.json` axiomCount `1 → 0`.

  Consequently `grunskyConjectureFaithful` is definitionally equal to the parent's
  `grunskyConjecture`; `faithful_imp_grunsky` below is the identity.
-/

import Proofs.Erdos1047Problem
import Proofs.Erdos1047OQ02Certificate
import Mathlib.Tactic

open Polynomial Set Erdos1047

namespace Erdos1047OQ02

/-- **Faithful Grunsky question** (no small-`c` restriction): for every monic
    `f` of positive degree and *every* `c > 0`, all lemniscate components are
    convex.  This is the statement the Erdős #1047 docstring actually describes,
    and it is FALSE (Pommerenke 1961, Goodman 1966). -/
def grunskyConjectureFaithful : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree > 0 →
    ∀ c, 0 < c → ∀ z₀ ∈ lemniscate f c,
      IsConvexComplex (componentContaining (lemniscate f c) z₀)

/-- The faithful (∀ `c`) statement now **coincides** with the parent file's
    `grunskyConjecture`: the unsoundness has been repaired in `Erdos1047Problem.lean`,
    where `grunskyConjecture` was redefined to the faithful `∀ c > 0` form and its
    negation `grunskyConjecture_false` converted from an `axiom` to a theorem.  The
    two definitions are now definitionally equal, so this implication is the
    identity. -/
theorem faithful_imp_grunsky : grunskyConjectureFaithful → grunskyConjecture :=
  fun h => h

/-- **The corrected axiom, fully proved — no assumptions.**  The faithful Grunsky
    statement is false (`f = (z²+1)(z−2)²` at `c = 5^{3/2}/4`).  The witness is now
    `Erdos1047OQ02Cert.goodman_counterexample_proof`, a `sorry`-free, axiom-free
    theorem (it replaces the parent's `goodman_counterexample` *axiom* with the
    machine-checked Goodman certificate: a preconnected arc inside the lemniscate
    whose chord midpoint escapes it, via the topological bridge
    `componentContaining_lemniscate_not_convex_of_chord_exits`).  So this negation —
    and hence the Erdős #1047 answer (NO) along this route — rests on **no** analytic
    axiom. -/
theorem grunsky_false_faithful : ¬grunskyConjectureFaithful := by
  intro h
  obtain ⟨z₀, hz₀, hnc⟩ := Erdos1047OQ02Cert.goodman_counterexample_proof
  exact hnc (h goodmanPolynomial goodmanPolynomial_monic goodmanPolynomial_degree_pos
    goodmanCriticalValue (by unfold goodmanCriticalValue; positivity) z₀ hz₀)

/- Axiom audit (Docker-verified): `#print axioms grunsky_false_faithful` reports
   exactly `[propext, Classical.choice, Quot.sound]` — Mathlib's standard axioms,
   which do not count as assumptions.  No problem-specific axiom, no `sorry`. -/

end Erdos1047OQ02
