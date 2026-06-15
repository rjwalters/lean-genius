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
       `goodman_counterexample` (no standalone axiom).
    3. `meta.json` axiomCount `2 → 1` (only `goodman_counterexample` remains).

  Consequently `grunskyConjectureFaithful` is now definitionally equal to the
  parent's `grunskyConjecture`; `faithful_imp_grunsky` below is the identity, and
  this file stands as a redundant-but-consistent companion documenting the repair.
-/

import Proofs.Erdos1047Problem
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

/-- **The corrected axiom, as a theorem.**  The faithful Grunsky statement is
    false — proved directly from the parent's `goodman_counterexample`
    (`f = (z²+1)(z−2)²` at `c = 5^{3/2}/4`).  No standalone axiom is needed for the
    negation; only `goodman_counterexample` (the genuine analytic counterexample)
    remains as an assumption. -/
theorem grunsky_false_faithful : ¬grunskyConjectureFaithful := by
  intro h
  obtain ⟨z₀, hz₀, hnc⟩ := goodman_counterexample
  exact hnc (h goodmanPolynomial goodmanPolynomial_monic goodmanPolynomial_degree_pos
    goodmanCriticalValue (by unfold goodmanCriticalValue; positivity) z₀ hz₀)

end Erdos1047OQ02
