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

  ── Proposed parent patch (apply in a live Docker session) ────────────────────

  In `Proofs/Erdos1047Problem.lean`:
    1. Replace the body of `grunskyConjecture` (`:118`) with the `∀ c > 0` form
       (= `grunskyConjectureFaithful` here), matching the docstring.
    2. Delete `axiom grunskyConjecture_false` (`:124`); re-introduce it *after*
       `goodman_counterexample` as
          theorem grunskyConjecture_false : ¬grunskyConjecture := by
            intro h
            obtain ⟨z₀, hz₀, hnc⟩ := goodman_counterexample
            exact hnc (h goodmanPolynomial goodmanPolynomial_monic
              goodmanPolynomial_degree_pos goodmanCriticalValue
              (by unfold goodmanCriticalValue; positivity) z₀ hz₀)
       (move `goodmanPolynomial_degree_pos` above this theorem, or inline the
       `rw [goodmanPolynomial_natDegree]; omega`).
    3. `meta.json`: axiomCount `2 → 1` (only `goodman_counterexample` remains).

  This file is UNREGISTERED (authored under a Docker + Aristotle blackout; the
  axiom-edit-under-blackout rule forbids a blind edit of the registered flagship).
  It imports the parent and reuses `goodman_counterexample`, so it adds **no new
  axioms** of its own and serves as a machine-checkable proof-of-concept for the
  patch above.
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

/-- The faithful (∀ `c`) statement is **strictly stronger** than the parent file's
    small-`c` `grunskyConjecture`: take the threshold `c₀ = 1`.  Consequently the
    parent's `axiom grunskyConjecture_false : ¬grunskyConjecture` negates the
    *weaker* statement and over-claims — the root cause of its unsoundness. -/
theorem faithful_imp_grunsky : grunskyConjectureFaithful → grunskyConjecture := by
  intro h f hm hd
  exact ⟨1, one_pos, fun c hc _ z₀ hz₀ => h f hm hd c hc z₀ hz₀⟩

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
