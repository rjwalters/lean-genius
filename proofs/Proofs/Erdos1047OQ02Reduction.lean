/-
  Erdős #1047 — OQ-02: a topological reduction for lemniscate non-convexity
  (erdos-1047-oq-02, companion to `Erdos1047OQ02.lean`)

  ── Purpose ───────────────────────────────────────────────────────────────────

  After the parent patch (`Erdos1047Problem.lean`), the Grunsky-conjecture file
  carries exactly ONE genuine analytic assumption:

      axiom goodman_counterexample :
        ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
          ¬ IsConvexComplex (componentContaining
              (lemniscate goodmanPolynomial goodmanCriticalValue) z₀)

  De-axiomatizing it is the open task recorded in this entry's `meta.json`.  The
  obstacle is purely *topological*: `componentContaining S z₀ = connectedComponentIn
  S z₀` is a connectedness notion, so witnessing non-convexity of a *component*
  (not merely of `S`) requires controlling which points share `z₀`'s component.

  This file isolates that topological core once and for all, reducing the problem to
  an elementary, checkable geometric statement:

      *Exhibit a preconnected arc `C ⊆ {|f| ≤ c}` joining two points `z₀, z₁`
       whose connecting chord pokes outside `{|f| ≤ c}` (i.e. `‖f(m)‖ > c` for the
       midpoint `m`).*

  Given such an arc, `componentContaining_lemniscate_not_convex_of_chord_exits`
  produces the non-convex component with no further topology.  This is the reusable
  bridge behind *every* Grunsky counterexample — Pommerenke (1961), Goodman (1966),
  and the referee's example — turning the remaining work into the production of one
  concrete arc plus a `norm_num`/analytic chord estimate.

  No new axioms are introduced.  The two lemmas are pure ZFC/topology facts about
  `connectedComponentIn` and the file's `IsConvexComplex` predicate.

  STATUS: BUILD-VERIFIED and REGISTERED (2026-06-15). `docker-build.sh
  Proofs.Erdos1047OQ02Reduction` compiled green (3059 jobs); now imported in
  `Proofs.lean` so the gallery machine-checks it.  Both proofs rest only on the
  standard Mathlib lemmas `IsPreconnected.subset_connectedComponentIn` and
  `connectedComponentIn_subset`.
-/

import Proofs.Erdos1047Problem
import Mathlib.Tactic

open Polynomial Set Erdos1047

namespace Erdos1047OQ02

/-- **Topological reduction for component non-convexity.**

    To certify that the `z₀`-component of a set `S ⊆ ℂ` is *not* convex, it suffices
    to exhibit a single *preconnected* subset `C ⊆ S` that contains both `z₀` and a
    second point `z₁`, together with a chord parameter `t ∈ [0,1]` whose point
    `(1−t)·z₀ + t·z₁` escapes `S`.

    Reason: by maximality of `connectedComponentIn`, the preconnected set `C` lies
    entirely inside `z₀`'s component, so `z₀` and `z₁` are *in the same component*;
    if that component were convex it would contain the escaping chord point, yet the
    component is contained in `S`, which the point left — contradiction.

    This is the purely topological half of any Grunsky counterexample: it removes
    all reasoning about connected components, leaving only the production of one
    preconnected arc inside the lemniscate with an escaping chord. -/
theorem not_isConvexComplex_componentContaining_of_preconnected_chord_exits
    {S C : Set ℂ} {z₀ z₁ : ℂ}
    (hCpc : IsPreconnected C) (hCS : C ⊆ S)
    (hz₀ : z₀ ∈ C) (hz₁ : z₁ ∈ C)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hexit : (1 - t) • z₀ + t • z₁ ∉ S) :
    ¬ IsConvexComplex (componentContaining S z₀) := by
  unfold componentContaining IsConvexComplex
  intro hconv
  have hCcomp : C ⊆ connectedComponentIn S z₀ :=
    hCpc.subset_connectedComponentIn hz₀ hCS
  have hmid : (1 - t) • z₀ + t • z₁ ∈ connectedComponentIn S z₀ :=
    hconv z₀ z₁ (hCcomp hz₀) (hCcomp hz₁) t ht0 ht1
  exact hexit (connectedComponentIn_subset S z₀ hmid)

/-- **Lemniscate specialization.**  For a polynomial lemniscate `{z : ‖f z‖ ≤ c}`,
    a preconnected arc `C` joining `z₀, z₁` whose chord midpoint `m` satisfies
    `‖f(m)‖ > c` certifies that the `z₀`-component of the lemniscate is non-convex.

    This is exactly the shape of input needed to discharge `goodman_counterexample`
    (and the Pommerenke / referee counterexamples): give one arc inside the
    sublevel set and one numeric chord estimate. -/
theorem componentContaining_lemniscate_not_convex_of_chord_exits
    {f : ℂ[X]} {c : ℝ} {C : Set ℂ} {z₀ z₁ : ℂ}
    (hCpc : IsPreconnected C) (hCS : C ⊆ lemniscate f c)
    (hz₀ : z₀ ∈ C) (hz₁ : z₁ ∈ C)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hexit : c < ‖f.eval ((1 - t) • z₀ + t • z₁)‖) :
    ¬ IsConvexComplex (componentContaining (lemniscate f c) z₀) := by
  refine not_isConvexComplex_componentContaining_of_preconnected_chord_exits
    hCpc hCS hz₀ hz₁ ht0 ht1 ?_
  simp only [lemniscate, Set.mem_setOf_eq, not_le]
  exact hexit

end Erdos1047OQ02
