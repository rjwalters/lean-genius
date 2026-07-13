# S3 ACT — reachability redefinition fixes the soundness bug

**Date**: 2026-06-20
**Phase**: ACT
**Researcher**: researcher-9
**Mode**: REVISIT (continued S1/S2 work)
**Outcome**: progress (soundness restored; robustness re-proved; build verification pending)

## Summary

S1/S2 (researcher-2) found that `hasDependentArc` in `Proofs/Erdos1006OQ01.lean`
had its rank inequality backwards (`rank v ≤ rank u`), which made it *vacuously
false* for every acyclic orientation, collapsing `isRobustlyAcyclic ≡ isAcyclic`
and rendering the `cover_graph_characterization` and `nesetril_rodl_counterexample`
axioms **unsound** (both became false statements). S2 proposed fixing the
inequality to `rank u < rank v`, but that forces a Szpilrajn / linear-extension
construction for `cover_graph_admits_robust` (hard, build-gated, offloaded to an
Aristotle job that is now gone — `f4e7c237…` returns "Resource not found").

S3 takes a cleaner route: **redefine `hasDependentArc` via reachability** instead
of ranks.

## The fix

```lean
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    Relation.TransGen (fun a b => O.arc a b ∧ (a, b) ≠ (u, v)) u v
```

An arc `(u,v)` is dependent iff there is an alternate directed path `u ⇝ v`
through the *other* arcs. Reversing `(u,v)` to `(v,u)` then closes a directed
cycle `v → u ⇝ v`. This is the textbook meaning of "reversing the arc creates a
cycle" and is equivalent to the (corrected) rank formulation for finite acyclic
orientations, but is far more tractable to reason about.

## Why this is better than the rank `<` fix

The reachability definition makes all three robustness obligations **elementary
structural inductions on `Relation.TransGen`** — no Szpilrajn / linear-extension
machinery, no build-gated Aristotle dependency:

- `empty_graph_robust`: no arcs ⟹ no path. (one line)
- `cover_graph_admits_robust`: any sub-cover path `u ⇝ v` strictly increases the
  order (`TransGen` induction with `CovBy.lt` + `lt_trans`); a path of length ≥2
  yields a middle `w` with `u < w < v`, contradicting `u ⋖ v` (`CovBy.2`). A
  length-1 path is the excluded arc itself.
- `bipartiteOrientation_robust`: every arc runs `false → true`, so the head of
  any path is on the true side (`TransGen` induction); a length-≥2 path needs a
  middle vertex that is simultaneously true (as a head) and false (as a tail) —
  contradiction. Length-1 is the excluded arc.

## Soundness status after the fix

`admitsRobustAcyclicOrientation` now means the genuine "acyclic + every edge
reversible" property. Consequently:

- `cover_graph_characterization` is now the *true* Pretzel–Brightwell theorem.
- `nesetril_rodl_counterexample` is now the *true* Nešetřil–Rödl theorem.

Both axioms are **sound** (true statements) rather than false. `axiomCount`
remains **3** — this session restores soundness and faithfulness; it does not
de-axiomatize the deep characterization (that remains the OQ-01-OQ-01 goal).

## Verification

Aristotle was unavailable this session (`prove`/`prove_file`/`check_proof` all
returned "Resource not found"). Verification is via `docker-build.sh
Proofs.Erdos1006OQ01` (12 GB cap). **The corrected file must build green before
commit — the deployer auto-merges math PRs.**

## Lean gotchas handled

- `CovBy` is defeq to `And`, so the numeric anonymous projection `huv.2` reaches
  the no-middle field `∀ ⦃c⦄, u < c → ¬ c < v`.
- Field notation `.lt` / numeric `.1/.2` whnf through the `GraphOrientation.arc`
  structure projection (the original file already relied on this with `huv.lt`).
- `cases hpath` on `Relation.TransGen` gives `single`/`tail`; the middle vertex
  in `tail` is recovered with `rename_i`.

## Next steps

- Confirm green build, open PR, update `meta.json` lineCount.
- STEP B (de-axiomatization): the reverse direction (robust ⟹ cover graph) via
  the reachability preorder `Relation.ReflTransGen O.arc` as a `PartialOrder`,
  is now *more natural* given the reachability definition — the dependent-arc
  notion already speaks the same language. This remains the hard open step.
