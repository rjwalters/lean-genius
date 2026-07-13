# 2026-06-27 — S03: Newton-polygon endpoint theorems

**Researcher**: researcher-3
**Branch**: `research/puiseux-oq03-newton-polygon-endpoints`
**Mode**: ACT (extend the combinatorial Newton-polygon API)
**Outcome**: two new verified theorems + worked-example corollary added to
`proofs/Proofs/PuiseuxTheoremOQ03.lean` (0 sorries, 0 axioms).

## What I added

The file already carried the combinatorial Newton-polygon API (supporting-line
`IsLowerVertex`, `IsLowerEdge`, convexity `edgeSlope_mono`, supporting-slope
bounds, `interior_slopes`).  The one existence result, `exists_lowerVertex`,
produces the point of **minimum valuation** (a *vertical* extremum).  This
session adds the complementary **horizontal** extrema — the endpoints of the
polygon:

* `isLowerVertex_of_leftmost` — the minimum-*index* support point is a lower
  vertex.  Supporting line: through `p`, take the least edge-slope leaving `p`
  (`List.argmin` over the other support points); convexity of the division
  inequality (`le_div_iff₀`) shows it lies weakly below every point.
* `isLowerVertex_of_rightmost` — symmetric, via `List.argmax` and `div_le_iff₀`.
* `ysqMinusX_endpoints` — both endpoints of the worked example `Y² − x` are
  recovered by the endpoint theorems.

## Why this matters

Together with `isLowerVertex_of_minimal`, these say the lower hull has a
well-defined left endpoint, lowest point, and right endpoint, so it stretches
across the entire `Y`-degree range `[iₘᵢₙ, iₘₐₓ]`.  That horizontal span is the
combinatorial reason the edge widths sum to the `Y`-degree, i.e. why **every**
root (counted with ramification index) is accounted for by the polygon — the
correctness backbone underneath any Newton–Puiseux complexity claim.

## Scope honesty

This is incremental combinatorial infrastructure, not the open question itself.
The genuinely hard, still-blocked directions are unchanged:

* **Newton polygon theorem** (edge slopes = root valuations): needs a valuation
  API on `K((x))[Y]` absent from Mathlib v4.26.0.
* **S2-B** termination measure for one reduction step.
* **S2-C** quasi-linear complexity (Poteaux–Weimann `Õ(d·δ)`): blocked on the
  absence of an arithmetic-complexity model in Mathlib.

## Build note (environmental)

The shared Docker `lean-mathlib-cache` volume and bind-mounted `.lake/packages`
are contended by many concurrent agent builds; `cache get` replays raced and
produced transient `permission denied (13)` / "corrupted file" errors.
`LEAN_SKIP_CACHE=true` is *not* a workaround — it forces a full from-source
Mathlib rebuild that overruns the timeout.  Build the normal (cache-get) path
and retry on transient replay races.  Also: this worktree's assigned branch was
auto-rebased mid-session, discarding an uncommitted edit — committing to a
dedicated branch immediately is the safe pattern.

## Files modified

- `proofs/Proofs/PuiseuxTheoremOQ03.lean` (+~70 lines, 3 theorems)
- this session note
