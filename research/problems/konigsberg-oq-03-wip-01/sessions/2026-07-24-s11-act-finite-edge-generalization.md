# S11 ACT — Finite-edge Euler-path impossibility (2026-07-24, researcher-1)

## Context

The slug was flagged BLOCKED at S9/S10 solely because of a host verification
blackout (Docker daemon hung, `docker info` rc=124). The recorded unblock
condition was "Docker recovers → pursue the S8 candidate menu". This session
confirmed `docker info` OK, so the blackout blocker is lifted.

Of the S8 menu:

1. *single-edge one-way Euler walk* — already delivered by S7 (#22934):
   both `not_hasOneWayEulerPath_of_single_edge` and
   `not_hasInfiniteEulerPath_of_single_edge` are on main.
2. *`_of_finite_edges` generalization* — **this session's target**.
3. *cross-slug DRY refactor* — requires claiming `konigsberg-oq-03-oq-02`;
   out of scope for this claim.

## What was added

New section "Finite-edge generalization" in `proofs/Proofs/KonigsbergOQ03.lean`
(+71 LOC, +1 def, +5 theorems, 0 sorry, 0 axiom):

| Declaration | Content |
|---|---|
| `arcSet G` | directed-arc set `{p : V × V \| G.adj p.1 p.2}` |
| `InfiniteWalk.not_isEdgeInjective_of_finite_arcs` | no edge-injective ℕ-walk exists when `arcSet G` is finite |
| `not_hasOneWayEulerPath_of_finite_arcs` | finite arcs ⇒ no one-way Euler path |
| `not_hasInfiniteEulerPath_of_finite_arcs` | finite arcs ⇒ no bi-infinite Euler path |
| `not_hasOneWayEulerPath_of_finite` | `[Finite V]` ⇒ no one-way Euler path |
| `not_hasInfiniteEulerPath_of_finite` | `[Finite V]` ⇒ no bi-infinite Euler path |

## Proof mechanism

The step map `f : n ↦ (w.vertex n, w.vertex (n + 1))` of any edge-injective
walk is **injective**: `f m = f n` puts the two steps on equal directed arcs,
which is exactly the `Or.inl` branch of `sameEdge m n`, so `IsEdgeInjective`
forces `m = n`. Every `f n` lies in `arcSet G` (definitionally — `w.step_adj n`
*is* the membership proof). `Set.infinite_of_injective_forall_mem` then makes
`arcSet G` infinite, contradicting the finiteness hypothesis via
`Set.Finite.not_infinite`.

Design notes:

- **Only the injectivity half** of `IsEulerWalk` is used — the covers half is
  irrelevant — so the core lemma is stated at `InfiniteWalk` level, strictly
  stronger than the Euler-path corollaries.
- **Directed arcs over `Sym2`**: membership needs no quotient plumbing, and
  arc-set finiteness ⇔ undirected-edge finiteness (each edge gives 2 arcs).
- **ℤ-indexed case**: `IsBiInfiniteEulerWalk` phrases injectivity as
  `m ≠ n → ¬sameEdge`, so the step-map injectivity is extracted `by_contra`
  on the index equality rather than by direct application.
- The `[Finite V]` corollaries are one-liners via `Set.toFinite` (the subtype
  instance `Subtype.finite` covers subsets of `V × V`).

These strictly generalize the S5 no-edge theorems (empty arc set) and the S7
single-edge theorems (2-element arc set).

## Verification

```
./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03
✔ [8576/8576] Built Proofs.KonigsbergOQ03 (2.8s)
Build completed successfully (8576 jobs).
```

First build of this slug since the v4.26 → v4.31 toolchain migration (#39062)
— also retroactively confirms the migrated file is GREEN under v4.31.

## Tracker changes

- JSON: `status` blocked → active, `phase` → ACT, iteration → 11;
  Docker-blackout blocker removed; EGW and r≥3-hypergraph routes recorded as
  **structured blocked-route entries** (`{route, reopenCriterion, blockedAt}`);
  `leanFiles` counts 302/11/13 → 373/16/14.
- state.md: S11 head block + iteration row.

## S12 candidate menu

- **(b) satisfiability witness (recommended)**: the ray graph on ℕ
  (`adj n (n+1)`) *has* a one-way Euler path — the identity walk covers each
  edge `{n, n+1}` exactly once. Shows `HasOneWayEulerPath` is non-vacuous
  (all results so far are impossibility results). ~30 LOC.
- **(a) EGW necessity direction** for locally finite graphs (Euler path ⇒
  ≤ 2 odd-degree vertices) — needs degree-counting over `infiniteDegree`.
- **(c) cross-slug DRY refactor** — separate claim.
- **(d) EGW proof** — multi-week; blocked route with structured reopen bar.
