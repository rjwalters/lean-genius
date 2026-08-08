# 2026-08-07/08 (evening–night): descent tower, d = 124 terminal, strict gap

**Participants**: claude (Fable), codex — continuous squad-room collaboration,
continuing the same day as the large-prime capstone (see previous log).
All results Docker- or host-`lake`-verified, sorry-free; axiom audits
exactly `[propext, Classical.choice, Quot.sound]` except where certificate
axioms are explicitly disclosed below.

## Part I recap (see previous log)

Large-prime sector capstone → defect-cycle lengths d-smooth → universal
dichotomy u·w ≤ 2d−1 → minimum-layer design equation
R² = wJ + (s−3)I with s² − s + 3 = u·w.

## Part II: the descent tower

- **Descent** (`Erdos85MinimumLayerDescent.lean`, codex): the union U of
  minimum components induces an s-regular C4-free graph on s(s−1)+3
  vertices, s even, s < d outside {4,12} — every nonexceptional
  exact-boundary graph strictly contains a smaller exact-boundary graph.
  d=6 pin: child s ∈ {0,2}.
- **Extension rigidity** (`Erdos85MinimumLayerExtension.lean`, codex):
  parent defect restricted to U equals the child defect; distinct
  U-vertices have disjoint external neighborhoods; counting gives
  d ≥ (s−1)²+3, and the sharp alternative
  **d = (s−1)²+3 (saturated) ∨ s(s−1)+4 ≤ d** with a parity refinement
  and forbidden intervals.
- **Saturated structure** (codex, several files; claude bricks in
  `Erdos85DegreeSixMinimumSectorTerminal.lean` and
  `Erdos85MinimumLayerGramMatrix.lean`): perfect 1-design ownership of
  the exterior; fiber blocks empty over child edges / perfect matchings
  over child non-edges; Latin-resolution two-step bijections; the
  four-block no-closure (C4) law; exterior defect = matching **graph
  covering** of the child defect (no cross edges); minimum component
  order divides every component order; the saturated child is
  equal-cycle, so `equalCycle_degree_eq_four_or_twelve` collapses the
  entire saturated branch to the single residual **d = 124**
  (s = 12, u = 45, w = 3).
- **Guardrail** (codex): the d=124 child quotient is
  SRG(45,12,3,3)-realizable (GQ(4,2)-type objects exist), so no
  quotient-level argument can kill it — any terminal must use the
  exterior lift. A determinant/monodromy lane was explored and cleanly
  refuted (odd cover cycles contribute square factors; 121 = 11²).

## Part III: the d = 124 terminal (goal #18, ~3.5 hours from idea to close)

Codex's trace-escape observation: on the exterior hard sector
(fiber-sum-zero, dimension 14985), the owner-fiber machinery yields
commuting S, T with **tr S = −135**, **S² = 123·I − T**, T semisimple
(symmetric restriction). If every nonprincipal cycle-frequency μ had
nonsquare 123−μ norm, the residual trace would vanish and the principal
μ=2 sector (square root 11) would carry the whole trace — but 11 ∤ 135.

Division of labor (verbatim from the room):
- **claude — certificate lane** (`Erdos85OneTwentyThreeNormCertificate.lean`):
  executable Möbius-inversion certificates at parameter 123 for every
  conductor 3 ≤ n ≤ 15255 — the quotient of C_k(123)−2 divides exactly,
  is a perfect square, and its root (the primitive real norm of
  123−(ζ+ζ⁻¹)) is **not** a square (`primitiveNormOTT_not_isSquare`);
  stage-2 factorization `C_n(123)−2 = 121·(125 if 2∣n)·∏ R_k²`
  (`cycleChebyshevOTT_primitive_factorization`). Nine native_decide
  blocks; rational factors 121 = 11² (the principal sector's square) and
  125 = 5³. Cross-checked against codex's independent exact big-int
  Python sweep (23 s, zero square hits).
- **claude — abstract trace escape** (`Erdos85AbstractTraceEscape.lean`):
  J-free operator abstraction of the uniform trace-split engine —
  commuting S, T on a finite-dimensional ℚ-space, S² = κ·1 − T, T
  annihilated by gP, all monic irreducible divisors of gP except X − μ0
  nonsquare at κ ⟹ trace of S on ker r(T) vanishes for any residual
  r ∣ minpoly T with r(μ0) ≠ 0. (Authored during a Docker outage,
  pushed flagged-unverified; compiled clean with zero fixes on codex's
  host — the engine's argument with (d−1) → κ and J deleted.)
- **codex — graph transport**: hard-sector package
  (`range_restrict_oneTwentyThree_semisimple_package`), symmetric
  restriction semisimplicity + μ=2 residual peel
  (`Erdos85SymmetricRestrictionSemisimple.lean`), factor divisibility
  (irreducible factors of hard-sector T divide global cycle Chebyshev
  factors, conductors ≤ 15255), parametric cyclotomic resultant norm,
  the strong-induction cancellation
  (`oneTwentyThree_cycleFactor_eval_nonsquare_except_two`), and the
  terminal **`no_minimumLayer_saturated_124_hardSector`** @ b53249d22a.

Axiom ledger of the terminal: standard-3 + exactly 9 disclosed
native_decide certificate axioms (5 stage-1 + 4 stage-2), isolated in the
certificate file.

## The season theorem

**`secondOrder_minimumLayer_strict_gap`** (@ 97efab9b57): for every exact
even boundary d ∉ {4, 12}, the descent child satisfies
**s(s−1) + 4 ≤ d, unconditionally** — the saturated branch is gone.

Remaining exact-boundary nonexistence surface: **d = 6** (child s ∈ {0,2}:
lone antipodal triangle or induced C5; SAT certificate instance grinding;
K1/K2 analytic candidates mapped), **d = 16** (children s ∈ {0,2,4}, entry
lemma @ 9e2cc9bc47; note the gap is TIGHT at (s,d) = (4,16) — 16 = 4·3+4 —
making it the extremal unsaturated case, with the d=4 child on 15 vertices
being the known fifteenRegular-type equal-cycle objects and 48 orphan
exterior vertices), and the d ∈ {4, 12} equal-cycle seeds themselves.

## Infrastructure notes

- Root-disk exhaustion crashed Docker mid-evening (operator reclaimed
  ~13 GB + 15 GB codex-side; standing policy: artifacts stage on AWS and
  rsync to Stripe, localhost for code and hot state only). During the
  outage the team switched to host `lake` verification with deferred
  Docker re-audit — host builds proved ~10× faster under load.
- BBBB orbit sweep continued on the coordinator (~90+/768 head-shard,
  all UNSAT); two spot workers lost to AWS reclamation, third live;
  15-minute rsync-back cadence to the durable volume with sha256
  manifests; coordinator disk-full incident found and fixed (gzip DRATs
  after verification, 8 corrupted verdicts re-queued).
- d=6 direct SAT instance (33 vertices, min-degree 6, C4-free — an
  independent check of Boza's R(C4,K_{1,27}) = 33) grinding for hours;
  expected UNSAT; will feed the h=9-style LRAT→Lean pipeline if so.

## Corrections during the span (methodology record)

- codex's saturation-impossibility count (msg 1058) — off by two on
  |common nonneighbors| for a D-adjacent pair (D-adjacency means ZERO
  common neighbors, not two); caught by both sides simultaneously; the
  honest theorem became the Latin-resolution bijection.
- claude's "all P-components odd" red-team on the mod-3 valuation
  (unjustified parity assumption) — codex then refuted the whole
  determinant lane cleanly (square factors per odd cycle).
- claude's "w=5 dies immediately" for d=16/s=2 — wrong (δ(δ−1) = 2 has
  the solution δ = 2); corrected within minutes.
