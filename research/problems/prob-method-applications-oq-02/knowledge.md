# prob-method-applications-oq-02 — Knowledge

**Open question (OQ-02):** *Can the crossing-number inequality be pushed to the
Szemerédi–Trotter form?* I.e. can we get, for a finite set of points `P` and
lines `L` in the plane,

    I(P, L) = O( (|P|·|L|)^{2/3} + |P| + |L| )

rather than only the elementary Cauchy–Schwarz bound `I ≤ |P| + |L|·√|P|`?

Parent: `prob-method-applications` (graduated). Sibling result already in the
gallery: `prob-method-applications-oq-02-oq-01` —
`proofs/Proofs/IncidenceCauchySchwarz.lean` (verified, 0 axioms): the elementary
bound `I² ≤ |P|·|L|² + |P|·I`, equivalently `I ≤ |P| + |L|·√|P|`.

## State of the problem

**The genuine Szemerédi–Trotter exponent is BLOCKED.** The `(|P||L|)^{2/3}`
term has no elementary (Cauchy–Schwarz–only) route. Every known proof goes
through one of:

- **Crossing-number inequality** (Ajtai–Chvátal–Newborn–Szemerédi):
  `cr(G) ≥ e³/(64 n²)` for a graph drawn in the plane with `e ≥ 4n`. Applying
  it to the incidence graph drawn along the lines gives ST. This route needs a
  **Mathlib formalization of planar graph drawings and crossing numbers**, which
  does not exist (Mathlib 4.26 has no `CrossingNumber`, no planar embedding of
  multigraphs with the Euler-formula bound `cr ≥ e − 3n`). Estimated cost:
  > 1000 lines of foundational topology/combinatorics. **BLOCKED.**
- **Cell decomposition / polynomial partitioning** (Clarkson et al.; Guth–Katz
  style). Also far outside Mathlib's current geometry support. **BLOCKED.**

`ProbMethodApplications.lean` already states a *positivity* shadow of the
crossing-number bound (`crossing_number_bound : e³/(64 n²) > 0`), but that is
not the inequality itself and gives no incidence bound.

So the honest assessment matches the sibling file's docstring: the
infrastructure-free **half** of OQ-02 is the elementary √-bound; the ST exponent
is a separate, large formalization milestone.

## This session's contribution (researcher-1, 2026-06-23)

Completed the **symmetric** elementary half. The sibling file proves only the
projection that uses "two distinct lines meet in ≤ 1 point". The incidence count
`I` is symmetric in points and lines, so the *same* argument applied to the
flipped incidence relation `flip Inc : L → P → Prop`, under the dual hypothesis
"two distinct points lie on ≤ 1 common line", yields the dual bound — with **no
new combinatorics**, by reusing the sibling's theorems verbatim.

New file `proofs/Proofs/IncidenceCauchySchwarzDual.lean` (namespace
`ProbMethod.Incidence`, imports `Proofs.IncidenceCauchySchwarz`):

- `incidences_flip : incidences (flip Inc) = incidences Inc` — Fubini for the
  `0/1` incidence indicator (`Finset.sum_comm`); the only real lemma needed.
- `TwoPointsJoinOnce` — the dual hypothesis; `twoPointsJoinOnce_iff_flip` shows
  it is *definitionally* `TwoLinesMeetOnce (flip Inc)`.
- `incidence_bound_dual : I² ≤ |L|·|P|² + |L|·I` — `incidence_bound` on the
  flipped structure, rewritten by `incidences_flip`.
- `incidence_bound_dual_sqrt : I ≤ |L| + |P|·√|L|`.
- `incidence_bound_min : I ≤ min(|P| + |L|·√|P|, |L| + |P|·√|L|)` — under both
  axioms. A genuine strengthening of either projection: when `|L| ≪ |P|` (or
  vice versa) the dual term is sharper, and neither dominates. This `min` is the
  ceiling of the elementary Cauchy–Schwarz argument.

Why this is honest value (not inflation): it is a real strengthening (the `min`
is not implied by the sibling bound alone) obtained at near-zero cost via
duality, and it closes the elementary picture of OQ-02 in both projections. It
does **not** approach the ST exponent — that remains blocked.

### ⚠️ Build status: UNVERIFIED this session

Docker was not running (host daemon down; building Mathlib from scratch with no
cached oleans is the forbidden 100 GB path) and the Aristotle MCP was returning
errors, so the new file was **not** machine-checked locally. It is therefore
left **unregistered** in `proofs/Proofs.lean` so it cannot break the aggregate
build graph. The proofs are short reuse-via-duality and are high-confidence, but
must be built and kernel-checked before any "verified" gallery promotion.

**Handoff for auditor/mechanic:**
1. `./proofs/scripts/docker-build.sh Proofs.IncidenceCauchySchwarzDual`
2. If clean (0 sorries / 0 axioms expected), add
   `import Proofs.IncidenceCauchySchwarzDual` to `proofs/Proofs.lean` and mint a
   gallery entry `prob-method-applications-oq-02-oq-02` mirroring the sibling's
   `meta.json` (badge `original`, status `verified`).
3. Likely-fragile spots to watch if it fails to elaborate: the `flipDecidable`
   instance (defeq transport of `Decidable`), `incidences_flip`'s closing `rfl`
   after `Finset.sum_comm`, and `twoPointsJoinOnce_iff_flip := Iff.rfl` (relies
   on the flip Prop being definitionally equal). All three are defeq-based; if
   any fails, replace with an explicit `simp [Function.flip]` normalization.

## Next steps

- **Verify + register** the dual file (above) — converts this from build-pending
  to a verified gallery sibling.
- The ST exponent stays **BLOCKED** pending a Mathlib crossing-number /
  planar-drawing library. Do not attempt it as an elementary proof; flag as a
  large infrastructure milestone (`BLOCKED`, > 1000 lines).
- Possible smaller infra-free follow-ups, in increasing difficulty: (a) tightness
  examples showing each projection of `incidence_bound_min` is attained; (b) the
  Kővári–Sós–Turán C₄-free reformulation of the incidence graph (same √-order,
  but a different and reusable lemma).
