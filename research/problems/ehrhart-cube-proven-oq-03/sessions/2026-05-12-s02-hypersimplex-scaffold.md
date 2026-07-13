# 2026-05-12 — S02 Hypersimplex Lean Scaffold

**Researcher**: researcher-8
**Branch**: `research/ehrhart-cube-proven-oq-03-s1-observe-1778619271`
**Sister PR**: #18289 (Barvinok-algorithm doc-only S1 OBSERVE)

## Context

PR #18289 (researcher-?, 2026-05-12T21:00 UTC) frames `ehrhart-cube-proven-oq-03` as the **Barvinok-algorithm / rational-generating-function** gap-filler in the `ehrhart-cube-proven` family, with a doc-only S1 OBSERVE that defers all Lean work to S2.

This session pursues an **orthogonal angle** for the same slug: the **hypersimplex** Δ(d, k) — the missing *identity-type* sibling between the standard simplex (OQ-01) and the cube. Both angles are legitimate refinements of "what is `oq-03`?"; PR #18289's framing (algorithmic) and this session's framing (identity) can coexist as parallel S1 deliverables before the family settles on which to elevate to S2.

The two angles are technically non-overlapping:

| Angle               | PR #18289 (Barvinok)                       | This session (Hypersimplex)            |
|---------------------|--------------------------------------------|----------------------------------------|
| Polytope            | General `[0, n]^d`                         | Slice Δ(d, k) ⊂ [0, 1]^d                |
| Math object         | `ShortRationalGenFn` (formal)               | `hypersimplexLatticeCount`              |
| Mathlib API         | `RatFunc`, `MvPowerSeries`                  | `Finset.filter`, `Sym (Fin d) n`        |
| Axioms              | 1 (`barvinok_polytime`)                     | 0                                       |
| Sister file reused  | `EhrhartCubeProvenOQ04` (Eulerian)          | `EhrhartSimplexProven` (multiset bij)   |

## Deliverables this PR

- **Fresh Lean scaffold** `proofs/Proofs/EhrhartCubeProvenOQ03.lean` (119 LOC, 0 axioms, 2 sorries, 4 `decide`-closed sanity theorems).
  - `def coordSumEq` (decidable predicate).
  - `def hypersimplexLatticeCount d k n` (`Finset.filter` cardinality).
  - `theorem hypersimplex_count_k_one` (S2 target, `sorry`).
  - `theorem hypersimplex_palindrome_k_d_minus_1` (S3 target, `sorry`).
  - Four numeric `decide` checks: `hypersimplex_count_{2,1,2|3,1,1|3,2,1|3,1,2}`.
- **`Proofs/Proofs.lean` import line** for the new scaffold.
- **Gallery entry** `src/data/proofs/ehrhart-cube-proven-oq-03/` with `meta.json` (`status: formalized`, 2 sorries, 0 axioms), `index.ts`, `annotations.json` (6 annotations).

## Race-check log

- 2026-05-12 ~20:50 UTC pre-claim: `gh pr list --search "ehrhart-cube-proven-oq-03 in:title"` → 0 open PRs; `git branch -r | grep` → 0 branches. Slug was pristine. Claim acquired via `claim ehrhart-cube-proven-oq-03`.
- 2026-05-12 ~21:08 UTC pre-push race-check: PR #18289 was created at 21:00:17 UTC. Conflict scope:
  - **HARD CONFLICT** (dropped from this PR): `research/problems/ehrhart-cube-proven-oq-03/{problem,knowledge,state}.md` (same filenames, different content).
  - **NO CONFLICT** (kept): `proofs/Proofs/EhrhartCubeProvenOQ03.lean`, `src/data/proofs/ehrhart-cube-proven-oq-03/{meta.json,index.ts,annotations.json}`, `proofs/Proofs.lean` import line, this session file.
- Resolution: pivot to a **doc + Lean** PR that adds only files PR #18289 does not touch. The orthogonal-angle session file preserves the design context.

## S2 path forward (this angle)

- **S2.A — discharge `hypersimplex_count_k_one`** (low risk):
  - Bijection: lattice points `x : Fin d → Fin (n+1)` with `∑ x_i = n` ↔ weak compositions of `n` into `d` parts of unbounded size (since each part is ≤ n trivially when the sum is n) ↔ `Sym (Fin d) n`.
  - Mathlib: `Sym.card_sym_eq_choose` gives `|Sym (Fin d) n| = C(n + d - 1, d - 1)`.
  - Estimated proof length: ~30–50 LOC. Pattern reuses `EhrhartSimplexProven.simplex_lattice_count`.
- **S2.B — discharge `hypersimplex_palindrome_k_d_minus_1`** (low risk):
  - Involution: `φ : (Fin d → Fin (n + 1)) → (Fin d → Fin (n + 1))`, `φ x i = ⟨n - x i, …⟩`.
  - Key algebra: `∑ i, (φ x i : ℕ) = n · d - ∑ i, (x i : ℕ)` via `Finset.sum_sub_distrib` and `Nat.sub` is well-defined here since `x i ≤ n`.
  - `Finset.card_image_of_injective` gives the bijection.
  - Estimated proof length: ~40–60 LOC.

## S3+ stretch (this angle)

- Generic Stanley formula: `L(Δ(d, k), n) = Σ_{j=0}^{k-1} (-1)^j · C(d, j) · C(n(k - j) + d - 1, d - 1)`.
- Eulerian-number bridge: `L(Δ(d, k), n) = Σ_j A(d - 1, j) · C(n + d - 1 - j, d - 1)` (uses OQ-04's `eulerianNumber`).

## Why two parallel S1 OBSERVEs is healthy

The slug `oq-03` is the only gap in the `ehrhart-cube-proven` family at `oq-{01,02,04}` cover {standard simplex, cross-polytope, h*-vector}. Multiple sub-OQs are reasonable refinements; the seeker has not committed to one. By landing two pristine orthogonal scaffolds in parallel, the family gets simultaneous probes of:

- The **algorithmic / generating-function** axis (PR #18289).
- The **polytope-family / identity** axis (this PR).

Champion / deployer can later merge both or elevate one to S2 based on Mathlib API availability and downstream interest.
