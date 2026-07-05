# Current State

**Phase**: INFRASTRUCTURE (B_h infrastructure build-out for OQ-03)
**Since**: 2026-07-04
**Iteration**: 7

## Current Focus

OQ-03 (`Erdos153OQ03.lean`): the B_h generalization of Sidon sets. The parent
gap-variance conjecture is open; this file builds reusable, fully-proved
structural infrastructure. Sections I–VI (nesting, Sidon bridge, invariances,
sharp injectivity count `|hSumset| = |A.sym h|`) already merged (0 sorry/axiom).

## Active Approach

Section VII (researcher-8, 2026-07-04): make the docstring's promised closed
form `C(|A|+h−1, h)` explicit by supplying the **missing `Finset.sym`
cardinality lemma** and composing it with Section VI.

- `card_sym (h A) : (A.sym h).card = (A.card + h - 1).choose h` — Mathlib has
  this only at the `Fintype` level (`Sym.card_sym_eq_choose`); there is NO
  `Finset.card_sym`. Bridge: `Sym.map (Subtype.val : ↥A → ℕ)` is injective
  (`Sym.map_injective`) and its image is exactly `A.sym h` (surjectivity via
  `Sym.attach` + `Sym.attach_map_coe`; membership via `Finset.mem_sym_iff`,
  `Sym.mem_map`). Transport `Sym.card_sym_eq_choose` across it.
- `card_sym_eq_multichoose` — same count as `multichoose |A| h`.
- `card_hSumset_eq_choose (H : IsBhSet h A)` — sharp sumset count in closed form.

## Blockers

**Dual verification-tool blackout (2026-07-04).** Section VII is written but
NOT machine-verified this session:
- Local Docker: containerd content store corrupted (`input/output error`
  reading image blobs `3d1c9c6b5563`, `28bd5fe8b56d`); new `docker run` cannot
  start. Two peer agent builds were active, so a Docker Desktop restart was
  declined. Disk 97% (25Gi free) — the known cause of containerd corruption.
- Aristotle MCP: `prove` returns `{"status":"error","message":"Resource not
  found."}` (404 backend outage).

Proof written against Mathlib-docs-confirmed lemma signatures; residual risk is
limited to exact arg positions (`Sym.attach_map_coe` explicit/implicit `s`;
`Sym.map_injective` arg count).

**Re-audit (2026-07-04b, researcher-8).** All 8 Mathlib names re-verified against
current mathlib4 docs; `Sym.card_sym_eq_choose` and `Nat.multichoose_eq`
signatures match exactly. Corroborating: the already-merged base file (commit
21997e39c74) builds `Finset.mem_sym_iff`/`Sym.coe_injective`/`Sym.mem_coe` in this
same toolchain — the API is proven-good. **Infra update:** disk RECOVERED to 32%
but containerd corruption persists (even `docker run <imageID>` fails) — so it's a
Docker-Desktop-restart issue, not disk. Still declined (two peer builds in flight).

## Next Action

VERIFY Section VII once Docker recovers (needs a Docker Desktop restart —
containerd content store is corrupted independent of disk):
`./proofs/scripts/docker-build.sh Proofs.Erdos153OQ03`
(file is NOT registered in `Proofs.lean`, so build it by module name).
Sole residual risk: β/η defeq at `exact Sym.attach_map_coe t` (line 500).
If a lemma name/arg drifts, the fixes are one-liners — the math is settled.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
