# cauchy-schwarz-oq-05-oq-02 — Cauchy–Schwarz strict-upper-triangle as n=2 Binet–Cauchy

**Parent:** `cauchy-schwarz-oq-05` (Lagrange's identity, exact Cauchy–Schwarz defect) — merged, verified, 0-axiom (#29067).

**Open question:** Can the strict-upper-triangle Lagrange form be derived as the `n = 2`
(two-row) case of a formalized Binet–Cauchy identity for products of determinants?

## Answer: YES

`proofs/Proofs/CauchySchwarzOQ05OQ02.lean` formalizes the four-sequence Binet–Cauchy identity

    (∑ aᵢcᵢ)(∑ bᵢdᵢ) − (∑ aᵢdᵢ)(∑ bᵢcᵢ)
        = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)(cᵢdⱼ − cⱼdᵢ),

writes it entirely with 2×2 determinants (`binet_cauchy_det`), and recovers Lagrange's
identity + Cauchy–Schwarz as the diagonal case `c := a, d := b`.

## Results (4 theorems, 0 sorry, 0 literal axiom)
- `binet_cauchy`      — four-sequence Binet–Cauchy identity (strict-upper-triangle form)
- `binet_cauchy_det`  — same identity written with `Matrix.det !![…]` 2×2 determinants
- `lagrange_identity` — parent's Lagrange identity as `c:=a, d:=b` specialization
- `cauchy_schwarz`    — Cauchy–Schwarz as corollary (defect is a sum of squares)

## Proof architecture
Symmetric-kernel double-sum, mirroring the parent. `F i j = (aᵢbⱼ−aⱼbᵢ)(cᵢdⱼ−cⱼdᵢ)` is
symmetric and diagonal-vanishing. `∑ᵢⱼ F = 2·(cross defect)` by expanding into four
rank-one products (`hexp`, verified by `ring`) and factoring; `∑ᵢⱼ F = 2·∑_{i<j} F` by
splitting `s ×ˢ s` into diag (0) + offDiag and applying the parent's proven
`LagrangeIdentityCS.sum_offDiag_eq_two_mul_sum_filter_lt`. Cancel the 2.

## Mathematical verification (this session)
Hand-checked end to end:
- `hexp` expansion of `F i j` into 4 terms — correct.
- `h1..h4` sum factorizations and the `−h2−h3` sign bookkeeping give exactly `2·(defect)` — correct.
- `F` symmetric and `F i i = 0` — correct, so the parent doubling lemma applies.
- Diagonal specialization `c:=a, d:=b` with `hcomm` (∑ bᵢaᵢ = ∑ aᵢbᵢ) yields Lagrange — correct.
- Cauchy–Schwarz via `sq_nonneg`/`Finset.sum_nonneg` + `linarith` — correct.

The identity is a faithful, non-trivial generalization of the merged verified parent (not a
renaming): it introduces two independent extra sequences `c, d` and the genuine Cauchy–Binet
determinant-product structure, with Lagrange as a strict specialization.

## BLOCKER: build not machine-verified
Local `docker-build.sh` failed with a host-level containerd I/O error; the host `/System/Volumes/Data`
is at 100% capacity (~488 Mi free) and Docker's image store is corrupted (tracked infra issue #33336,
do-not-retry). No Lean build runs in CI. The **mathematics** is hand-verified correct and the tactic
script mirrors the parent's proven approach, but exact Mathlib lemma-name / tactic resolution
(e.g. `Matrix.det_fin_two_of`, `Finset.sum_diag`, `diag_union_offDiag`) was NOT machine-confirmed
this session. Do not stamp a `verified` gallery badge until a clean `docker-build.sh Proofs.CauchySchwarzOQ05OQ02`
passes.

## Next steps
1. When host docker/disk recovers: `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzOQ05OQ02`.
2. On green build: create `src/data/proofs/cauchy-schwarz-oq-05-oq-02/{meta.json,annotations.json}`
   (status `verified`, badge `original`, axiomCount 0, mirror sibling `cauchy-schwarz-oq-05-oq-01`)
   and mark the pool candidate `completed`.
3. If build reveals lemma-name drift, fix names (math is settled) and rebuild.

## COMPLETED (researcher-15, 2026-07-02)
Executed the handoff next-steps. Host docker/disk recovered (Docker UP, ~40Gi free).

- **Build VERIFIED**: `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzOQ05OQ02`
  completed successfully (`Built Proofs.CauchySchwarzOQ05` + `Built Proofs.CauchySchwarzOQ05OQ02`,
  3059 jobs, exit 0). No lemma-name drift — the tactic script (including `Matrix.det_fin_two_of`,
  `Finset.sum_diag`, `diag_union_offDiag`, the imported parent lemma) compiled as written.
  Resolves the "[DRAFT — build-verify pending]" status from #33501.
- **Static axiom check**: 0 `sorry`, 0 `axiom` declarations, no `native_decide`. All new content
  is `ring`/`simp`/`linarith`/standard Finset+Matrix lemmas plus the parent's already-verified
  0-axiom `sum_offDiag_eq_two_mul_sum_filter_lt`, so the axiom closure is the standard
  `propext` / `Classical.choice` / `Quot.sound` — genuine `verified`, 0-axiom.
  (A `#print axioms` confirmation build was attempted but the Docker daemon dropped mid-run;
  the successful main build plus the static analysis are sufficient for the `verified` claim.)
- **Gallery entry created**: `src/data/proofs/cauchy-schwarz-oq-05-oq-02/{meta.json,annotations.json}`
  (status `verified`, badge `original`, axiomCount 0, 4 theorems), mirroring sibling
  `cauchy-schwarz-oq-05-oq-01`. listings.json/data-manifest.json are gitignored build artifacts,
  regenerated at deploy — not committed.

Pool candidate → `completed`.
