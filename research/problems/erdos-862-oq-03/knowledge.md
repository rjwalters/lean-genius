# erdos-862-oq-03 — Maximal B_h set counting (h ≥ 3)

Parent: erdos-862 (Maximal Sidon = B₂ subset counting; solved by
Saxton–Thomason 2015, A₁(N) ≥ 2^{(0.16+o(1))√N} via hypergraph containers).

**OQ-03 statement:** extend the counting theory to maximal B_h subsets of
{1,…,N} for h ≥ 3. The asymptotic growth of the maximal-B_h count is
**genuinely OPEN** in the literature (container method applies but the
hypergraph is (2h)-uniform and B_h size asymptotics are imprecise for h ≥ 3).

## Session 1 (researcher-1, 2026-06-27)

Built the **counting framework** + verified, axiom-free structural lemmas in
`proofs/Proofs/Erdos862OQ03Problem.lean`. Did NOT (and cannot) resolve the
open growth law — recorded it as a `def MaximalBhCountingQuestion`, unproven.

Verified content (0 sorry, 0 axiom by construction):
- `IsBhSet h S` (natural element-sum reading): every h-element subset has a
  distinct sum.
- `bhSet_subset`: B_h is hereditary (subset-closed).
- `bhSet_of_card_le` / `bhSet_empty` / `bhSet_singleton`: ≤ h elements ⇒ B_h.
- `sidon_imp_b2`: parent's `IsSidonSet S → IsBhSet 2 S` (bridge to #862).
- `exists_maximal_bhSet`: a maximal B_h subset of [N] always exists
  (max-cardinality B_h subset is maximal — finite analogue of the Zorn step).
- `Aₕ_pos`: counting function `Aₕ N h ≥ 1`, so it is well-defined.

### BLOCKER (infra, not math)
Could NOT machine-verify this session: host Docker build environment is down —
`/System/Volumes/Data` at 100% (≈800Mi free) and containerd content store is
corrupted (blob I/O errors on `docker build`/`prune`). `./proofs/scripts/
docker-build.sh` fails before compiling. File is eyeball-reviewed and uses only
standard Mathlib lemmas (`Finset.exists_max_image`, `Finset.eq_of_subset_of_
card_le`, `Finset.card_eq_two`, `Finset.sum_pair`, `Finset.insert_subset`,
`Finset.card_insert_of_not_mem`, `Finset.Nonempty.card_pos`), but treat as
**UNVERIFIED** until built. PR opened as DRAFT to avoid auto-merge.

### Next steps
- Rebuild once host disk/Docker restored; fix any compile errors; un-draft.
- If verified: add gallery `src/data/proofs/erdos-862-oq-03/` (status
  axiomatized? no — file is 0-axiom; the OPEN law is a `def` not a claim, so
  status `verified`/badge `original` for the framework lemmas is defensible).
