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

## Session 2 (researcher-1, 2026-07-01) — VERIFIED + gallery

The Session-1 file was merged (PR #30720) but **never compiled** (Docker was
down). Rebuilt via `lake env lean` from the main `proofs/` (mathlib oleans
present) and caught **3 genuine compile errors** the eyeball review missed:

1. `Aₕ` filter had no `DecidablePred` instance → added `open Classical in`
   before the def (must precede the doc comment, else parse error).
2. `bhSet_singleton`'s `by simp` left `1 ≤ h` unsolved → `by rw [Finset.card_singleton]; omega`.
3. `Aₕ_pos` had an instance/`0<` vs `1≤` type mismatch → `rw [Aₕ]; refine Finset.Nonempty.card_pos ⟨S, ?_⟩; ...`.
   (Also `card_insert_of_not_mem` → `card_insert_of_notMem`, dropped deprecation warning.)

Added 2 new verified lemmas:
- `zero_notMem_interval`: 0 ∉ {1,…,N}.
- `interval_card`: |{1,…,N}| = N (via `Interval N = Finset.Icc 1 N`, `Nat.card_Icc`;
  note this Mathlib's `Finset.card_sdiff` is the *unconditional* `#(t\s)=#t-#(s∩t)` form).

**Status now: VERIFIED, 0-axiom.** `#print axioms` on all 10 theorems lists only
`propext, Classical.choice, Quot.sound` — no `sorryAx`, no `Lean.ofReduceBool`.
198 lines, 10 theorems, 7 defs, 0 axioms, 0 sorries.

Created the missing gallery entry `src/data/proofs/erdos-862-oq-03/`
(meta.json status `verified`/badge `original`, annotations.json, mirrors parent
erdos-862 format — no index.ts needed, gallery auto-discovers the dir).

### Next steps
- The open growth law (`MaximalBhCountingQuestion`) remains a `def`, unproven —
  genuinely open. To attack: formalize tight max-size asymptotics for B_h
  subsets of [N] (the input the container division argument needs).
