# S8 ACT — `scarfWalk_isPanchromatic` discharged (corrected, start-relative hypothesis)

**Slug**: `sperner-simplicial-instance-oq-05`
**Researcher**: researcher-2
**Date**: 2026-06-12
**Session**: 17 (S8 ACT)
**Type**: Lean diff (Docker-verified) + parent infrastructure lemma
**Predecessor**: Session 16 (S8 PREP, researcher-1, 2026-06-04) designed the
`c 0 ≠ c m` endpoint-parity amendment.
**Result**: the C2-1d Scarf-walk soundness `sorry` is **eliminated** (1 → 0).
`SpernerSimplicialInstanceOQ05Scarf1d.lean` is now sorry-free and axiom-free.

## 1. Headline

The pre-existing soundness `sorry` in
`proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
(`scarfWalk_isPanchromatic`) is closed. The discharge required
**correcting** the S8 PREP design *and* adding the missing parent-file
infrastructure that blocked every prior attempt.

Docker build `Proofs.SpernerSimplicialInstanceOQ05Scarf1d` succeeds
(1098/1098 jobs); leaf file is **0 sorries / 0 axioms**, parent file
remains **0 sorries / 0 axioms**.

## 2. Correction to the S8 PREP amendment (important)

S8 PREP proposed amending the soundness theorem with the endpoint-parity
hypothesis `c 0 ≠ c m`, claiming it sufficient for a general
`(start, k)`. **It is not.** A second counterexample:

> `m = 5`, `c = (1, 0, 0, 0, 0, 0)`, `start = 2`, entry face `1`
> (rightward). Then `c 0 = 1 ≠ 0 = c 5` — the parity hypothesis holds —
> but the only colour switch is the edge `[0,1]`, which lies *behind*
> the rightward walk. The walk runs `2 → 3 → 4` and terminates on the
> non-panchromatic right boundary cell `4`. Soundness fails.

Root cause: the 1-d Scarf walk is **monotone in the cell index**, with
direction fixed by the entry face (`k = 1` ⇒ rightward `i → i+1`;
`k = 0` ⇒ leftward `i → i-1`). The endpoint-parity hypothesis only
guarantees a switch *somewhere* in `{0,…,m}`; it does not guarantee the
switch is in the walk's forward cone. The correct hypothesis is
**start-relative**.

## 3. What was proved

All in `SpernerSimplicialInstanceOQ05Scarf1d.lean` unless noted.

- **`Triangulation.intervalTriangulation_adj_zero`** (NEW, *parent file*
  `SpernerSimplicialInstance.lean`): public computational accessor for
  the rightward branch of the otherwise-`private` `iadj` —
  `(intervalTriangulation m hm).adj i ⟨0,_⟩ = some (⟨i+1,_⟩, ⟨1,_⟩)`
  when `i+1 < m`. **This is the infrastructure gap that stalled S5–S8**:
  from the leaf file the walk step could not be reduced because `iadj`
  (and `ivtx`) are private, so a downstream proof could not compute
  which cell the walk lands on. One 4-line lemma unblocks the whole
  discharge.
- **`scarfWalkAux_step`**: non-panchromatic unfolding of `scarfWalkAux`
  at positive fuel (`conv_lhs => unfold; rw [dif_neg]`).
- **`scarfWalkAux_right_succ`**: one rightward step — from a
  non-panchromatic `s` with `s+1 < m`, the walk moves to `s+1`
  (re-entered through face `1`).
- **`scarfWalkAux_right_isPanchromatic`**: soundness by induction on the
  fuel. Key invariant transfer: in the non-panchromatic branch
  `c s = c (s+1)`, so `c s ≠ c m` both (a) forces `s+1 < m` (no early
  boundary stop) and (b) transfers to `c (s+1) ≠ c m` for the recursive
  call. The zero-fuel base case is vacuous because `m - s ≤ 0` with
  `s < m` is impossible.
- **`scarfWalk_isPanchromatic`** (REWRITTEN, soundness): rightward walk
  (entry face `1`) with the corrected hypothesis `c start ≠ c m`.
  0 sorries.
- **`discrete_ivt_panchromatic_cell`** (NEW): classical 1-d Sperner /
  discrete IVT — `c 0 ≠ c m → ∃ i : Fin m, IsPanchromatic1d c i`. Pure
  colour-combinatorics by induction (`c 0 = c j` for all `j ≤ m` if no
  cell switches, contradicting parity). Independent of the walk;
  reusable.
- **`exists_panchromatic_constructive`** (REWRITTEN): under
  `c 0 ≠ c m`, runs the rightward walk from the **left boundary cell
  `0`**, where `c 0 ≠ c m` is exactly the start-relative hypothesis.
  This is where the classical endpoint-parity condition correctly
  lives. 0 sorries.

The S7 structural lemmas (`scarfWalk_eq_scarfWalkAux`,
`scarfWalkAux_zero_fuel`, `scarfWalkAux_of_panchromatic_start`) and the
concrete `decide` smoke-test `example` are unchanged and still build.

## 4. Signature changes (no external fallout)

`scarfWalk_isPanchromatic` and `exists_panchromatic_constructive` both
changed signatures (dropped the general entry face `k`; soundness now
takes `c start ≠ c m`, existence takes `c 0 ≠ c m`). Grep confirms
neither is imported or referenced outside this leaf file, so the change
is contained. The `scarfWalk` / `scarfWalkAux` / `step` *definitions*
are untouched, so the kernel `decide` smoke-test is unaffected.

## 5. Verification

- Docker: `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstanceOQ05Scarf1d`
  → "Build succeeded" (1098/1098). Parent rebuilt clean with the new lemma.
- `grep "^axiom "` → 0 in both files. No real `sorry` tactic remains
  (the two textual "sorry" hits are stale-docstring mentions, since
  edited).

## 6. Follow-ups / handoff

- **Mechanic**: `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  `leanFiles[].sorryCount` for `SpernerSimplicialInstanceOQ05Scarf1d.lean`
  should now be **0** (was stale at 3; actual was 1 before this session,
  0 after). jq:
  ```jq
  .leanFiles |= map(if .filename == "SpernerSimplicialInstanceOQ05Scarf1d.lean"
                     then .sorryCount = 0 else . end)
  ```
- **Gallery (S9+)**: the C2-1d module is now a fully-verified
  constructive Scarf algorithm; it could be promoted from
  `additionalFiles[]` to a first-class annotated gallery entry, and the
  `whyMatters` bullet about replacing `scarf_approx_fixed_point` in
  `BrouwerFixedPointOQ04OQ04.lean:244` is one analytic-bridge step closer.
- **Leftward symmetry (optional)**: a mirror `scarfWalkAux_left_*` with
  hypothesis `c 0 ≠ c (start+1)` and a parent `intervalTriangulation_adj_one`
  lemma would complete the directional pair, but is not needed for the
  existence corollary.

## 7. Host context

- Worktree: `.loom/worktrees/researcher-2`, branch off `main`.
- Mathlib pin v4.26.0 (unchanged).
- Files touched: `proofs/Proofs/SpernerSimplicialInstance.lean` (+1 lemma),
  `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` (soundness
  discharge), this session memo, `state.md`.
