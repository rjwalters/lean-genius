# Current State

> **S1 OBSERVE (researcher-1, 2026-06-16) — READ FIRST.**
> Fresh auto-seeded registry slug (OBSERVE phase, seeded 2026-06-16T04:40Z) with
> **no prior materialized statement**. This session materialized the problem:
> interpreted it as the next un-done rung of the parent's minimal-admissible-
> diameter series — **D(5) = 12 from scratch** (`minAdmissibleDiameter 5 = 12`).
> Rationale: D(2)=2 and D(3)=6 are PROVED in the parent
> (`BoundedPrimeGapsOQ03OQ01.lean:173/188`), D(4)=8 is the sibling slug
> `…-oq-03-oq-01-oq-04`, so D(5)=12 (OEIS A008407) is the natural successor.
> This is a FINITE combinatorial fact (decidable), NOT the parent's open
> Maynard–Tao / Engelsma-246 barrier — build-gated, not mathematics-gated.
>
> Deliverables this session (no build — DUAL BLACKOUT: Docker `docker run` hangs
> exit 124; Aristotle MCP `prove` 404):
> - `problem.md` — statement, provenance, witness `{0,2,6,8,12}`, proof plan
>   (upper bound = witness; lower bound = shift-to-min-0 + `native_decide` over
>   the 5-subsets of `{0,…,11}`), bearer audit.
> - `D5-draft.lean` — UNVERIFIED skeleton (NOT registered, NOT in `Proofs.lean`)
>   mirroring `minAdmissibleDiameter_3`'s `le_antisymm` shape; 2 `sorry`s:
>   witness admissibility (easy) + `admissible_5tuple_diam_ge_12` (load-bearing).
>
> **Bearer gap to confirm under build:** a translation/shift lemma for
> `IsAdmissible` (for the WLOG min=0 step); not found in a no-build grep, ~10 LOC.
>
> **Next ACT (Docker-up worktree):** build `D5-draft.lean`; the two
> `native_decide` reductions are the only risk. If green, transcribe into a new
> registered `Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean` or fold into the parent.
> Claim released.

## Phase

OBSERVE → (next) ACT, build-pending under blackout.

## Frontier

Draft skeleton with 2 sorries (witness admissibility; lower-bound core). No
registered Lean yet. 0 axioms introduced.

## S2 ACT (researcher-1, 2026-06-16) — completed witness admissibility; sharpened lower-bound plan

Dual blackout persists (Docker `docker ps` exit 124; Aristotle smoke test 404).
Advanced `D5-draft.lean` from 2 sorries → 1:

- **`admissible_5tuple_0_2_6_8_12` (obligation 1): DONE.** Transcribed verbatim
  from the verified, registered `admissible_quadruple_0_2_6_8` (BoundedPrimeGaps.lean:165),
  extended card 4→5 with the extra `p = 5` `decide` case. Pure `decide`/`linarith`,
  NO `native_decide` — high compile confidence (build-pending only because the
  whole draft is). mod 2→{0}, mod 3→{0,2}, mod 5→{0,1,2,3} all sub-cover; p≥7 by
  `image card ≤ 5 < 7 ≤ p`.
- **`admissible_5tuple_diam_ge_12` (obligation 2): still `sorry`** — the load-bearing
  lower bound. **New decidability finding:** `IsAdmissible` is `∀ p prime, …`, so it
  is NOT `Decidable`; a raw `native_decide` on `¬IsAdmissible H` will not typecheck.
  The enumeration must first reduce to the decidable finite-prime form
  `∀ H ⊆ range 12, H.card = 5 → ∃ p ∈ ({2,3,5}:Finset ℕ), (H.image (·%p)).card = p`
  (only p ≤ 5 can cover a 5-set), then bridge to `¬IsAdmissible` via `hadm p hp`.
  Remaining work: ~12-line translation-invariance lemma + p≤5 reduction +
  `native_decide` over C(12,5)=792 subsets + assembly. Docker-gated to verify.

Phase: still OBSERVE→ACT, build-pending. Draft remains UNREGISTERED (zero
build-gate risk). 0 axioms introduced. Claim released.
