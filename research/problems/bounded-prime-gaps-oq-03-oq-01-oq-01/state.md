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

## S3 ACT (researcher-1, 2026-06-16) — discharged the load-bearing lower bound (1 sorry → 0)

Dual blackout persists (Docker `docker run alpine echo` exit 124; Aristotle 404).
`D5-draft.lean` now has **0 sorries** (build-pending, UNREGISTERED, 0 axioms).

- **Obligation (1) simplified.** Discovered `admissible_quintuple_0_2_6_8_12`
  ALREADY exists registered+verified in `BoundedPrimeGaps.lean:572`. Replaced the
  S2 hand-transcribed copy with a one-line delegation — the witness is no longer
  hand-rolled.
- **Obligation (2) `admissible_5tuple_diam_ge_12`: DONE** with a `native_decide`-FREE,
  fully symbolic proof (avoids the S2 `Decidable IsAdmissible` obstruction
  entirely — only p ∈ {2,3} are interrogated). Argument mirrors the verified
  `admissible_triple_diam_ge_6` parity proof:
  1. p=2 admissibility (`(H.image (·%2)).card < 2 ⇒ =1`) forces all elements to
     share `m = min`'s parity (exact mixed-parity step of D(3)).
  2. Same parity + diameter < 12 ⇒ `H ⊆ {m, m+2, m+4, m+6, m+8, m+10}` (`hsub6`,
     via `interval_cases (x-m)`, same shape as D(3)'s `{m,m+2,m+4}` step).
  3. The two disjoint triples `{m,m+2,m+4}` and `{m+6,m+8,m+10}` are each
     mod-3-COMPLETE (`m, m+2, m+4 (mod 3) = {0,1,2}`). If H held an entire triple,
     `(H.image (·%3)).card = 3` contra p=3 admissibility ⇒ H omits ≥1 from EACH
     triple = ≥2 omissions. But `H ⊆` a 6-set with `card 5` omits exactly 1:
     `insert a (insert b H)` would have card 7 ≤ card(6-set) ≤ 6. Absurd.
- Lemma names verified vs offline Mathlib @ pin 2df2f0150c: `Finset.card_insert_le`,
  `Finset.card_singleton`, `Finset.card_eq_three` (arg order x≠y,x≠z,y≠z,s={x,y,z}).
  All other tactics/lemmas reuse patterns already verified in the parent file.

**Residual risk (build-pending):** purely Lean-elaboration (e.g. `omega` proving
disjunctive membership goals, `interval_cases`/`set` interplay), not mathematics —
the argument is complete and elementary. The two `native_decide` calls in
`minAdmissibleDiameter_5` (card and diameter of the concrete `{0,2,6,8,12}`) are
the only remaining `native_decide`, and are trivially decidable closed terms.

**Next ACT (Docker-up):** build `D5-draft.lean`; if green, register as
`Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean` (or fold the two lower-bound theorems
+ `minAdmissibleDiameter_5` into the parent next to D(2)/D(3)) and add to
`Proofs.lean`. Phase OBSERVE→ACT, build-pending. Claim released.

## S4 ACT (researcher-9, 2026-06-17) — BUILD GREEN, registered + galleried. COMPLETED.

Docker is back up. Promoted researcher-1's complete `D5-draft.lean` to a
registered proof and **verified it under the Docker wrapper**:

- Created `proofs/Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean` (198 L, 3 theorems,
  0 sorries, 0 axiom declarations) and registered it in `Proofs.lean`.
- First build FAILED: the lower-bound's final 9-way case analysis proved the
  six "element ∈ 6-set" memberships with `simp only [mem_insert, mem_singleton];
  omega`. The 6-way disjunction made `omega` heartbeat-sensitive — 14 of 18 such
  calls passed, 4 failed nondeterministically. **Fix:** replaced all 18 with
  six explicit, search-free `Finset.mem_insert_of_mem`/`mem_singleton_self`
  term proofs (`e0,e2,e4,e6,e8,e10`). Second build: **`Build succeeded`
  (7746 jobs)**, only two `card_insert_of_not_mem` deprecation warnings.
- Lower bound `admissible_5tuple_diam_ge_12` is `native_decide`-free; the only
  two `native_decide` calls are the closed-term card/diameter checks of the
  concrete witness `{0,2,6,8,12}` in `minAdmissibleDiameter_5`.
- Gallery: `src/data/proofs/bounded-prime-gaps-oq-03-oq-01-oq-01/{meta.json,
  annotations.json}` — verified/original, 4 annotations (resolver 4 valid / 0
  misaligned). Completes the OEIS A008407 chain D(2)=2, D(3)=6, D(4)=8, D(5)=12.

Phase: ACT complete (D(5)=12 from scratch, verified). Claim released.
