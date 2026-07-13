# S21 STATE-SYNC (Docker-down) — meta-accuracy fix: Fano axiom is discharged

**Researcher**: researcher-1
**Date**: 2026-06-13
**Phase**: STATE-SYNC (doc-only; Docker daemon down → no ACT/build possible)
**Branch**: `research/shannon-oq02oq01-s21-meta-fano-discharge-sync-<ts>`

## §1. Infra preflight

- Disk: `/dev/disk3s1s1` 15% used, **67 Gi free** — RECOVERED (well above 30 Gi build-pending floor; cf. memory `project-disk-full-docker-down-20260613`).
- Docker: `docker info` times out at 8 s (exit 124) — **daemon DOWN/unresponsive**. No Lean build verification is possible this session. ACT (S18a-2 lemma paste + Docker-verify) remains **blocked on infra**, not on math.
- HEAD: `fa1c4d27aa8` (origin/main). S20's cascade-repair fixes are confirmed in HEAD (`Fintype.sum_prod_type` @170, `refine Finset.sum_eq_single` @236, `IsEmpty (α × β)` @304 in `ShannonChannelCodingOQ02OQ01.lean`).
- Race: 0 open PRs on slug (`gh pr list --search "shannon-channel-coding-oq-02-oq-01 in:title" --state open` → empty). Shipped on session-specific branch per `feedback_researcher_shared_branch_bundle_trap`.

## §2. Discovery — the Fano axiom is already discharged; slug meta understated it

The problem's **primary stated goal** (problem.md) is: discharge the `fano_inequality` axiom in `ShannonChannelCoding.lean`. Source inspection shows this is **already done**:

- `proofs/Proofs/ShannonChannelCoding.lean:199` — `fano_inequality` is a `theorem` (not an `axiom`), defined as
  `:= FanoFromConditionalEntropy.fano_inequality_proved pXY hp hsum`.
- That bridge theorem (`ShannonChannelCodingOQ02OQ01.lean:293`) dispatches on `Fintype.card α`:
  `fano_singleton_card_one` (card = 1) and `fano_from_oq03_std` (card ≥ 2, built on OQ-03's `fano_theorem`).
- The parent file's own header (lines 11–18) self-documents: **"Axioms: 3 (channel_coding_achievability, channel_coding_converse, bsc_capacity_eq)"** and lists `fano_inequality` among its **13 theorems**. Parent `meta.json` `axiomCount: 3`.

The route through OQ-03's `fano_theorem` **bypasses** the ShannonEntropy.lean `strong_subadditivity` blocker entirely — that blocker is no longer load-bearing for Fano.

**Stale documentation found** in `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json`:
- `assumptions` claimed Fano "would discharge it once ShannonEntropy.lean's strong_subadditivity is fixed" — a forward-looking blocked framing that is now false.
- `description` framed the ShannonEntropy blocker as "prevent[ing] full axiom elimination" — misleading post-discharge.

## §3. What I did (build-free)

- Corrected the `assumptions` field to state the Fano axiom **is DISCHARGED**, citing the exact source location (line 199), the dispatch route, and the 4 → 3 axiomCount drop.
- Corrected the `description` clause to reflect the discharge via the OQ-03 route (bypassing the ShannonEntropy blocker) instead of describing it as a pending blocker.
- Validated JSON (`json.load` OK). No Lean files touched (Docker down → unverifiable; and no Lean change is needed — the discharge already landed).

Both edits are grounded in the source file's own authoritative self-documentation, so they are safe to land without a build.

## §4. Files modified

- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (`assumptions` + `description` accuracy)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-06-13-s21-statesync-docker-down-meta-fano-discharge.md` (this memo)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` (Current State header + this entry)

## §5. Next steps (unchanged math, gated on Docker)

- **S22 ACT (Docker-up required)**: paste the S17 PREP §6.2 capacity bundle — `DMChannel.IsWeaklySymmetric` def + `output_marginal_uniform_of_uniform_input_and_column_sum_const` (S18a) + `row_entropy_invariant_under_input` (S18b), then `uniform_input_achieves_capacity_of_weakly_symmetric` (S18c, carries one `sorry` on the conditional-entropy chain). NOTE: these target `DMChannel`/`channelMI`/`channelCapacity`, which live in the **parent** `ShannonChannelCoding.lean`, not in `ShannonChannelCodingOQ02OQ01.lean`. Re-pin the insertion point in the parent file before pasting (the S17 "line 466" pin predates the parent-file edits).
- This capacity bundle is aimed at the **remaining** axioms (`bsc_capacity_eq`, `channel_coding_achievability`), a separate thread from the now-complete Fano goal.
