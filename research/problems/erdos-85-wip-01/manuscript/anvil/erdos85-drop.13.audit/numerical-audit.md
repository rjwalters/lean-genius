# Numerical audit: erdos85-drop.13

Pinned source: `2029149d7e42b74036ff0e1e82af6d33c2e32748`. Reads used `git show 2029149d7e42:<path>` or a `git archive` extract of the pin in scratch. `RP` = `research/problems/erdos-85-wip-01`. No Lean build, Lean compilation, `lake` invocation, SAT replay or cloud compute was run.

## Scope of change v12 to v13

`diff erdos85-drop.12/main.tex erdos85-drop.13/main.tex` adds no number and removes none. Every number, count and size in v13 also appears in v12, which the v12 audit traced against the v12 pin `fa2b41268df` (see `erdos85-drop.12.audit/numerical-audit.md`). The new pin differs from `fa2b41268df` only in six record or script files, with no Lean, receipt-table or JSON evidence change. So the v12 traces carry over unchanged to the new pin. `scope_lint.py` re-traced every number with 4+ digits and every decimal-with-unit against the refs corpus. It passes both without `--proofs` and with `--proofs <pin>/proofs/Proofs` (38 numbers, 46 Lean names).

## New or reworded factual claims in v13 (fresh checks)

| Text claim (main.tex line) | Source at pin | Source value | Match | Notes |
|---|---|---|---|---|
| Availability: "at commit `2029149d7e42`" (L274) | `\repocommit` (L32); `git ls-remote` | full hash `2029149d7e42b740...`; branch head of `erdos85/release-assembly-20261011` | yes | v12 C1 resolved. `\repocommitshort` is a hand-written literal, not derived from `\repocommit`. It matches today; see the non-critical note in flags.md. |
| Read-only audit of the retained output "repeated independently by a second AI author" (L113) | `RP/release_cold_build_20261011/ACCEPTED.md` (final paragraph); squad `review_requests` row 2749 (read-only query of the room DB) | ACCEPTED: "Independent re-audit (Codex, squad review #2749, PASS, 2026-10-12): reran `audit.py` on the retained bundle (893 sources, exact 601/607/604, same RUN.json sha256), rehashed the archive ..., checked ... 2,692-file manifest ..." Room row 2749: requested_by `claude`, claimed and resolved by `codex` at 2026-10-12T14:34:05Z, resolution "PASS ... Independently reran audit.py: 893 sources, exact 601/607/604, RUN SHA fba3a248...; Rehashed 2,389,485,055-byte archive: 842425345d6a...; checked exact 2,692-file manifest coverage ..." | yes | v12 M1 resolved. The ACCEPTED.md summary matches the primary room record. The re-audit re-ran the same author-written `audit.py` and added independent rehash and manifest checks. "Repeated" is accurate; it is not an independently implemented checker. |
| "A further cold rebuild" (L113) | third-party `ACCEPTED.md` | job `20261012T143935-...`; 893/893; byte-identical objects (893) vs attempt 2; axiom lists 601/607/604 | yes | Wording fix for the v12 minor note. |
| "The September 2026 cold axiom audit (pinned Lean 4.31.0 image, fresh build volume)" printed three per-declaration `native_decide` axioms per witness, beyond the standard three; Theorem B standard-only in the same audit (L95, Table 2 row 1, L238) | `RP/AXIOM_AUDIT_COLD_20260927/AXIOM_AUDIT_COLD_20260927.md` and `axioms.out` (byte-identical to `erdos85-drop/refs/` copies) | image `lean4-arm64:v4.31.0` digest `a5ca6c4e...`, Lean 4.31.0; fresh Docker volume `lean-e85-cold-20260927`; `boza48Graph*` ×3 and `orderFortyNineDegreeSixGraph*` ×3 `._native.native_decide.ax_*`; `not_erdos85Question_of_binarySquareRegularExclusion` → `[propext, Classical.choice, Quot.sound]` | yes | Re-attribution from v12's ambiguous "a cold rebuild" to the September audit. The record header still reads "SINGLE-SEAT (claude), Sol re-audit pending". The output is byte-identical (sha256 `53192372...`) to the 2026-09-16 overlay readout (`AXIOM_AUDIT_OVERLAY_20260916.md`), which was run from a `sol1` input file. Non-critical note in flags.md. |
| "Every arrow is a dependency of Theorem B and was compiled in the September 2026 cold axiom audit" (L238) | same record | build targets `Proofs.Erdos85BinarySquareRegularCapstone` + witnesses, 8,680 jobs, fresh volume for project modules | yes | |
| Table 2, H7 t≥1: "replayed from the published files in the October 2026 cold rebuild" (L225) | cold-build README/PLAN (13 artifacts hash-pinned to `strata-lrat.MANIFEST.sha256`); third-party fetch log | as in v12 audit | yes | Moved from the "Open" column to "How it is checked" (v12 minor note addressed). |
| Output bundle "2.39 GB ... retained outside the repository and is not published" (L282) | `ACCEPTED.md` at pin | 2,389,485,055 bytes; "retained on the project's artifact volume, not published" | yes | |
| Fetch script "exercised end to end only with credentials of the bucket owner's account"; "authenticated credentials" (L282) | `proofs/scripts/fetch-h7-certificates.sh` at pin; third-party `ACCEPTED.md`/`THIRDPARTY.md` | script: "authenticated AWS credentials are needed (tested so far only with credentials of the bucket owner's account)"; ACCEPTED: "the fetch ran under the bucket owner's AWS account; access from a separate AWS account is still untested" | yes | The script comment is now aligned (v12 non-critical note resolved). |
| FAILURE.md "records the earlier failed attempt" (L113, L282) | `FAILURE.md` at pin | new banner: "Superseded. This records attempt 1 only. The corrected attempt 2 completed and was accepted; see ACCEPTED.md." | yes | |
| Date "12 October 2026" (L60) | ACCEPTED (attempt 2 exit about 08:08 UTC 12 Oct); third-party run 12 Oct | consistent | yes | |

## Spot re-checks of carried values at the new pin

- 893 modules; 601 = 3 + 598, 607 = 3 + 604, 604 = 3 + 601: ACCEPTED.md at pin (unchanged bytes for these lines).
- Thirteen packed files, 2,574,916,357 bytes (about 2.57 GB): fetch-script header at pin.
- 12,094 + 1,160 + 96 + 1 = 13,351; 13,541 − 190 = 13,351; 28 + 377,776 = 377,804: arithmetic re-checked.

## Figures

There are no `\includegraphics` and no `figures/` directory, so no stale-figure check applies.

## Mismatches

None.
