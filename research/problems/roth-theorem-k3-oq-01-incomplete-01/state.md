# Research State: roth-theorem-k3-oq-01-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-01T00:00:00Z (S3 ACT REPAIR-DISCOVERY this PR)
**Iteration**: 3

## Current Focus

**S3 ACT REPAIR-DISCOVERY (researcher-1, 2026-06-01)** — STATE-SYNC
plus a fresh-build Docker audit of
`proofs/Proofs/RothTheoremQuantitative.lean`. The session began as a
small-N enumeration ACT (target: `r₃(4) ∈ [2, 3]` bounds). When I ran
`./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative` to
verify the additions, the build surfaced **six distinct compile
failures** in the file *as it sits on `main`* (i.e., independent of my
additions). After investigation, all six trace back to two root causes
that are not addressable in a single small-N enumeration ACT, so this
S3 ACT pivots to discovery + state-sync.

### Findings (file as it sits on `main`, fresh Docker build, no cache)

1. **Mathlib v4.26.0 API drift**: `div_lt_iff` (line 174) and
   `div_le_iff` (line 218) were renamed to `div_lt_iff₀` /
   `div_le_iff₀` in Mathlib v4.26.0 (commit `2df2f0150c`). Both are
   simple drop-in renames (same signature `(0 < c) : b / c ≤ a ↔ b ≤
   a * c`).

2. **Math bug in `max_iterations_bound`** (line 195–212): the
   statement `δ + kδ²/100 > 1 → k > ⌊100/δ²⌋₊` is **false** for
   `δ > 1`. Counterexample: `δ = 2, k = 0` gives `δ + 0 = 2 > 1` ✓
   but `⌊100/4⌋₊ = 25 ≥ 0 = k`. Algebraically the correct contrapositive
   from `δ + kδ²/100 > 1` is `k > 100(1 - δ)/δ²` (strictly weaker than
   `100/δ²` whenever `δ > 0`). The previous `linarith` proof appeared
   to close on an older Mathlib snapshot but in fact relied on the
   now-removed `div_le_iff` lemma whose elaboration drift masked the
   underlying mathematical gap. The companion lemma
   `iterations_before_contradiction` (line 214) was a downstream
   consumer.

3. **`rothNumber_three` `simp_all` timeout** (line 134): the proof
   `fin_cases a <;> fin_cases d <;> simp_all` over `Finset (ZMod 3)`
   (9 subcases) exceeds the default 200 000 heartbeat budget in a
   fresh build. Cached lake builds skip re-verification, which is
   why merged CI on PR #21520 didn't flag it.

4. **`rothNumber_achieved` type mismatch** (line 118): `Finset.mem_filter.mp`
   leaves a metavariable `?m.52 = ?` that the elaborator can't pin to
   `filter APFree` without a hint. Likely needs an explicit type
   annotation on the `set S := ...` line or an `(· : Finset (ZMod N))`
   ascription.

### Decision

REVERT the small-N enumeration additions (they sat on top of broken
code and shouldn't be merged in isolation). Ship only the state.md /
JSON updates documenting the regressions. The full repair belongs to
a dedicated REPAIR session (or a paired-fix PR that bundles the
small-N enumeration with the four repairs above and a Docker-verified
fresh build).

### Pre-2026-06-01 STATE-SYNC

The slug's `state.md` had been stuck at "OBSERVE iteration 1" since
2026-04-03 despite a successful S2 contribution merged on 2026-05-31
via PR #21520 (`rothNumber_div_tendsto_zero` qualitative asymptotic).
The JSON's `currentState` had already moved to iteration 2 / ORIENT,
but state.md was unaware. This S3 ACT also brings state.md into sync
with the JSON.

## Prior Focus (S2 contribution merged 2026-05-31, PR #21520)

S2 (researcher unknown — pre-S3 STATE-SYNC) shipped the qualitative
asymptotic `rothNumber_div_tendsto_zero : Tendsto (n ↦ rothNumber n / n)
atTop (𝓝 0)` to `proofs/Proofs/RothTheoremQuantitative.lean` (lines
156–207 as of f486a19). Proof reduces to `Szemeredi.Roth.roth_density_bound`
via the corners-theorem chain. **PR #21520 merged with a green CI
that relied on Lake's incremental cache; rebuilding the file from a
clean state on Mathlib v4.26.0 surfaces the four issues above.**

## Prior Focus (S1 OBSERVE, 2026-04-03)

Initial problem understanding from problem.md. The Lean file
`RothTheoremQuantitative.lean` has 4 landmark sorries remaining
(Roth 1953, Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023),
each requiring ≥ 1000 LOC of formalization. None tractable in a
single session. Tractable adjacent contributions identified:
qualitative asymptotic + small-N exact values.

## Active Approach
Small-N enumeration → blocked on pre-existing build regressions.
S4 should be a REPAIR session (or paired-fix PR) to restore the
file to a fresh-rebuild-green state before resuming small-N
enumeration.

## Attempt Count
- Total attempts: 3 (S1 OBSERVE, S2 ACT qualitative, S3 ACT REPAIR-DISCOVERY)
- Current approach attempts: 1
- Approaches tried: 3 (initial OBSERVE, qualitative ACT, REPAIR-DISCOVERY)

## Blockers
`RothTheoremQuantitative.lean` fails fresh Docker build on Mathlib
v4.26.0 due to API drift + 1 math bug + 1 `simp_all` heartbeat
overshoot + 1 type-inference issue (4 root causes, 6 surfaced
errors). S4 needs to be a dedicated repair session.

## Next Action

**S4 ACT REPAIR (recommended)** — a focused repair PR:

1. Rename `div_lt_iff` → `div_lt_iff₀` at line 174 and
   `div_le_iff` → `div_le_iff₀` at line 218.

2. Either remove `max_iterations_bound` + `iterations_before_contradiction`
   as mathematically-incorrect dead code (no callers in the repo),
   OR restate them with `(hδ : δ ≤ 1)` and the corrected bound
   `k > 100(1 - δ)/δ²`.

3. Add `set_option maxHeartbeats 400000 in` (or hoist the membership
   `simp` to a separate helper) for `rothNumber_three` to fit the
   `fin_cases a <;> fin_cases d <;> simp_all` proof within budget on
   fresh builds.

4. Fix `rothNumber_achieved`: add a `(S : Finset (Finset (ZMod N)))`
   annotation on the `set` line, OR refactor to `Finset.exists_max_image`
   with explicit type arguments, so `Finset.mem_filter.mp hAS` resolves
   `filter APFree` cleanly.

5. Docker-verify the file builds clean from a fresh image.

Once S4 REPAIR ships, **S5 ACT SMALL-N** can resume the original
plan: `r₃(4) ∈ [2, 3]` via `apFree_zero_one_zmod_four`,
`two_le_rothNumber_four`, `rothNumber_four_le_three`. The proofs
themselves are simple (≤ 30 LOC) and were drafted in this session;
they just can't ship on a broken base.

The four landmark sorries (`roth_quantitative_upper_bound`,
`behrend_lower_bound`, `bloom_sisask_bound`, `kelley_meka_upper_bound`)
remain multi-PR research efforts.
