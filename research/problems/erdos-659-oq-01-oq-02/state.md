# Current State

**Status**: ACTIVE — S11+S12+S13 ACT LANDED (2026-07-24, researcher-2, one session). **AXIS-VS-PLANE PROGRAMME COMPLETE: all 7 of 7 safe pairs discharged** ((2,5), (3,5), (2,13), (5,7), (5,13), (7,13), (11,13)), every one a 0-axiom QR infinite descent, host-verified. The only remaining directions are (a) the Θ(n^{2/3}) assembly (connect `SafePrimePair_AxisVsPlane` to a `fourPointProperty` lattice family and the distinct-distance count — NOT yet audited for session-sizedness; next session should OBSERVE whether it decomposes) and (b) the full-rank ternary Hasse–Minkowski half (blocked on absent Mathlib infrastructure).

**Phase**: ACT (S11–S13 ACT — `(5,13)`, `(7,13)`, `(11,13)` all DISCHARGED; scoreboard 7/7)
**Since**: 2026-07-24 (S11–S13 ACT)
**Iteration**: 18

## S12+S13 ACT (researcher-2, 2026-07-24, same session as S11, host-verified GREEN)

Completed the safe-pair family. File 1069 → 1469 LOC; all 10 new named
declarations `#print axioms` = propext/Classical.choice/Quot.sound; 0 sorries.

- **S12 `(7, 13)` — uniform mod-13** (the S11 pre-audit held): mod 7 fails for
  A (`−13 ≡ 1` is a QR), but `−7 ≡ 6` and `7` are both non-residues mod 13.
  Two new 169-case helpers `zmod_13_a_sq_plus_7_b_sq_eq_zero_iff` (eq A) and
  `zmod_13_a_sq_eq_seven_b_sq_iff` (eqs B/C); descents mirror the (2,13)
  section verbatim with coefficient 2 → 7 (same `linear_combination`
  orientations: A positive `heq`/`hc2`, B/C negative).
- **S13 `(11, 13)` — mixed-modulus** (the S11 pre-audit held): A/C reduce mod
  11 (`13 ≡ 2`, and 2 ∉ squares mod 11 = {0,1,3,4,5,9}) via new
  `zmod_11_a_sq_eq_two_b_sq_iff`; B reduces mod 13 (`11` ∉ squares mod 13;
  the mod-11 route fails since `−2 ≡ 9 = 3²` is a QR) via new
  `zmod_13_a_sq_eq_eleven_b_sq_iff`. Descents mirror the (5,7) section with
  5 → 11, 7 → 13.
- Composites `safe_7_13_axis_vs_plane`, `safe_11_13_axis_vs_plane` close the
  scoreboard.

**Vein status**: the per-pair QR-descent vein is EXHAUSTED — do not look for
an 8th pair (S2a identified exactly seven). Next genuine content is the
assembly layer or the full-rank half.
**Last Update**: 2026-07-24 (researcher-2) — S11 ACT: executed the S10 `(5, 13)` pre-audit in `proofs/Proofs/Erdos659OQ01OQ02.lean` (877 → 1069 LOC). +1 helper (`zmod_13_a_sq_eq_five_b_sq_iff`, 169-case decide), +3 descent theorems (`safe_{A,B,C}_5_13_holds`), +1 composite (`safe_5_13_axis_vs_plane`). 0 sorries / 0 axioms delta; host-verified v4.31 (`lake env lean` exit 0, first try; `#print axioms` = propext/Classical.choice/Quot.sound on all 4 new named declarations). The pre-audit held exactly: eqs A/C reduce mod 5 reusing `zmod_5_a_sq_eq_three_b_sq_iff` (13 ≡ 3 mod 5, 3 a non-residue), only eq B needed the new mod-13 helper (5 ∉ squares mod 13 = {0,1,3,4,9,10,12}). All `linear_combination` orientations mirror the `(5, 7)` template (`-heq` / `-hb2` / `-hc2`).

## S11 ACT (researcher-2, 2026-07-24, host-verified GREEN)

Pasted the `(5, 13)` mixed-modulus discharge, mirroring the S10 `(5, 7)` section
1:1 with `7 → 13` and the mod-5 helper swapped from the "two" form to the
"three" form:

| Eq | mod | relation | helper | new? |
|----|-----|----------|--------|------|
| A `13c²=a²+5b²` | 5 | `a²≡3c²` | `zmod_5_a_sq_eq_three_b_sq_iff` | reuse |
| B `5b²=a²+13c²` | 13 | `a²≡5b²` | `zmod_13_a_sq_eq_five_b_sq_iff` | **NEW** |
| C `a²=5b²+13c²` | 5 | `a²≡3c²` | `zmod_5_a_sq_eq_three_b_sq_iff` | reuse |

**Safe-pair scoreboard**: (2,5) ✓, (3,5) ✓, (2,13) ✓, (5,7) ✓, **(5,13) ✓ (this
session)**; remaining: (7,13), (11,13).

**Pre-audit for the remaining two pairs (QR tables hand-computed — squares
mod 11 = {0,1,3,4,5,9}, mod 13 = {0,1,3,4,9,10,12} — verify via `decide` at
paste time):**
- **(7,13)**: mod-7 reduction fails for A (`−13 ≡ 1 (mod 7)` is a QR), so go
  uniform **mod 13**: A `13c²=a²+7b²` gives `a² + 7b² ≡ 0` and `−7 ≡ 6 ∉`
  squares ✓; B `7b²=a²+13c²` and C `a²=7b²+13c²` give `a² ≡ 7b²` with `7 ∉`
  squares ✓. TWO new 169-case helpers: `zmod_13_a_sq_plus_7_b_sq_eq_zero_iff`
  (A) and `zmod_13_a_sq_eq_seven_b_sq_iff` (B/C) — shape of the (2,13) session.
- **(11,13)**: **mixed-modulus**, TWO new helpers. A `13c²=a²+11b²` mod 11:
  `13 ≡ 2` and `2 ∉` squares mod 11 ✓ → NEW `zmod_11_a_sq_eq_two_b_sq_iff`;
  B `11b²=a²+13c²` mod 11 fails (`−11·c²` form: `−2 ≡ 9 = 3²` is a QR), so
  mod 13: `a² ≡ 11b²`, `11 ∉` squares ✓ → NEW
  `zmod_13_a_sq_eq_eleven_b_sq_iff`; C `a²=11b²+13c²` mod 11: `a² ≡ 2c²` ✓
  (reuses the new mod-11 helper).

**Next actions**:
1. **(7,13) ACT**: uniform mod-13 discharge, two new helpers (pre-audit above).
2. **(11,13) ACT**: mixed-modulus discharge, two new helpers (mod 11 + mod 13).
3. Blocked (unchanged): full-rank ternary Hasse–Minkowski safety; Θ(n^{2/3})
   assembly.

---

**Status (S10, superseded)**: ACTIVE — S10 ACT LANDED (2026-07-24, researcher-1). The 2026-06-13 BLOCKED flag is cleared: Docker is no longer required (host `lake env lean` verification works), and the S9 PREP `(5, 7)` mixed-modulus recipe has been pasted and verified GREEN on the first try. 4 of 7 safe pairs discharged.

**Phase**: ACT (S10 ACT — `(5, 7)` axis-vs-plane safety DISCHARGED)
**Since**: 2026-07-24 (S10 ACT)
**Iteration**: 17
**Last Update**: 2026-07-24 (researcher-1) — S10 ACT: pasted the S9 PREP `(5, 7)` mixed-modulus recipe into `proofs/Proofs/Erdos659OQ01OQ02.lean` (683 → 886 LOC). +1 helper (`zmod_7_a_sq_eq_five_b_sq_iff`, 49-case decide), +3 descent theorems (`safe_{A,B,C}_5_7_holds`), +1 composite (`safe_5_7_axis_vs_plane`). 0 sorries / 0 axioms delta; host-verified v4.31 (`lake env lean` exit 0, first try; `#print axioms` = propext/Classical.choice/Quot.sound on all 5 new declarations). Every hand-derived S9 sign/coefficient was correct — the failure register (§8) was not needed. The mixed-modulus insight held: eqs A/C reduce mod 5 reusing `zmod_5_a_sq_eq_two_b_sq_iff` (since 7 ≡ 2 mod 5), only eq B needed the new mod-7 helper.

## S10 ACT (researcher-1, 2026-07-24, host-verified GREEN)

Executed §5–§6 of the S9 PREP recipe verbatim (sessions/2026-06-13-s9-prep-5-7-axis-vs-plane-mixed-modulus-recipe.md). Deltas from the S8 `(2,13)` template exactly as designed: modulus/helper per equation (A: mod 5, B: mod 7 NEW, C: mod 5), helper output variable order (A/C hand back (a,c), derive b), descent variable = isolated LHS variable. All `linear_combination` orientations: `-heq` / `-hb2` / `-hc2` (computed at paste time, all correct first try).

**Safe-pair scoreboard**: (2,5) ✓, (3,5) ✓, (2,13) ✓, **(5,7) ✓ (this session)**; remaining: (5,13), (7,13), (11,13).

**Next actions**:
1. **(5,13) PREP+ACT**: re-audit moduli — `13 ≡ 3 (mod 5)` so A/C candidate reduction mod 5 needs the EXISTING `zmod_5_a_sq_eq_three_b_sq_iff` (3 non-residue mod 5 ✓); eq B (`5b² = a² + 13c²`) reduces mod 13 needing `zmod_13_a_sq_eq_five_b_sq_iff` (5 a non-residue mod 13? squares mod 13 = {0,1,3,4,9,10,12}; 5 ∉ ✓). Likely ONE new helper again — same shape as this session.
2. **(7,13)**, **(11,13)** analogously (check QR tables first, mixed-modulus where needed).
3. Blocked (unchanged): full-rank ternary Hasse–Minkowski safety; Θ(n^{2/3}) assembly.

**Status**: BLOCKED (2026-06-13, researcher-2) — the only remaining concrete next action is S10 ACT (paste the S9 PREP `(5, 7)` mixed-modulus recipe into `Erdos659OQ01OQ02.lean` and `docker-build`-verify). That is **Docker-gated** and the daemon is down (`docker info` times out). The math is settled: the `(5, 7)` recipe is paste-ready (`sessions/2026-06-13-s9-prep-5-7-axis-vs-plane-mixed-modulus-recipe.md`), and every other open candidate (`(5,13)`/`(7,13)`/`(11,13)` axis-vs-plane, full-rank Hasse-Minkowski safety, Θ(n^{2/3}) assembly) is likewise either Docker-gated paste-work or blocked on absent Mathlib v4.26.0 infrastructure. PREP/OBSERVE are saturated — a further doc-only memo would be churn. Re-open when Docker returns (paste + verify S9 PREP recipe at S10 ACT).

**Phase**: PREP (S9 PREP — `(5, 7)` axis-vs-plane mixed-modulus recipe; doc-only)
**Since**: 2026-06-13 (S9 PREP designs the next safe-pair discharge from the S8 menu)
**Iteration**: 16 (was 15; S9 PREP designs `(5, 7)`)
**Last Update**: 2026-06-13 (researcher-2) — S9 PREP (doc-only): designed the `(5, 7)` axis-vs-plane discharge. **Corrects the S8 next-action menu**: `(5, 7)` is NOT a uniform mod-7 analog of `(2, 13)`. Because `−5 ≡ 2 (mod 7)` is a quadratic *residue* mod 7, equation A `7c²=a²+5b²` cannot be killed mod 7. The correct discharge is **mixed-modulus**: equations A and C reduce mod 5 (`a² ≡ 2c²`, reusing the EXISTING `zmod_5_a_sq_eq_two_b_sq_iff` since `7 ≡ 2 mod 5`) and only equation B reduces mod 7 (`a² ≡ 5b²`, needing the single NEW helper `zmod_7_a_sq_eq_five_b_sq_iff`). So `(5,7)` needs **one** new helper, not two — and no `_plus_`-form helper. Paste-ready skeletons + failure register at `sessions/2026-06-13-s9-prep-5-7-axis-vs-plane-mixed-modulus-recipe.md`. **Build NOT verified: Docker daemon down on host** (`decide`/`lake build` unavailable); all QR facts and descent algebra hand-computed and flagged for verification at the S10 ACT paste. No `.lean` / `meta.json` edits this session.

## S9 PREP (researcher-2, 2026-06-13, doc-only; Docker down)

Designed the `(5, 7)` axis-vs-plane discharge. Full recipe at
`sessions/2026-06-13-s9-prep-5-7-axis-vs-plane-mixed-modulus-recipe.md`.

**Key correction to the S8 menu.** The menu listed `(5,7)` as "needs
mod-7 reduction (49-case `decide` per helper)" — implying a 2-new-helper
mod-7 analog of `(2,13)`. That is wrong for equation A: `−5 ≡ 2 (mod 7)`
is a QR mod 7, so `a² + 5b² ≡ 0 (mod 7)` has non-trivial solutions and
the mod-7 reduction does not force triviality.

**The mixed-modulus discharge** (QR tables hand-computed, VERIFY via
`decide`): squares mod 5 = {0,1,4}, mod 7 = {0,1,2,4}.

| Eq | mod | relation | helper | new? |
|----|-----|----------|--------|------|
| A `7c²=a²+5b²` | 5 | `a²≡2c²` | `zmod_5_a_sq_eq_two_b_sq_iff` | reuse |
| B `5b²=a²+7c²` | 7 | `a²≡5b²` | `zmod_7_a_sq_eq_five_b_sq_iff` | **NEW** |
| C `a²=5b²+7c²` | 5 | `a²≡2c²` | `zmod_5_a_sq_eq_two_b_sq_iff` | reuse |

Eq A/C reuse the existing mod-5 helper because `7 ≡ 2 (mod 5)`. Only one
new 49-case `decide` helper is required.

**Build status: UNVERIFIED.** Docker daemon down; no `decide`/`lake
build` ran. QR facts and descent algebra are hand-derived; the descent
skeletons mirror the Docker-verified `safe_{A,B,C}_{3_5,2_13}_holds`
template 1:1 (deltas only in modulus, helper, and which variables the
helper returns). Must Docker-verify at S10 ACT.

### Legacy header (S8 ACT, retained below)

**Phase**: ACT (S8 ACT — (2, 13) axis-vs-plane safety DISCHARGED; Docker-verified GREEN)
**Iteration**: 15
**Last Update**: 2026-06-09T23:55Z (researcher-1) — S8 ACT: applied the (2, 13) mod-13 QR-descent recipe to `proofs/Proofs/Erdos659OQ01OQ02.lean` (PRE: 488 LOC → POST: 683 LOC; delta +195 LOC). Adds `safe_2_13_axis_vs_plane`, the third member of the {(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)} safe-pair family identified by S2a OBSERVE PR #18494. 2 new mod-13 helpers (`zmod_13_a_sq_plus_2_b_sq_eq_zero_iff`, `zmod_13_a_sq_eq_two_b_sq_iff`); 3 new descent theorems `safe_{A,B,C}_2_13_holds`; 1 new corollary. 0 sorries / 0 axioms delta (file remains 0 / 0). Docker-verified GREEN: `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` → "✔ [3058/3058] Built Proofs.Erdos659OQ01OQ02 (19s)" → "Build completed successfully (3058 jobs)". The 169-case `decide` checks for the mod-13 helpers succeed without strain. No meta.json / problem.md / knowledge.md / sibling-slug / lake-manifest edits — `Erdos659OQ01OQ02.lean` is not surfaced in the parent gallery entry `erdos-659-oq-01`'s `additionalFiles`-counted axioms, so `axiomCount: 3` in `src/data/proofs/erdos-659-oq-01/meta.json` is unaffected.

## S8 ACT (researcher-1, 2026-06-09, Docker-verified GREEN)

Executed the top entry of the S7 ACT next-action menu: `(2, 13)` axis-vs-plane safety. Memo at `sessions/2026-06-09-s8-act-2-13-axis-vs-plane-discharge.md`.

### Lean delta (Docker-verified)

| Section | Before | After | Δ |
|---|---|---|---|
| `proofs/Proofs/Erdos659OQ01OQ02.lean` LOC | 488 | 683 | +195 |
| `def`s | 4 | 4 | 0 |
| `theorem`s | 8 | 12 | +4 (`safe_A_2_13_holds`, `safe_B_2_13_holds`, `safe_C_2_13_holds`, `safe_2_13_axis_vs_plane`) |
| `lemma`s | 4 | 6 | +2 (`zmod_13_a_sq_plus_2_b_sq_eq_zero_iff`, `zmod_13_a_sq_eq_two_b_sq_iff`) |
| Sorries | 0 | 0 | 0 |
| `axiom` declarations | 0 | 0 | 0 |

### Build verification

`./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` →
`✔ [3058/3058] Built Proofs.Erdos659OQ01OQ02 (19s)` → `Build completed successfully (3058 jobs).`

### Why (2, 13) was the lowest-LOC choice

S7 ACT identified (2, 13) as the lowest-LOC remaining candidate among the
six unproved safe pairs from S2a OBSERVE PR #18494. The coefficient on
`b²` stays at `2` (same as (2, 5)), so the descent skeleton lifts even
more directly than the (3, 5) extension did — only the prime modulus
moves from 5 to 13. Mod-13 has 169 cases (vs 25 for mod-5); `decide`
handles this in a fraction of a second.

### QR table — mod 13

Squares in `ZMod 13` = `{0, 1, 3, 4, 9, 10, 12}`. Non-residues =
`{2, 5, 6, 7, 8, 11}`. Both `2` and `−2 = 11` are non-residues, which is
exactly what equations A (`−2` non-residue) and B/C (`2` non-residue)
need to force `a ≡ b ≡ 0 (mod 13)` and then `13 ∣ c`.

### Cumulative axis-vs-plane safety progress

| Prime pair `(p, q)` | Status | Iteration | Helper modulus |
|---|---|---|---|
| `(2, 5)` | ✅ proved | S4 ACT | mod 5 |
| `(3, 5)` | ✅ proved | S7 ACT | mod 5 |
| `(2, 13)` | ✅ proved | **S8 ACT (this)** | mod 13 |
| `(5, 7)` | ⏳ candidate | next iter | mod 5 + mod 7 |
| `(5, 13)` | ⏳ candidate | future | mod 5 + mod 13 |
| `(7, 13)` | ⏳ candidate | future | mod 7 + mod 13 |
| `(11, 13)` | ⏳ candidate | future | mod 11 + mod 13 |

3/7 safe pairs from S2a OBSERVE PR #18494 now have proved axis-vs-plane
safety.

### Updated next-action menu

The S7/S8 next-action menu shrinks by one (the `(2, 13)` axis-vs-plane
safety is now discharged). Remaining concrete candidates:

1. **`(5, 7)` axis-vs-plane safety** — needs mod-7 reduction (49-case
   `decide` per helper). Lowest new-API surface remaining.
2. **`(5, 13)` axis-vs-plane safety** — can reuse mod-13 helpers from
   this S8 ACT (the existing `zmod_13_a_sq_eq_two_b_sq_iff` and
   `zmod_13_a_sq_plus_2_b_sq_eq_zero_iff` carry the coefficient `2`; for
   `(5, 13)` the analogous helpers would carry `5`, so two new
   `zmod_13_*_5_*` helpers are needed — but no new modulus).
3. **`(7, 13)`, `(11, 13)` axis-vs-plane safety** — require mod-7,
   mod-11, mod-13 helpers.
4. **Full-rank safety for `(2, 5)`, `(3, 5)`, or `(2, 13)`** — still
   blocked on ternary Hasse-Minkowski (Mathlib v4.26.0 absence per S2c
   PREP §5.6) or honest axiomatisation per S2c §6.1.
5. **Θ(n^{2/3}) assembly** — still blocked on S3/S4 plan
   axiomatisations.

## S7 ACT (researcher-1, 2026-06-04, Docker-verified GREEN)

Applied the S7 PREP-2 recipe (see `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md`) verbatim to the Lean file. Memo at `sessions/2026-06-04-s7-act-3-5-axis-vs-plane-discharge.md`.

### Lean delta (Docker-verified)

| Section | Before | After | Δ |
|---|---|---|---|
| `proofs/Proofs/Erdos659OQ01OQ02.lean` LOC | 292 | 488 | +196 |
| `def`s | 4 | 4 | 0 |
| `theorem`s | 4 | 8 | +4 (`safe_A_3_5_holds`, `safe_B_3_5_holds`, `safe_C_3_5_holds`, `safe_3_5_axis_vs_plane`) |
| `lemma`s | 2 | 4 | +2 (`zmod_5_a_sq_plus_3_b_sq_eq_zero_iff`, `zmod_5_a_sq_eq_three_b_sq_iff`) |
| Sorries | 0 | 0 | 0 |
| `axiom` declarations | 0 | 0 | 0 |

### Build verification

`./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` →
`✔ [3058/3058] Built Proofs.Erdos659OQ01OQ02 (14s)` → `Build completed successfully (3058 jobs).`

### Updated next-action menu

The S6/S7 next-action menu shrinks by one (the `(3, 5)` axis-vs-plane safety
is now discharged). Remaining concrete candidates:

1. **`(2, 13)` axis-vs-plane safety** — needs mod-13 reduction (169-case
   `decide` per helper). Lowest-LOC remaining safe pair.
2. **`(5, 7)` axis-vs-plane safety** — needs mod-7 reduction. Second-lowest.
3. **Full-rank safety for `(2, 5)` or `(3, 5)`** — still blocked on ternary
   Hasse-Minkowski (Mathlib v4.26.0 absence per S2c PREP §5.6) or honest
   axiomatisation per S2c §6.1.
4. **Θ(n^{2/3}) assembly** — still blocked on S3/S4 plan axiomatisations.

## S7 PREP-2 (researcher-1, 2026-06-04, doc-only)

Claim-random landed at 2026-06-04T17:52Z (T+3d post-S6 STATE-SYNC). Pre-S7-PREP-2 drifts: **none** — state.md head and JSON `currentState.{phase, focus, nextAction, lastUpdate}` were all refreshed by S6 STATE-SYNC three days ago and remain accurate.

This S7 PREP-2 picks the **lowest-LOC** of the three S7 ACT candidates listed in S6 STATE-SYNC's next-action menu: generalise the proved (2, 5) axis-vs-plane safety to a second prime pair. Selection criterion: minimise the new Mathlib-API surface and reuse the existing mod-5 helpers as much as possible.

### Why (3, 5) and not another safe pair

S2a OBSERVE PR #18494 §"Empirical search" found seven safe pairs at R ≤ 22: `{(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`. Among the six remaining (post-(2, 5)):

| Pair | New modulus needed | Helpers reused | New helpers | Verdict |
|---|---|---|---|---|
| (3, 5) | mod 5 (same!) | 0 (different coefficients) | 2 | **lowest cost** |
| (5, 7) | mod 5 + mod 7 | 0 | 2–4 | second-lowest |
| (5, 13) | mod 5 + mod 13 | 0 | 2–4 | |
| (7, 13) | mod 7 + mod 13 | 0 | 4 | |
| (11, 13) | mod 11 + mod 13 | 0 | 4 | |
| (2, 13) | mod 13 | 0 | 2 (mod-13 = 169-case `decide`) | |

(3, 5) wins because all three of its equations reduce mod 5, and the existing
file already imports `Mathlib.Data.ZMod.Basic` (no new imports needed). The
descent skeleton lifts verbatim with the coefficient `2 → 3` swap.

### S7 PREP-2 deliverables

| File | Change | Why |
|---|---|---|
| `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md` | NEW (~370 lines) | Paste-ready Lean recipe |
| `state.md` head + this block | UPDATED | Iteration 12 → 13; phase ACT → PREP; absorbed-session table entry |
| `src/data/research/problems/erdos-659-oq-01-oq-02.json` | `currentState.{focus, nextAction, iteration, lastUpdate, phase, since}` | sync with the new PREP iteration |

**No Lean / meta.json / problem.md / knowledge.md / sibling-slug / lake-manifest edits.**

### Why doc-only (not S7 ACT directly)

`docker info` at 2026-06-04T17:54Z reports `Cannot connect to the Docker daemon`. Per the project's `CLAUDE.md` "DANGER: Never Run `lake build` Directly" policy, **no Lean change can be verified at this moment**. Two prior S7 ACT contributions today shipped under the "(build pending — Docker daemon down)" convention with explicit acknowledgement (#22238 sum-of-divisors-oq-02). This PREP avoids the convention by being doc-only — the recipe is paste-ready for a follow-up S7 ACT PR once Docker returns.

### Next action (S7 ACT)

Apply the recipe from `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md` to `proofs/Proofs/Erdos659OQ01OQ02.lean`:

1. Insert the 2 new mod-5 helpers immediately after `zmod_5_a_sq_eq_two_b_sq_iff` (currently line 80).
2. Insert the 3 new descent theorems (`safe_A_3_5_holds`, `safe_B_3_5_holds`, `safe_C_3_5_holds`) and the corollary `safe_3_5_axis_vs_plane` immediately before `end Erdos659OQ01OQ02` (currently line 292).
3. Expected diff: +142 LOC, 0 sorries, 0 axioms (file 292 → ~434 LOC).
4. `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` from the worktree directory once Docker is back; see S4 PREP §"Build status" for the worktree mount-path gotcha.

If Docker is still down at S7 ACT write-time, ship the diff under the "(build pending — Docker daemon down)" convention.

See `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md` for the full recipe (370 lines, including QR reduction tables, paste-ready Lean blocks for each of the three descent theorems, Mathlib v4.26.0 verification table, and risk notes).

## S6 STATE-SYNC (researcher-1, 2026-06-01, doc-only)

Claim-random landed at 2026-06-01T20:44Z (T+3d post-S4 ACT merge). Pre-S6 drifts:

| Surface | Pre-S6 status | S6 disposition |
|---------|---------------|----------------|
| state.md head `Iteration` | 10 (matches S5 STATE-SYNC, BEHIND S4 ACT #20921 = iter 11) | → 12 (S6 STATE-SYNC) |
| state.md head `Phase` | "S3 SCAFFOLD shipped → S4 PREP + S4 PREP-2 ... ACT-ready for S5 ACT discharge" (stale: discharge happened) | → "S4 ACT DISCHARGED — three axis-vs-plane sorries proved" |
| state.md head `Last Update` | "2026-05-16T16:10Z ... S5 STATE-SYNC" | → "2026-06-01T20:46Z ... S6 STATE-SYNC" |
| JSON `currentState.focus` | "S5 STATE-SYNC ... absorbs S4 PREP-2 #19128 ..." (1 S behind) | refreshed to S4 ACT absorbed narrative |
| JSON `currentState.nextAction` | "discharge the 3 strategic sorries ... per S4 PREP-2 ... explicit Nat.strongRecOn descent bodies" (stale: discharged) | refreshed to next-step menu (full-rank safety; other safe pairs; Θ(n^{2/3}) assembly) |
| JSON `currentState.iteration` | 10 | → 12 |
| JSON `currentState.since` | "2026-05-16T16:10:00.000Z" | → "2026-05-29T08:45:00.000Z" (S4 ACT merge time) |
| JSON `currentState.phase` | "ACT" | unchanged (still ACT) |
| JSON `lastUpdate` | "2026-05-16T16:10:00.000Z" | → "2026-06-01T20:46:00.000Z" |
| `sessions/` last entry | `2026-05-16-s5-statesync-absorb-s4-prep-2.md` | NEW `2026-06-01-s6-statesync-absorb-s4-act.md` |

**No Lean / no meta.json / no problem.md / no knowledge.md / no sibling-slug / no lake-manifest edits.** The S4 ACT deliverable on `origin/main` (proofs/Proofs/Erdos659OQ01OQ02.lean with three proved descent theorems, 0 sorries, 0 axioms, Docker-verified GREEN) is unchanged.

See `sessions/2026-06-01-s6-statesync-absorb-s4-act.md` for full memo.

## Next-action menu (post S4 ACT discharge)

Three concrete candidates per the S4 ACT knowledge.md entry §Next-action candidates:

1. **Full-rank safety for (2,5)** — either elementary descent for genuinely-ternary equidistant configurations not reducible to one axis vs. a coordinate plane, or honest axiomatisation. S2c PREP §6.1 recommends explicit typeclass decomposition `SafePrimePair = SafePrimePair_AxisVsPlane ∧ SafePrimePair_FullRank` with `fullRank_empirically_safe` axiomatised, since Mathlib v4.26.0 lacks ternary Hasse-Minkowski infrastructure.
2. **Generalise to other safe prime pairs** — S2a identified 15 candidates with R ≤ 22; the safe ones are {(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}. The descent template here applies whenever both `p` and `q · (±)` are quadratic non-residues mod a common small prime.
3. **Assemble the Θ(n^{2/3}) rate** — connect `SafePrimePair_*` to a `fourPointProperty` lattice family and the distinct-distance count. Requires axiomatising or proving the distance-count bound (S3 of original plan) and the Solymosi–Vu lower bound (S4 of original plan).

---

## S5 STATE-SYNC (researcher-9, 2026-05-16, doc-only)

Claim-random landed at 2026-05-16T16:08Z (T+2d post-S4 PREP-2 merge). Pre-S5 drifts:

| Surface | Pre-S5 status | S5 disposition |
|---------|---------------|----------------|
| state.md head `Iteration` | 9 (matches S4 PREP #19028, BEHIND S4 PREP-2 #19128) | → 10 |
| state.md head `Last Update` | "2026-05-14 ... S4 PREP" | → "2026-05-16T16:10Z ... S5 STATE-SYNC" |
| JSON `lastUpdate` | `null` | → `"2026-05-16T16:10:00.000Z"` |
| JSON `currentState.focus` | "S3 ACT SCAFFOLD shipped (PR #18947, iter 8): ..." (2 iters behind) | refreshed to S4 PREP-2 absorbed |
| JSON `currentState.nextAction` | S4 PREP-2 next-action narrative | refreshed to S5 ACT discharge plan |
| JSON `currentState.iteration` | 9 (matches S4 PREP) | → 10 |
| `sessions/` last entry | `2026-05-14-s4-prep-2-explicit-descent-bodies-for-three-sorries.md` | NEW `2026-05-16-s5-statesync-absorb-s4-prep-2.md` |

**No Lean / no meta.json / no problem.md / no knowledge.md / no sibling-slug / no lake-manifest edits.** The S4 PREP-2 deliverable on `origin/main` (3 explicit descent bodies for the 3 strategic sorries in `proofs/Proofs/Erdos659OQ01OQ02.lean`) is unchanged.

See `sessions/2026-05-16-s5-statesync-absorb-s4-prep-2.md` for full memo.



## Session Log (STATE-SYNC, 2026-05-13, researcher-4)

state.md had drifted from "Phase: OBSERVE / Iteration 1 / lastUpdate 2026-05-12"
to its current frozen form after **six** subsequent merged sessions (S1b/S1c/S1d/S2a/S2b/S2c),
each landing a doc-only PREP/OBSERVE PR that left state.md untouched. This STATE-SYNC
adds 1-entry-per-merged-session and refreshes Phase / Iteration / Last Update so a
returning agent can pick up cold.

| Session | Date | Mode | PR | Title / focus | LOC |
|---|---|---|---|---|---|
| **S1** | 2026-05-12 | OBSERVE | #18322 | 4-point-property in ℝ^d, d ≥ 3 — initial OBSERVE; provisional rate Θ(n^(2/d)); 3-axiom plan | doc-only |
| **S1b** | 2026-05-12 | OBSERVE | #18421 | Cartesian-lattice 4-point square falsification at d=3 — **corrected the S1 upper-bound plan** (Cartesian lattice fails the 4-point property because of axial squares like {(0,0,0), (1,0,0), (0,1,0), (1,1,0)}; planar squares exist at every k ≥ 1) | +281 |
| **S1c** | 2026-05-12 | OBSERVE | #18431 | Pell-equation safety condition for d=3 quadratic-form lattices — **proposed a Pell-safe restriction** acknowledging the S1b correction; sub-lattice Q(δ) = δ₁² + p·δ₂² + q·δ₃² avoids axial squares when no x²−py²=0 has small solutions | +330 |
| **S1d** | 2026-05-13 | OBSERVE | #18442 | `QuadraticForm.weightedSumSquares` Mathlib recasting — recasts the d≥3 Cartesian-lattice squared-distance form as a direct `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:1371` instance; opens S2a/S2b/S2c Mathlib-API targets | +233 |
| **S2a** | 2026-05-13 | OBSERVE | #18494 | Extended Pell-safety search + mod-q descent — empirical search over `R ≤ 22` produces 15 safe prime-pair lattices L_{p,q}; mod-q QR descent gives rigorous safety for the axis-vs-plane stratum; full-rank stratum still empirical | +447 |
| **S2b** | 2026-05-13 | PREP | #18554 | Mathlib audit + descent template for `safe_2_5_axis_vs_plane` — **errata**: cited `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic` does NOT exist at v4.26.0; replaced by `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`; 3 load-bearing lemmas pinned with line numbers; revised LOC estimate "~40 LOC per pair" → "~140 LOC for (2,5)" | +512 |
| **S2c** | 2026-05-13 | PREP | #18696 | Mathlib v4.26.0 audit-correction of S2b §8.1 — **negative claim verified** (no Hasse-Minkowski / genus theory at v4.26.0); **two line-number errata** on S2b §3 (off by 1); **new caveat** (search/code matches HEAD not pin); 5 alternative routes enumerated with insufficiency classification; recommendation: explicit typeclass decomposition `SafePrimePair = SafePrimePair_AxisVsPlane ∧ SafePrimePair_FullRank` with `fullRank_empirically_safe` axiomatised | +465 |

**Cumulative doc footprint**: 7 session markdown files in `sessions/` + `problem.md` + `knowledge.md` + this `state.md`. ~2.5K total LOC of analysis. Zero Lean changes across all 7 sessions (consistent doc-only stream).

## Open questions — PREP coverage (post-STATE-SYNC)

The S2 PREP saturation now exposes which planning gaps remain open for S3 ACT:

| Concern | Resolved? | Source |
|---|---|---|
| Provisional rate Θ(n^(2/d)) — empirical | partial | S1 §3 (synthesis from Solymosi-Vu + Cartesian-lattice); no rigorous derivation in published literature |
| Cartesian-lattice upper-bound construction valid? | **no** (refuted by S1b) | S1b — axial squares break 4-point property |
| Pell-safe sub-lattice family addresses S1b? | yes (with axiomatised full-rank fallback) | S1c + S2a + S2c §6.1 recommendation |
| Mathlib API present for `weightedSumSquares` recasting? | yes | S1d (`QuadraticForm/Basic.lean:1371`) |
| Mathlib API present for QR descent on `(p,q) = (2,5)`? | yes (3 lemmas pinned) | S2b §3 (with S2c errata) |
| Mathlib API present for full-rank Hasse-Minkowski safety? | **no** (negative claim verified at v4.26.0) | S2c §5.6 |
| LOC estimate for S3 ACT (axis-vs-plane only, (2,5) pair)? | yes (~140 LOC) | S2b §6 |
| LOC estimate for full SafePrimePair typeclass? | no (depends on number of pairs ultimately formalised) | open |

## ACT readiness assessment

- **S3 ACT-AxisVsPlane (LOC ≈ 140 for (2,5) pair)**: ready. All Mathlib bearers verified at v4.26.0; descent template in `sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md` §7.
- **S3 ACT-FullRank**: blocked on `fullRank_empirically_safe` axiomatisation choice (S2c §6.1 recommends explicit axiom for `R ≤ 22` empirical search; alternative is `Mathlib.LinearAlgebra.QuadraticForm.Anisotropic` shape-matching, but S2c §5 finds it insufficient for ternary).
- **S3 ACT-Lattice infrastructure**: ready. S1d §3 specifies `primeWeight d` + `cartesianLatticeFormD d = weightedSumSquares ℤ (primeWeight d)`, ~20 LOC. Sanity-check at d=3 is `rfl`-provable per S1d §3.

**Recommended next session**: S3 ACT-AxisVsPlane on (2,5) pair, ~140 LOC, sorry-free, single new file `Erdos659OQ01OQ02.lean`. Build-pending convention applies (Docker wrapper for the 1996+ Mathlib import surface).

---

## Original Current Focus (frozen at S1, 2026-05-12, researcher-10)

S1 (researcher-10): OBSERVE survey for `erdos-659-oq-01-oq-02` — the seeker-extracted child of the verified gallery entry `erdos-659-oq-01` ("The O(n/√log n) Distance Bound is Sharp" in ℝ²). The sub-OQ asks the natural higher-dimensional extension:

> Can the result be extended to higher dimensions (ℝ^d with d ≥ 3)?

This iteration produces:

- `problem.md` — formal problem statement with full Lean target signatures (`distinctDistancesD`, `fourPointPropertyD`, `dim_d_lower_bound`, `dim_d_upper_bound`, `dim_d_distance_rate`); decomposition into S2–S6 deliverables; Mathlib infrastructure map.
- `knowledge.md` — historical timeline (Landau 1908 → Bernays 1912 → Erdős 1946 → Solymosi–Vu 2008 → Moree–Osburn 2006 → Guth–Katz 2015 → KMSS 2017); Cartesian-lattice construction computation; Mathlib gap table; computational verification notes for $k = 10$ in $d = 3, 4$.
- `state.md` (this file) — phase NEW → OBSERVE.

No Lean changes in S1.

## Active Approach

**The 2D result does NOT extend in the same form** — the answer for $d \ge 3$ is qualitatively different.

The parent's 2D rate $\Theta(n/\sqrt{\log n})$ rests on **Landau's binary-form theorem** (the count of integers $\le N$ representable by a positive-definite binary quadratic form is $\Theta(N/\sqrt{\log N})$). This rate is **2D-specific**:

- In 2D, binary forms have a "class-number-1 ($L$-function)" counting profile giving the $\sqrt{\log}$ factor.
- In 3D and higher, ternary/d-ary positive-definite forms represent positive density of integers (Bernays 1912, Davenport–Cassels 1937), giving a linear-in-$N$ count.

**Conjectured higher-dimensional rate**: $\Theta(n^{2/d})$ for the 4-point property in ℝ^d, $d \ge 3$.

| $d$ | Rate (4-point property) | Tool |
|----:|:-----------------------|:-----|
| 2 | $\Theta(n/\sqrt{\log n})$ | Landau (1908), Moree–Osburn (2006) |
| 3 | $\Theta(n^{2/3})$ (conjectural) | Solymosi–Vu (2008), Cartesian-lattice construction |
| 4 | $\Theta(n^{1/2})$ (conjectural) | KMSS (2017), Cartesian-lattice construction |
| $\ge 5$ | $\Theta(n^{2/d})$ (conjectural) | analogous |

### Upper bound — Cartesian lattice construction

$L_d(k) := \{(a_1, a_2 \sqrt{2}, a_3 \sqrt{3}, \ldots, a_d \sqrt{p_{d-1}}) : a_i \in \mathbb{Z} \cap [-k, k]\}$ where $p_i$ is the $i$-th prime.

Cardinality $(2k+1)^d \asymp k^d = n$. Squared distances lie in $\{Q(\delta_1, \ldots, \delta_d) = \delta_1^2 + 2 \delta_2^2 + \cdots + p_{d-1} \delta_d^2 : \delta_i \in [0, 2k]\}$, bounded by $k^2 \cdot (1 + 2 + \cdots + p_{d-1}) = O(k^2)$ values. Hence $O(n^{2/d})$ distinct distances.

### Lower bound — Solymosi–Vu transfer

The 4-point property only *restricts* the family of $n$-point sets; it cannot increase the minimum number of distinct distances over the generic distance problem. So any 4-point-property family in ℝ^d ($d \ge 3$) satisfies
$$ \mathrm{distinctDistances} \ge \Delta_d(n) \ge \Omega(n^{2/d - \epsilon}) \quad \text{(Solymosi-Vu 2008)}. $$

Matching the upper bound up to $\epsilon$.

## Blockers

None mathematical for S1 (this is an OBSERVE iteration).

Practical infrastructure constraints (deferred to S2+):

- **No Mathlib Solymosi–Vu**: the lower-bound side must be axiomatised.
- **No Mathlib Davenport–Cassels density**: not directly needed for axiomatised S2, but a prerequisite for any future formal-proof iteration.
- **Cartesian-lattice 4-point property is non-routine**: even though intuitively true (prime-multiplier separation), a Lean proof requires a careful case analysis on 4-tuple configurations. Axiomatised at S3.

## Next Action

**S2 (any researcher)**: Define `distinctDistancesD` and `fourPointPropertyD` in `proofs/Proofs/Erdos659OQ01OQ02.lean`. The structure mirrors the parent `Erdos659OQ01.lean` Section I but parameterised on `d : ℕ`.

Concrete plan:

```lean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos659OQ01OQ02

variable {d : ℕ}

/-- Distinct positive distances determined by a finite point set in `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def distinctDistancesD
    (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card

/-- The 4-point property in `d`-dimensional Euclidean space. -/
def fourPointPropertyD (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ T : Finset (EuclideanSpace ℝ (Fin d)),
    T ⊆ S → T.card = 4 → distinctDistancesD T ≥ 3

/-- A family of `n`-point sets in `ℝ^d` with the 4-point property for all n ≥ 4. -/
def dimDFamily (d : ℕ) (A : ℕ → Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ n, (A n).card = n) ∧ (∀ n, n ≥ 4 → fourPointPropertyD (A n))

/-- Sanity check at d = 2: the parent's 2D definitions agree (modulo Fin 2 ↔ ℝ × ℝ coercion). -/
example (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    distinctDistancesD S = (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card := rfl

end Erdos659OQ01OQ02
```

Expected line count: ~25 lines including docstrings. No theorems yet (those come in S3-S5).

**S3 (after S2)**: Define `cartesianLattice` and axiomatise its 4-point property + distance-count bound.
**S4 (after S3)**: Axiomatise Solymosi–Vu.
**S5 (after S4)**: Combine to prove `dim_d_distance_rate`.
**S6 (after S5)**: Gallery integration with `axiomatized` status.

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 3 markdown files (`problem.md`, `knowledge.md`, this `state.md`)
- 1 gallery JSON entry (`src/data/research/problems/erdos-659-oq-01-oq-02.json`)

The provisional rate $\Theta(n^{2/d})$ is the author's synthesis from published bounds (Solymosi–Vu 2008 for the lower side, Cartesian-lattice construction for the upper). **No published paper gives the exact rate for the 4-point property in $d \ge 3$**; this OQ probes a genuinely open question in metric combinatorics.

The future Lean entry will be `status: "axiomatized"` with `axiomCount ≥ 3`.

---

## Iteration 8 (researcher-1, 2026-05-13) — S3 ACT SCAFFOLD (merged, PR #18947)

**Outcome**: built — created `proofs/Proofs/Erdos659OQ01OQ02.lean` (133
LOC; **(build pending)** convention). Ships the outer scaffold for the
axis-vs-plane safety predicate at `(p, q) = (2, 5)`:

- `def safe_A`, `def safe_B`, `def safe_C` — the three QR equations
  isolated by S2b PREP §4 (`5c² = a² + 2b²`, `2b² = a² + 5c²`,
  `a² = 2b² + 5c²`).
- `theorem safe_A_holds`, `safe_B_holds`, `safe_C_holds` —
  **3 strategic sorries** (one per equation), descent bodies deferred
  to S4 ACT.
- `def SafePrimePair_AxisVsPlane (p q : ℕ)` — composite predicate
  parameterised on the prime pair.
- `theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5` —
  derived as the conjunction of the three `safe_*_holds`.

Sorries: 3 (strategic, all in `safe_*_holds`). Axioms: 0. The build is
pending pending Docker verification (recursive `.lake` symlink in the
researcher worktree precluded local `lake build`).

## Iteration 9 (researcher-12, 2026-05-14) — S4 PREP — ZMod 5 QR helpers

**Outcome**: built (Docker-verified — see Build status below) —
extended `proofs/Proofs/Erdos659OQ01OQ02.lean` (133 → ~165 LOC) with
**two decidable ZMod 5 helpers** that compress the mod-5 step of the
S4 ACT descent proofs to a 25-case `decide`. Also dropped the stale
`import Mathlib.Data.Int.Defs` left over from S3 ACT SCAFFOLD (the
module does not exist at v4.26.0 — surfaced by the first Docker
build attempt this iteration; this iter is the first Docker
verification of the OQ02 Lean file).

### What I added

```lean
import Mathlib.Data.ZMod.Basic   -- (new import)

/-- Mod-5 step for equation A: `a² + 2b² ≡ 0 (mod 5)` ⇔ `a = 0 ∧ b = 0`. -/
lemma zmod_5_a_sq_plus_2_b_sq_eq_zero_iff (a b : ZMod 5) :
    a ^ 2 + 2 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b; decide

/-- Mod-5 step for equations B and C: `a² ≡ 2b² (mod 5)` ⇔ `a = 0 ∧ b = 0`. -/
lemma zmod_5_a_sq_eq_two_b_sq_iff (a b : ZMod 5) :
    a ^ 2 = 2 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b; decide
```

### Why these helpers, and why now

S2b PREP §4 sketches the mod-5 step via
`ZMod.exists_sq_eq_two_iff` (line 74 of
`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`) and
`ZMod.exists_sq_eq_neg_two_iff` (line 80). The character-theoretic
route works, but the mod-5 reduction itself is finite combinatorics
over the 25 pairs `(a, b) ∈ ZMod 5 × ZMod 5`. A `decide` reflection
over the underlying `Decidable` instance closes both lemmas in two
lines of tactic and is mathematically equivalent to specialising
`exists_sq_eq_{two,neg_two}_iff` at `p = 5`.

Picking the `decide` form has three advantages:

1. **No `Fact (Nat.Prime 5)` instance plumbing** — the two
   QR-reciprocity routes need it (`haveI := fact_prime_five`),
   adding 1–2 LOC per call site. The `decide` form has no instance
   requirements.
2. **Single load-bearing lemma for B and C** — both equations reduce
   modulo 5 to "`a² = 2b²` in `ZMod 5`", and the same helper
   `zmod_5_a_sq_eq_two_b_sq_iff` discharges both. (The S2b PREP §4.2
   and §4.3 paths used two separate citations.)
3. **Trivially auditable** — `decide` over a 25-case finite type is a
   first-principles proof; an auditor can re-run it without any
   number-theory background.

### What this does NOT do

- Does **not** discharge `safe_A_holds`, `safe_B_holds`,
  `safe_C_holds` — the strategic sorries from S3 ACT SCAFFOLD
  remain. Those need the integer-side descent infrastructure
  (`Nat.strongRecOn` + substitution arithmetic), which is S4 ACT
  scope.
- Does **not** introduce new axioms or change `axiomCount`.
- Does **not** touch the full-rank safety predicate (S2c PREP §6.1)
  or full SafePrimePair conjunction.

### Next action (S4 ACT)

Lift the helpers into the descent proof of `safe_A_holds`
(~30 LOC body) following the S2b PREP §5 template:

1. From `5c² = a² + 2b²` and the new
   `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff`, deduce `5 ∣ a` and `5 ∣ b`
   in ℤ.
2. Substitute `a = 5a'`, `b = 5b'`; rearrange to `c² = 5(a'² + 2b'²)`;
   apply `Int.Prime.dvd_natAbs_of_coe_dvd_sq` (line 38 of
   `Mathlib/Data/Int/NatPrime.lean`) to deduce `5 ∣ c`.
3. Substitute `c = 5c'`; get `5c'² = a'² + 2b'²` — same equation,
   smaller `a.natAbs + b.natAbs + c.natAbs`.
4. `Nat.strongRecOn` on the sum to close the descent.

`safe_B_holds` and `safe_C_holds` mirror the structure with the second
helper `zmod_5_a_sq_eq_two_b_sq_iff` doing the mod-5 step.

Estimated S4 ACT size: **~40–50 LOC total** for all three discharges
(down from the S2b PREP §5 estimate of ~50 LOC, after factoring out the
two helpers).

### Build status

**Build verified by Docker wrapper** — log
`.loom/logs/researcher-12-erdos659-s4-prep-build3.log`,
`✔ Build completed successfully (3058 jobs)`. Both helpers compile
cleanly via `decide`; the only warnings are the three pre-existing
strategic sorries (lines 118/126/134) inherited from S3 ACT SCAFFOLD.

Note: the first two Docker attempts failed because I ran the script
from the main repo path (`cd /Users/rwalters/GitHub/lean-genius`),
which mounts the main repo into the container — not the worktree. The
fix was to invoke `./proofs/scripts/docker-build.sh …` from the
worktree directory (`cwd: .loom/worktrees/researcher-12`); the script
resolves `REPO_ROOT` from `BASH_SOURCE` and mounts whichever working
tree contains the script invocation. Worth noting for future builds
from worktrees with uncommitted edits.

### Blockers

None. S4 ACT is unblocked: the mod-5 step is now a two-line lemma
call; the integer descent infrastructure is standard Mathlib
(`Nat.strongRecOn`, `Int.Prime.dvd_natAbs_of_coe_dvd_sq`).
