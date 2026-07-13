# S11b ACT — Tenth partial quotient `cbrt3_a9 = 6`

**Researcher**: researcher-1
**Date**: 2026-05-31
**PR**: (this PR)
**Phase**: ACT (iteration 12)

## Summary

Shipped the main theorem

```lean
theorem cbrt3_a9 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)
      - 4) - 1) - 5) - 1) - 1)⌋ = (6 : ℤ)
```

— the tenth partial quotient `a₉ = 6` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945. This is the
largest partial quotient in the known prefix. The sandwich pair was
already in place: lower bound `7155/4961 < cbrt3` (S11a helper, PR
#19456) + upper bound `cbrt3 < 6206/4303` (S10 helper, reused).

The proof is a 17-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
chain on a nine-fold-nested fraction, followed by floor antisymmetry
via `Int.le_floor` / `Int.floor_lt`. Heartbeat budget:
`set_option maxHeartbeats 1600000 in` (2× S10's 800_000, per the
empirical 2× per-depth scaling validated through S7–S10).

## Algebraic chain

From `7155/4961 < cbrt3 < 6206/4303` derive in order:

| Step | Variable | Lower bound | Upper bound |
|------|----------|-------------|-------------|
| 1 | `cbrt3 - 1` | (positive) | — |
| 2 | `1/(cbrt3-1)` | `4303/1903` | `4961/2194` |
| 3 | `x₂ := 1/(cbrt3-1) - 2` | `497/1903` | `573/2194` |
| 4 | `1/x₂` | `2194/573` | `1903/497` |
| 5 | `x₃ := 1/x₂ - 3` | `475/573` | `412/497` |
| 6 | `1/x₃` | `497/412` | `573/475` |
| 7 | `x₄ := 1/x₃ - 1` | `85/412` | `98/475` |
| 8 | `1/x₄` | `475/98` | `412/85` |
| 9 | `x₅ := 1/x₄ - 4` | `83/98` | `72/85` |
| 10 | `1/x₅` | `85/72` | `98/83` |
| 11 | `x₆ := 1/x₅ - 1` | `13/72` | `15/83` |
| 12 | `1/x₆` | `83/15` | `72/13` |
| 13 | `x₇ := 1/x₆ - 5` | `8/15` | `7/13` |
| 14 | `1/x₇` | `13/7` | `15/8` |
| 15 | `x₈ := 1/x₇ - 1` | `6/7` | `7/8` |
| 16 | `1/x₈` | `8/7` | `7/6` |
| 17 | `x₉ := 1/x₈ - 1` | `1/7` | `1/6` |
| 18 | `1/x₉` (floor) | `6` | `7` |

`⌊1/x₉⌋ = 6` follows from `6 < 1/x₉ < 7`.

## Files modified

1. `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (1289 → 1505 LOC,
   +216 LOC; theorem count 16 → 17): added `cbrt3_a9` with the
   18-step chain.
2. `src/data/research/problems/cube-root-3-irrational-oq-04.json`:
   bump `currentState.iteration` 11 → 12, refresh
   `currentState.focus` / `currentState.nextAction`,
   update `knowledge.progressSummary` + `knowledge.builtItems[+1]`
   + `knowledge.nextSteps[0]`, update `leanFiles[4]` lineCount
   1289 → 1505 / theoremCount 16 → 17, bump `lastUpdated`.
3. `research/problems/cube-root-3-irrational-oq-04/state.md`:
   bump head Iteration → 12, replace Current Focus with S11b ACT,
   refresh Next Action with S12 sketch.
4. NEW `research/problems/cube-root-3-irrational-oq-04/sessions/2026-05-31-s11b-act-tenth-partial-quotient.md`
   (this file).

No edits to:
- `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (helper sandwich already complete from S10 + S11a)
- `proofs/Proofs/CubeRoot3Irrational.lean` (parent, unchanged)
- `src/data/proofs/cube-root-3-irrational-oq-04/` gallery (no meta changes)
- sibling slugs

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04
```

Result: **clean** (7745 jobs; final file `Proofs.CubeRoot3IrrationalOQ04`
built in 218s on the standard Docker image). Pre-existing
`Mathlib.Data.Real.Irrational` deprecation warning at
`Proofs/CubeRoot3Irrational.lean:8` is unchanged from S10 build (parent
module, not owned by this slug).

0 sorries, 0 axioms (slug remains 0/0).

## Heartbeat budget validation

| Iteration | Depth | Steps | maxHeartbeats |
|-----------|-------|-------|---------------|
| S2–S6 | 1–4 | 5–9 | 200_000 (default) |
| S7 | 5 | 11 | 200_000 |
| S8 | 6 | 12 | 200_000 |
| S9 | 7 | 14 | 400_000 |
| S10 | 8 | 16 | 800_000 |
| S11b | 9 | 18 | 1_600_000 ✓ |

The 2× per-depth scaling rule continues to hold through S11b.
For S12 (depth 10, ~19 steps): try `maxHeartbeats 3_200_000`.

## Contraction validation

S10's upper-side gap: `11_435 / 79_673_526_127 ≈ 1.43·10⁻⁷`.
S11a's lower-side gap: `18_168 / 122_097_755_681 ≈ 1.488·10⁻⁷`.
The S11a gap is barely tighter (~4%) — consistent with the
alternating-convergent contraction. The big-jump partial quotient
`a₉ = 6` is what gave S10's odd-index convergent `6206/4303` an
unusually-large LOC-per-partial-quotient ratio; S11a's even-index
convergent `7155/4961` (with `a₁₀ = 1`) is a smaller delta as
expected.

## Next ACT picker priority

**S12 (any researcher)**: Prove `cbrt3_a10 = 1` — the eleventh partial
quotient. Per OEIS A002945, `a₁₀ = 1`. Need a new UPPER bound
(since the alternation puts the 11th convergent on the upper side
again). Eleventh CF convergent using `a₁₁ = ?` is:

  `p₁₁/q₁₁ = (a₁₁·p₁₀ + p₉) / (a₁₁·q₁₀ + q₉)`

Per OEIS A002945, the prefix continues `[…, 1, 6, 1, 2, …]`, so
`a₁₁ = 2`. Then:

  `q₁₁ = 2·4961 + 4303 = 14225`
  `p₁₁ = 2·7155 + 6206 = 20516`

So `p₁₁/q₁₁ = 20516/14225`. Pre-claim Python cube sanity:

  `20516³ = ?`
  `3 · 14225³ = ?`

(Future S12 picker MUST verify these cube digits independently per
the math-correction precedent established at S7→S8, S8→S9, S10→S11
sketches. Do NOT trust this current sketch's cube values blindly.
The S11 PREP MATH-CORRECTION discipline applies.)

Direction expected: `(20516/14225) > cbrt3` (odd-index convergent
above cbrt3, alternating with the even-index `7155/4961` below).
Cube target: `20516³ > 3 · 14225³`.

Algebraic chain: ~19 steps (one rung deeper than S11b's 17 steps).
Heartbeat budget guess: `set_option maxHeartbeats 3200000 in`
(2× S11b's 1_600_000; the 2× per-depth scaling has held through
S7–S11b).

Estimated main-file delta: ~220 LOC (consistent with the S10 234-LOC,
S11b 216-LOC trend).

## Open questions / future work (S12+)

The chain `cbrt3_a0, …, cbrt3_a9` now covers ten partial quotients
of the simple CF of `∛3` — the entire OEIS A002945 prefix that has
been independently cross-checked to 50 decimal places. Continuing
deeper is mechanical but expensive (each step doubles heartbeat
budget and adds ~220 LOC).

Strategic considerations for S12+:

1. **Continue the prefix chain**: S12 (`a₁₀ = 1`), S13 (`a₁₁ = 2`),
   etc. Linear progress, but each step is one Docker build and one
   ACT iteration. Mechanical.

2. **Bundle into `IntFractPair.stream`**: Once we have ~10 partial
   quotients, formalize the GenContFract.of cbrt3 statement at indices
   0..N. This requires understanding the Mathlib API and connecting
   our floor identities to `IntFractPair.stream`.

3. **Convergent lemmas**: Prove `convergent_n cbrt3 = (h_n, k_n)`
   with the recurrence `h_n = a_n h_{n-1} + h_{n-2}` etc. Requires
   chaining our `cbrt3_aN` identities through the Mathlib convergent
   definition.

4. **Lagrange obstacle**: Prove that the CF of cbrt3 is non-periodic
   (using cubic-irrationality). This is the natural "completion" of
   this slug — a structural theorem stating that no all-aᵢ formula
   is possible.

Of these, (3) and (4) are the most theoretically valuable but require
substantial Mathlib infrastructure work (or careful API porting).
(1) is the path of mechanical incremental progress. (2) is somewhere
in between. The seeker may want to consider (4) as a separate
sub-problem after a few more partial quotients are in hand.

## End of session

Researcher-1 releases claim on slug after pushing this PR.
