# Iteration S8 ACT — `(2, 13)` axis-vs-plane safety DISCHARGED

**Date**: 2026-06-09
**Researcher**: researcher-1
**Phase**: ACT (discharges the lowest-LOC entry in the S7 ACT next-action menu)
**Type**: Lean ACT (Docker-verified GREEN).
**Build**: `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02` →
`✔ [3058/3058] Built Proofs.Erdos659OQ01OQ02 (19s)` → `Build completed successfully (3058 jobs)`.

## Headline

The second-listed safe prime pair from S2a OBSERVE PR #18494's empirical
search at R ≤ 22 — `(p, q) = (2, 13)` — now has its axis-vs-plane safety
fully proved. The S7 ACT next-action menu shrinks by one again:

> 1. **`(2, 13)` axis-vs-plane safety** — needs mod-13 reduction (169-case
>    `decide` per helper). Lowest-LOC remaining safe pair.  ← **discharged this session**
> 2. **`(5, 7)` axis-vs-plane safety** — second-lowest. Now the new top.

## Lean delta (Docker-verified)

| Section | Before (S7 ACT close) | After (S8 ACT close) | Δ |
|---|---|---|---|
| `proofs/Proofs/Erdos659OQ01OQ02.lean` LOC | 488 | 683 | +195 |
| `def`s | 4 | 4 | 0 |
| `theorem`s | 8 | 12 | +4 (`safe_A_2_13_holds`, `safe_B_2_13_holds`, `safe_C_2_13_holds`, `safe_2_13_axis_vs_plane`) |
| `lemma`s | 4 | 6 | +2 (`zmod_13_a_sq_plus_2_b_sq_eq_zero_iff`, `zmod_13_a_sq_eq_two_b_sq_iff`) |
| Sorries | 0 | 0 | 0 |
| `axiom` declarations | 0 | 0 | 0 |

## QR table — mod 13

Squares in `ZMod 13`:

| `x` | `x²` |  | `x` | `x²` |
|---|---|---|---|---|
| 0 | 0 |  | 7 | 10 |
| 1 | 1 |  | 8 | 12 |
| 2 | 4 |  | 9 | 3 |
| 3 | 9 |  | 10 | 9 |
| 4 | 3 |  | 11 | 4 |
| 5 | 12 |  | 12 | 1 |
| 6 | 10 |  |  |  |

**Quadratic residues** = `{0, 1, 3, 4, 9, 10, 12}`.
**Non-residues** = `{2, 5, 6, 7, 8, 11}`.

So `2` is a **non-residue** mod 13 (needed for equations B and C) and
`−2 = 11` is also a **non-residue** mod 13 (needed for equation A).
Both 169-case `decide` checks succeed.

## Equations and helper map

For the prime pair `(p, q) = (2, 13)`, the three axis-vs-plane equations
from the `SafePrimePair_AxisVsPlane 2 13` predicate are:

| Eq | Statement | Mod-13 reduces to | Helper used |
|----|-----------|-------------------|-------------|
| A | `13 c² = a² + 2 b²` | `a² + 2 b² ≡ 0 (mod 13)` ⇒ `a ≡ 0 ∧ b ≡ 0` | `zmod_13_a_sq_plus_2_b_sq_eq_zero_iff` (`−2` non-residue) |
| B | `2 b² = a² + 13 c²` | `2 b² ≡ a² (mod 13)` ⇒ `a ≡ 0 ∧ b ≡ 0` | `zmod_13_a_sq_eq_two_b_sq_iff` (`2` non-residue) |
| C | `a² = 2 b² + 13 c²` | `a² ≡ 2 b² (mod 13)` ⇒ `a ≡ 0 ∧ b ≡ 0` | `zmod_13_a_sq_eq_two_b_sq_iff` (same) |

This is *closer* to the `(2, 5)` case than to the `(3, 5)` case (the
coefficient on `b²` is still `2`, only the prime modulus moves from 5 to
13). The descent skeleton lifts verbatim from `safe_{A,B,C}_holds` with
the substitutions:

- `5` → `13` everywhere (in the integer descent, the ZMod, the
  `mul_left_cancel₀` cofactor, the `Int.natAbs_mul` rewrite, and the
  `Prime` instance — `Prime (13 : ℤ)` is closed by `norm_num`)
- mod-5 helper name → mod-13 helper name

No other structural change.

## Descent skeleton, equation A specialisation

The proof of `safe_A_2_13_holds` follows the same `Nat.strong_induction_on`
schema as `safe_A_holds`. At a high level:

1. Strong induction on `n := c.natAbs`. The base case `n = 0` forces
   `c = 0`, and then `0 = a² + 2 b²` with both squares non-negative gives
   `a = b = 0` via `sq_nonneg` + `nlinarith`.
2. Reduce both sides of `13 c² = a² + 2 b²` mod 13: the LHS vanishes
   (`(13 : ZMod 13) = 0`), so the cast equation gives
   `(a : ZMod 13)² + 2 (b : ZMod 13)² = 0`. Apply the new
   `zmod_13_a_sq_plus_2_b_sq_eq_zero_iff` helper to extract
   `(a : ZMod 13) = 0 ∧ (b : ZMod 13) = 0`, then lift to integer
   divisibilities `13 ∣ a` and `13 ∣ b` via
   `ZMod.intCast_zmod_eq_zero_iff_dvd`.
3. Write `a = 13 a'`, `b = 13 b'`, substitute, and use `linear_combination`
   to extract `c² = 13 (a'² + 2 b'²)`. Conclude `13 ∣ c` via
   `Prime.dvd_of_dvd_pow` on `13 ∣ c²`.
4. Write `c = 13 c'`, simplify to `13 c'² = a'² + 2 b'²`, and apply the
   strong-induction hypothesis at `c'.natAbs < n`.

Equation B (`safe_B_2_13_holds`) descends on `b.natAbs`; equation C
(`safe_C_2_13_holds`) descends on `a.natAbs`. Each uses the
`zmod_13_a_sq_eq_two_b_sq_iff` helper. The remaining structure is
identical.

## Cumulative axis-vs-plane safety progress

| Prime pair `(p, q)` | Status | Iteration | Helper modulus |
|---|---|---|---|
| `(2, 5)` | ✅ proved | S4 ACT (2026-05-29) | mod 5 |
| `(3, 5)` | ✅ proved | S7 ACT (2026-06-04) | mod 5 |
| `(2, 13)` | ✅ proved | **S8 ACT (this session)** | mod 13 |
| `(5, 7)` | ⏳ candidate | next iter | mod 5 + mod 7 |
| `(5, 13)` | ⏳ candidate | future | mod 5 + mod 13 |
| `(7, 13)` | ⏳ candidate | future | mod 7 + mod 13 |
| `(11, 13)` | ⏳ candidate | future | mod 11 + mod 13 |

3/7 safe pairs from S2a OBSERVE PR #18494 now have proved axis-vs-plane
safety.

## Next-action menu (updated)

1. **`(5, 7)` axis-vs-plane safety** — needs mod-5 + mod-7 reductions.
   The mod-5 step reuses `zmod_5_a_sq_eq_two_b_sq_iff` /
   `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff` already in the file (since 7
   would appear as the q-coefficient on `b²`, but actually the (5, 7)
   pair has `5` as the smaller prime — re-check QR analysis). Two new
   mod-7 helpers (49-case `decide` each). Second-lowest new-API surface.
2. **`(5, 13)` axis-vs-plane safety** — similar pattern, mod-5 + mod-13.
   Could re-use both existing helper sets.
3. **`(7, 13)`, `(11, 13)`** — require mod-7, mod-11, mod-13 helpers.
4. **Full-rank safety for any proved pair** — still blocked on ternary
   Hasse-Minkowski (Mathlib v4.26.0 absence per S2c PREP §5.6) or honest
   axiomatisation per S2c §6.1.
5. **Θ(n^{2/3}) assembly** — still blocked on S3/S4 plan axiomatisations.

## Why doc-only meta is unchanged

The gallery surfaces `erdos-659-oq-01` (the parent slug), not this
`oq-01-oq-02` sub-slug. Per S7 ACT, `Erdos659OQ01OQ02.lean` is not
counted in the parent's `additionalFiles`-axiom census, so
`axiomCount: 3` in `src/data/proofs/erdos-659-oq-01/meta.json` is
unaffected by S8 ACT (still 0 axioms in this file, still 0 sorries).

## Deliverables (this PR)

1. **Lean file**: `proofs/Proofs/Erdos659OQ01OQ02.lean`
   - Insertion 1 (after S7 ACT mod-5 helpers, ~line 102): two new mod-13
     helpers.
   - Insertion 2 (after `safe_3_5_axis_vs_plane`, before
     `end Erdos659OQ01OQ02`): the new S8 ACT section header, three
     descent theorems, one corollary.
2. **NEW session memo**: this file.
3. **state.md head**: S8 ACT prepend.
4. **Canonical JSON** (`src/data/research/problems/erdos-659-oq-01-oq-02.json`):
   `currentState.{phase, focus, nextAction, iteration, lastUpdate}` +
   `knowledge.progressSummary` prepend.

## Out of scope (deferred)

- Gallery `meta.json` numerics — file unchanged, no drift (this file is
  not surfaced in the parent gallery entry).
- `problem.md` / `knowledge.md` edits — no underlying mathematical
  framing change; the S2a/S2b OBSERVE+PREP narrative still describes the
  same plan, S8 ACT just executes the next step.
- `(5, 7)` axis-vs-plane safety — banked for the next iteration.
- Full-rank safety axiomatisation — blocked on Mathlib infrastructure.
