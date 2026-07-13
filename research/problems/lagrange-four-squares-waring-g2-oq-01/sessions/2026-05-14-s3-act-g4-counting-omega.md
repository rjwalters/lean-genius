# S3 ACT — `g(4) ≥ 19` via counting + omega (sibling of S2b ACT, k = 4)

**Session**: 2026-05-14, researcher-12
**Mode**: ACT — fresh Lean deliverable, sibling file
**Slug**: lagrange-four-squares-waring-g2-oq-01
**Status**: **Build-verified on first iteration. 7743 jobs clean.**

## 0. Position in the iteration arc

After S2b ACT (counting+omega for `k = 3`, PR #18928) and its
BUILD-VERIFY (PR #19041, in-flight), the parametric template
established by S2b/S3/S5/S6b/S7 PREPs was ready for re-use at higher
`k`. State.md (per PR #18866, researcher-1) ranks S3 ACT first among
the five queued ACTs, citing the smallest jump from a verified S2b ACT
recipe.

This session ports the S2b ACT recipe **line-for-line** to `k = 4`:
- `Fin 8 → Fin 18` (witness `s = g(4) − 1 = 18`)
- `23 → 79` (witness for `k = 4`: `79 = 4·16 + 15`)
- `8 → 16` (= `2^4`)
- `27 → 81` (= `3^4`)
- `^3 → ^4`
- `IsSumOfCubes → IsSumOfFourthPowers`

No new bearer lemmas, no new tactic primitives. The proof file is
141 LOC including a 60-line docstring header and the case-analysis
table audit.

## 1. The Lean deliverable

**File**: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (new, ~140 LOC)

**Theorem**: `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79`

**Definition added**: `IsSumOfFourthPowers s n := ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 4) = n`
(local; mirrors `WaringG2OQ01.IsSumOfCubes` for the `k = 4` instance)

**Axiom count**: 0 — no `axiom` declarations, no structure-encoded
assumptions, no `native_decide`. The proof discharges via `omega` over
the 2-equation linear system in ℕ.

**Sorry count**: 0.

## 2. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG4
...
✔ [7743/7743] Built Proofs.LagrangeFourSquaresWaringG2OQ01CountingG4 (10s)
Build completed successfully (7743 jobs).
```

Build log: `.loom/logs/researcher-12-lagrange-waring-g4-build1.log`.

**First-iteration success.** No retries; the S2b ACT BUILD-VERIFY
`by simp` form was incorporated up front, sidestepping the v4.26.0
`Set β`-coercion regression on the `Finset.card_eq_sum_card_fiberwise`
membership goal.

## 3. Strategy (parallel to S2b ACT)

The six-step proof structure is identical to S2b ACT (cf.
`LagrangeFourSquaresWaringG2OQ01Counting.lean`):

1. **Bound** `f i < 3` from `(f i)^4 ≤ 79 < 81 = 3^4` via
   `Nat.pow_le_pow_left` + `Finset.single_le_sum` + `omega`.
2. **Lift** `f : Fin 18 → ℕ` to `g : Fin 18 → Fin 3`,
   `g i := ⟨f i, hbnd i⟩`.
3. **Fiber** the sum via `Finset.sum_fiberwise`:
   `∑ i, ((g i : ℕ))^4 = ∑ k : Fin 3, ((k : ℕ))^4 · n k`
   where `n k := #{i | g i = k}`.
4. **Partition** count via `Finset.card_eq_sum_card_fiberwise` +
   `Fin.sum_univ_three`:  `n 0 + n 1 + n 2 = 18`.
5. **Expand** `Fin.sum_univ_three` + numeral simp:
   `∑ k, ((k : ℕ))^4 · n k = n 1 + 16 · n 2`.
6. **Discharge** `omega` on
   `(n 0 + n 1 + n 2 = 18) ∧ (n 1 + 16·n 2 = 79)`.

## 4. Case analysis (audited)

| `n 2` | `n 1 = 79 − 16·n 2` | `n 0 = 18 − n 1 − n 2` | Feasibility |
|------:|--------------------:|------------------------:|-------------|
| 0     | 79                  | −61                     | ✗ (`n 0 < 0`) |
| 1     | 63                  | −46                     | ✗ (`n 0 < 0`) |
| 2     | 47                  | −31                     | ✗ (`n 0 < 0`) |
| 3     | 31                  | −16                     | ✗ (`n 0 < 0`) |
| 4     | 15                  | −1                      | ✗ (`n 0 < 0`) |
| ≥ 5   | ≤ −1                | —                       | ✗ (`n 1 < 0`) |

The `n 2 = 4` row matches the S3 PREP witness `79 = 4·16 + 15` (four
cubes of value 2 plus fifteen ones) — the residual `n 0 = −1` is the
"miss by 1" calibration characteristic of the Waring lower-bound
construction.

## 5. Bearer audit (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same bearer set as S2b ACT (audited in PR #18895). No new bearers:

- `Nat.pow_le_pow_left` (step 1)
- `Finset.single_le_sum` (step 1)
- `Finset.sum_congr` (steps 3, 5)
- `Finset.sum_fiberwise` (step 3)
- `Finset.card_eq_sum_card_fiberwise` (step 4)
- `Finset.mem_filter` (step 3)
- `Fin.sum_univ_three` (steps 4, 5)
- `Finset.sum_const`, `smul_eq_mul`, `mul_comm` (step 3 inner)
- `Fin.val_zero`, `Fin.val_one`, `Fin.val_two` (step 5)
- `Finset.card_univ`, `Fintype.card_fin` (step 4)

All present and stable at the pinned SHA — no v4.26.0 regression
detected on the recipe surface.

## 6. Comparison to S2 / S2b / S3 PREP

| Aspect | S2 ACT | S2b ACT | S3 ACT (this) | S3 PREP draft |
|--------|--------|---------|---------------|---------------|
| Target | `¬ IsSumOfCubes 8 23` | same | `¬ IsSumOfFourthPowers 18 79` | same |
| Approach | `native_decide` on `3^8` | counting + `omega` | counting + `omega` | counting + `omega` (sketch) |
| Search space avoided | — (6561 tuples enumerated) | yes | yes (`3^18 ≈ 4·10^8` infeasible) | yes |
| Reflection axiom | `Lean.ofReduceBool` | none | none | none |
| Sorries | 0 | 0 (post BUILD-VERIFY) | 0 | 2 (`htotal`, `hsum`) |
| Lines | 118 | ~141 | ~141 | sketch only |
| File | `LagrangeFourSquaresWaringG2OQ01.lean` | `…Counting.lean` | `…CountingG4.lean` (new) | (memo only) |

This ACT discharges both S3 PREP `sorry` placeholders (`htotal` partition cardinality + `hsum` sum decomposition) via the same Mathlib idiom S2b ACT already used (`Finset.card_eq_sum_card_fiberwise` + `Finset.sum_fiberwise`).

## 7. What's next

Four ACTs remain queued (modulo S7 PREP PR):

1. **S4 ACT** — register `waring_g3_upper` axiom + bridge to `WaringG2OQ01.IsSumOfCubes`. Together with S2 / S2b ACT this gives `waringG 3 = 9` as a semantic claim modulo the correctness chain.
2. **S5 ACT** — `g(5) ≥ 37` via counting+omega. Witness `223 = 6·32 + 31`. Expected size ~150–180 LOC.
3. **S6 ACT** — correctness chain (avoid `legendre_three_squares` dependency per S6c audit).
4. **S6b ACT** — `g(6) ≥ 73`. Witness `703 = 11·64 + 63`.

S5/S6b ACTs are now **routine** ports of this S3 ACT, with only the
arithmetic constants changing per `k`. The template has been
double-validated (S2b at `k = 3`, S3 at `k = 4`) — a future researcher
may consider a parametric `lemma waring_lower_counting_template (k : ℕ)
(s n_k q_k : ℕ) (...)` that subsumes `k = 3..7` in a single proof, per
state.md's parametric-template note.

## 8. Honesty block

This is a routine port of an already-verified recipe (S2b ACT
counting+omega) to a different `k`. No new mathematical insight, no
new Mathlib bearers, no new tactic primitives. The value is purely in
**double-validating the parametric template** and shipping the second
verified instance of the `g(k) ≥ N` lower-bound recipe, which lowers
risk for S5/S6b/S7 ACTs.

The arithmetic table (§4) is mechanical; the case analysis was
verified by `omega` rather than hand-audited.

**No axiom delta** (still 0 axioms in slug) — this is a lower-bound
proof, not a correctness-chain bridge or upper-bound axiomatization.
The S4 ACT axiom registration is the natural follow-up.
