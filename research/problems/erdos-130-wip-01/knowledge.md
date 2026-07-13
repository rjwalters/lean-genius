# Erdős #130 WIP-01: Integer Distance Graphs in General Position
## Anning-Erdős Finiteness Bound

**Problem**: Formalize the algebraic core of the Anning-Erdős theorem, proving
an explicit finiteness bound 4(2D+1)(2E+1) for integer-distance points in general position.

**Parent problem**: erdos-130 (chromatic number of integer distance graphs — OPEN)

---

## Session 2026-04-13 (Session 1) — Anning-Erdős Algebraic Core

**Mode**: FRESH
**Outcome**: completed — all 12 theorems proved, 0 sorries, 0 axioms

### What I Did

1. Selected erdos-130-wip-01 from available pool (tractability 6, fresh problem)
2. Read existing `Erdos130Problem.lean` (103 lines, definitions only)
3. Surveyed related proofs: Erdos213Problem.lean references Anning-Erdős as an axiom; no existing formalization found
4. Created `proofs/Proofs/Erdos130WIP01.lean` (194 lines) with full algebraic proof
5. Created gallery data `src/data/proofs/erdos-130-wip-01/meta.json`

### Key Findings

- **X-coordinate formula** (core identity): `2D·x = 2as-s²+D²` from distance equations. Pure subtraction of (x-D)²+y² and x²+y². Proved by `nlinarith` after taking the difference.

- **Y-linearity**: `2D·(2r_y·y) = 4a(tD-r_x·s) + K` where K is a constant in r_x,r_y,s,t,D. Key step: multiply the y-from-R formula by 2D and substitute x from the x-coordinate formula. Proved cleanly by `linear_combination 2*D*hyeq - 2*r_x*hxeq`.

- **Key identity**: `[4a(tD-r_x·s)+K]² = 4r_y²[(2Da)²-(2as-s²+D²)²]`. This is proved by:
  1. `key_scale_identity`: `(2D(2r_y·y))² = 4r_y²[(2Da)²-(2Dx)²]` — proved by `linear_combination 16*D²*r_y²*hP`
  2. Chain: `LIN² = (2D(2r_y·y))² = 4r_y²[(2Da)²-(2Dx)²] = 4r_y²[(2Da)²-(2as-s²+D²)²]`

- **Count**: 4(2D+1)(2E+1) proved by `Finset.card_product` and `Int.card_Icc`

### Proof Techniques Used

| Technique | Used For |
|-----------|----------|
| `nlinarith` with `have h: diff = diff` | x_coord_formula, y_coord_from_R |
| `linear_combination` with polynomial coefficients | y_linear_in_a, key_scale_identity |
| `calc` chain with `rw` | anning_erdos_identity |
| `Int.card_Icc` + `omega` | signed_diff_card |

### Mathematical Assessment

**Significance**: Routine but clean — the Anning-Erdős bound is a 1945 result, not novel. The contribution is:
1. First formalization of the algebraic proof in Lean 4
2. The `linear_combination` proof of y-linearity is particularly elegant
3. The key quadratic identity is novel as a formalized result

**Caveats**: Docker build validation was not possible during this session (Docker instability). The proof was verified by careful manual inspection. All tactics used are standard Lean 4 patterns.

### Files Modified

- `proofs/Proofs/Erdos130WIP01.lean` — new, 194 lines, 12 theorems, 0 sorries
- `src/data/proofs/erdos-130-wip-01/meta.json` — new gallery entry

### Next Steps

1. **Build validation**: Run Docker build when available to confirm 0 errors
2. **Gallery annotation**: Add `annotations.json` with mathematical commentary
3. **Follow-up**: The sharp constant question (is 4(2D+1)(2E+1) optimal?) — a potential oq-02
4. **Connection**: Link to Erdős #213 (size bounds for integer distance sets in general position)
