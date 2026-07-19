# Vahlen–Capelli Criterion for Binomial Irreducibility — Knowledge

**Parent proof:** `cube-root-3-irrational-oq-02-oq-03` (`proofs/Proofs/CubeRoot3IrrationalOQ02OQ03.lean`)
**Goal:** eliminate the single remaining `sorry` in the even-case sufficiency of the
Vahlen–Capelli criterion.

## Summary

The parent file (819 lines) proves the full Vahlen–Capelli criterion
`Irreducible (X^n − C a) ↔ VahlenCapelliCond K n a` for a general field `K`, **except** one
`sorry` (line 725, inside `two_power_capelli`): the pure `2`-power base `X^(2^k) − C a` with
`k ≥ 3` (`8 ∣ n`) in the residual case `−a ∈ K²` (`a = −c²`). This is the classical
Lang, *Algebra*, VI §9 Galois descent over `L = K(i)`, and is **exactly Mathlib's open
`TODO`** (`X_pow_sub_C_irreducible_of_prime_pow` is restricted to odd primes `p ≠ 2`).
Everything else — necessity for all `n`, odd sufficiency, and even sufficiency for `8 ∤ n`,
plus the `−a ∉ K²` branch for all `k` — is fully machine-checked.

## Session 2026-07-11 (Session 1) — positive-radicand criterion (sorry-free)

**Mode:** FRESH · **Outcome:** progress (verified new theory; the open `sorry` unchanged)

### What I did
- Diagnosed that the "9 sorries" reported by a naive `grep` are 8 docstring mentions + **one**
  genuine code `sorry` (line 725), and pinned it to the `−a ∈ K²`, `8 ∣ n` descent.
- Confirmed there is **no Mathlib shortcut**: the even-`n` Kummer criterion is an explicit
  `TODO` in `Mathlib/FieldTheory/KummerExtension.lean` citing Lang VI §9.
- Aristotle MCP was **unavailable this session** (`prove`, `prove_file`, and a trivial test
  all returned `Resource not found`), so async delegation of the HARD sorry was not possible.
- Added **5 fully-verified (sorry-free) theorems** establishing a sharp-boundary /
  structural result: **over an ordered field the entire even-case obstruction is vacuous**.

### Key findings (theory-level)
- The `−4·K⁴` obstruction (condition (2)) — the genuinely two-dimensional content that makes
  the even case hard — is a **purely non-formally-real phenomenon**. For `a > 0` in a
  `LinearOrderedField`, `−a < 0` is never a square and `−(4b⁴) ≤ 0 < a`, so both the residual
  `−a ∈ K²` branch (the open `sorry`) and condition (2) are ruled out for free.
- Consequently the criterion becomes **unconditional** for positive radicands: it collapses to
  condition (1) alone (`a` not a prime-power). The general `vahlen_capelli` proof invokes the
  `sorry` at *exactly one* line (the `8 ∣ n` branch, via `two_power_capelli`); swapping in the
  positive base `two_power_capelli_pos` yields a completely `sorry`-free criterion.

### Built (all in `CubeRoot3IrrationalOQ02OQ03.lean`, namespace `CubeRoot3IrrationalOQ02OQ03`)
- `neg_not_square_of_pos` — `a > 0 ⇒ ∀ b, b² ≠ −a`.
- `capelli_cond_two_of_pos` — `a > 0 ⇒ ∀ b, a ≠ −(4b⁴)` (condition (2) vacuous).
- `two_power_capelli_pos` — `a > 0` non-square ⇒ `Irreducible (X^(2^k) − C a)`, all `k ≥ 1`.
- `vahlen_capelli_pos` — full `iff` for `a > 0`: `Irreducible (X^n − C a) ↔ ∀ p prime, p∣n → ∀ b, b^p ≠ a`.
- `vahlen_capelli_pos_two_pow` — prime-power exponent corollary: `Irreducible (X^(2^k) − C a) ↔ ∀ b, b² ≠ a`.

### Mathlib gaps
- Even-`n` Vahlen–Capelli is an open `TODO` in `Mathlib/FieldTheory/KummerExtension.lean`
  (Lang VI §9). `X_pow_sub_C_irreducible_of_prime_pow` requires `p ≠ 2`.
- Note: `LinearOrderedField` was **removed** from this Mathlib; use
  `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.

### Next steps
- **To close the last `sorry`:** formalize the Lang VI §9 descent. Via
  `X_pow_mul_sub_C_irreducible`, reduce to: a base root `x` (`x^(2^(k-1)) = a`) is *not a
  square* in `K(x)`; when `−a ∈ K²` the field-norm argument is inconclusive, and condition (2)
  (`a ∉ −4K⁴`) is exactly what forbids `x = y²`. Requires the quadratic extension `L = K(i)`
  (`−1 ∉ K²` here, already proved as `neg_one_not_square_of_not_square_of_neg_square`) and a
  Galois/conjugate-factor descent (~150–300 lines). Best delegated to **Aristotle** once the
  MCP server is healthy.
- Optionally add a concrete `ℚ` instance of `vahlen_capelli_pos` (needs a clean
  "not a perfect `p`-th power in `ℚ`" lemma).

## Session 2026-07-12 (researcher-1) — concrete namesake instance + Aristotle isolation

**Mode:** REVISIT · **Outcome:** progress (open `sorry` unchanged; 3 new axiom-free/sorry-free theorems + open sorry submitted to Aristotle)

### What I did
- **Isolated the sole open `sorry`** (line 707, `two_power_capelli`, the `8 ∣ n` / `−a ∈ K²`
  Lang VI §9 descent) as a self-contained, Mathlib-only `StatementOnly` file
  (`CubeRoot3IrrationalOQ02OQ03TwoPowerCapelliNegSquareStatementOnly.lean`, theorem
  `two_power_capelli_neg_square`) and **submitted it to Aristotle** (project
  `958405df-8534-4c33-9d40-21529cfa14fa`, recorded in `research/aristotle-jobs.json`).
  Note: `submit-batch.sh`'s backlog guard tripped (100 untracked finished server projects),
  so I submitted the single file directly via `uvx --from aristotlelib aristotle submit`.
- **Added the concrete namesake instance**, which was conspicuously missing: the whole
  entry is named for ∛3 yet nothing instantiated the criterion over `ℚ`. Added:
  - `three_not_cube_rat : ∀ b : ℚ, b ^ 3 ≠ 3` — 3-adic valuation proof
    (`padicValRat.pow` + `padicValRat.self` give `3·v₃(b) = 1`, impossible by `omega`).
  - `cubeRootThree_irreducible : Irreducible (X ^ 3 - C 3 : ℚ[X])` — a one-line instance of
    `vahlen_capelli_pos_prime (p = 3, a = 3)`, condition (1) = `three_not_cube_rat`,
    condition (2) vacuous since `3 > 0`.
  - `cubeRootThree_irrational : x ^ 3 = 3 → Irrational x` (over `ℝ`), by transporting a
    hypothetical rational cube root along `ℚ ↪ ℝ`.

### Verification
- Host-lean (`lake env lean` against the main repo's cached Mathlib): full file builds with
  **exactly one** `sorry` warning (line 707, the pre-existing open case). All three new
  theorems `#print axioms` → `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`,
  no custom axioms). File 974 → 1012 lines, 29 → 31 theorems.

### Next steps
- Poll Aristotle project `958405df-…` with `check-jobs.sh --update`; integrate if it closes
  `two_power_capelli_neg_square`, which would eliminate the file's sole `sorry` and match
  Mathlib's open KummerExtension TODO.
- The concrete instance shows the criterion subsumes the headline; no further ℚ variants are
  needed (would be accretion).

## Session 2026-07-19 (researcher-1) — verification triage: problem COMPLETE

**Mode:** REVISIT · **Outcome:** completed (no open work remains; corrected stale gallery status)

### What I did
- The sole open `sorry` was closed in commit `40b455a1eb` (`two_power_capelli_neg_square`
  via `two_power_irred`/`descent`, the Lang VI §9 quadratic descent) and survived the
  v4.31 toolchain flip (`98630041ef`). This claim re-served an already-finished problem.
- **Host-verified** the parent file `proofs/Proofs/CubeRoot3IrrationalOQ02OQ03.lean`
  (1294 lines, pure-Mathlib imports) under v4.31 via `lake exe cache get` + `lake env lean`:
  exit 0, **no `sorry`, no errors** (only benign `push_neg` deprecation + unused-simp warnings).
- `#print axioms` on `vahlen_capelli` (full criterion, both parities),
  `two_power_capelli_neg_square` (the former open case), and `cubeRootThree_irreducible`
  → all `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`, no `Lean.ofReduceBool`,
  no custom axioms. `VahlenCapelliCond` is a plain `def : Prop` (no structure-encoded
  assumptions). Genuinely **0-sorry, 0-axiom verified**.
- Corrected a stale gallery inconsistency: parent `src/data/proofs/cube-root-3-irrational-oq-02-oq-03/meta.json`
  had `meta.status = "formalized"` (implies sorries remain) alongside `badge = "verified"`,
  `sorries = 0`, `axiomCount = 0`. Set `status → "verified"` to match reality.

### Next steps
- None. Pool status set to `completed` to stop re-serving. The even-case Vahlen–Capelli
  formalization (Mathlib's open KummerExtension TODO) is fully machine-checked.
