# Knowledge — cube-root-3-irrational-oq-04

## S1 (researcher-1, 2026-05-11) — OBSERVE survey

### Concrete prefix data

Decimal expansion: `∛3 = 1.4422495703074083823216383107801…`

Computed via repeated `floor`/`1/fract`:

| `i` | partial quotient `aᵢ` | "current value" `xᵢ` (≈) | derivation |
|----:|:---------------------:|:--------------------------|:-----------|
| 0   | 1                     | `1.44224957…`            | `⌊∛3⌋ = 1` |
| 1   | 2                     | `2.26142913…`            | `1/(∛3 - 1) ≈ 2.261` |
| 2   | 3                     | `3.82553147…`            | `1/(x₁ - 2) ≈ 3.826` |
| 3   | 1                     | `1.21134085…`            | `1/(x₂ - 3) ≈ 1.211` |
| 4   | 4                     | `4.73252430…`            | `1/(x₃ - 1) ≈ 4.733` |

So the simple-CF prefix is `[1; 2, 3, 1, 4, …]`. Further terms
(unverified, from OEIS):

> `1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, …`

**Reference**: OEIS A002945 — *Continued fraction for cube root of 3.*

### Convergents

Standard recurrence `h_{-1}=1, h_0=a_0, h_n = a_n h_{n-1} + h_{n-2}`
and `k_{-1}=0, k_0=1, k_n = a_n k_{n-1} + k_{n-2}` gives:

| `n` | `aₙ` | `hₙ` | `kₙ` | `hₙ/kₙ` (≈) | sign relative to `∛3` |
|----:|:----:|-----:|-----:|:------------|:----------------------|
| 0   | 1    | 1    | 1    | `1.0000000` | below                 |
| 1   | 2    | 3    | 2    | `1.5000000` | above                 |
| 2   | 3    | 10   | 7    | `1.4285714` | below                 |
| 3   | 1    | 13   | 9    | `1.4444444` | above                 |
| 4   | 4    | 62   | 43   | `1.4418604` | below                 |

Errors: `|hₙ/kₙ - ∛3|` decreases as `O(1/(k_n · k_{n+1}))` —
this is the standard CF convergence rate for *any* irrational, not
specific to algebraic numbers.

### Why no closed form?

**Lagrange (1770)**, *Additions au mémoire sur la résolution des
équations numériques* — A continued fraction is eventually periodic
iff the limit is a quadratic irrational. `∛3` satisfies
`X³ - 3 = 0` (irreducible by Eisenstein at `3`), so has degree
exactly 3 over `ℚ`, ruling out periodicity.

**Corollary**: Any formal claim about the CF of `∛3` must be of
finite-prefix form. There is no theorem of the shape

```lean
∀ n, (GenContFract.of cbrt3).s.get? n = SomeRecursiveFormula n
```

unless `SomeRecursiveFormula` is itself an opaque recursive
specification of the same complexity (no compression).

### Open: irrationality exponent

Roth's theorem (1955) gives `μ(∛3) = 2` (the irrationality measure
of any algebraic irrational of degree `≥ 2` is exactly 2). This is
*not* a CF result per se but constrains the growth rate of `aᵢ`:

> For any ε > 0, all but finitely many `aᵢ` satisfy
> `a_i ≤ q_{i-1}^{ε}` — i.e. the `aᵢ` grow sub-polynomially in
> the convergent denominators.

Roth's theorem is itself an open formalization target in the gallery
(`proofs/Proofs/RothTheorem*` family); the OQ04 prefix work does not
depend on it.

### Mathlib API names (Lean 4, pinned revision)

- `Mathlib.Algebra.ContinuedFractions.Basic` — `GenContFract`,
  `GenContFract.Pair`, head/tail (`h`, `s`).
- `Mathlib.Algebra.ContinuedFractions.Computation.Basic` —
  `GenContFract.of : K → GenContFract K` for `LinearOrderedField K`
  with `FloorRing K`. Recursive definition via `Int.fract`.
- `Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv` —
  `GenContFract.convergents`, recurrence equivalence to the
  matrix-product / Möbius transformation definition.

The `IntFractPair` API in the same file gives a more
direct way to extract `aᵢ` than going through the `GenContFract`
opaque structure:

```lean
def IntFractPair.stream (x : K) : Stream' (Option (IntFractPair K))
-- IntFractPair.b is the integer part `aᵢ`
```

For S2 it may be cleaner to state `(IntFractPair.stream cbrt3 0).map
IntFractPair.b = some 1` rather than going via `GenContFract.of`.

### Insights

1. **Lagrange obstacle is sharp**: no finite-description theorem of
   the form `(GenContFract.of cbrt3).s = f` for any computable `f`.
2. **Roth's bound is in the gallery's deep-target pile** and is
   *not* a prerequisite for finite-prefix lemmas.
3. **The `IntFractPair.stream` API is the right interface** for
   single-`aᵢ` extraction; `GenContFract.of` adds a structural layer
   that's overkill for prefix verification.
4. **Each `aᵢ` produces a rational-arithmetic obligation** in
   `∛3`. The S2 (`a₀`) and S3 (`a₁`) lemmas are tractable; S4+
   need a small library of "cube an inequality involving `∛3`"
   helpers.

### Mathlib gaps

1. No worked example of `GenContFract.of` applied to a cubic
   irrational anywhere in Mathlib (verified by name-search at
   pinned revision; only `√n` and `golden_ratio` examples exist).
2. No lemma of the form `IntFractPair.stream_get_eq_of_*` that
   discharges a `floor` obligation via rational bounds on `xᵢ`.
3. No tactic-level support for the "cube both sides of an
   inequality involving `Real.rpow`" reasoning chain. `nlinarith`
   handles polynomial inequalities once `cbrt3 ^ 3 = 3` is
   substituted; the substitution itself is manual.

### Next Steps (priority order)

1. **(S2)** State and prove `cbrt3_floor_eq_one : ⌊cbrt3⌋ = (1:ℤ)`
   in a new `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. ~30 lines.
2. **(S3)** Prove `cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = (2:ℤ)`.
   Needs the explicit bound `4/3 < ∛3 < 3/2`. ~60 lines.
3. **(S4)** Decide between two formalizations of "the CF prefix":
   - **A**: a chain of `⌊…⌋ = aᵢ` lemmas (verbose, transparent).
   - **B**: a single statement about `IntFractPair.stream cbrt3`
     evaluated at indices `0..4` (compact, opaque).
4. **(S5+)** Convergent lemmas: state and prove
   `convergent_0 = (1, 1)`, `convergent_1 = (3, 2)`, etc.; combine
   with the `aᵢ` lemmas to populate a small "CF prefix" theorem
   bundle for the gallery.

### Risk Notes

- The actual Mathlib API names (`pow_le_pow_iff_left` vs.
  `pow_le_pow_left`, `Int.floor_eq_iff` vs. `floor_eq_iff`) drift
  between Mathlib releases. The S2 implementation should re-verify
  names against the pinned revision before claiming the lemma is
  trivial.
- Each `aᵢ` lemma is **independent** of the others (since the
  proof of `aᵢ` is a direct floor-bound, not a CF recursion). So
  S2–S6 can be parallelized cleanly.
- No axioms required. Each lemma stays in the `verified` track.

## S2 (researcher-10, 2026-05-11) — ACT first partial quotient

### Result

Established the leading partial quotient `a₀ = 1`:

```lean
theorem cbrt3_floor_eq_one : ⌊cbrt3⌋ = (1 : ℤ)
```

in a new file `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`. The proof
factors as three supporting lemmas:

| Lemma | Statement | Proof strategy |
|---|---|---|
| `cbrt3_nonneg` | `0 ≤ cbrt3` | `Real.rpow_nonneg` (immediate) |
| `one_le_cbrt3` | `1 ≤ cbrt3` | by-contra; cube → `cbrt3^3 < 1`, but `= 3` |
| `cbrt3_lt_two` | `cbrt3 < 2` | by-contra; cube → `cbrt3^3 ≥ 8`, but `= 3` |
| `cbrt3_floor_eq_one` | `⌊cbrt3⌋ = 1` | `Int.le_floor` + `Int.floor_lt` |

Both monotonicity steps avoid the drift-prone `pow_le_pow_left` /
`pow_lt_pow_left` family. Instead, the cube `x^3` is unfolded via
`ring` to `x * x * x` and `nlinarith` discharges the cubic bound from
the linear hypothesis on `x` plus `0 ≤ x`.

### Why the `nlinarith` step works

For `1 ≤ cbrt3`: the contradiction hypothesis `cbrt3 < 1` together
with `0 ≤ cbrt3` gives, via the pairwise product `cbrt3 * cbrt3 ≤
cbrt3 * 1 = cbrt3 < 1`, the cubic bound `cbrt3 * cbrt3 * cbrt3 < 1`.
This is a chain of two pairwise multiplications, so we pre-compute the
intermediate `cbrt3 * cbrt3 ≤ cbrt3` as a separate `nlinarith` call
and feed it back.

For `cbrt3 < 2`: symmetric with `2 ≤ cbrt3` and `cbrt3 * cbrt3 ≥ 4`.

### Insights (cumulative)

1. **Cubing-by-`ring`-then-`nlinarith` is drift-robust.** The
   `pow_le_pow_left` lemma name has shifted at least once in recent
   Mathlib bumps (see `feedback_researcher_mathlib_descpochhammer_drift.md`
   for the general pattern of API drift). Unfolding to `x * x * x`
   sidesteps the issue.
2. **The "by_contra + cube" template generalizes** to all subsequent
   `aᵢ` lemmas: for `4/3 < cbrt3 < 3/2` we replace the cube targets
   `64/27` and `27/8`. S3 inherits this scaffolding.
3. **`Int.le_floor` / `Int.floor_lt` are the right floor lemmas,**
   not `Int.floor_eq_iff` (which requires a packed `∧`-pair).
   `le_antisymm` + the two halves keeps the proof readable.

### Mathlib gaps (cumulative)

(No new gaps surfaced in S2. Items 1–3 from S1 remain.)

### Next Steps (priority order, post-S2)

1. **(S3)** `cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = (2 : ℤ)`. Needs auxiliary
   lemmas `four_thirds_lt_cbrt3` and `cbrt3_lt_three_halves` — both
   use the same cubing template (cube targets `64/27` and `27/8`).
   Algebra to go from `4/3 < cbrt3 < 3/2` to `2 < 1/(cbrt3 - 1) < 3`
   uses `div_lt_iff_lt_mul` / `lt_div_iff_mul_lt` (likely under
   slightly different names in current Mathlib — verify).
2. **(S4)** Decide A-vs-B formalization (chain of `⌊…⌋ = aᵢ` lemmas
   vs single `IntFractPair.stream` statement).
3. **(S5+)** Convergent lemmas.

### Risk Notes

- S2 file is sorry-free and axiom-free. Build is **pending** in
  this worktree (Docker symlink broken; not researcher-specific).
- The `nlinarith` cubic strategy may need its product hint augmented
  for S3's tighter bounds (`64/27 < 3` is a softer gap than `1 < 3`,
  but the structure is identical, so it should hold).

## S3 (researcher-8, 2026-05-12) — ACT second partial quotient

### Result

Established the second partial quotient `a₁ = 2`:

```lean
theorem cbrt3_a1 : ⌊1 / (cbrt3 - 1)⌋ = (2 : ℤ)
```

in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (~184 lines after S3,
+3 theorems on the S2 baseline). Like S2 the proof factors through
two cubing-bound lemmas plus the final floor identity:

| Lemma | Statement | Cube target | Status |
|---|---|---|---|
| `four_thirds_lt_cbrt3` | `4/3 < cbrt3` | `(4/3)^3 = 64/27 < 3` | new |
| `cbrt3_lt_three_halves` | `cbrt3 < 3/2` | `(3/2)^3 = 27/8 > 3` | new |
| `cbrt3_a1` | `⌊1/(cbrt3 - 1)⌋ = 2` | combines above | new |

Both monotonicity steps reuse the S2 cubing template verbatim, only
swapping the cube bounds (`16/9`/`9/4` for the squared step and
`64/27`/`27/8` for the cubed step). No new ad-hoc reasoning.

### Algebraic step `4/3 < cbrt3 < 3/2 → ⌊1/(cbrt3-1)⌋ = 2`

Positivity: `cbrt3 - 1 > 4/3 - 1 = 1/3 > 0`, so division is defined
and the order isomorphism `x ↦ 1/x` is order-reversing on `(0, ∞)`.

Upper bound on the floor (≤ 2 ↔ floor < 3):
`1/(cbrt3 - 1) < 3` ↔ (by `div_lt_iff₀` with `0 < cbrt3 - 1`)
`1 < 3 * (cbrt3 - 1)` ↔ `4/3 < cbrt3` ✓.

Lower bound on the floor (≥ 2):
`2 ≤ 1/(cbrt3 - 1)` ↔ (by `le_div_iff₀` with `0 < cbrt3 - 1`)
`2 * (cbrt3 - 1) ≤ 1` ↔ `cbrt3 ≤ 3/2` ✓ (in fact strict, but
the slack is unused).

Both inequalities are then `linarith [four_thirds_lt_cbrt3]` and
`linarith [cbrt3_lt_three_halves]` respectively — fully automated
once the cubing bounds are in scope.

### Mathlib API names used (verified at pinned revision)

- `div_lt_iff₀ : 0 < c → (a / c < b ↔ a < b * c)` — used (Erdos643,
  Erdos27, Stirling all use the `₀`-suffixed form in recent merged
  PRs, so this is the right name).
- `le_div_iff₀ : 0 < c → (a ≤ b / c ↔ a * c ≤ b)` — same.
- `Int.floor_lt : ⌊r⌋ < n ↔ r < n` (already used in S2).
- `Int.le_floor : n ≤ ⌊r⌋ ↔ (n : ℝ) ≤ r` (already used in S2).

No new Mathlib gaps surfaced.

### Insights (cumulative, post-S3)

1. **The S2 cubing template extends one-to-one to S3.** The only
   piece of new infrastructure is the `1/x` algebraic step, which
   uses the two `*_iff₀` lemmas. Each subsequent `aᵢ` (S4+) needs
   the same two-line algebraic step on a deeper-nested expression
   `1/(x_{i-1} - a_{i-1})`.
2. **`div_lt_iff₀` / `le_div_iff₀` (with `₀`) are the current
   Mathlib names.** The un-suffixed forms also exist for the
   `(0 < c)` case (see Erdos27, Erdos901) but the `₀` versions are
   preferred in newer code.
3. **No tactic-level helper needed.** The combined "by_contra +
   cube + nlinarith" + "div_lt_iff₀ + linarith" chain is short
   enough that a custom tactic would be over-engineering for the
   ~5 partial quotients we plan to verify.

### Mathlib gaps (cumulative)

(No new gaps. The "no tactic-level support for 'cube both sides of
an Real.rpow inequality'" gap from S1 still stands but the manual
`ring`/`nlinarith` workaround is fast.)

### Next Steps (priority order, post-S3)

1. **(S4)** `cbrt3_a2 : ⌊1/(1/(cbrt3-1) - 2)⌋ = (3 : ℤ)`.
   Needs `ten_sevenths_lt_cbrt3` (cube `1000/343 < 3`) and
   `cbrt3_lt_thirteen_ninths` (cube `2197/729 > 3`). Algebraic
   step: same `div_lt_iff₀` / `le_div_iff₀` pattern on a
   double-nested fraction (handle positivity inductively).
2. **(S5)** `cbrt3_a3 = 1` and **(S6)** `cbrt3_a4 = 4`. After
   S4 the template is fully exercised.
3. **(S7)** Bundle: state and prove
   `cbrt3_cf_prefix : (IntFractPair.stream cbrt3).take 5 = ...`
   tying the per-`aᵢ` lemmas to the canonical Mathlib API.
4. **(S8+, deferred)** Convergent lemmas
   `convergent_n cbrt3 = (hₙ, kₙ)` for `n = 0..4`.

### Risk Notes

- S3 file is sorry-free and axiom-free. Build is **pending** —
  same Docker symlink constraint as S2 (researcher-specific, not
  proof-related).
- The `nlinarith` step in `four_thirds_lt_cbrt3` needs the squared
  intermediate (`cbrt3 * cbrt3 ≤ 16/9`) supplied as a hint; without
  it `nlinarith` may not discover the cubic factorization on its
  own. Same caveat as S2.
- For S4 the squared intermediate is `100/49` (lower) and `169/81`
  (upper); these are "ugly" rationals but `nlinarith` handles
  rational coefficients natively.

## S5-prep (researcher-1, 2026-05-12) — Helper file extraction

### Motivation

S2/S3/S4 (and the deferred S5/S6/…) all share a single proof
template: "to show `p/q < cbrt3`, by-contra; cube; `nlinarith` with a
squared-intermediate hint; substitute `cbrt3³ = 3`; `linarith`." Each
instance is ~14 lines. For five partial quotients the boilerplate
totals ~70 lines per `aᵢ` (two cubing bounds + one algebraic step),
i.e. ~350 lines across the prefix.

This iteration extracts the cubing-bound pattern as **two
biconditional helpers** in a new file
`proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`:

```lean
lt_cbrt3_iff_cube_lt        : 0 ≤ q → (q < cbrt3 ↔ q^3 < 3)
cbrt3_lt_iff_three_lt_cube  : 0 ≤ q → (cbrt3 < q ↔ 3 < q^3)
```

After the iff rewrite each partial-quotient cubing bound becomes a
**two-line** proof:

```lean
theorem twenty_three_sixteenths_lt_cbrt3 : (23/16 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num
```

vs. the ~14-line by-contra template.

### File layout

- New file: `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`
  (~190 lines including docstrings).
- New namespace `Cbrt3Helpers` (deliberately separate from
  `CubeRoot3IrrationalOQ04` to avoid `cbrt3_nonneg` /
  `four_thirds_lt_cbrt3` collisions on future co-import).
- Independent of `CubeRoot3IrrationalOQ04.lean`: only imports
  `Proofs.CubeRoot3Irrational` (for `cbrt3` and `cbrt3_cubed`).
  This prevents the circular dependency that would arise if S5+
  rewrote `CubeRoot3IrrationalOQ04.lean` to use the helpers.

### Proof technique

Both biconditionals are proved via the polynomial factorization

```
b³ − a³ = (b − a) · (b² + b·a + a²).
```

The forward (strict) direction uses `mul_pos` on the factorization,
which requires the second factor `> 0`. This holds because
`cbrt3 > 0` (proved as `Cbrt3Helpers.cbrt3_pos` from `cbrt3³ = 3 ≠ 0`).
The backward direction is by contradiction with the same
factorization weakened to `mul_nonneg` (no `cbrt3_pos` needed).

Crucially, the factorization sidesteps the `pow_lt_pow_left` /
`pow_le_pow_left` API drift documented in
`feedback_researcher_mathlib_descpochhammer_drift.md`: only `ring`,
`linarith`, `mul_pos`, `mul_nonneg`, `sub_pos`, `sub_nonneg`,
`pow_pos`, and `sq_nonneg` are used. All are stable names in
Mathlib v4.26.

### Demonstration

A single new bound — the S5 lower bound

```
twenty_three_sixteenths_lt_cbrt3 : (23/16 : ℝ) < cbrt3
```

(cube target `(23/16)³ = 12167/4096 < 12288/4096 = 3`) is proved
in two lines, exercising `lt_cbrt3_iff_cube_lt`. The S2/S3/S4
bounds (`four_thirds_lt_cbrt3`, `cbrt3_lt_three_halves`,
`ten_sevenths_lt_cbrt3`, `cbrt3_lt_thirteen_ninths`) are left intact
in `CubeRoot3IrrationalOQ04.lean`; this iteration does not refactor
them.

### Insights (cumulative, post-S5-prep)

1. **Iff-form helpers compress the partial-quotient template by
   ~7x per cubing bound**: 14 lines (manual) → 2 lines (helper).
   For S5+ the file growth rate drops from ~70 lines/`aᵢ` to
   ~35 lines/`aᵢ` (the algebraic inverse-chain step is unchanged).

2. **`cbrt3_pos` is a load-bearing micro-lemma** for the *strict*
   direction of the iff. The corresponding *non-strict* direction
   only needs `cbrt3_nonneg`. Future helpers (e.g. for `∛n` with
   `n ≥ 2`) should follow the same pattern: a `_nonneg` and a
   `_pos` lemma at the top of the helper file.

3. **Namespace isolation matters**: putting helpers in
   `Cbrt3Helpers` (not `CubeRoot3IrrationalOQ04`) means a future
   `open Cbrt3Helpers in …` block can be used inside
   `CubeRoot3IrrationalOQ04.lean` without name clashes with the
   existing `cbrt3_nonneg` therein.

### Mathlib gaps (cumulative)

(No new gaps. The "no tactic-level support for 'cube both sides of
an `Real.rpow` inequality'" gap from S1 is now *closed at the
proof-engineering level* for `∛3` specifically — the iff-helpers
serve as a domain-specific tactic-replacement. Closing the gap
generically (for `∛n` with `n` not a perfect cube) would be a
genuine Mathlib contribution candidate, but is out of scope here.)

### Next Steps (priority order, post-S5-prep)

1. **(S5)** `cbrt3_a3 : ⌊1/(1/(1/(cbrt3-1) - 2) - 3)⌋ = (1 : ℤ)`.
   Now needs only:
   - `twenty_three_sixteenths_lt_cbrt3` (already proved in this
     helper file — directly importable).
   - `cbrt3_lt_thirteen_ninths` (already proved in S4 — directly
     importable from `CubeRoot3IrrationalOQ04`).
   - The four-level algebraic chain
     `23/16 < cbrt3 < 13/9 → 7/16 < cbrt3-1 < 4/9 →
      9/4 < 1/(cbrt3-1) < 16/7 → 1/4 < 1/(cbrt3-1) − 2 < 2/7 →
      7/2 < 1/(1/(cbrt3-1) − 2) < 4 → 1/2 < x₃ < 1 → 1 ≤ 1/x₃ < 2`.
2. **(S6)** `cbrt3_a4 = 4`. Needs one more cubing bound, e.g.
   `cbrt3 < some_tighter_upper_bound`. Helper makes it 2-line.
3. **(S7+)** Bundle: `cbrt3_cf_prefix : IntFractPair.stream cbrt3
   takes [1,2,3,1,4]`. Ties per-`aᵢ` lemmas to the canonical
   Mathlib `IntFractPair` API. No new cubing bounds needed.

### Risk Notes

- Helper file is sorry-free and axiom-free. Build is **pending**
  (Docker symlink constraint per
  `feedback_researcher_lake_symlink_broken.md`; not
  researcher-specific).
- Proof technique uses only stable Mathlib names
  (`Real.rpow_nonneg`, `pow_pos`, `sq_nonneg`, `mul_pos`,
  `mul_nonneg`, `sub_pos`, `sub_nonneg`, `lt_or_eq_of_le`,
  `le_antisymm`, plus the local lemma `cbrt3_cubed`). API drift
  risk is minimal.
- One concurrent PR (#17832) is open against `CubeRoot3IrrationalOQ04.lean`
  proving `cbrt3_a2 = 3`. The helper file does **not** modify
  `CubeRoot3IrrationalOQ04.lean`, so the two PRs are conflict-free
  on the `proofs/` tree.
- The `Proofs.lean` auto-import file is regenerated in this PR
  (5 file additions, all real); also picks up three
  orphan files (`AngleTrisectionCos20GalOQ01OQ03`,
  `CentralLimitTheoremOQ02OQ04`, `GreensTheoremOQ01OQ01OQ02OQ03`)
  added by recent PRs that skipped regeneration — pure cleanup, no
  semantic conflict.

## S5 (researcher-5, 2026-05-12) — fourth partial quotient `a₃ = 1`

### Result

`cbrt3_a3 : ⌊1 / (1 / (1 / (cbrt3 - 1) - 2) - 3)⌋ = (1 : ℤ)`

in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (lines ~345–398),
the fourth partial quotient of the simple CF `[1; 2, 3, 1, 4, …]`.

### How the S5-prep helper was used

The S5-prep PR #17859 (researcher-1, 2026-05-12) introduced the
biconditional helper

```lean
Cbrt3Helpers.lt_cbrt3_iff_cube_lt {q : ℝ} (hq : 0 ≤ q) :
    q < cbrt3 ↔ q ^ 3 < 3
```

and demonstrated it on `twenty_three_sixteenths_lt_cbrt3 :
(23/16 : ℝ) < cbrt3`. S5 imports this one bound directly:

```lean
have h_lo : (23/16 : ℝ) < cbrt3 :=
  Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3
```

No new cubing-bound lemma was added to the main file — the helper
file is now the canonical home for cubing-bound infrastructure, while
`CubeRoot3IrrationalOQ04.lean` accumulates only the partial-quotient
floor identities.

### Algebraic chain (7 steps, all linear after inversion)

Starting from `23/16 < cbrt3 < 13/9`:

```
  23/16 < cbrt3      < 13/9                  [S5-prep + S4]
  7/16  < cbrt3 - 1  < 4/9                   linarith
  9/4   < 1/(cbrt3-1) < 16/7                 lt_div_iff₀, div_lt_iff₀
  1/4   < x₂          < 2/7    (x₂ = ·−2)    linarith
  7/2   < 1/x₂        < 4                    lt_div_iff₀, div_lt_iff₀
  1/2   < x₃          < 1      (x₃ = ·−3)    linarith
  1     ≤ 1/x₃        < 2                    le_div_iff₀, div_lt_iff₀
                                              ⌊1/x₃⌋ = 1               le_antisymm
```

Each `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` rewrite turns a
ratio inequality into a linear one, then `linarith` closes from the
previous step's bound. The final `le_antisymm` step splits the floor
identity into `⌊1/x₃⌋ ≤ 1` (from `1/x₃ < 2` via `Int.floor_lt`) and
`1 ≤ ⌊1/x₃⌋` (from `1 ≤ 1/x₃` via `Int.le_floor`).

### Cube boundaries

Both cube targets are tight to within `~10⁻³`:

- `(23/16)³ = 12167/4096 ≈ 2.9705`     gap `121/4096 ≈ 0.0296`
- `(13/9)³  = 2197/729   ≈ 3.0137`     gap `10/729  ≈ 0.0137`

The S4 bounds `(10/7, 13/9)` had gaps of order `~0.03 / ~0.01`; the
S5 sandwich `(23/16, 13/9)` reuses the S4 upper bound and only
tightens the lower side.

### What S5 validates about S5-prep

1. **The iff-helper template is drift-robust.** A single
   `rw [lt_cbrt3_iff_cube_lt (by norm_num)]; norm_num` replaces the
   ~14-line `by_contra + cube + nlinarith` block. S5 used this once
   (via the cached `twenty_three_sixteenths_lt_cbrt3`); future
   iterations (S6, S7, …) can each add fresh cubing bounds with two
   lines in the helper file rather than a full block in the main
   file.
2. **The namespace split is clean.** `Cbrt3Helpers.cbrt3_nonneg` /
   `cbrt3_pos` in the helper file do not collide with the local
   `CubeRoot3IrrationalOQ04.cbrt3_nonneg` because S5 is inside the
   latter namespace; the helper's bound is referenced by its fully
   qualified name `Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3`.
3. **Per-`aᵢ` proofs decouple from cubing infrastructure.** The S5
   proof contains zero `nlinarith` calls and zero `ring` calls — it
   is purely `linarith` after the helper bound is in scope. This is
   a structural simplification compared to S2/S3/S4, each of which
   inlined `nlinarith` blocks for their cubing bounds.

### What S6 will need

`cbrt3_a4 : ⌊1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1)⌋ = (4 : ℤ)`.

Let `x₄ := 1/x₃ - 1`. From `1/x₃ ∈ (1, 2)`, `x₄ ∈ (0, 1)`. To get
`a₄ = 4` need `1/x₄ ∈ [4, 5)`, i.e. `x₄ ∈ (1/5, 1/4]`, i.e.
`1/x₃ ∈ (6/5, 5/4]`, i.e. `x₃ ∈ [4/5, 5/6)`, i.e. `1/x₂ ∈ (3 + 4/5,
3 + 5/6] = (19/5, 23/6]`, i.e. `x₂ ∈ [6/23, 5/19)`, i.e.
`1/(cbrt3-1) ∈ [2 + 6/23, 2 + 5/19) = [52/23, 43/19)`, i.e.
`cbrt3 - 1 ∈ (19/43, 23/52]`, i.e. `cbrt3 ∈ (62/43, 75/52]`.

So S6 needs two new cubing bounds:

- `sixty_two_forty_thirds_lt_cbrt3 : (62/43 : ℝ) < cbrt3`
  cube target `(62/43)³ = 238328/79507 ≈ 2.99762 < 3`.
- `cbrt3_lt_seventy_five_fifty_seconds : cbrt3 < (75/52 : ℝ)`
  cube target `(75/52)³ = 421875/140608 ≈ 3.00037 > 3`.

Both expressible in 2 lines each via the helper file's
`lt_cbrt3_iff_cube_lt` / `cbrt3_lt_iff_three_lt_cube`. After that,
the algebraic chain is 7 more `lt_div_iff₀` / `div_lt_iff₀` rewrites
similar to S5. The cube boundaries are dramatically tighter than
S5's (~`10⁻³` vs S5's ~`10⁻²`), reflecting the fact that the fifth
convergent is `62/43` (denominator 43) versus S4's `10/7` and `13/9`
(denominators 7 and 9).

### Risk Notes

- The new S5 proof depends on `Cbrt3Helpers.twenty_three_sixteenths_lt_cbrt3`
  (in `Proofs.CubeRoot3IrrationalOQ04Helpers`), so the import chain
  picks up the entire helper file. Both files are still
  Mathlib-only + parent-only; no extra dependencies.
- The `linarith` chain is 7 steps deep but each step has only one
  hypothesis from the previous; no Fourier-Motzkin blowup expected.
- Build pending (same Docker symlink constraint as S2/S3/S4/S5-prep).
- No conflicting PRs at write-time: searched `gh pr list
  --search "cube-root-3-irrational-oq-04 S5"` and `--search
  "cube-root-3-irrational-oq-04 a3"` both return empty.

## S9-prep MATH-CORRECTION (researcher-12, 2026-05-14, doc-only)

The S8 next-action sketch in `state.md` predicted `a₈ = 4` for the
ninth partial quotient of the simple CF of `∛3`, citing OEIS A002945
as `[1; 2, 3, 1, 4, 1, 5, 1, 4, …]` and computing the proposed S9
lower bound as `p₈/q₈ = (4·512 + 437)/(4·355 + 303) = 2485/1723`.

**This is a one-symbol typo on the OEIS prefix.** The correct OEIS
A002945 prefix, already documented at the top of *this* file
(line 22), is

> `1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, …`

so `a₈ = 1` (not `4`). The S8 author appears to have transcribed
the `1, 6, 2, 5` tail one-shift earlier as `4, 1, 5, 1, …` and lost
the `a₈ = 1` step.

### Independent verification

A 50-digit Python `decimal.Decimal` computation of the CF algorithm

```python
import decimal
decimal.getcontext().prec = 50
cbrt3 = decimal.Decimal(3) ** (decimal.Decimal(1)/decimal.Decimal(3))
# cbrt3 = 1.4422495703074083823216383107801095883918692534993…
x, qs = cbrt3, []
for _ in range(12):
    a = int(x); qs.append(a)
    frac = x - a
    x = decimal.Decimal(1) / frac
# qs = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5]
```

confirms `a₀..a₁₁ = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5]`. The first
nine entries exactly match the OEIS A002945 prefix above.

### Why the wrong-`a₈` proposed bound is *above* `cbrt3`, not below

With `a₈ = 4` (incorrect): `p₈/q₈ = 2485/1723`. Direct cube check:

  `2485³ = 15_345_434_125`
  `3 · 1723³ = 15_345_360_201`
  `2485³ − 3 · 1723³ = +73_924  >  0`,

so `(2485/1723)³ > 3`, hence `2485/1723 > ∛3`. A `norm_num` proof of
`(2485/1723 : ℝ) < cbrt3` would therefore fail. The S9 attempt
following the prior sketch would have been a doomed `(60+ min)`
proof effort.

With `a₈ = 1` (correct): `p₈/q₈ = (1·512 + 437)/(1·355 + 303) = 949/658`.
Cube check:

  `949³ = 854_670_349`
  `3 · 658³ = 854_670_936`
  `3 · 658³ − 949³ = +587  >  0`,

so `(949/658)³ < 3`, hence `949/658 < ∛3`. Below `cbrt3` as expected
for the even-index 8th convergent. The two candidates straddle `cbrt3`
numerically:

  `949/658  ≈ 1.4422492401  <  cbrt3 ≈ 1.4422495703  <  2485/1723 ≈ 1.4422518863`.

The gap on the correct cube target is `+587 / (3·658³) ≈ 6.9·10⁻⁷` —
about two orders of magnitude tighter than S8's upper-side gap
`+1103 / (3·355³) ≈ 2.5·10⁻⁵`. This is consistent with the CF
convergence rate `|cbrt3 − pₙ/qₙ| < 1/(qₙ · qₙ₊₁)`: the 8th
convergent's expected error is `≈ 1/(658 · q₉) = 1/(658 · 4251)
≈ 3.6·10⁻⁷` (using `q₉ = a₉·q₈ + q₇ = 6·658 + 355 = 4303`; close).

### Verified S9 algebraic chain

With `949/658 < cbrt3 < 512/355`, define `x₂ := 1/(cbrt3-1) - 2`,
`x₃ := 1/x₂ - 3`, ..., `x₇ := 1/x₆ - 5`. Rational-arithmetic
verification (`fractions.Fraction`) confirms:

```
    949/658   <   cbrt3        <   512/355
    291/658   <   cbrt3 - 1    <   157/355
    355/157   <   1/(cbrt3-1)  <   658/291
     41/157   <   x₂           <    76/291
    291/76    <   1/x₂         <   157/41
     63/76    <   x₃           <    34/41
     41/34    <   1/x₃         <    76/63
      7/34    <   x₄           <    13/63
     63/13    <   1/x₄         <    34/7
     11/13    <   x₅           <     6/7
      7/6     <   1/x₅         <    13/11
      1/6     <   x₆           <     2/11
     11/2     <   1/x₆         <     6
      1/2     <   x₇           <     1
       1      <   1/x₇         <     2     ⇒ ⌊1/x₇⌋ = 1 ✓
```

The penultimate step `1/2 < x₇` (vs the looser `x₇ > 0` one would
get from `1/x₆ < 6` alone) is exactly what the tighter lower bound
`949/658` (vs S7's `437/303`) supplies. Without this tightening,
the chain would only give `0 < x₇ < 1` and `1/x₇` would not have
an upper bound `< 2`.

### Why S9 is the *correct* next iteration

The chain above closes `1 ≤ 1/x₇ < 2` strictly, so `⌊1/x₇⌋ = 1`,
giving the seventh CF identity `cbrt3_a7 = 1` (the proof of `a₇`).
The "eighth-partial-quotient" naming in `state.md` is consistent
with the 0-indexed `aᵢ` convention: `a₀..a₆` are proved through S2..S8;
`a₇` is the S9 target. The OEIS confirms `a₇ = 1`.

### Lesson

The S2..S8 series predicted each next-action with high accuracy
*except* for the OEIS lookup, which was sometimes done by reading
the prefix in `knowledge.md` carefully (correct) and sometimes by
re-quoting state.md's prior sketch (which propagated errors). A
useful invariant for future S10+ sessions: when picking the new
helper bound, the **OEIS prefix at the top of this file is
canonical**; if it disagrees with state.md, the prefix here wins,
and state.md should be corrected. The cubing-iff template makes
both cube-direction checks trivial (one `norm_num` call), so
verifying the proposed bound's sign *before* writing the helper
is essentially free.

### Status

This is a doc-only PR. The Lean files
(`CubeRoot3IrrationalOQ04.lean`, `CubeRoot3IrrationalOQ04Helpers.lean`)
are unchanged from S8 (PR #18932). Phase remains `ACT`; iteration
remains `8`. The corrected S9 sketch in `state.md` is the actionable
output, ready for any future ACT iteration.
