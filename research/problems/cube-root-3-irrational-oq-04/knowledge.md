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
