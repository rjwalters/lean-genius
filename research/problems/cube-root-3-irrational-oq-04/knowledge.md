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
