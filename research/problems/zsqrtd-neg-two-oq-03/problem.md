# Problem: x²+ny² Representations for n ∈ {3, 7, 11} — Parallel Constructions

## Statement

### Plain Language

The parent gallery proof `zsqrtd-neg-two` formalizes the case `n = 2`:
primes `p ≡ 1, 3 (mod 8)` are representable as `x² + 2y²`. The
construction uses `ℤ[√-2]` as a Euclidean domain, with norm
`N(a + b√-2) = a² + 2b²`, and applies a single-line splitting argument
via `ZMod.exists_sq_eq_neg_two_iff` (Mathlib's second supplementary
law for `(-2/p)`).

OQ-03 asks: **can the same proof template be replayed for n ∈ {3, 7, 11}**,
the next three values of `n` such that `ℚ(√-n)` is an imaginary quadratic
field of class number 1? Concretely, the open question has three
interlocking sub-questions:

1. **Direct Lean port for n = 3**: prove `∀ prime p ≡ 1 (mod 3) ∨ p = 3,
   ∃ x y : ℤ, x² + 3y² = p`. This is **Fermat's other theorem**
   (Fermat 1640, first proof by Euler 1763).
2. **n = 7, 11 ports**: analog theorems with the conjectured Mathlib
   prerequisite (a class-number-1 result for the *maximal order* of
   `ℚ(√-n)`, NOT for the sub-ring `ℤ[√-n]`).
3. **Typeclass abstraction**: state the parent's three-step pipeline
   (Euclidean-via-rounding → splitting-via-Legendre → norm-extraction)
   as a typeclass over `EuclideanDomain` instances of imaginary
   quadratic rings, with `n ∈ {1, 2, 3, 7, 11}` as worked instances.

### Subtlety: Maximal Order vs. ℤ[√-n]

For `n ≥ 3`, the ring `ℤ[√-n]` is **NOT** the ring of integers of
`ℚ(√-n)`:

| n | ℤ[√-n] class number | Max-order class number | Max order |
|---|-----|--------|----|
| 1 | 1   | 1      | ℤ[i]                  |
| 2 | 1   | 1      | ℤ[√-2]                |
| 3 | 2 (not PID) | 1 | ℤ[ω] = ℤ[(-1+√-3)/2] (Eisenstein integers) |
| 7 | 2 (not PID) | 1 | ℤ[(1+√-7)/2]         |
| 11| 3 (not PID) | 1 | ℤ[(1+√-11)/2]        |

For `n ≡ 3 (mod 4)` the ring of integers `𝒪_K` properly contains
`ℤ[√-n]`. The naive Euclidean-rounding construction in the parent
file fails at `d = -n` for `n ≥ 3`: the bound `(1/2)² + n·(1/2)² =
(1+n)/4 ≥ 1` for `n ≥ 3`, so simple rounding does NOT give a
remainder of strictly smaller norm.

The parent proof's algebraic heart — *"non-irreducibility in a UFD
forces `p = N(α)`"* — therefore must be transposed to the maximal
order `𝒪_K`. The classical representation theorems then take the form

- (n=3): `p = a² + 3b²` iff `p = 3` or `p ≡ 1 (mod 3)` (with `a,b ∈ ℤ`).
- (n=7): `p = a² + 7b²` iff `p = 7` or `p ≡ 1, 2, 4 (mod 7)`
  (with `a,b ∈ ℤ`).
- (n=11):`p = a² + 11b²` iff `p = 11` or `p ≡ 1, 3, 4, 5, 9 (mod 11)`
  (with `a,b ∈ ℤ`).

The right-hand-side congruence conditions are exactly the residues
where `(-n/p) = 1`, i.e., where `-n` is a quadratic residue mod `p`.

### Formal Statement (target form, n = 3 sub-case)

```lean
/-- Fermat's other theorem: primes p ≡ 1 (mod 3) are sums x² + 3y². -/
theorem sq_add_three_sq_of_prime_one_mod_three
    {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 3 = 1) :
    ∃ a b : ℤ, a ^ 2 + 3 * b ^ 2 = p := by sorry

/-- p = 3 is trivially 3 = 0² + 3·1². -/
example : ∃ a b : ℤ, a ^ 2 + 3 * b ^ 2 = 3 := ⟨0, 1, by norm_num⟩
```

The natural analog target for n = 7:

```lean
theorem sq_add_seven_sq_of_prime_qr
    {p : ℕ} [Fact (Nat.Prime p)] (hqr : IsSquare (-7 : ZMod p)) :
    ∃ a b : ℤ, a ^ 2 + 7 * b ^ 2 = p := by sorry
```

(Here `(-7/p) = 1` iff `p ≡ 1, 2, 4 (mod 7)` for odd `p ≠ 7`.)

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - number-theory
  - algebraic-number-theory
  - quadratic-forms
  - class-number
  - eisenstein-integers
  - cyclotomic-field
```

**Significance**: 6/10 — moderate-high. Each closed-form `x² + ny²`
representation theorem is a classical landmark (Fermat, Euler, Gauss),
and a successful port establishes a **template gallery family** that
extends naturally to the seven other class-number-1 imaginary
quadratic fields (Heegner numbers: `n ∈ {1, 2, 3, 7, 11, 19, 43, 67,
163}`). The Eisenstein-integer construction (`n = 3`) is the third
member of a triplet (`ℤ[i]`, `ℤ[√-2]`, `ℤ[ω]`) that every
algebraic-number-theory textbook covers.

**Tractability**: 5/10 — non-trivial. The `n = 3` case via Eisenstein
integers is well within reach (~400-600 Lean lines) if Mathlib's
cyclotomic infrastructure (`IsCyclotomicExtension`, `Polynomial.Cyclotomic 3`,
`IsPrimitiveRoot.toInteger`) supplies the Euclidean structure for `ℤ[ω]`.
The `n = 7, 11` cases are harder because Mathlib has **no construction
of `ℤ[(1+√-d)/2]` for arbitrary squarefree `d ≡ 3 (mod 4)`** at the
pinned revision; they would require defining the maximal order
explicitly or working with a quotient by a single quadratic relation.

The typeclass abstraction sub-question is **ambitious** (>1500 lines)
and is recommended as a long-term Mathlib contribution rather than a
gallery deliverable.

## Three Routes

### R1 — Direct n = 3 via Eisenstein integers (recommended for S2-S5)

Use `Mathlib.NumberTheory.NumberField.Embeddings` plus
`Mathlib.NumberTheory.Cyclotomic.Three` (or the more general
`Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`) to construct the
Eisenstein integers `ℤ[ω]` where `ω = e^(2πi/3) = (-1+√-3)/2`.

Pipeline:
1. **Setup** (S2, ~150 lines): introduce a fresh `Zsqrtd`-like structure
   (or use the cyclotomic library directly) for `ℤ[ω]`, with norm
   `N(a + bω) = a² - ab + b²` (= `(a + b/2)² + 3(b/2)² · 1` — the
   integer-quadratic-form representative).
2. **Euclidean structure** (S3, ~200 lines): rounding-based division
   using the `b/2`-rounding bound `(1/2)² - (1/2)(1/2) + (1/2)² = 3/4 < 1`.
3. **Splitting argument** (S4, ~100 lines): use
   `ZMod.exists_sq_eq_neg_three_iff` (Mathlib's third supplementary
   law: `(-3/p) = 1` iff `p ≡ 1 (mod 3)`, conditional on
   API existence at the pinned revision) to show `p` is not
   irreducible in `ℤ[ω]`.
4. **Norm extraction** (S5, ~100 lines): from `p = α·β` with neither
   factor a unit, deduce `p = N(α) = a² - ab + b²` for some `a, b ∈ ℤ`,
   then convert to the **`x² + 3y²` shape** via the algebraic identity
   `a² - ab + b² = (a - b/2)² + 3(b/2)²` (with appropriate parity
   handling: if `b` is even, set `(x, y) = (a - b/2, b/2)`; if `b`
   is odd, the identity instead gives `4(a² - ab + b²) = (2a - b)² +
   3b²`, then verify `2 | (2a - b)` and `2 | b` via mod-4 analysis).

Total: ~550-700 Lean lines, 0 sorries, 0 axioms (assuming Mathlib API).

### R2 — Full Mathlib detour via cyclotomic Galois theory (~1000+ lines)

Use `IsCyclotomicExtension {3} ℤ ℤ[ω]` (Mathlib) to derive the ring
structure of `ℤ[ω]` from the abstract cyclotomic library. Then prove
`IsEuclideanDomain (CyclotomicIntRing ⟨3, …⟩)` via the Mathlib chain
`CyclotomicField {3} ℚ → IsDedekindDomain → IsPrincipalIdealRing`
(class number 1 needs to be shown, then `PID → Euclidean` is not
automatic in Mathlib — it requires picking a Euclidean function).

This route gives the *most reusable* output (everything reduces to
existing Mathlib infrastructure) but is **substantially longer**
because the Mathlib cyclotomic library is structured around abstract
characteristic-0 algebraic-number-theory, not concrete integer
arithmetic. Verbose `simp`/`change` chains are typical.

### R3 — Typeclass abstraction over class-number-1 imaginary quadratic rings

The original OQ-03 wording requests an "`n`-parametric version stated
as a typeclass over `EuclideanDomain` instances." Concretely:

```lean
class IsImagQuadClassOne (R : Type*) [CommRing R] where
  d : ℤ                            -- the discriminant
  d_neg : d < 0
  norm_fn : R → ℤ
  norm_nonneg : ∀ x, 0 ≤ norm_fn x
  norm_mul : ∀ x y, norm_fn (x * y) = norm_fn x * norm_fn y
  euclidean : EuclideanDomain R
  -- … plus an explicit description of representable primes
```

Worked instances at `n ∈ {1, 2, 3, 7, 11}`. The instances differ
substantially in how the Euclidean structure is built (rounding vs.
Eisenstein-style sublattice), so the typeclass should **NOT** force
a particular Euclidean function — only the existence + the norm
identity. Estimated ~1500-2500 lines including all five instances.
Suitable as a **long-term Mathlib contribution**, deferred from the
gallery scope.

## Mathlib Infrastructure Map

### What exists (v4.26.0 at pinned rev)

- `Mathlib.NumberTheory.Zsqrtd.Basic` — `Zsqrtd d` for arbitrary
  `d : ℤ`, with `Zsqrtd.norm`, `Zsqrtd.norm_eq_zero_iff`,
  `Zsqrtd.norm_mul`, `Zsqrtd.norm_eq_one_iff'` (used in the
  parent file `ZsqrtdNegTwo.lean`). **Does NOT** include a Euclidean
  instance for `Zsqrtd (-3)` (which would be wrong — `ℤ[√-3]` is not
  Euclidean!).
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` —
  `ZMod.exists_sq_eq_neg_two_iff` (used in parent), and the
  third supplementary law `ZMod.exists_sq_eq_neg_three_iff` /
  Jacobi-symbol API for general `(-n/p)`.
- `Mathlib.NumberTheory.Cyclotomic.Three` — `IsPrimitiveRoot.toInteger`
  for ω = primitive 3rd root of unity. Provides the Eisenstein-integer
  ring structure but with abstract `IsCyclotomicExtension` framing
  rather than concrete `ℤ[ω]` arithmetic.
- `Mathlib.NumberTheory.NumberField.Discriminant.Basic` — discriminant
  formulas for `ℚ(√-d)` and related.

### What is MISSING (pinned revision)

- **No explicit `EuclideanDomain` instance for `Zsqrtd (-3)`** — the
  parent's rounding pattern fails (proof would need to fail). Any
  R1 path must build the Eisenstein-integer ring fresh or via the
  cyclotomic library.
- **No `Mathlib.NumberTheory.Zsqrtd.MaxOrder`** module: there is no
  generic construction of the maximal order of `ℚ(√-d)` for `d ≡ 1
  (mod 4)` in `Zsqrtd`-style terms. Required for R1 ports to
  `n = 7, 11`.
- **No representation-theorem corollary for x² + ny²** at any `n ≥ 3`
  in Mathlib. Each `n` in `{3, 7, 11}` is a fresh deliverable.

## Known Results (literature)

### Proven

- **Fermat (1640) / Euler (1763)**: prime `p` is `x² + 3y²` iff
  `p = 3` or `p ≡ 1 (mod 3)`.
- **Fermat (1640) / Lagrange (1775)**: prime `p` is `x² + 7y²` iff
  `p = 7` or `p ≡ 1, 2, 4 (mod 7)`.
- **Fermat (1640) / unspecified**: prime `p` is `x² + 11y²` iff
  `p = 11` or `p ≡ 1, 3, 4, 5, 9 (mod 11)`.
- **Gauss, Disquisitiones (1801)**: full classification of primes
  represented by quadratic forms of discriminant `D`, via genus theory.
- **Cox, *Primes of the form x² + ny²* (Wiley 1989/2013)**: monograph
  treatment of class field theory for the general case `n ≥ 1`,
  including the `n = 14, 27, ...` cases where ring class fields are
  needed.

### Open

- The `n`-parametric typeclass abstraction (R3 above) — this
  question has no published literature analog; it is a Lean-side
  infrastructure question.

## Path Decomposition (proposed for R1, n = 3)

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This OBSERVE survey (text-only) | — |
| S2 | `Proofs/ZsqrtdNegTwoOQ03.lean` — Eisenstein scaffold + norm | ~150 |
| S3 | Euclidean structure via rounding (rounding bound 3/4) | ~200 |
| S4 | Splitting argument via `(-3/p) = 1` | ~100 |
| S5 | `sq_add_three_sq_of_prime_one_mod_three` | ~100 |
| S6+ | Port to n = 7, 11 (each ~400 lines, optional) | TBD |
| S∞ | R3 typeclass abstraction (long-term, deferred) | ~1500 |

## Numerical Sanity (n = 3, first few primes)

| p (mod 3) | `a² + 3b² = p` decomposition |
|-----------|------------------------------|
| 7  ≡ 1    | 2² + 3·1² = 4 + 3 |
| 13 ≡ 1    | 1² + 3·2² = 1 + 12 |
| 19 ≡ 1    | 4² + 3·1² = 16 + 3 |
| 31 ≡ 1    | 2² + 3·3² = 4 + 27 |
| 37 ≡ 1    | 5² + 3·2² = 25 + 12 |
| 43 ≡ 1    | 4² + 3·3² = 16 + 27 |
| 61 ≡ 1    | 7² + 3·2² = 49 + 12 |
| 67 ≡ 1    | 8² + 3·1² = 64 + 3 |

All eight `p ≡ 1 (mod 3)` primes below 70 verified. The `p = 3`
edge case is `3 = 0² + 3·1²`.

## References

- P. Fermat, letters to Mersenne (1640) — original conjecture for
  `x² + 3y², x² + 7y²`, etc.
- L. Euler, *De numeris qui sunt aggregata duorum quadratorum
  multiplicatorum* (1763) — first proof of `n = 3` case.
- J.-L. Lagrange, *Recherches d'arithmétique* (1775) — refines
  Euler's method to `n = 7`.
- C. F. Gauss, *Disquisitiones Arithmeticae* (1801) — Sections IV-V
  on quadratic forms.
- D. A. Cox, *Primes of the form x² + ny²: Fermat, class field
  theory, and complex multiplication*, Wiley (1989, 2nd ed. 2013) —
  standard monograph.
- K. Ireland, M. Rosen, *A Classical Introduction to Modern Number
  Theory*, Springer GTM 84 (2nd ed. 1990) — Chapter 17 covers
  `ℤ[ω]` and the `x² + 3y²` theorem in an undergraduate-accessible
  style.
- Mathlib4 source: `Mathlib.NumberTheory.Zsqrtd.Basic`,
  `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`,
  `Mathlib.NumberTheory.Cyclotomic.Three`.
