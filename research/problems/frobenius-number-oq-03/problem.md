# Problem: Frobenius Number — Three Generators with Explicit Formulas

## Statement

### Plain Language

The two-generator Frobenius number `g(a, b) = ab − a − b` for coprime
`a, b ≥ 2` admits the closed form proved by Sylvester (1882) and
already formalized in `Proofs/FrobeniusNumber.lean` / `…OQ01.lean` /
`…OQ02.lean`. Extending to **three or more generators** is dramatically
harder: the general k-generator Frobenius problem is NP-hard for
`k ≥ 4` (Ramírez Alfonsín 1996), and no closed-form analog of the
Sylvester formula exists.

However, for **structured families of three generators**, explicit
formulas are known. This open question (OQ-03) asks whether the
gallery's two-generator infrastructure can be extended to formalize
one or more of these special-family three-generator formulas in Lean.

The cleanest concrete targets are:

1. **Three consecutive integers** `(n, n+1, n+2)`:
   $$g(n, n+1, n+2) = \left\lfloor \tfrac{n-2}{2} \right\rfloor \cdot n + (n-1) \quad (n \ge 3)$$
   This is the `d = 1` specialization of Roberts (1956) below.

2. **Arithmetic-progression triples** `(a, a+d, a+2d)`, with
   `a ≥ 2` and `gcd(a, d) = 1` (Roberts 1956):
   $$g(a, a+d, a+2d) = \left\lfloor \tfrac{a-2}{2} \right\rfloor \cdot a + (a-1) \cdot d$$
   Equivalent re-statement (Bateman 1957): the k+1-generator
   arithmetic-progression formula
   `g(a, a+d, …, a+kd) = ⌊(a-2)/k⌋·a + (a-1)·d` at `k = 2`.

3. **Fibonacci triples** `(F_k, F_{k+1}, F_{k+2})` (Marín, Ramírez
   Alfonsín, Revuelta 2007): the Frobenius number admits a closed form
   expressed in terms of further Fibonacci numbers.

4. **General three-generator algorithm** (Selmer 1977, Davison 1994,
   Killingbergtrø 2000): polynomial-time computability of `g(a, b, c)`
   via the Apéry set `Ap({a,b,c}, a) = {smallest representable element
   in each residue class mod a}`, with `g = max Ap − a`.

### Formal Statement (target form)

```lean
-- Step 1: predicate analogous to Representable
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = a * x + b * y + c * z

-- Step 2: Frobenius number (largest non-representable, when it exists)
noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
  sSup { n : ℕ | ¬ Representable3 a b c n }

-- Step 3a (CONCRETE TARGET — three consecutive integers):
theorem frobenius_three_consecutive (n : ℕ) (hn : 3 ≤ n) :
    frobeniusNumber3 n (n + 1) (n + 2)
      = (n - 2) / 2 * n + (n - 1) := by sorry

-- Step 3b (GENERALIZATION — Roberts 1956 for 3-AP):
theorem frobenius_three_arith_prog (a d : ℕ) (ha : 2 ≤ a)
    (hcop : Nat.Coprime a d) :
    frobeniusNumber3 a (a + d) (a + 2 * d)
      = (a - 2) / 2 * a + (a - 1) * d := by sorry
```

(`Step 3a` is the `d = 1` case of `Step 3b`. Independent direct proof
is straightforward by `omega` / `decide` on the bounded cases plus an
inductive lift; the AP formula needs the Apéry-set argument.)

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - coin-problem
  - combinatorics
  - coprime
  - frobenius
  - number-theory
```

**Significance**: 6/10 — moderate. The 3-AP formula is a clean
extension of the gallery's flagship 2-generator result and provides
a concrete bridge to **numerical-semigroup theory**, a moderate-sized
research area in algebra with combinatorial and algebraic flavors
(Rosales–García-Sánchez monograph 2009). Each "specific family"
that is formalized adds a worked example for Mathlib's
(currently very thin) numerical-semigroup coverage.

**Tractability**: 6/10 — non-trivial but bounded. The three-consecutive
case can plausibly be handled by extending the
`representable_add_a` / `large_representable` infrastructure already in
`FrobeniusNumber.lean` from two to three generators; the bookkeeping is
heavier but the proof skeleton (large_representable → frobenius_alt →
non-representability of the candidate) ports directly.

## Mathlib Infrastructure Map

### What exists (Mathlib v4.26.0 at pinned rev `2df2f0150c`)

- `Mathlib.NumberTheory.Frobenius` (and related files): contains
  `frobeniusNumber_pair` for **two coprime** generators. No
  3-generator analog.
- `Nat.Coprime` and `Finset.gcd`: standard infrastructure for
  `gcd(a,b,c) = 1` style coprimality.
- `Mathlib.Combinatorics.NumericalSemigroup` — **DOES NOT EXIST**
  as of v4.26.0 (sanity-checked via GitHub Contents API). There is
  no Mathlib-level theory of numerical semigroups, Apéry sets, or
  Frobenius generalizations beyond the two-coprime case.

### What this entry would provide

The S2+ implementation would introduce, in
`Proofs/FrobeniusNumberOQ03.lean`:

- `Representable3 a b c n` definition + basic lemmas
  (`representable3_zero`, `representable3_a`, `representable3_b`,
  `representable3_c`, `representable3_add_a`, etc.) — direct port
  of the two-generator infrastructure.
- `frobeniusNumber3` definition and existence lemma (for
  `gcd(a,b,c) = 1` with `a,b,c ≥ 2`, the set of non-representable
  positive integers is finite, so the `sSup` is well-defined and
  attained).
- One of the closed-form theorems (3-consecutive or 3-AP) with
  full proof.

This is **substantial new content** (likely 300-600 lines), but
each layer is self-contained and could be staged across S2–Sn.

### Theoretical Background (proof structure)

For the **three-consecutive** case `(n, n+1, n+2)`:

The Apéry-set approach. Fix `a = n` as the residue modulus.
For each residue class `r ∈ {0, 1, …, n-1}`, the smallest representable
element with that residue is one of the form
`k · (n+1) + j · (n+2)` with `k, j ≥ 0` and `k + 2j ≡ r (mod n)`.

With `gcd(n, n+1) = 1`, every residue class `r mod n` is realized by
`r · (n+1)` (since `n+1 ≡ 1 mod n`), giving an Apéry set whose maximum
sits at residue `n-1`. Working out the cases yields

$$\max \mathrm{Ap}(\{n, n+1, n+2\}, n) = (n-1)(n+1) - \lfloor (n-1)/2 \rfloor$$

modulo a careful parity tracking on `n`. By the
**Brauer–Shockley theorem** `g(S) = max Ap(S, a) − a` (for any `a ∈ S`):

$$g(n, n+1, n+2) = (n-1)(n+1) - \lfloor (n-1)/2 \rfloor - n = \lfloor (n-2)/2 \rfloor \cdot n + (n-1)$$

(after expansion and the algebraic identity
`(n-1)(n+1) - n = n^2 - n - 1 = n(n-1) - 1`).

The Lean-formalizable shape:
- (a) Case-split on parity of `n`.
- (b) Exhibit explicit witness `(x, y, z)` representations for each
  `m > g(n, n+1, n+2)`.
- (c) Show non-representability of `g(n, n+1, n+2)` itself via a
  finite residue-class case check modulo `n`.

For the **3-AP** case `(a, a+d, a+2d)`, the same Apéry-set argument
generalizes: with modulus `a`, the residue class `r mod a` is hit by
`r · d` (since `gcd(a, d) = 1` so `d` is a unit mod `a`), and the
minimum representative is `r · d + ⌊r / 2⌋ · a` or similar. The
formula `g = ⌊(a-2)/2⌋ · a + (a-1) · d` falls out.

## Known Results

### Proven (literature)

- **Roberts (1956)**: For `a ≥ 2`, `gcd(a, d) = 1`, and `k ≥ 1`:
  `g(a, a+d, …, a+kd) = a · ⌊(a-2)/k⌋ + (a-1) · d`. The `k = 2` case
  gives the 3-AP formula. (Also: Brauer 1942 for `d = 1`, Bateman 1957
  re-derivation.)

- **Selmer (1977)**: Polynomial-time algorithm for `g(a, b, c)` via
  Apéry sets for three arbitrary coprime generators (no closed form,
  but algorithmic). Refined by Davison (1994), Killingbergtrø (2000),
  Beihoffer–Hendry–Nijenhuis–Wagon (2005).

- **Marín–Ramírez Alfonsín–Revuelta (2007)**: Closed form for
  `g(F_k, F_{k+1}, F_{k+2})` (Fibonacci triples), Tribonacci variants.

- **Cooper–Karikomi–Snabb / many authors**: Mersenne triples
  `g(2^a-1, 2^b-1, 2^c-1)` and other parametric families.

### Open (no known closed form)

- `g(a, b, c)` for three *arbitrary* coprime integers — polynomial
  algorithm exists (Selmer) but no closed-form expression.

- Four or more generators in arithmetic progression (Roberts
  formula extends, but for non-AP 4+ tuples the problem is NP-hard).

- Density and statistics of Frobenius numbers over random tuples
  (active research; Aliev–Henk–Hinrichs 2011, …).

### Goal (this entry)

Add a fully verified Lean proof of **at least one** explicit-formula
case for three generators — minimum-viable target is the
three-consecutive case `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n-1)` for
`n ≥ 3`. Stretch target: the Roberts 3-AP formula.

## Path Decomposition (proposed for S2+)

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This survey (text-only, no Lean) | — |
| S2 | `Representable3` + basic closure lemmas | ~100 |
| S3 | `frobeniusNumber3` + existence proof | ~80 |
| S4 | `large_representable3` for 3 consecutive | ~120 |
| S5 | `frobenius_three_consecutive` (main theorem) | ~100 |
| S6+ | Lift to 3-AP / Fibonacci / Mersenne cases | TBD |

Each stage commits sorry-free; PR titles `S<N> — <stage>`.

## Numerical Sanity (n = 3..7)

| `n` | `(n, n+1, n+2)` | `⌊(n-2)/2⌋·n + (n-1)` | Direct max non-rep |
|-----|----------------|----------------------|--------------------|
| 3 | (3, 4, 5) | 0·3 + 2 = 2 | 2 (since 3, 4, 5, 6=3+3, 7=3+4, 8=3+5, 9=4+5 or 3+3+3 …) |
| 4 | (4, 5, 6) | 1·4 + 3 = 7 | 7 (8=4+4, 9=4+5, 10=4+6 or 5+5, 11=5+6, 12=6+6, …; 1,2,3,7 non-rep) |
| 5 | (5, 6, 7) | 1·5 + 4 = 9 | 9 (1,2,3,4,8,9 non-rep; 10=5+5, 11=5+6, 12=5+7 or 6+6, …) |
| 6 | (6, 7, 8) | 2·6 + 5 = 17 | 17 (16,17 non-rep; 18=6+6+6, 19=6+6+7, …) |
| 7 | (7, 8, 9) | 2·7 + 6 = 20 | 20 (19, 20 non-rep; 21=7+7+7, 22=7+7+8, …) |

All five sanity values confirmed by direct enumeration.

## References

- W. J. LeVeque (ed.), *Studies in Number Theory*, Math. Assoc. Amer.
  1969 — includes Roberts' formula.
- J. B. Roberts, *Note on linear forms*, Proc. Amer. Math. Soc. 7 (1956)
  465–469.
- A. Brauer, *On a problem of partitions*, Amer. J. Math. 64 (1942)
  299–312.
- E. S. Selmer, *On the linear diophantine problem of Frobenius*,
  J. Reine Angew. Math. 293/294 (1977) 1–17.
- J. L. Ramírez Alfonsín, *The Diophantine Frobenius Problem*, Oxford
  Lecture Series in Math. and Its Applications **30**, OUP 2005 —
  the standard reference monograph.
- J. C. Rosales, P. A. García-Sánchez, *Numerical Semigroups*, Springer
  Developments in Math. **20**, 2009 — the algebraic perspective.
- F. Marín, J. L. Ramírez Alfonsín, M. P. Revuelta, *On the Frobenius
  number of Fibonacci numerical semigroups*, Integers 7 (2007) #A14.
- D. Beihoffer, J. Hendry, A. Nijenhuis, S. Wagon, *Faster algorithms
  for Frobenius numbers*, Electron. J. Combin. 12 (2005) #R27.
