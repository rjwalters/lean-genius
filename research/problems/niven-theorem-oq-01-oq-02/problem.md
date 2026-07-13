# Problem: Unfold Niven's Algebraic-Integer Step into the Explicit Monic Chebyshev Recurrence

**Slug**: niven-theorem-oq-01-oq-02
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $C_n(x)$ be the sequence of monic integer polynomials ("Vieta–Lucas" /
normalized Chebyshev-of-the-first-kind polynomials) defined by the recurrence

$$
C_0(x) = 2,\qquad C_1(x) = x,\qquad C_{n+1}(x) = x\,C_n(x) - C_{n-1}(x).
$$

The goal is to prove, fully from scratch, the fundamental cosine identity

$$
2\cos(n\theta) \;=\; C_n\!\bigl(2\cos\theta\bigr)\qquad\text{for all } n\in\mathbb{N},\ \theta\in\mathbb{R},
$$

and to use it to give a self-contained proof that $2\cos\theta$ is an **algebraic
integer** whenever $\theta$ is a rational multiple of $\pi$. Concretely, if
$\theta=(m/n)\pi$ then $n\theta=m\pi$ so $\cos(n\theta)=\pm 1\in\mathbb{Z}$, and

$$
C_n\!\bigl(2\cos\theta\bigr) - 2\cos(n\theta) \;=\; 0
$$

exhibits $2\cos\theta$ as a root of the **monic integer polynomial**
$C_n(X) - 2\cos(n\theta) \in \mathbb{Z}[X]$. Hence

$$
\texttt{IsIntegral } \mathbb{Z}\ (2\cos\theta),
$$

replacing the current delegation to Mathlib's
`Real.isIntegral_two_mul_cos_rat_mul_pi` with an explicit witness polynomial.

### Plain Language

The gallery entry `niven-theorem-oq-01` proves Niven's theorem — the only rational
values of $\cos\theta$ at rational-multiple-of-$\pi$ angles are $0,\pm\tfrac12,\pm 1$.
Its hard step ("$2\cos\theta$ is an algebraic integer") is currently handed off to a
single Mathlib lemma, `Real.isIntegral_two_mul_cos_rat_mul_pi`, which is proved
internally via roots of unity. That works, but it hides the classical mechanism.

The classical argument is elementary and beautiful: there is a sequence of polynomials
$C_n$ with **integer coefficients and leading coefficient $1$** such that plugging in
$2\cos\theta$ gives exactly $2\cos(n\theta)$. For example
$C_2(x)=x^2-2$ (so $2\cos 2\theta = (2\cos\theta)^2 - 2$), and
$C_3(x)=x^3-3x$ (so $2\cos 3\theta = (2\cos\theta)^3 - 3(2\cos\theta)$). Because these
polynomials are monic with integer coefficients, and because $2\cos(n\theta)=\pm2$ is
an integer when $\theta=(m/n)\pi$, the number $2\cos\theta$ satisfies a monic integer
equation — i.e. it is an algebraic integer. This task asks to build that ladder of
polynomials in Lean and prove the identity by induction, so the Niven proof no longer
rests on a Mathlib black box.

### Why This Matters

- **Self-contained proof.** It removes the last external dependency in the deep half of
  Niven's theorem, turning the gallery entry from a "presentation citing Mathlib" into a
  genuinely from-scratch formalization of the whole argument.
- **Exposes the real mechanism.** The monic Chebyshev recurrence is *the* reason the
  theorem is true; making it explicit is far more instructive than "roots of unity give
  integrality."
- **Reusable machinery.** The identity $2\cos(n\theta)=C_n(2\cos\theta)$ and the
  "monic integer polynomial $\Rightarrow$ algebraic integer" packaging are exactly what
  is needed for the sibling cyclotomic/irrationality results (e.g. irrationality of
  $\cos(2\pi/n)$ for most $n$), so a clean statement pays dividends elsewhere.

## Known Results

### What's Already Proven

- `Real.isIntegral_two_mul_cos_rat_mul_pi` — Mathlib's statement that $2\cos(q\pi)$ is
  integral over $\mathbb{Z}$ for rational $q$ (currently cited by the parent entry). In
  `Mathlib.NumberTheory.Niven`.
- `Polynomial.Chebyshev.T` — Mathlib's Chebyshev polynomials of the first kind $T_n$
  (defined over any commutative ring, including $\mathbb{Z}$), with the recurrence
  $T_{n+1} = 2\,X\,T_n - T_{n-1}$, $T_0 = 1$, $T_1 = X$.
- `Polynomial.Chebyshev.T_real_cos` / `T_complex_cos` (cosine evaluation) — the
  defining trigonometric identity $T_n(\cos\theta) = \cos(n\theta)$. In
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev`.
- `Polynomial.Monic`, `Polynomial.Monic.natDegree`, and the `IsIntegral` API
  (`isIntegral_of_mem_of_fg`, root-of-monic constructors) — for packaging "root of a
  monic integer polynomial" as `IsIntegral ℤ`.
- The parent entry's enumeration tail (`niven`) and `IsIntegral.exists_int_iff_exists_rat`
  are unaffected and can be reused verbatim once the core lemma is re-derived.

### What's Still Open

- No explicit *monic normalized* $C_n$ with the from-scratch induction is present in the
  gallery; the parent simply cites the packaged Mathlib lemma.
- The bridge $C_n(x) = 2\,T_n(x/2)$ between the monic normalization and Mathlib's $T_n$
  (which has leading coefficient $2^{n-1}$, not $1$) is not spelled out anywhere in the
  entry.

### Our Goal

Replace `two_cos_int_of_rational`'s appeal to
`Real.isIntegral_two_mul_cos_rat_mul_pi` with an explicit construction:

1. define the monic integer sequence $C_n$ by the recurrence above (either directly as a
   `Polynomial ℤ` recursion or as $C_n := 2\,T_n(X/2)$ scaled back into $\mathbb{Z}[X]$);
2. prove $2\cos(n\theta) = C_n(2\cos\theta)$ by two-step induction;
3. prove `Monic (C n)` and conclude `IsIntegral ℤ (2 * Real.cos θ)` by exhibiting the
   monic witness $C_n(X) - 2\cos(n\theta)$ with $2\cos(n\theta)\in\mathbb{Z}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| niven-theorem-oq-01 | Parent entry; this task unfolds its delegated algebraic-integer step | `IsIntegral`, `interval_cases`, cosine bounds |
| nth-root-irrational-oq-01-oq-01 | Sibling cyclotomic/Niven work resting on the same "2cos(qπ) is integral" fact | roots of unity, minimal polynomials |
| sqrt2-minpoly-oq-01-oq-02-oq-01 | Another "rational algebraic integer is an ordinary integer" instance | minimal/monic integer polynomials, integrality |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct monic recursion in $\mathbb{Z}[X]$.** Define
   `C : ℕ → Polynomial ℤ` by `C 0 = 2`, `C 1 = X`, `C (n+2) = X * C (n+1) - C n`. Prove
   `(C n).Monic` by two-step induction (the leading term of $x\cdot C_{n+1}$ dominates
   $C_{n-1}$ because $\deg C_{n+1} = n+1 > n-1 = \deg C_{n-1}$). Then prove the evaluation
   identity `2*cos(n·θ) = eval (2*cos θ) (C n)` by induction using the addition formula.
   - Why it might work: keeps everything over $\mathbb{Z}$, so `Monic`/`IsIntegral` are
     immediate; the recurrence mirrors the cosine identity one-to-one.
   - Risk: managing `natDegree`/`leadingCoeff` bookkeeping for the monic proof, and the
     Lean `Nat.rec`/`Nat.strong_induction` plumbing for a two-step recurrence.

2. **Approach B — Renormalize Mathlib's $T_n$.** Use `Polynomial.Chebyshev.T ℤ n` and set
   $C_n(x) := 2\,T_n(x/2)$, i.e. work with $2\,T_n\!\big(\tfrac{X}{2}\big)$; equivalently
   define the scaling so $C_n \in \mathbb{Z}[X]$ and derive its monicity and the cosine
   identity from `T_real_cos` ($T_n(\cos\theta)=\cos(n\theta)$) by the substitution
   $\theta \mapsto \theta$, $\cos\theta \mapsto \tfrac{2\cos\theta}{2}$.
   - Why it might work: reuses Mathlib's already-proved $T_n(\cos\theta)=\cos(n\theta)$,
     so only the *renormalization* (halving/doubling) and monicity need new work.
   - Risk: the substitution $X\mapsto X/2$ leaves $\mathbb{Z}[X]$; must show
     $2\,T_n(X/2)$ has integer coefficients (true — $T_n$'s coefficients are integers with
     $2$-power denominators exactly cancelled) and is monic with leading coefficient $1$.

### Key Difficulties

- Proving `Monic (C n)` for the two-step recurrence: needs $\deg C_n = n$ and that the
  subtraction $x\cdot C_{n+1} - C_{n-1}$ does not lower the top-degree coefficient.
- The evaluation identity's induction step *is* the cosine addition/product-to-sum
  identity $2\cos((n{+}1)\theta) = 2\cos\theta\cdot 2\cos(n\theta) - 2\cos((n{-}1)\theta)$;
  formalizing this cleanly (`Real.cos_add`, `Real.cos_sub`, or `Real.cos_add_cos`) with a
  two-step (strong / `Nat.le_induction`-style) induction.
- Bridging to `IsIntegral ℤ (2*cos θ)`: assembling the monic witness polynomial
  $C_n(X) - (2\cos(n\theta))$ and feeding it to the `IsIntegral` root constructor, with
  $2\cos(n\theta)=\pm2$ pushed to a concrete integer.

### What Would a Proof Need?

- Key lemma 1: `C_cos : ∀ n θ, 2 * Real.cos (n*θ) = Polynomial.eval (2*Real.cos θ) ((C n).map (Int.cast)) ` — the fundamental identity, by two-step induction from the cosine product-to-sum formula.
- Key lemma 2: `C_monic : ∀ n, (C n).Monic` (equivalently `natDegree (C n) = n` plus leading coefficient $1$), by two-step induction on the recurrence.
- Key lemma 3: at $\theta=(m/n)\pi$, `2*Real.cos (n*θ) = 2*Real.cos (m*π) = ±2 ∈ ℤ`, using `Real.cos_int_mul_two_pi` / `Real.cos_nat_mul_pi` style facts, so the constant term of the witness polynomial is an integer.
- Technical requirement: connect the monic integer witness to `IsIntegral ℤ (2*Real.cos θ)` and then finish exactly as the parent does via `IsIntegral.exists_int_iff_exists_rat` and the `interval_cases` tail.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already provides Chebyshev polynomials `Polynomial.Chebyshev.T` **and** the
  cosine identity `T_real_cos` ($T_n(\cos\theta)=\cos(n\theta)$), so the deep
  trigonometry is not re-derived from nothing — the work is the monic *renormalization*
  $C_n(x)=2T_n(x/2)$ and the accompanying `Monic`/`IsIntegral` bookkeeping.
- Two-step polynomial inductions with degree/leading-coefficient tracking are routine but
  fiddly in Lean; the cosine product-to-sum step is a standard `Real.cos_add`/`cos_sub`
  manipulation.
- Similar "root of an explicit monic integer polynomial $\Rightarrow$ `IsIntegral ℤ`"
  packaging has been done in sibling entries, so the final assembly has precedent.
- The enumeration tail and the rational-algebraic-integer collapse are already proven in
  the parent and reused unchanged.

**Estimated Effort**:
- Exploration: 0.5–1 day (decide Approach A vs B; check `T`'s degree/leadingCoeff API)
- If tractable: 3–6 days (monicity induction + evaluation identity + `IsIntegral` bridge)
- If hard: 1–2 weeks (if the monic-degree bookkeeping or the $X\mapsto X/2$ integrality
  proof proves stubborn)

## References

### Papers
- Ivan Niven, *Irrational Numbers*, Carus Mathematical Monographs 11, MAA, 1956 — the
  original source of the theorem and of the "$2\cos\theta$ is an algebraic integer"
  argument via the monic recurrence.
- J. M. H. Olmsted, "Rational values of trigonometric functions", *Amer. Math. Monthly*
  52 (1945) — an early exposition of the rational-cosine classification.
- François Viète (Vieta), *Ad angulares sectiones* — origin of the "Vieta–Lucas"
  polynomials $V_n$ satisfying $V_n(2\cos\theta)=2\cos(n\theta)$.

### Online Resources
- https://en.wikipedia.org/wiki/Niven%27s_theorem — statement, history, sine/tangent
  companions.
- https://en.wikipedia.org/wiki/Chebyshev_polynomials — first-kind $T_n$, the monic
  normalization, and the recurrence.
- https://en.wikipedia.org/wiki/Lucas_sequence — the $V_n$ (Vieta–Lucas) family and its
  monic recurrence $V_{n+1}=x V_n - V_{n-1}$.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev` — `Polynomial.Chebyshev.T`
  and `T_real_cos` / `T_complex_cos` giving $T_n(\cos\theta)=\cos(n\theta)$.
- `Mathlib.RingTheory.Polynomial.Chebyshev` — the recurrence and degree facts for $T_n$
  ($T_{n+1}=2X T_n - T_{n-1}$).
- `Mathlib.RingTheory.IntegralClosure` / `IsIntegral` — root-of-monic constructors and
  `IsIntegral.exists_int_iff_exists_rat` (ℤ integrally closed in ℚ).
- `Mathlib.NumberTheory.Niven` — the existing `Real.isIntegral_two_mul_cos_rat_mul_pi`
  being replaced.

## Metadata

```yaml
tags:
  - number-theory
  - algebraic-integers
  - chebyshev-polynomials
  - trigonometry
  - rational-multiples-of-pi
related_proofs:
  - niven-theorem-oq-01
  - nth-root-irrational-oq-01-oq-01
  - sqrt2-minpoly-oq-01-oq-02-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-30T22:49:26-07:00
```
