# Problem: A total computable binary GCD for the Gaussian integers

**Slug**: binary-gcd-oq-04-oq-01
**Created**: 2026-07-02T11:12:11-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $\mathbb{Z}[i]$ denote the Gaussian integers (`GaussianInt` = `ℤ[i]` in Mathlib), a Euclidean
domain with norm $N(a+bi) = a^2 + b^2$ and ramified prime $\pi = 1+i$ (with $N(\pi) = 2$). The parent
entry `binary-gcd-oq-04` proves the parity dichotomy $\pi \mid z \iff 2 \mid (z.\mathrm{re} + z.\mathrm{im})$,
the exact division map $\mathrm{divPi}$ with $N(z) = 2\,N(z/\pi)$, and the three reduction identities
(both-even pull-out, one-even drop, both-odd subtraction), each up to `Associated`.

The task is to package those reductions into an explicit **total** function

$$
\mathrm{binaryGcdGaussian} : \mathbb{Z}[i] \to \mathbb{Z}[i] \to \mathbb{Z}[i]
$$

defined by well-founded recursion on the norm measure $z \mapsto (N\,z).\mathrm{natAbs}$ (or,
equivalently, by a `Nat`-fuel-indexed unfolding bounded by that measure), applying at each step
one of the reduction rules, and to prove that it agrees with the Mathlib Euclidean gcd up to a unit:

$$
\forall\, a\, b : \mathbb{Z}[i], \quad \mathrm{Associated}\ (\mathrm{binaryGcdGaussian}\ a\ b)\ (\mathrm{EuclideanDomain.gcd}\ a\ b).
$$

Here `Associated x y` means `∃ u : (ℤ[i])ˣ, x * u = y`, i.e. equality up to one of the four units
$\{\pm 1, \pm i\}$.

### Plain Language

The parent entry proved all the *arithmetic facts* that make a binary (Stein-style) GCD work over
the Gaussian integers: how to test "π-evenness" (a parity check on `re + im`), how to divide exactly
by $\pi = 1+i$ while halving the norm, and three rewrite rules that shrink a `gcd` problem to a
smaller one. But it never actually assembled these into a *running algorithm*. This problem asks to
write that algorithm as one honest Lean function `binaryGcdGaussian a b` — no `sorry`, no partiality,
guaranteed to terminate — and then prove it computes the "right answer": the same gcd Mathlib's
`EuclideanDomain.gcd` computes, up to multiplication by a unit $\pm 1$ or $\pm i$ (since in $\mathbb{Z}[i]$
there is no canonical choice of gcd representative). The termination guarantee comes from the fact
that every step strictly decreases the natural-number norm $N(z) = z.\mathrm{re}^2 + z.\mathrm{im}^2$.

### Why This Matters

A binary GCD avoids full Euclidean division entirely — it uses only additions, subtractions,
comparisons, and the cheap "divide by $\pi$" operation (a fixed linear map on coordinates). Turning
the parent's correctness *layer* into a total, definitionally computable *function* delivers a
genuinely executable GCD for $\mathbb{Z}[i]$ inside Lean, one whose correctness is machine-checked
against Mathlib's abstract `EuclideanDomain.gcd`. This closes the loop between "we proved the reduction
identities hold" and "here is a program that terminates and computes a gcd," and it provides a reusable
template for transplanting Stein's parity structure to any imaginary-quadratic Euclidean ring that has
a small ramified prime.

## Known Results

### What's Already Proven

- `Zsqrtd.norm_mul` (multiplicativity $N(zw) = N(z)N(w)$) and `Zsqrtd.norm_eq_one_iff` — `Mathlib.NumberTheory.Zsqrtd.Basic`
- `GaussianInt` is a `EuclideanDomain` with `r_wellFounded := (measure (Int.natAbs ∘ norm)).wf` — `Mathlib.NumberTheory.Zsqrtd.GaussianInt` (`instance : EuclideanDomain ℤ[i]`)
- `EuclideanDomain.gcd`, `EuclideanDomain.gcd_dvd_left/right`, `EuclideanDomain.dvd_gcd` (universal property) — `Mathlib.Algebra.EuclideanDomain.Defs`/`Basic`
- `associated_of_dvd_dvd` (mutual divisibility ⟹ `Associated`) — `Mathlib.Algebra.GroupWithZero.Associated`
- Parent `binary-gcd-oq-04`: `pi_norm` ($N(\pi)=2$), `pi_dvd_iff` (the $\mathbb{Z}[i]/(\pi) \cong \mathbb{F}_2$ dichotomy), `pi_prime`, `pi_dvd_sub_of_not_dvd`, `divPi`, `pi_mul_divPi`, `norm_divPi` ($N(z)=2\,N(z/\pi)$), and the three reduction identities `gcd_pi_mul`, `gcd_pi_mul_odd`, `gcd_sub`, each stated up to `Associated` — `Proofs/BinaryGcdOQ04.lean`

### What's Still Open

- No explicit total function `binaryGcdGaussian` packaging the reductions exists yet — the parent supplies only the step-wise identities, not a recursive definition.
- The equivalence `Associated (binaryGcdGaussian a b) (EuclideanDomain.gcd a b)` is unproven.
- The step-count / bit-complexity analysis (sibling OQ-02) and the extension to other rings $\mathbb{Z}[\sqrt{-d}]$ (sibling OQ-03) remain open and are out of scope here.

### Our Goal

Define `binaryGcdGaussian : ℤ[i] → ℤ[i] → ℤ[i]` by well-founded recursion on
`fun z => (Zsqrtd.norm z).natAbs` (with `termination_by`/`decreasing_by` discharged by `norm_divPi`
and the parity facts), or equivalently by a `Nat`-fuel version `binaryGcdGaussianFuel (n : ℕ)` with
`n` an a-priori bound from the norm; then prove the single correctness theorem
`Associated (binaryGcdGaussian a b) (EuclideanDomain.gcd a b)` by induction on the termination
measure, closing each recursive case with the matching parent reduction identity and transitivity of
`Associated`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binary-gcd-oq-04 | Direct parent: supplies every reduction identity and the norm-halving measure this function is built from | `Zsqrtd.norm`, `pi_dvd_iff`, `divPi`, `Associated`, Euclidean-gcd universal property |
| binary-gcd | Grandparent: Stein's binary GCD over ℤ, the parity/subtraction/halving template being transplanted | parity dichotomy, subtractive reduction, halving termination measure |
| binary-gcd-oq-03-oq-02 | Sibling in the binary-gcd family (asymptotically fast GCD over ℤ); orthogonal complexity direction | HGCD recursion, native_decide |

## Initial Thoughts

### Potential Approaches

1. **Approach A — well-founded recursion on the norm**: Define
   `binaryGcdGaussian a b` by `termination_by (Zsqrtd.norm a).natAbs + (Zsqrtd.norm b).natAbs`
   (or a lexicographic/max measure), branching on `pi ∣ a`, `pi ∣ b` via the decidable `pi_dvd_iff`
   parity test, and recursing on `divPi`-shrunk or subtracted arguments. Base cases: `a = 0 ⟹ b`,
   `b = 0 ⟹ a`.
   - Why it might work: `norm_divPi` gives an *exact* factor-2 drop, and `pi_dvd_sub_of_not_dvd`
     guarantees the both-odd difference is π-even so the next `divPi` step is legal and strictly
     decreasing — every branch has a ready-made measure-decrease lemma in the parent.
   - Risk: Lean's `decreasing_by` obligations require rephrasing `norm_divPi` and the subtraction
     bound as strict `Nat` inequalities on the *chosen* measure; getting the branch structure and
     the measure to line up (especially the "subtract then divide" combined step) can be fiddly.

2. **Approach B — `Nat`-fuel-indexed total function**: Define
   `binaryGcdGaussianFuel : ℕ → ℤ[i] → ℤ[i] → ℤ[i]` by structural recursion on the fuel `n`
   (returning a default like `0`/`a` when fuel is exhausted), set
   `binaryGcdGaussian a b := binaryGcdGaussianFuel ((N a).natAbs + (N b).natAbs + 1) a b`, and prove
   the fuel bound is never actually exceeded.
   - Why it might work: structural recursion on `ℕ` is definitionally trivial and sidesteps all
     `decreasing_by` obligations; totality is immediate; one then proves a "fuel monotonicity" lemma
     (extra fuel doesn't change the result once the bound is met).
   - Risk: correctness now needs both the fuel-sufficiency lemma *and* the associated-to-gcd lemma;
     the fuel bookkeeping adds a layer that must be discharged from the same norm-decrease facts, so
     it trades `decreasing_by` pain for `Nat.le` bookkeeping.

### Key Difficulties

- **Termination proof**: assembling the parent's per-step norm facts (`norm_divPi`, the subtraction
  bound) into the exact strict-decrease obligation Lean demands for the *combined* both-odd step
  (subtract, then divide by π).
- **Unit ambiguity**: the result is only determined up to a unit $\{\pm1,\pm i\}$, so the theorem must
  be `Associated`, and the inductive proof must thread `Associated` through each reduction via
  transitivity (`Associated.trans`) and congruence (`Associated.mul_left` for the both-even pull-out).
- **The $(1+i)$-factoring step**: `divPi` is only exact when `pi ∣ z`; the recursion must branch on
  the decidable dichotomy and feed `pi_mul_divPi` into the reduction identity in exactly the case the
  identity expects.

### What Would a Proof Need?

- Key lemma 1: a total definition `binaryGcdGaussian` (via `termination_by`/`decreasing_by` on
  `(Zsqrtd.norm ·).natAbs`, or the fuel version) that compiles with no `sorry`.
- Key lemma 2: `Associated (binaryGcdGaussian a b) (EuclideanDomain.gcd a b)`, proved by strong
  induction on the norm measure, each case closed by the matching parent identity
  (`gcd_pi_mul`, `gcd_pi_mul_odd`, `gcd_sub`) plus `Associated.trans`.
- Technical requirements: reuse `norm_divPi`, `pi_mul_divPi`, `pi_dvd_iff` (decidable), and
  `pi_dvd_sub_of_not_dvd` from the parent; `EuclideanDomain.gcd_zero_left`/`gcd_zero_right` for base
  cases; `associated_of_dvd_dvd` / `Associated.trans` / `Associated.mul_left` for the gcd algebra.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Every mathematical fact needed already exists and is verified in the parent (`binary-gcd-oq-04`);
  the remaining work is definitional packaging plus a bookkeeping induction, not new mathematics.
- Similar "reductions ⟹ total recursive function ⟹ correctness up to a canonical answer" tasks are
  routine in Mathlib-style formalization; the `EuclideanDomain.gcd` universal property gives a clean
  target.
- The chief risk is purely engineering: satisfying Lean's `decreasing_by` obligations (or the fuel
  bookkeeping) and threading `Associated` through the induction — well-trodden but detail-heavy.

**Estimated Effort**:
- Exploration: 1–2 days (settle on well-founded vs. fuel; pin the exact measure and branch structure).
- If tractable: 3–7 days (write the definition, discharge termination, prove the associated-to-gcd induction).
- If hard: unknown (only if the combined subtract-then-divide step resists a clean `decreasing_by`, forcing the fuel detour with its extra sufficiency lemma).

## References

### Papers
- Stein, Josef, "Computational problems associated with Racah algebra", *J. Comput. Phys.* 1 (1967), 397–405 — the original binary GCD over ℤ using only parity tests, subtractions, and halvings, whose structure is transplanted to ℤ[i].
- Knuth, Donald E., *The Art of Computer Programming, Vol. 2: Seminumerical Algorithms*, 3rd ed. (1997), §4.5.2 (binary gcd, Algorithm B) and §4.5.4 (gcd over the Gaussian integers) — the reference treatment combined here.
- Hardy, G. H. & Wright, E. M., *An Introduction to the Theory of Numbers*, 6th ed. (2008), §12.6–12.8 — Euclidean structure, norm, units, and primes of ℤ[i].

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Zsqrtd/GaussianInt.html — Mathlib docs for `GaussianInt` and its `EuclideanDomain` instance.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/EuclideanDomain/Defs.html — Mathlib docs for `EuclideanDomain.gcd` and its universal property.

### Mathlib
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — the `GaussianInt = ℤ[i]` type and its `EuclideanDomain` instance with `r_wellFounded := (measure (Int.natAbs ∘ norm)).wf`, the exact norm measure this recursion uses.
- `Mathlib.NumberTheory.Zsqrtd.Basic` — `Zsqrtd.norm`, `Zsqrtd.norm_mul`, `Zsqrtd.norm_eq_one_iff`, the multiplicative norm underlying the termination measure.
- `Mathlib.Algebra.EuclideanDomain.Defs` / `.Basic` — `EuclideanDomain.gcd`, `gcd_dvd_left/right`, `dvd_gcd`, `gcd_zero_left/right`, the correctness target and base cases.
- `Mathlib.Algebra.GroupWithZero.Associated` — `Associated`, `associated_of_dvd_dvd`, `Associated.trans`, `Associated.mul_left`, the notion of gcd equality up to a unit.

## Metadata

```yaml
tags:
  - number-theory
  - algorithm
  - gaussian-integers
  - binary-gcd
  - euclidean-domain
  - computability
related_proofs:
  - binary-gcd-oq-04
  - binary-gcd
  - binary-gcd-oq-03-oq-02
difficulty: medium
source: user-request
created: 2026-07-02T11:12:11-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
