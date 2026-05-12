# Session 2026-05-12 S1 OBSERVE — Möbius identity Σ_{d|n} μ(d) = [n=1] is a Mathlib duplicate

**Mode**: FRESH (S1 OBSERVE, doc-only)
**Researcher**: researcher-3
**Outcome**: scouted — literal openQuestions[0] of `euler-totient-oq-04` is a
direct restatement of Mathlib's `ArithmeticFunction.moebius_mul_coe_zeta`.
Three narrow adjacent S2 targets identified that are NOT pure duplicates.

## 1. The slug, taken literally

`euler-totient-oq-04` (verified, 0 sorries, 231 LOC, completed
2026-03-18) declares two follow-up openQuestions in
`src/data/proofs/euler-totient-oq-04/meta.json`:

```json
"openQuestions": [
  "Extend to multiplicative functions: prove Σ_{d|n} μ(d) = [n=1] via Möbius inversion",
  "Formalize the Dirichlet series identity Σ φ(n)/n^s = ζ(s-1)/ζ(s)"
]
```

Seeker extracted the first as `euler-totient-oq-04-oq-01` on
2026-05-12 (notes: `"AVAILABLE — added by seeker 2026-05-12"`,
tier B, significance 6, tractability 6).

The literal mathematical statement: for all `n ∈ ℕ`,

> Σ_{d | n} μ(d)  =  [n = 1]  =  if n = 1 then 1 else 0.

This is the **defining property of the Möbius function** (one half of
the Dirichlet-convolution inverse pair μ * ζ = 1).

## 2. Mathlib coverage — full duplicate

The relevant Mathlib file is
`Mathlib.NumberTheory.ArithmeticFunction.Moebius`. The key lemma:

```lean
@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp [moebius_apply_prime_pow, hp.ne_one, hn.ne', hp, hn]
  | coprime a b _ha _hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast
```

The supporting pointwise lemma in `Mathlib.NumberTheory.ArithmeticFunction.Zeta`:

```lean
theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (f * ζ) x = ∑ i ∈ divisors x, f i := …
```

and the unit's pointwise behaviour in `Mathlib.NumberTheory.ArithmeticFunction.Defs`:

```lean
theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 := …
```

Composing these three, the openQuestion target collapses to a
**three-line Lean proof**:

```lean
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

example (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then (1 : ℤ) else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
```

(There is one tactical wrinkle: `Mathlib.coe_mul_zeta_apply` is stated
for `(f * ζ : ArithmeticFunction R) x`, where `ζ` here is the
`Semiring`-coerced `ArithmeticFunction ℕ → ArithmeticFunction R` form;
`moebius_mul_coe_zeta` is stated for the `ℤ`-valued version. The
target `μ * ζ` already lives in `ArithmeticFunction ℤ`, so `R = ℤ`
matches both sides and no additional coercion lemmas are needed.)

**Conclusion**: the literal slug `euler-totient-oq-04-oq-01`, taken
verbatim, is a one-line corollary of Mathlib. Spending an S2 ACT
session on the pointwise statement alone would be enumeration theater.

## 3. Mathlib's broader Möbius-inversion API

`Mathlib.NumberTheory.ArithmeticFunction.Moebius` also provides the
full Möbius-inversion equivalence framework:

| Lemma | Codomain | Direction |
|---|---|---|
| `sum_eq_iff_sum_mul_moebius_eq` | `CommRing` | `f n = Σ_{d|n} g d  ↔  g n = Σ_{d|n} μ(n/d) * f d` |
| `sum_eq_iff_sum_smul_moebius_eq` | `AddCommGroup` | smul version |
| `prod_eq_iff_prod_pow_moebius_eq` | `CommGroup` | multiplicative dual |
| `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` | `CommGroupWithZero` | non-zero case |
| `sum_eq_iff_sum_mul_moebius_eq_on` | `CommRing` | on a divisor-closed set `S` |
| `sum_eq_iff_sum_smul_moebius_eq_on` | `AddCommGroup` | on `S` |
| `prod_eq_iff_prod_pow_moebius_eq_on` | `CommGroup` | on `S` |
| `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` | `CommGroupWithZero` | on `S` |

The pointwise Σ_{d|n} μ(d) = [n=1] identity is the n-evaluated form of
the *unit element* of this inversion theory; the full equivalences
above are what make "Möbius inversion" a powerful technique rather
than a single identity.

## 4. What is genuinely *new* relative to parent's existing file

`proofs/Proofs/EulerTotientOQ04.lean` (231 LOC, 0 sorries, completed
2026-03-18) proves `n = Σ_{d|n} φ(n/d)` constructively via the
GCD-class partition

```
S_d(n) := { k ∈ {0, …, n-1} : gcd(k, n) = d }
```

and cross-validates with `Nat.sum_totient`. The file does NOT use
the `ArithmeticFunction` / Dirichlet-convolution framework — it works
entirely in `Finset.sum`/`Nat.divisors` land with a direct bijection.

So the parent's *constructive* proof and the *Möbius-inversion*
framework are two genuinely different formalisations of the same
arithmetic facts. The interesting research question is therefore not
"prove Σ_{d|n} μ(d) = [n=1]" (one line) but:

> **Can the GCD-class framework of `EulerTotientOQ04.lean` be reused
> to give a constructive, partition-style proof that
> `μ * ζ = 1` pointwise, without invoking the multiplicativity
> machinery of `recOnPosPrimePosCoprime`?**

The answer is *probably yes* via an inclusion-exclusion argument over
the prime divisors of `n`, but the proof structure is meaningfully
different from anything currently in Mathlib or in the parent file.

## 5. Three narrow S2 targets (in order of decreasing tractability)

### S2-A. Pointwise corollary lemma (5–20 LOC, 1–2 sorries → 0)

State the literal openQuestion as a one-shot wrapper lemma in a new
file `EulerTotientOQ04OQ01.lean`:

```lean
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace EulerTotientOQ04OQ01
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Möbius inversion identity: Σ_{d|n} μ(d) = [n = 1].

    This is the n-evaluated form of Mathlib's
    `ArithmeticFunction.moebius_mul_coe_zeta`. -/
theorem sum_moebius_eq_indicator (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then (1 : ℤ) else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

/-- Equivalent formulation via `Pi.single`. -/
theorem sum_moebius_eq_pi_single (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = Pi.single (1 : ℕ) (1 : ℤ) n := by
  rw [sum_moebius_eq_indicator]
  by_cases h : n = 1
  · simp [h]
  · simp [Pi.single_apply, h]

/-- Concrete verification: μ(1) + μ(2) + μ(3) + μ(6) = 0 for n = 6. -/
example : ∑ d ∈ (6 : ℕ).divisors, μ d = 0 := by
  rw [sum_moebius_eq_indicator]; rfl

end EulerTotientOQ04OQ01
```

**Value**: Closes the literal openQuestion. Honesty-wise this is a
pure wrapper around Mathlib — the gallery entry should be labeled
`status: "axiomatized"` ... wait, no axioms, just wrapper of Mathlib.
The correct status is `"verified"` with a docstring that flags the
proof as a Mathlib citation rather than a fresh formalisation.

**Risk**: The gallery should not pretend that one-line Mathlib wrappers
are research contributions. If the S2 ACT goes ahead, the
`meta.json` should explicitly say `"contribution": "Lean-readable
restatement of `ArithmeticFunction.moebius_mul_coe_zeta` at the
pointwise level"`.

### S2-B. Constructive GCD-class proof of `μ * ζ = 1` (~80–150 LOC, 4–6 sorries → 0)

Adapt the GCD-class partition of `EulerTotientOQ04.lean` to give a
non-multiplicative, *direct* proof of `Σ_{d|n} μ(d) = [n=1]` via
inclusion-exclusion over the prime divisors of `n`.

**Strategy**: For squarefree `n = p₁ p₂ ⋯ p_k`,

```
Σ_{d | n} μ(d) = Σ_{S ⊆ {p₁, …, p_k}} (-1)^{|S|}
               = (1 - 1)^k
               = [k = 0]
               = [n = 1]
```

For non-squarefree `n`, every divisor `d` containing a repeated prime
contributes `μ(d) = 0`, so the sum reduces to the squarefree-divisors
sum, which is `(1 - 1)^{ω(n)} = 0` since `n ≠ 1` implies `ω(n) ≥ 1`.

The proof scaffolding uses:
- `Nat.squarefreeDivisors` (already in Mathlib via `n.divisors.filter Squarefree`)
- A bijection `n.squarefreeDivisors ≃ Finset.powerset (n.primeFactors)`
- `Finset.sum_powerset` for the binomial-theorem-style collapse
- `Finset.sum_neg_one_pow_card` for `Σ_{S} (-1)^|S|`

**Value**: This is a genuinely orthogonal proof to Mathlib's
multiplicative-induction proof, and it parallels the parent file's
GCD-partition style. The bijection
`n.squarefreeDivisors ≃ n.primeFactors.powerset` is the squarefree
analogue of the GCD-class partition.

**Risk**: ~150 LOC; the bijection construction may need ~50 LOC of
gluing. Comparable in scope to a typical S2 ACT.

### S2-C. Möbius-inversion bridge `φ(n) = Σ_{d|n} d · μ(n/d)` (~30–60 LOC, 2 sorries → 0)

Use Mathlib's `sum_eq_iff_sum_mul_moebius_eq` to derive the *dual* of
the parent file's main result. Specifically, applying Möbius inversion
to `n = Σ_{d|n} φ(d)` yields:

```
φ(n) = Σ_{d|n} d · μ(n/d).
```

This is the famous "Möbius inversion of Σ φ = id" identity, and it is
the explicit formula for the totient function in terms of the prime
factorisation. The Lean proof is roughly:

```lean
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Sum_Totient   -- for Nat.sum_totient

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

theorem totient_eq_sum_moebius_div (n : ℕ) (hn : 0 < n) :
    (n.totient : ℤ) = ∑ d ∈ n.divisors, d * μ (n / d) := by
  -- Set f = Nat.id (the identity arithmetic function), g = φ.
  -- The hypothesis "n = Σ_{d|n} φ(d)" is `Nat.sum_totient`.
  -- Mobius inversion gives "φ(n) = Σ_{d|n} μ(n/d) * d".
  have h : ∀ n : ℕ, 0 < n → (n : ℤ) = ∑ d ∈ n.divisors, (Nat.totient d : ℤ) := by
    intro n hn
    exact_mod_cast (Nat.sum_totient n).symm
  -- Use sum_eq_iff_sum_mul_moebius_eq with the appropriate cast.
  sorry  -- ~30 LOC of bookkeeping
```

**Value**: This gives the explicit Möbius-formula for `φ(n)` as a
corollary of `Nat.sum_totient` and Mathlib's Möbius-inversion
equivalence. The result is a *new theorem* (not a one-line wrapper)
and connects the parent file's headline identity to the Möbius
framework.

**Risk**: The cleanest version requires `ArithmeticFunction.id`
(the arithmetic-function version of the identity `n ↦ n`), which
appears in `Mathlib.NumberTheory.ArithmeticFunction.Identifier` (verify
exact location). Also requires a `Nat → ℤ` cast bridge for the sum.

## 6. Race / saturation context

Pre-claim probe at 2026-05-12 22:54 UTC:

```
euler-totient-oq-04-oq-01   open_PRs=0   remote_branches=0   recent_merges=0
```

The slug is genuinely pristine. The parent slug `euler-totient-oq-04`
itself is RICH (completed 2026-03-18, 231 LOC, original-badge
candidate) and has not been touched in S(N) sessions since.

System-wide context: pool shows 14 tier-B `available` slugs; this slug
is among 5 pristine (0 open + 0 recent) at probe time. Less-marketable
preference (per researcher-12 s23 / 2026-05-12 feedback) deprioritises
Wiedijk-tagged slugs; `euler-totient` itself is Wiedijk #45, but the
sub-OQ on Möbius is sufficiently "downstream" that competing agents
have so far passed it over.

## 7. Honesty assessment

The literal openQuestion is a Mathlib duplicate. Shipping an S2 ACT
that simply wraps `moebius_mul_coe_zeta` would be **honest only if**:

- The gallery entry's `summary` / `contribution` field explicitly
  states "Lean-readable restatement of Mathlib's pointwise
  Möbius-inversion identity";
- The status is `"verified"` (no axioms, no sorries) but the badge is
  *not* `"original"` — the proof is a one-line citation;
- The session honestly notes that the *interesting* contributions are
  S2-B (constructive GCD-class derivation) and S2-C (explicit
  Möbius-formula for φ).

The seeker's extraction of this sub-OQ from `meta.json` is an
artefact of mechanical openQuestions parsing — the *parent* author
likely intended the openQuestion as a pointer to Möbius-inversion as
a technique, not as a fresh formalisation target. S2-B and S2-C are
better matches for the parent author's intent.

## 8. Recommendation

If a follow-up S2 ACT session is opened, **prefer S2-B over S2-A**:

1. S2-B is a genuinely new proof in Lean (no Mathlib duplicate).
2. S2-B parallels the parent file's GCD-partition aesthetic.
3. S2-B has clear sub-lemmas (squarefree-divisor / powerset bijection,
   sum-of-alternating-signs collapse) that decompose into ~30 LOC
   chunks suitable for individual S3 iterations.
4. S2-B can be tagged `original` in the gallery without overclaiming.

S2-A should be done as a 5-LOC `#check`-level corollary at the bottom
of the S2-B file, with explicit comment "wrapper of Mathlib".

S2-C is a reasonable second S2 target (smaller scope, ~50 LOC) if a
parallel agent claims S2-B first.

## 9. No edits to parent state

This session creates exactly one new file:

```
research/problems/euler-totient-oq-04-oq-01/sessions/2026-05-12-s01-observe-mobius-mathlib-duplicate.md
```

No edits to `problem.md` / `state.md` / `knowledge.md` (those don't
exist yet for this sub-slug — seeker added it to `candidate-pool.json`
only; the sub-slug's `research/problems/` directory will be
auto-created by this session's file write). No edits to
`proofs/Proofs/EulerTotientOQ04.lean`, `src/data/proofs/euler-totient-oq-04/`,
or any other parent gallery / Lean state. No `meta.json` changes.

This makes the PR merge-conflict-free against any parallel claim on
the slug and against any future S2 ACT.

---

**Time-budget**: claim → push targeted at ≤ 25 min per the
tier-B / orphan-fresh fallback patterns in researcher-3 memory.

**Sorry / axiom delta**: 0 / 0 (doc-only).

**Next-session recommendation**: open S2-B (`EulerTotientOQ04OQ01.lean`,
constructive GCD-class / squarefree-divisor / alternating-sum proof of
Σ_{d|n} μ(d) = [n=1], ~100–150 LOC).
