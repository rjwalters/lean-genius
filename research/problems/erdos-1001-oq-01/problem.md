# Problem: Explicit formula for `limitValue(A,c)` outside the EST regime

## Statement

### Plain Language

The parent gallery proof `erdos-1001` (`Proofs/Erdos1001Problem.lean`,
249 lines, 0 sorries, 2 axioms) formalises **Erdős Problem #1001**:

> Let `S(N, A, c) := volume { α ∈ (0,1) | ∃ y, N ≤ y ≤ cN, gcd(x,y) = 1,
> |α − x/y| < A/y² }`. Does `lim_{N→∞} S(N, A, c)` exist? What is its
> explicit form?

**Erdős–Szüsz–Turán (1958)** answered both questions inside the **EST
regime** `inESTRegime A c := 0 < A ∧ A < c / (1 + c²)`: the limit
equals `f(A, c) := 12 · A · log(c) / π²`. **Kesten–Sós (1966)** showed
the limit exists for all valid `A, c`, but their method does not give
an explicit formula.

This open question (`oq-01`) asks for an explicit form of `limitValue(A, c)`
in the **complementary regime**

```
outsideESTRegime A c := 0 < A ∧ c / (1 + c²) ≤ A
```

Outside the EST regime, the Farey approximation intervals
`(x/y − A/y², x/y + A/y²)` for distinct coprime `x/y` with denominator
`y ∈ [N, cN]` may **overlap**, so the union's Lebesgue measure is **strictly
less** than the EST sum `12 A log(c) / π²` and the formula breaks down.

### Formal Statement (Goal Shape)

Within `namespace Erdos1001` in `Proofs/Erdos1001Problem.lean`:

```lean
-- (Already defined in parent)
noncomputable def limitValue (A c : ℝ) : ℝ := ...
def outsideESTRegime (A c : ℝ) : Prop := 0 < A ∧ c / (1 + c^2) ≤ A

-- Goal: an explicit function g : ℝ → ℝ → ℝ such that
theorem limit_outside_est_regime (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : outsideESTRegime A c) :
    limitValue A c = g A c := by
  sorry
```

Two **weaker** sub-goals decompose the problem:

```lean
-- (Sub-goal A): boundary case A = c / (1 + c²)
theorem limit_at_est_boundary (c : ℝ) (hc : c > 1) :
    limitValue (c / (1 + c^2)) c = 12 * (c / (1 + c^2)) * log c / π^2 := by
  sorry  -- conjecturally equal to the EST formula by continuity

-- (Sub-goal B): large-A saturation
theorem limit_tendsto_one_as_A_infty (c : ℝ) (hc : c > 1) :
    Tendsto (fun A => limitValue A c) atTop (nhds 1) := by
  sorry  -- the approximation set fills (0, 1)
```

Sub-goal A is the **continuity of `limitValue` at the EST boundary**,
which is a moderately tractable conjecture if Kesten–Sós is upgraded to
a continuity statement.  Sub-goal B is the **saturation limit** as
`A → ∞`, a separate measure-theoretic claim that the union of Farey
approximation intervals covers `(0, 1)` to full measure.

The **main goal** (full explicit formula outside EST) is generally
believed to be **open** — see §References for the
Boca–Cobeli–Zaharescu (2001) pair-correlation framework, which provides
an *implicit* characterisation via Farey-pair statistics but no closed
form.

## Classification

```yaml
tier: B
significance: 6
tractability: 4    # main goal genuinely open; sub-goals A, B tractable
tags:
  - seeker-selected
  - extension
  - number-theory
  - diophantine-approximation
  - measure-theory
  - farey-fractions
  - mathlib-gap
  - erdos-1001
```

(S1 OBSERVE revises tractability from the placeholder 6 to **4** because
the main goal — a closed-form explicit formula — is genuinely open in
the literature.  Sub-goal A and Sub-goal B remain individually tractable
at significance 4-5 / tractability 5-6 each.)

## Theoretical Setup

### The EST formula and its boundary

In the EST regime `A < c/(1+c²)`, the union

```
U(N, A, c) := ⋃_{y ∈ [N, cN]} ⋃_{x: gcd(x,y)=1} (x/y − A/y², x/y + A/y²) ∩ (0,1)
```

is, **up to negligible boundary effects**, a disjoint union: for any two
distinct coprime fractions `x₁/y₁` and `x₂/y₂` with `N ≤ y_i ≤ cN`,
the Farey-fraction gap bound

```
|x₁/y₁ − x₂/y₂| ≥ 1 / (y₁ y₂) ≥ 1 / (cN)²
```

(an easy consequence of `gcd(...) = 1`) is **larger** than the combined
interval radius `A/y₁² + A/y₂² ≤ 2A/N²` precisely when

```
1 / (cN)² ≥ 2A/N²  ⟺  A ≤ 1 / (2c²),
```

which is (almost) the EST regime modulo the actual sharper bound
`A < c/(1+c²)` derived by a more careful pair-by-pair analysis.

Outside this regime, **overlap is generic** and a simple inclusion-
exclusion sum

```
volume U(N,A,c) = Σ_{y, x} 2A/y² − Σ_{pairs} overlap + ...
```

does not telescope to a clean closed form — the pair-correlation
distribution of Farey fractions enters explicitly.

### Three independent obstacles

1. **The Boca–Cobeli–Zaharescu pair correlation.** Outside EST, the
   leading correction is the **pair-correlation density** of Farey
   fractions: the joint distribution of nearest-neighbour gaps
   `(x₁/y₁, x₂/y₂)` as `N → ∞`.  BCZ (2001) computed this distribution
   explicitly in terms of a parameter-dependent integral involving
   `Z(t) := ∑_{(p,q): 1/y_i ≤ 1/q ≤ t}`.  The outside-EST formula
   `limitValue(A, c) = ∫_{0}^{∞} h(A, c, t) dt` for an explicit `h`
   built from BCZ pair correlation is the "explicit" answer — but it
   is an integral, not a closed-form elementary function of `(A, c)`.

2. **The Farey-fraction Mathlib gap.** Mathlib (v4.26.0) has
   `Mathlib.NumberTheory.DiophantineApproximation` (Dirichlet's
   theorem, Legendre's theorem, continued-fraction convergents) and
   `Mathlib.NumberTheory.WellApproximable` (Khintchine–Groshev), but
   **no Farey-fraction infrastructure**: no `Mathlib.NumberTheory.Farey`,
   no `FareyFraction` type, no `Farey.gap_bound`, no
   `Farey.pair_correlation`.  The parent file's stub
   `FareyFraction (n : ℕ) : Set ℚ` is uninstantiated — closing the
   main OQ-01 goal requires upstream Farey infrastructure.

3. **The Kesten–Sós axiomatisation.** The parent file formalises
   Kesten–Sós (1966) as `axiom kesten_sos`, providing limit existence
   but no formula.  `limitValue` is defined via `Classical.choose`
   from this axiom — so any explicit-form theorem must either
   (a) prove `limitValue = explicit_form` from `kesten_sos` plus
       the BCZ machinery (a major undertaking), or
   (b) state a sub-goal that *equates* `limitValue` to a particular
       value in a limit case, using `tendsto_nhds_unique` (the
       technique used to discharge `limit_in_est_regime`).

   Sub-goals A and B above use approach (b) — both are
   `tendsto_nhds_unique`-style arguments against an independently-
   stated tendsto axiom or theorem.

### Mathlib API map (S1-level, to verify at S2)

| Symbol | Module | Use |
|---|---|---|
| `Real.exists_rat_abs_sub_le_and_den_le` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:147` | Dirichlet: existence of `q` with `|ξ − q| ≤ 1/((n+1)·q.den)` and `q.den ≤ n` |
| `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:197` | The set `{q : ℚ | |ξ − q| < 1/q.den²}` is infinite for irrational ξ |
| `Real.convergent` | `Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean` (TBD) | Continued-fraction convergents (for Xiong–Zaharescu) |
| `Real.exists_rat_eq_convergent` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:538` | Legendre's theorem: good rational approximations are convergents |
| `MeasureTheory.volume` (Lebesgue on ℝ) | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | Already used by parent for `S(N, A, c)` |
| `Filter.Tendsto.lim` / `tendsto_nhds_unique` | `Mathlib/Order/Filter/AtTopBot/Basic.lean` | Sub-goals A, B closure pattern |
| (Mathlib gap) `Farey.gap_lower_bound` | NOT IN MATHLIB | `|x₁/y₁ − x₂/y₂| ≥ 1/(y₁y₂)` for distinct coprime fractions |
| (Mathlib gap) `Farey.pair_correlation_density` | NOT IN MATHLIB | BCZ pair-correlation limit measure on `[0,∞)²` |

### Why the parent file's existing `FareyFraction` stub is insufficient

Parent `Proofs/Erdos1001Problem.lean:181`:

```lean
def FareyFraction (n : ℕ) : Set ℚ :=
  { r : ℚ | 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ n ∧ r.den.Coprime r.num.natAbs }
```

This is a **set**, not a `Finset`, with no enumeration, no neighbour
relation, no pair-correlation projection.  Any nontrivial OQ-01 work
requires either:

- (a) upgrading this to a `Finset` + a proven cardinality
  `FareyFraction.card_eq_sum_phi` (i.e., the Stern–Brocot
  cardinality `1 + Σ_{k=1}^n φ(k)`); OR
- (b) leveraging Mathlib's continued-fraction machinery to bypass
  Farey altogether (the Xiong–Zaharescu approach).

Both are substantial.

## Why It Matters

- **Erdős problem #1001 — partial.** The parent file marks
  `erdosProblemStatus: solved` because Kesten–Sós closed the limit-
  existence question.  But the **explicit formula** outside EST is the
  natural follow-up that the parent's `Outside the EST Regime` block
  flags as "an active research direction".  Closing even a
  sub-goal (A or B) advances the formalisation toward a more complete
  picture of the problem.

- **Mathlib contribution surface.** Whichever route is taken
  (Farey infrastructure or continued-fraction-based Xiong–Zaharescu)
  produces a meaningful Mathlib PR target.  Farey-fraction
  infrastructure in particular is a long-standing Mathlib gap (cf.
  the absence of `Mathlib.NumberTheory.Farey` as of v4.26.0).

- **Bridge to other Erdős problems.** Erdős's problems on
  Diophantine approximation density (#1001, #1098, and others) all
  share the Farey / pair-correlation infrastructure.  Closing a
  sub-goal of OQ-01 builds reusable lemmas for #1098 and downstream
  Erdős-Sárközy / Erdős-Ko / etc.

## Suggested Decomposition

**S1 (this session, doc-only):** Survey complete.  Identify the three
obstacles above and three Mathlib bearer surfaces.  Decompose the OQ
into two tractable sub-goals (A, B) and one open main goal.  Update
state.md `NEW → OBSERVE`.

**S2 (Sub-goal A — boundary case):** State and prove (or axiomatise via
a continuity-of-`limitValue` assumption) that

```
limit_at_est_boundary :
  limitValue (c / (1 + c²)) c = 12 · (c / (1 + c²)) · log c / π²
```

This is a continuity-of-`limitValue` consequence + an explicit
substitution.  Estimated: +20-40 lines in `Proofs/Erdos1001Problem.lean`,
possibly +1 axiom `axiom continuity_of_limitValue` or a tendsto-from-EST
argument that bypasses continuity.

**S3 (Sub-goal B — saturation limit):** State and prove that for
fixed `c > 1`,

```
limit_tendsto_one_as_A_infty :
  Tendsto (fun A => limitValue A c) atTop (nhds 1)
```

This is the measure-theoretic claim that the Farey-approximation set
fills `(0, 1)` to full measure as `A → ∞`.  Likely uses Borel–Cantelli
or a direct density estimate.  Estimated: +30-60 lines, possibly +1
axiom for the underlying measure-fill statement.

**S4+ (Main goal — explicit BCZ formula):** Defer.  Requires Farey-
fraction Mathlib infrastructure (out of scope of a single research
session).  Suggest spawning sibling open questions on:
- `oq-01-oq-01` "Farey-fraction Mathlib infrastructure"
- `oq-01-oq-02` "BCZ pair-correlation density"
- `oq-01-oq-03` "limitValue as a BCZ-pair-correlation integral"

## References

- **Parent gallery proof.** `Proofs/Erdos1001Problem.lean` (249 lines,
  0 sorries, 2 axioms: `erdos_szusz_turan` and `kesten_sos`).  Defines
  `S`, `f`, `limitValue`, `inESTRegime`, `outsideESTRegime`, `estBoundary`,
  `FareyFraction`.

- **Erdős, Szüsz, Turán (1958).** "On some properties of the Cantor
  product."  Acta Sci. Math. Szeged 19 (1958).  EST formula in EST
  regime.

- **Kesten, Sós (1966).** "On rational approximations of real numbers."
  Acta Arith. 12 (1966), 295–304.  Limit existence in general.

- **Boca, Cobeli, Zaharescu (2001).** "Distribution of lattice points
  visible from the origin."  Comm. Math. Phys. 213 (2001), 433–470.
  Pair-correlation density of Farey fractions; the "BCZ measure".

- **Xiong, Zaharescu (2006).** "A new approach to the Steinhaus
  conjecture."  Bull. Lond. Math. Soc. 38 (2006), 33–43.
  Continued-fraction-based alternative proof of Kesten–Sós.

- **Boca (2008).**  "A problem of Erdős, Szüsz, and Turán concerning
  Diophantine approximations."  Int. J. Number Theory 4 (2008),
  691–708.  Independent proof of Kesten–Sós via geometry of numbers.

- **Mathlib v4.26.0.**
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` (Dirichlet,
  Legendre); `Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`
  (`Real.convergent`); `Mathlib/NumberTheory/WellApproximable.lean`
  (Khintchine–Groshev).  No `Mathlib.NumberTheory.Farey`.

- **Sibling gallery slugs in the erdos-1001 family.**
  `erdos-1001-oq-02` (analogous open question, formalisation
  in-progress per parent `additionalFiles`),
  `erdos-1001-oq-02-oq-01` (sub-question of oq-02), and
  `erdos-1001-oq-03` (a different oq, status TBD).  See parent
  `meta.json` `crossReferences`.
