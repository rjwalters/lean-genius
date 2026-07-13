# S5 PREP — Transitivity-vs-Analytic-Inequality Obstruction

**Date**: 2026-05-13
**Slug**: roth-theorem-oq-02
**Researcher**: researcher-5
**Phase**: S5 PREP (doc-only, pre-flight obstruction audit)
**Mode**: post-S4-a PREP (researcher-4's PR #18443 merged 2026-05-13T02:06:38Z, ~50 min before this iteration claimed at 2026-05-13T02:56:53Z)
**Type**: Mathlib v4.26.0 API audit + obstruction theorem (no Lean changes)

## Why This PREP Exists

`proofs/Proofs/RothTheoremOQ02.lean` (S4-a, lines 198–210) proves

```lean
theorem kelley_meka_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_kelley_meka N hN)
```

via **pure transitivity through `rothNumberNat N`**: Mathlib's unconditional
`Behrend.roth_lower_bound` is `≤ rothNumberNat N` on the left, and the S4-a
axiom-form `rothNumberNat_le_kelley_meka N hN` is `rothNumberNat N ≤` on the
right. Composed, the two endpoints are `≤`.

This PREP investigates the **natural follow-up question**: *can the
underlying analytic inequality be proved directly, bypassing
`rothNumberNat`?* That is, can we prove (without invoking either axiom)

```lean
theorem analytic_envelope_kelley_meka_dominates_behrend (N : ℕ) (hN : 3 ≤ N) :
    -4 * Real.sqrt (Real.log N) ≤ -kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)
```

equivalently (after `neg_le_neg_iff` and dividing by `Real.log N ^ (1/12) > 0`,
which holds when `Real.log N > 0` i.e. `N ≥ 2`)

```
kelleyMekaConst * (Real.log N)^(1/12) ≤ 4 * (Real.log N)^(1/2)
```

i.e.

```
kelleyMekaConst ≤ 4 * (Real.log N)^(5/12).
```

**The answer is no: the analytic envelope inequality is UNPROVABLE within
the current axiomatic frame.** This document records why, and what the
correct S5 ACT looks like as a result.

## The Obstruction (Sharp Statement)

`kelleyMekaConst` is defined at `RothTheoremOQ02.lean:183-184` as

```lean
noncomputable def kelleyMekaConst : ℝ := rothNumberNat_kelley_meka.choose
```

where `rothNumberNat_kelley_meka` is an `axiom` (line 175-178):

```lean
axiom rothNumberNat_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 12))
```

The axiom **asserts existence** of `c > 0` but **fixes no upper bound** on
`c`. By `Exists.choose`, the witness `kelleyMekaConst` is some real number
in `(0, ∞)` with no additional constraints derivable from the axiom alone.

Concretely: any model that satisfies the axiom by exhibiting `c = 10^100` —
while compensating with a hypothetical Kelley–Meka–style direct proof that
`rothNumberNat N` decays at an absurdly slow rate consistent with this
huge `c` (since `exp(-10^100 · (log N)^{1/12})` is essentially zero for
all interesting `N`, so the bound is trivially satisfied) — is still a
model of the axiom.

In such a model, the analytic envelope inequality
`10^100 ≤ 4 · (Real.log N)^{5/12}` requires `Real.log N ≥ (10^100 / 4)^{12/5}
= exp(549.3) ≈ 10^{238.6}`, i.e. `N ≥ exp(exp(549.3))`, which is **NOT** the
`N ≥ 3` lower bound in the theorem statement. Hence the analytic envelope inequality FAILS in
this model, even though `kelley_meka_consistent_with_Behrend` continues to
hold (via transitivity).

**Formal obstruction theorem**: `kelley_meka_consistent_with_Behrend` is
provable via transitivity; the corresponding analytic envelope inequality
**is not provable** from the current axiomatic frame without strengthening
`rothNumberNat_kelley_meka` to specify (or upper-bound) `kelleyMekaConst`.

## Numerical Regime Check (For Concrete `c`)

To make the obstruction concrete, here is the regime in which the
analytic envelope DOES hold for a hypothetical concrete `c`:

| Hypothetical `c` (KM constant) | Min `N` for envelope to hold |
|---|---|
| `c = 1` (paper-style absolute constant) | All `N ≥ 3` (since `(log 3)^{5/12} ≈ 1.04 > 1/4`) |
| `c = 2` | All `N ≥ 3` (since `4 · 1.04 ≈ 4.16 > 2`) |
| `c = 4` | All `N ≥ 3` (since `4 · 1.04 ≈ 4.16 > 4`) |
| `c = 4.2` | Need `(log N)^{5/12} ≥ 1.05`, i.e. `log N ≥ 1.05^{12/5} ≈ 1.124`, i.e. `N ≥ 4` |
| `c = 10` | Need `(log N)^{5/12} ≥ 2.5`, i.e. `log N ≥ 2.5^{12/5} ≈ 9.017`, i.e. `N ≥ 8241` |
| `c = 100` | Need `(log N)^{5/12} ≥ 25`, i.e. `log N ≥ 25^{12/5} ≈ 2265`, i.e. `N ≥ exp(2265) ≈ 10^{984}` |
| `c = 10^100` | Need `log N ≥ exp(549.3) ≈ 10^{238.6}`, i.e. `N ≥ exp(10^{238.6})` (a number with ~10^{238.2} base-10 digits) |

**Computation key**: `(log N)^{5/12} ≥ c/4` ⇔ `log N ≥ (c/4)^{12/5}` ⇔
`N ≥ exp((c/4)^{12/5})`. Since `Exists.choose` permits arbitrary `c > 0`,
this lower bound on `N` is **unbounded** as a function of `c`. Hence no
uniform `N₀` works for the analytic envelope across all models of the
axiom — confirming that the analytic-inequality form is unprovable.

(Side note: the Kelley–Meka paper, arXiv:2302.05537, states the bound
with "some absolute constant" `c > 0` in Theorem 1.2 without committing
to a specific numerical value. The proof tracks `c` through Bohr-set
quasi-randomness; a careful audit of the paper would likely extract a
small absolute `c`, but the axiom as currently stated is faithful to the
paper's level of quantitative detail.)

## Mathlib v4.26.0 API Audit (Pin `2df2f0150c275ad`)

The lemmas that *would* prove the analytic envelope, IF the obstruction
were resolved (i.e. if we added a hypothesis `kelleyMekaConst ≤ K` for
some explicit `K`):

| Lemma | Statement | Location |
|---|---|---|
| `Real.sqrt_eq_rpow` | `√x = x ^ (1/2 : ℝ)` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988` |
| `Real.rpow_le_rpow_of_exponent_le` | `1 ≤ x → y ≤ z → x^y ≤ x^z` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:613` |
| `Real.rpow_le_rpow_left_iff` | `1 < x → (x^y ≤ x^z ↔ y ≤ z)` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:632` |
| `Real.log_pos` | `1 < x → 0 < Real.log x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (standard) |
| `Real.log_lt_log_iff` | `0 < y → (log x < log y ↔ x < y)` | same |
| `Real.exp_le_exp` | `Real.exp x ≤ Real.exp y ↔ x ≤ y` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |

**Mini-sketch of the conditional analytic-envelope proof** (assuming
`hKM_bound : kelleyMekaConst ≤ 4 * (Real.log 3)^((5 : ℝ) / 12)`):

```lean
theorem analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N)
    (hKM_bound : kelleyMekaConst ≤ 4 * (Real.log 3 : ℝ) ^ ((5 : ℝ) / 12)) :
    -(4 : ℝ) * Real.sqrt (Real.log N) ≤
      -kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) := by
  have h3 : (1 : ℝ) ≤ Real.log N := by
    -- log N ≥ log 3 > 1 needs `Real.log_lt_log_iff` + `Real.exp 1 < 3 :=
    -- by norm_num [Real.exp_one_lt_d9]` or similar. CAUTION: numerical fact.
    sorry
  have h_log3_le : (Real.log 3 : ℝ) ^ ((5 : ℝ) / 12) ≤
      Real.log N ^ ((5 : ℝ) / 12) := by
    apply Real.rpow_le_rpow (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN))
      (by norm_num : (0 : ℝ) ≤ 5 / 12)
  -- Combine: kelleyMekaConst ≤ 4 * (log N)^(5/12)
  -- Then multiply both sides by (log N)^(1/12) ≥ 0
  -- Use `Real.rpow_add` (or `mul_rpow`?) to combine exponents 5/12 + 1/12 = 1/2
  -- Conclude: kelleyMekaConst * (log N)^(1/12) ≤ 4 * (log N)^(1/2) = 4 * √(log N)
  -- Then `neg_le_neg`.
  sorry
```

The two `sorry`s correspond to: (a) numerical fact `1 < log 3`, which is
**false** (since `log 3 ≈ 1.0986 > 1`, this is fine — but it needs
`Real.exp_one_lt_d9` or hand-numerics in Lean); (b) the exponent-combining
arithmetic, routine via `Real.rpow_add` and `Real.rpow_one_div`. Both are
~30 LOC of Lean. *But* the hypothesis `hKM_bound` cannot be discharged
without strengthening the axiom — so this would only be a `theorem
analytic_envelope_conditional`, not an unconditional one. **Documented
here as a confirmation that the obstruction is genuinely structural, not
just a missing tactic.**

(Caveat: the numerical bound `4 * (log 3)^{5/12} ≈ 4.16` is for the
all-`N ≥ 3` regime. A weaker hypothesis `kelleyMekaConst ≤ K` with `K > 4.16`
would still permit the conditional proof, but with an explicit `N₀ =
⌈exp((K/4)^{12/5})⌉` instead of `3`.)

## Why The Transitivity Proof Is Strictly Stronger

The S4-a proof `kelley_meka_consistent_with_Behrend` works **for all
values** of `kelleyMekaConst`, including the absurdly-large `c = 10^100`
model above. It does so by **not touching the analytic content** at all
— the proof relies only on the joint existence of:

1. A lower bound `Behrend.roth_lower_bound : N · exp(-4√(log N)) ≤ rothNumberNat N`
   (unconditional, no axioms).
2. An upper bound `rothNumberNat_le_kelley_meka : rothNumberNat N ≤
   N · exp(-c · (log N)^{1/12})` (from the axiom, for the witness `c`).

Composed by `.trans`, this yields `N · exp(-4√(log N)) ≤ N · exp(-c · (log N)^{1/12})`
**regardless of whether the analytic envelope holds**. The hidden
mathematical content is: in any model of the axiom, both bounds must hold
of the same numerical sequence `rothNumberNat N`, so the "Behrend
lower-bound profile" cannot exceed the "Kelley–Meka upper-bound profile"
*on the values taken by `rothNumberNat N`*. The analytic envelope is
strictly stronger — it would assert the inequality between the two
profiles directly, irrespective of `rothNumberNat`.

This is a textbook illustration of a general principle: **transitivity
through a real-valued function is strictly weaker than an analytic
envelope between the bounding functions.** In Hardy–Littlewood–style
asymptotic analysis, this distinction is the difference between "both
bounds hold" (transitive consistency) and "the upper-bound function
dominates the lower-bound function" (envelope dominance).

## Generalization (For Future Sessions)

The same obstruction applies to **any pair of axiomatic asymptotic
bounds** asserted via `∃ c > 0, ∀ N ≥ N₀, ...`:

- **Bloom–Sisask (S2-A) vs Behrend** — `bloom_sisask_consistent_with_Behrend`
  at `RothTheoremOQ02.lean:138-141` is also a transitivity proof. Its
  analytic envelope `(N · exp(-4√(log N))) ≤ (N / (log N)^{1+c})` is
  similarly unprovable without an upper bound on `blasiConst`.
- **Sanders 2010, Schoen–Sisask 2016, Bourgain 1999** — any future axiom
  asserting `r₃(N) ≤ f_c(N)` for some `c`-parameterised family inherits
  the same obstruction.

**Pattern**: Whenever an axiom asserts `∃ c > 0, P(c)` and a downstream
theorem extracts the witness via `Exists.choose`, the witness is a "black
box" — *any* arithmetic bound on it requires either (a) strengthening the
axiom to `∃ c ∈ (0, K], P(c)` (replacing the existential with a bounded
existential), or (b) an additional axiom `kelleyMekaConst ≤ K` that
constrains the witness ex post.

## S5 ACT Plan (Recommended Path)

Given the obstruction documented here, the natural S5 ACT directions
ranked by lasting value:

### S5-a (recommended, smallest) — Document the obstruction explicitly in `RothTheoremOQ02.lean`

Add a `theorem` (or short docstring section) named, e.g.,
`kelley_meka_analytic_envelope_unprovable_documentation`, that:

1. States the analytic envelope as a `def` (not a `theorem`).
2. States in the docstring that it is unprovable from the current axiom set.
3. Provides the conditional version `analytic_envelope_conditional`
   (above), which adds an upper bound on `kelleyMekaConst` as a hypothesis
   and proves the envelope.

Effort: ~50 LOC Lean, no new axioms, 0 sorries. Risk: low.
**Value**: makes the obstruction discoverable by future researchers
reading the file, prevents wasted effort on a doomed direct proof.

### S5-b (medium) — Strengthen the Kelley–Meka axiom to a bounded existential

Replace `rothNumberNat_kelley_meka` with:

```lean
axiom rothNumberNat_kelley_meka_quantitative :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 12))
```

The added clause `c ≤ 1` is consistent with the Kelley–Meka paper (their
quantitative tracking yields a small absolute `c`) but is a non-trivial
strengthening of the axiom. The conditional analytic envelope then
becomes unconditional with `kelleyMekaConst ≤ 1 ≤ 4 · (log 3)^{5/12}`.

Effort: ~100 LOC (replace axiom + adjust downstream theorems +
add `analytic_envelope_unconditional`). Risk: low–medium (need to verify
the paper's `c` is indeed ≤ 1 — sketch in K–M Theorem 1.2 suggests this
is the case, but a literature audit is needed).
**Value**: enables a clean analytic-envelope proof.

### S5-c (large, multi-session) — Bohr-set scaffolding toward a non-axiomatic Kelley–Meka

The original S4-b plan (state.md:239–243). Multi-quarter effort: define
`BohrSet`, prove basic API, work toward Bogolyubov on Bohr sets, density
increment, etc. Not a single-session task; the present PREP does NOT
recommend starting this without a dedicated multi-session plan.

### Recommended next ACT: **S5-a**

It's the smallest, lowest-risk path; it prevents future researchers from
attempting the direct proof; and it documents a generally-applicable
principle (transitivity-vs-envelope) for the gallery. S5-b is a strict
strengthening but introduces a non-trivial axiomatic decision (committing
to `c ≤ 1`) that warrants a separate iteration.

## Race Safety / No-Edit Guarantee

This document is the **single new file** added by this iteration. It does
NOT touch:

- `problem.md`, `knowledge.md`, `state.md` (unchanged).
- `src/data/research/problems/roth-theorem-oq-02.json` (unchanged).
- Any `proofs/Proofs/*.lean` file (unchanged).
- `proofs/Proofs.lean` import index (unchanged).
- Any other `sessions/*.md` files (the `sessions/` subdir did not exist
  before this iteration; this file creates it).

In particular, this PR is **orthogonal** to the two open S3-tier PRs
(#18180 S3 OBSERVE, #18181 S3 ACT) — both of those PRs predate the now-merged
S3-B (PR #18238) and S4-a (PR #18443), so they are stale candidates for
closure-without-merge. This S5 PREP is forward-looking and does not
conflict with them in any case.

## Honesty / Calibration

- This is a **doc-only audit + obstruction theorem**, not a Lean
  formalization step. No new theorems, no new axioms, no new defs.
- The "obstruction theorem" (analytic envelope unprovability) is stated
  informally here; it is not itself a Lean `theorem`. A model-theoretic
  argument (above) suffices for the informal observation. A formal Lean
  proof of the unprovability would require Lean-side meta-reasoning
  (e.g. constructing two `axiom` choices and showing they yield distinct
  `analytic_envelope_*` provability), which is outside the scope of this
  iteration.
- The numerical regime table is a back-of-envelope calculation using
  `(log N)^{5/12}` monotonicity; it is correct to 2 decimal places at
  `log 3 ≈ 1.0986`.
- This PREP does **not** prove anything new about `r₃(N)`; it merely
  clarifies the formal status of the S4-a transitivity proof and
  identifies the cheapest next ACT.

## References

- Bloom, T. F. & Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions*. arXiv:2007.03528.
- Kelley, Z. & Meka, R. (2023). *Strong bounds for 3-progressions*.
  arXiv:2302.05537.
- Behrend, F. A. (1946). *On sets of integers which contain no three terms
  in arithmetical progression*. PNAS 32(12).
- `Mathlib.Combinatorics.Additive.AP.Three.Behrend` (v4.26.0,
  pin `2df2f0150c275ad`) — `Behrend.roth_lower_bound`.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` (v4.26.0) — `rpow` API.
- Prior `RothTheoremOQ02.lean` history: PRs #18031 (S1), #18094 (S2),
  #18238 (S3-B), #18443 (S4-a).
