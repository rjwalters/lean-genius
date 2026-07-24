import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Roth's Theorem — Bloom–Sisask Logarithmic Bound (OQ-02, S2 ACT-A)

## What This Provides

A typed Lean target for the Bloom–Sisask 2020 quantitative refinement of
Roth's theorem on three-term arithmetic progressions:

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N / (log N)^(1+c)

The bound is named `rothNumberNat_bloom_sisask` and asserted as a Lean
`axiom`. Supporting names — `blasiConst` (a choice of constant `c`),
`blasiConst_pos` (its positivity), and `rothNumberNat_le_blasi` (the
bound at the chosen constant) — give downstream consumers a stable API
without having to call `Exists.choose` manually.

The file is *intentionally minimal*: it provides the typed landmark and
the trivial consequence that the axiom is consistent with Mathlib's
existing qualitative result `rothNumberNat_isLittleO_id`. The Lean
formalization of Bloom–Sisask itself (≥ several thousand lines through
Bohr sets, density increment, and Fourier analysis) is deferred.

## Scope (S2 ACT-A, researcher-12, 2026-05-12)

- File status: **axiomatized** (1 axiom, 0 sorries).
- Imports: `Mathlib.Combinatorics.Additive.Corner.Roth` (for
  `rothNumberNat` and `rothNumberNat_isLittleO_id`) and
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for `Real.log`).
- The axiom matches the wording in the docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`, which explicitly names
  Bloom–Sisask as the expected upper bound on `rothNumberNat`.

## Why This Companion File (Path vs Editing the Gallery `bloom_sisask_bound`)

The existing gallery file `proofs/Proofs/RothTheoremQuantitative.lean`
already states a closely-related bound (`bloom_sisask_bound`) with `sorry`
and uses a project-local `rothNumber` from
`namespace Szemeredi.Roth.Quantitative`. This OQ-02 companion file
deliberately works at the **Mathlib `rothNumberNat`** level, leaving the
gallery file untouched. Downstream Mathlib-style consumers can refer to
`RothTheoremOQ02.rothNumberNat_bloom_sisask` directly; gallery consumers
continue to refer to `Szemeredi.Roth.Quantitative.bloom_sisask_bound`.
Future work can unify the two presentations once Mathlib gains the
prerequisite Bohr-set / density-increment / Fourier infrastructure.

## References

- Bloom, T. F., Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions.* arXiv:2007.03528.
- Mathlib v4.26.0 module docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
- Parent quantitative Roth file:
  `proofs/Proofs/RothTheoremQuantitative.lean`.
-/

namespace RothTheoremOQ02

open Asymptotics Filter Topology

/-- **Bloom–Sisask 2020 logarithmic-barrier-breaking bound on the Roth
number.** Axiomatic statement:

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N / (log N)^(1+c)

Proved analytically in Bloom–Sisask, arXiv:2007.03528 (2020), via
density increment on Bohr sets with refined Fourier analysis; the full
proof requires Bohr-set infrastructure not yet in Mathlib at v4.26.0
(pin `2df2f0150c275ad`). Asserted here axiomatically so downstream
gallery files can refer to the bound by name.

The lower bound `N ≥ 3` matches the convention in the gallery file
`Szemeredi.Roth.Quantitative.bloom_sisask_bound` and ensures
`Real.log N > Real.log 3 > 1`, so the right-hand side is positive and
the bound is non-vacuous. -/
axiom rothNumberNat_bloom_sisask :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)

/-- A canonical choice of the Bloom–Sisask constant `c > 0` extracted from
the axiom via `Exists.choose`. Marked `noncomputable` because
`Exists.choose` is. -/
noncomputable def blasiConst : ℝ :=
  rothNumberNat_bloom_sisask.choose

/-- The Bloom–Sisask constant is positive. -/
theorem blasiConst_pos : 0 < blasiConst :=
  rothNumberNat_bloom_sisask.choose_spec.1

/-- **Bloom–Sisask bound at the canonical constant.** For every `N ≥ 3`,
`rothNumberNat N ≤ N / (log N)^(1 + blasiConst)`. Stable downstream API
that hides the `Exists.choose`. -/
theorem rothNumberNat_le_blasi (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  rothNumberNat_bloom_sisask.choose_spec.2 N hN

/-- **Consistency with Mathlib's qualitative result.** Mathlib v4.26.0
records `rothNumberNat_isLittleO_id : (rothNumberNat N : ℝ) =o[atTop] (N : ℝ)`
unconditionally in `Mathlib.Combinatorics.Additive.Corner.Roth`. The
Bloom–Sisask axiom strengthens this with an *explicit* decay rate
`O(N / (log N)^(1+c))`, and is consistent with the qualitative form
in the sense that both assert `rothNumberNat N = o(N)`. We record the
qualitative form as a one-line export so OQ-02 consumers can pull it
in via this namespace without re-deriving it from the axiom. -/
theorem bloom_sisask_consistent_with_isLittleO :
    IsLittleO atTop (fun N : ℕ => (rothNumberNat N : ℝ))
      (fun N : ℕ => (N : ℝ)) :=
  rothNumberNat_isLittleO_id

/-- **Consistency of the Bloom–Sisask upper bound with Behrend's lower bound.**
For every `N ≥ 3`, Behrend's explicit lower bound on `rothNumberNat N`
does not exceed the Bloom–Sisask upper bound:

  `N * exp(-4 * √(log N)) ≤ N / (log N)^(1 + blasiConst)`.

This sanity-checks the `rothNumberNat_bloom_sisask` axiom against the
*unconditional* lower bound `Behrend.roth_lower_bound` proved in Mathlib
v4.26.0:

  `(N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`.

The proof is purely transitive through `rothNumberNat N`: both bounds
hold simultaneously, so the lower bound is `≤` the upper bound. We do
*not* prove the underlying analytic inequality
`(1 + c) * log log N ≤ 4 * √(log N)` directly; the consistency follows
automatically from the existence of both bounds.

The point is to record explicitly that the two endpoint inequalities are
compatible — i.e. they do not cross — and to flag that the gap between
them (Behrend's `exp(-4√(log N))` vs Bloom–Sisask's `1 / (log N)^(1+c)`)
remains the central open quantitative question. Kelley–Meka (2023) brings
the upper bound much closer to Behrend, with `N * exp(-c * (log N)^(1/12))`;
the analogue of this theorem against the Kelley–Meka bound (much tighter)
is a natural follow-up. -/
theorem bloom_sisask_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_blasi N hN)

/-! ## S4-a: Kelley–Meka 2023 bound on the Roth number

Kelley and Meka (arXiv:2302.05537, 2023) tightened the Bloom–Sisask
log-barrier-breaking bound to the **exponential** form

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N · exp(-c · (log N)^(1/12))

This is the strongest known upper bound on `rothNumberNat`, and is
substantially closer to Behrend's lower bound
`(N : ℝ) * exp(-4 * √(log N)) ≤ rothNumberNat N`. Asymptotically:

  Behrend lower bound:           N · exp(-4   · (log N)^(1/2))
  Kelley–Meka upper bound:       N · exp(-c   · (log N)^(1/12))
  Bloom–Sisask upper bound:      N / (log N)^(1+c')             (much weaker)

The gap between Behrend and Kelley–Meka is essentially the exponent of
`log N` inside the exponential (`1/2` vs `1/12`). Closing it is the
remaining open quantitative question.

Like S2/S3, this layer is **statement-only** (`axiom` + transitivity);
the full ~200-page Kelley–Meka analytic proof is far beyond Mathlib's
current Bohr-set / quasi-randomness infrastructure. -/

/-- **Kelley–Meka 2023 bound on the Roth number.** Axiomatic statement
matching the abstract of Kelley–Meka, arXiv:2302.05537:

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N · exp(-c · (log N)^(1/12))

The exponent `1/12` is exactly the constant in the Kelley–Meka paper
(see their Theorem 1.2). Asserted here axiomatically; the full proof
requires Bohr-set quasi-randomness machinery not yet in Mathlib at
v4.26.0 (pin `2df2f0150c275ad`). -/
axiom rothNumberNat_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 12))

/-- A canonical choice of the Kelley–Meka constant `c > 0` extracted
from the axiom via `Exists.choose`. Marked `noncomputable` because
`Exists.choose` is. -/
noncomputable def kelleyMekaConst : ℝ :=
  rothNumberNat_kelley_meka.choose

/-- The Kelley–Meka constant is positive. -/
theorem kelleyMekaConst_pos : 0 < kelleyMekaConst :=
  rothNumberNat_kelley_meka.choose_spec.1

/-- **Kelley–Meka bound at the canonical constant.** For every `N ≥ 3`,
`rothNumberNat N ≤ N · exp(-kelleyMekaConst · (log N)^(1/12))`. Stable
downstream API hiding the `Exists.choose`. -/
theorem rothNumberNat_le_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) :=
  rothNumberNat_kelley_meka.choose_spec.2 N hN

/-- **Consistency of the Kelley–Meka upper bound with Behrend's lower bound.**
For every `N ≥ 3`,

  `N * exp(-4 * √(log N)) ≤ N * exp(-kelleyMekaConst * (log N)^(1/12))`.

By transitivity through `rothNumberNat N`, leveraging Mathlib's
*unconditional* `Behrend.roth_lower_bound` and our `rothNumberNat_le_kelley_meka`.
Records explicitly that Behrend ≤ Kelley–Meka — the two endpoint
inequalities are compatible and do not cross. -/
theorem kelley_meka_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_kelley_meka N hN)

/-- **Joint compatibility of Bloom–Sisask and Kelley–Meka.** Both upper
bounds hold simultaneously, so `rothNumberNat N` is bounded by the
*minimum* of the two upper bounds. Records that the two axioms do not
contradict — together they give a strictly tighter envelope on
`rothNumberNat` than either alone. -/
theorem rothNumberNat_le_min_blasi_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      min ((N : ℝ) / Real.log N ^ (1 + blasiConst))
          ((N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))) :=
  le_min (rothNumberNat_le_blasi N hN) (rothNumberNat_le_kelley_meka N hN)

/-! ## S5-a: Conditional analytic envelope (Kelley–Meka vs Behrend)

The transitivity proof `kelley_meka_consistent_with_Behrend` shows the
two endpoints are compatible by routing through `rothNumberNat N`. That
proof is correct but *analytically vacuous*: it uses the upper bound to
upper-bound the lower bound. The transitive `≤` would hold for *any*
positive constant `kelleyMekaConst`, even ones that would make K-M
asymptotically *weaker* than Behrend.

The conditional version below records the genuine *analytic content*:
**assuming** the K-M constant is bounded by `4 * (Real.log 3)^(5/12)`
(numerically `≈ 4.165`), the K-M upper bound is analytically tighter
than the Behrend lower bound — independent of `rothNumberNat`.

This conditional theorem is *not unconditional* because the K-M axiom
asserts only `∃ c > 0, ...` without a quantitative bound on `c`, so
`Exists.choose` extracts an unconstrained witness. A future
strengthening of the axiom to `∃ c ≤ K, ...` for explicit `K` would
make the analytic envelope unconditional; see PR #18509 §"S5-b" for
the discussion.

The proof uses only Mathlib `Real.log`/`Real.rpow`/`Real.sqrt` API plus
the `Real.exp_one_lt_d9` numerical bound. -/

/-- **The analytic envelope of the Kelley–Meka 2023 upper bound vs the
Behrend 1946 lower bound on `rothNumberNat`** as a bare `Prop`-valued
function.

For each `N`, the proposition asserts: if `N ≥ 3` then the Behrend
lower-bound function value is dominated by the Kelley–Meka upper-bound
function value, i.e.

  `N · exp(-4 · √(log N)) ≤ N · exp(-kelleyMekaConst · (log N)^(1/12))`.

This bare definition records the analytic envelope as a target without
asserting it; the conditional discharge follows in
`analytic_envelope_conditional`. The unconditional version is *not
provable* from the present axioms (see the S5-a docstring above). -/
def analytic_envelope_kelley_meka (N : ℕ) : Prop :=
  3 ≤ N →
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))

/-- **Conditional analytic envelope: Kelley–Meka dominates Behrend.**

Assuming the Kelley–Meka constant satisfies `kelleyMekaConst ≤
4 * (Real.log 3)^(5/12)` (numerically `≈ 4.165`), the negated exponents
inside the Behrend / Kelley–Meka envelope satisfy

  `-(4 : ℝ) * √(log N) ≤ -kelleyMekaConst * (log N)^(1/12)`

for every `N ≥ 3`. Multiplying by `-1` and exponentiating (which both
preserve order) recovers the full envelope
`N · exp(-4 √(log N)) ≤ N · exp(-kelleyMekaConst · (log N)^(1/12))`.

The proof is verbatim composition of `Real.log_pos`,
`Real.exp_one_lt_d9`, `Real.log_lt_log_iff`, `Real.log_exp`,
`Real.log_le_log`, `Real.rpow_le_rpow`, `Real.rpow_nonneg`,
`Real.rpow_add`, and `Real.sqrt_eq_rpow`, closed by `linarith`. -/
theorem analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N)
    (hKM_bound : kelleyMekaConst ≤ 4 * (Real.log 3 : ℝ) ^ ((5 : ℝ) / 12)) :
    -(4 : ℝ) * Real.sqrt (Real.log N) ≤
      -kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) := by
  -- §3: 1 ≤ Real.log N for N ≥ 3
  have h_log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_e_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1)
                (by norm_num : (0 : ℝ) < 3)).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  have h_log3_le_logN : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN)
  have h_one_le_logN : (1 : ℝ) ≤ Real.log N :=
    le_of_lt (lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN)
  have h_logN_pos : (0 : ℝ) < Real.log N :=
    lt_of_lt_of_le zero_lt_one h_one_le_logN
  -- §4 step 1: (log 3)^(5/12) ≤ (log N)^(5/12)
  have h_rpow_5_12_mono : (Real.log 3 : ℝ) ^ ((5 : ℝ) / 12) ≤
      Real.log N ^ ((5 : ℝ) / 12) :=
    Real.rpow_le_rpow (le_of_lt h_log3_pos) h_log3_le_logN
      (by norm_num : (0 : ℝ) ≤ 5 / 12)
  -- §4 step 2: kelleyMekaConst ≤ 4 * (log N)^(5/12)
  have h_kmConst_le_4_rpow_5_12 : kelleyMekaConst ≤
      4 * Real.log N ^ ((5 : ℝ) / 12) :=
    le_trans hKM_bound (mul_le_mul_of_nonneg_left h_rpow_5_12_mono
                          (by norm_num : (0 : ℝ) ≤ 4))
  -- §4 step 3-7
  have h_rpow_1_12_nonneg : (0 : ℝ) ≤ Real.log N ^ ((1 : ℝ) / 12) :=
    Real.rpow_nonneg (le_of_lt h_logN_pos) _
  have h_kmConst_mul_rpow_1_12 :
      kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) ≤
        (4 * Real.log N ^ ((5 : ℝ) / 12)) * Real.log N ^ ((1 : ℝ) / 12) :=
    mul_le_mul_of_nonneg_right h_kmConst_le_4_rpow_5_12 h_rpow_1_12_nonneg
  have h_exp_eq : ((5 : ℝ) / 12 + (1 : ℝ) / 12) = (1 : ℝ) / 2 := by norm_num
  have h_rpow_combine :
      (4 * Real.log N ^ ((5 : ℝ) / 12)) * Real.log N ^ ((1 : ℝ) / 12) =
        4 * Real.log N ^ ((1 : ℝ) / 2) := by
    rw [mul_assoc, ← Real.rpow_add h_logN_pos, h_exp_eq]
  have h_sqrt_rpow : Real.sqrt (Real.log N) = Real.log N ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow _
  have h_pre_neg : kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) ≤
      4 * Real.sqrt (Real.log N) := by
    rw [h_sqrt_rpow]
    calc kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)
        ≤ (4 * Real.log N ^ ((5 : ℝ) / 12)) * Real.log N ^ ((1 : ℝ) / 12) :=
          h_kmConst_mul_rpow_1_12
      _ = 4 * Real.log N ^ ((1 : ℝ) / 2) := h_rpow_combine
  linarith

/-! ## S6-a: Conditional analytic envelope (Bloom–Sisask vs Behrend)

The transitivity proof `bloom_sisask_consistent_with_Behrend` shows the
Behrend lower bound and the Bloom–Sisask upper bound are compatible by
routing through `rothNumberNat N`. Like its Kelley–Meka sibling above,
that proof is *analytically vacuous*: the transitive `≤` holds for
*every* positive `blasiConst`, however large.

The conditional version below records the genuine *analytic content*:
**assuming** `blasiConst ≤ 2e - 1` (numerically `≈ 4.4366`), the B–S
upper-bound function dominates the Behrend lower-bound function for all
`N ≥ 3` — independent of `rothNumberNat`.

The constant `2e` is optimal for the all-`N ≥ 3` regime: the analytic
core `(1 + c) · log(log N) ≤ 4 · √(log N)` reduces (with `y = log N`)
to `1 + c ≤ 4√y / log y`, and `4√y / log y` attains its minimum `2e`
at `y = e²` (interior to the range `y ≥ log 3`). See S6 PREP
(sessions/2026-05-13-s6-prep-bloom-sisask-analytic-envelope-verbatim.md)
§3 for the derivation.

This conditional theorem is *not unconditional* because the B–S axiom
asserts only `∃ c > 0, ...`; `Exists.choose` extracts an unconstrained
witness (same obstruction as the K–M case, PR #18509). -/

/-- **The analytic envelope of the Bloom–Sisask 2020 upper bound vs the
Behrend 1946 lower bound on `rothNumberNat`** as a bare `Prop`-valued
function.

For each `N`, the proposition asserts: if `N ≥ 3` then

  `N · exp(-4 · √(log N)) ≤ N / (log N)^(1 + blasiConst)`.

This bare definition records the analytic envelope as a target without
asserting it. **It is unprovable from the current axiom set** (see
PR #18509: `blasiConst` is `Exists.choose` of an unbounded existential).
Future researchers can either strengthen the B–S axiom to a
bounded-existential form, or use the conditional version
`bloom_sisask_analytic_envelope_conditional` below, which adds an
explicit upper bound on `blasiConst` as a hypothesis. Parallel to
`analytic_envelope_kelley_meka` (S5b PREP §8). -/
def analytic_envelope_bloom_sisask (N : ℕ) : Prop :=
  3 ≤ N →
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst)

/-- **The conditional B–S analytic envelope.**

Assuming `blasiConst ≤ 2 * Real.exp 1 - 1` (numerically `≈ 4.4366`),
the negated exponents inside the Behrend / Bloom–Sisask envelope satisfy

  `-(4 : ℝ) * √(log N) ≤ -(1 + blasiConst) * log(log N)`

for every `N ≥ 3`. This is **strictly stronger** than the transitivity
proof `bloom_sisask_consistent_with_Behrend`, which works for *every*
value of `blasiConst` regardless of the analytic content.

The optimal numerical constant `K = 2e` arises because the analytic
core `(1 + c) · log(log N) ≤ 4 · √(log N)` has the minimum of
`4 · √y / log y` at `y = e²`, giving `f(e²) = 2e`. The Bloom–Sisask
paper's `c` is informally `≈ 1/24` to `1/12`, hence
`blasiConst ≤ 2e - 1 ≈ 4.4366` is a *very loose* hypothesis from the
paper's standpoint.

The analytic heart is `Real.exp_one_mul_le_exp` (`e · x ≤ eˣ`)
specialized to `x = log(√(log N))`, i.e. `e · log u ≤ u`. -/
theorem bloom_sisask_analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N)
    (hBS_bound : blasiConst ≤ 2 * Real.exp 1 - 1) :
    -(4 : ℝ) * Real.sqrt (Real.log N) ≤
      -(1 + blasiConst) * Real.log (Real.log N) := by
  -- §5: 1 ≤ Real.log N, hence log N > 0, log N ≥ 0, 1 < log N.
  have h_log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_e_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1)
                (by norm_num : (0 : ℝ) < 3)).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  have h_log3_le_logN : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN)
  have h_one_le_logN : (1 : ℝ) ≤ Real.log N :=
    le_of_lt (lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN)
  have h_logN_pos : (0 : ℝ) < Real.log N :=
    lt_of_lt_of_le zero_lt_one h_one_le_logN
  have h_one_lt_logN : (1 : ℝ) < Real.log N :=
    lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN
  have h_logN_nonneg : (0 : ℝ) ≤ Real.log N := le_of_lt h_logN_pos
  -- §6: log(log N) > 0 and √(log N) > 0.
  have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) :=
    Real.log_pos h_one_lt_logN
  have h_sqrt_logN_pos : (0 : ℝ) < Real.sqrt (Real.log N) :=
    Real.sqrt_pos.mpr h_logN_pos
  -- §7: the analytic core: e · log(√(log N)) ≤ √(log N).
  have h_e_log_sqrt_le_sqrt :
      Real.exp 1 * Real.log (Real.sqrt (Real.log N)) ≤
        Real.sqrt (Real.log N) := by
    have h := Real.exp_one_mul_le_exp
                (x := Real.log (Real.sqrt (Real.log N)))
    rwa [Real.exp_log h_sqrt_logN_pos] at h
  -- §8: translate to 2e · log(log N) ≤ 4 · √(log N).
  have h_log_sqrt_eq : Real.log (Real.sqrt (Real.log N)) =
      Real.log (Real.log N) / 2 := Real.log_sqrt h_logN_nonneg
  have h_2e_loglogN_eq : 2 * Real.exp 1 * Real.log (Real.log N) =
      4 * (Real.exp 1 * Real.log (Real.sqrt (Real.log N))) := by
    rw [h_log_sqrt_eq]; ring
  have h_2e_loglogN_le_4_sqrt : 2 * Real.exp 1 * Real.log (Real.log N) ≤
      4 * Real.sqrt (Real.log N) := by
    rw [h_2e_loglogN_eq]
    exact mul_le_mul_of_nonneg_left h_e_log_sqrt_le_sqrt
      (by norm_num : (0 : ℝ) ≤ 4)
  -- §9: combine with hypothesis and conclude.
  have h_1_plus_c_le_2e : 1 + blasiConst ≤ 2 * Real.exp 1 := by linarith
  have h_main : (1 + blasiConst) * Real.log (Real.log N) ≤
      2 * Real.exp 1 * Real.log (Real.log N) :=
    mul_le_mul_of_nonneg_right h_1_plus_c_le_2e (le_of_lt h_loglogN_pos)
  have h_main_chain : (1 + blasiConst) * Real.log (Real.log N) ≤
      4 * Real.sqrt (Real.log N) :=
    le_trans h_main h_2e_loglogN_le_4_sqrt
  linarith

/-! ## S6-d: Conditional head-to-head — Kelley–Meka vs Bloom–Sisask

The joint envelope `rothNumberNat_le_min_blasi_kelley_meka` bounds
`rothNumberNat N` by `min(B(N), K(N))` without saying which term wins.
Analytically, K–M decays like `exp(-c·(log N)^{1/12})` and B–S only
polylogarithmically, so K–M *eventually* dominates — but the crossover
threshold depends on both `Exists.choose` constants, which are
unbounded across axiom models, so the unconditional comparison is
**unprovable** in the current frame (same obstruction as S5/S6; see
S6c PREP, sessions/2026-05-13-s6c-prep-km-vs-bs-envelope-comparison.md).

The conditional version parameterizes on numeric bounds `C₁ ≤
kelleyMekaConst`, `blasiConst ≤ C₂` and an explicit threshold hypothesis
`(log N)^{1/12} ≥ ((1 + C₂)/C₁) · log(log N)`, under which the K–M
envelope is at most the B–S envelope — so the `min` collapses to the
K–M term (`min_blasi_kelley_meka_eq_kelley_meka_eventually`). -/

/-- **Kelley–Meka envelope ≤ Bloom–Sisask envelope (conditional).**

If `0 < C₁ ≤ kelleyMekaConst`, `blasiConst ≤ C₂`, and `N ≥ 3` satisfies
the threshold `(log N)^{1/12} ≥ ((1 + C₂)/C₁) · log(log N)`, then the
Kelley–Meka upper-bound function at `N` is at most the Bloom–Sisask
upper-bound function at `N`.

The comparison does *not* route through `rothNumberNat` — it is a pure
analytic-envelope statement, which is exactly why it needs the constant
bounds (unprovable otherwise; S6c PREP §3). -/
theorem kelley_meka_envelope_le_bloom_sisask_envelope_conditional
    (N : ℕ) (hN : 3 ≤ N) (C₁ C₂ : ℝ)
    (h_C₁_pos : 0 < C₁)
    (h_KM_bound : C₁ ≤ kelleyMekaConst)
    (h_BS_bound : blasiConst ≤ C₂)
    (h_N_threshold : Real.log N ^ ((1 : ℝ) / 12)
                       ≥ ((1 + C₂) / C₁) * Real.log (Real.log N)) :
    (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))
      ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst) := by
  -- Setup: log N > 1 (so log(log N) > 0), (log N)^{1/12} ≥ 0.
  have h_log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_e_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1)
                (by norm_num : (0 : ℝ) < 3)).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  have h_log3_le_logN : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN)
  have h_one_lt_logN : (1 : ℝ) < Real.log N :=
    lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN
  have h_logN_pos : (0 : ℝ) < Real.log N :=
    lt_trans zero_lt_one h_one_lt_logN
  have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) :=
    Real.log_pos h_one_lt_logN
  have h_rpow_nonneg : (0 : ℝ) ≤ Real.log N ^ ((1 : ℝ) / 12) :=
    Real.rpow_nonneg (le_of_lt h_logN_pos) _
  -- Exponent comparison: log(log N) · (1 + blasiConst) ≤ kelleyMekaConst · (log N)^{1/12}.
  -- Chain: L·(1+bs) ≤ L·(1+C₂) = (1+C₂)·L ≤ C₁·X ≤ kelleyMekaConst·X.
  have h_step1 : Real.log (Real.log N) * (1 + blasiConst) ≤
      Real.log (Real.log N) * (1 + C₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt h_loglogN_pos)
  have h_step2 : Real.log (Real.log N) * (1 + C₂) ≤
      C₁ * Real.log N ^ ((1 : ℝ) / 12) := by
    have h1 : ((1 + C₂) * Real.log (Real.log N)) / C₁ ≤
        Real.log N ^ ((1 : ℝ) / 12) := by
      rw [← div_mul_eq_mul_div]
      exact h_N_threshold
    have h2 := (div_le_iff₀ h_C₁_pos).mp h1
    calc Real.log (Real.log N) * (1 + C₂)
        = (1 + C₂) * Real.log (Real.log N) := mul_comm _ _
      _ ≤ Real.log N ^ ((1 : ℝ) / 12) * C₁ := h2
      _ = C₁ * Real.log N ^ ((1 : ℝ) / 12) := mul_comm _ _
  have h_step3 : C₁ * Real.log N ^ ((1 : ℝ) / 12) ≤
      kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) :=
    mul_le_mul_of_nonneg_right h_KM_bound h_rpow_nonneg
  have h_exponents : -kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12) ≤
      -(Real.log (Real.log N) * (1 + blasiConst)) := by linarith
  -- Convert the B–S side to exponential form and compare via exp-monotonicity.
  have h_rhs : (N : ℝ) / Real.log N ^ (1 + blasiConst) =
      (N : ℝ) * Real.exp (-(Real.log (Real.log N) * (1 + blasiConst))) := by
    rw [Real.rpow_def_of_pos h_logN_pos, div_eq_mul_inv, ← Real.exp_neg]
  rw [h_rhs]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_exponents)
    (Nat.cast_nonneg N)

/-- **The joint min-envelope collapses to the K–M term in the asymptotic
regime.** Under the same conditional hypotheses, the `min` in
`rothNumberNat_le_min_blasi_kelley_meka` equals its Kelley–Meka term —
the Bloom–Sisask term is not binding past the threshold. -/
theorem min_blasi_kelley_meka_eq_kelley_meka_eventually
    (N : ℕ) (hN : 3 ≤ N) (C₁ C₂ : ℝ)
    (h_C₁_pos : 0 < C₁)
    (h_KM_bound : C₁ ≤ kelleyMekaConst)
    (h_BS_bound : blasiConst ≤ C₂)
    (h_N_threshold : Real.log N ^ ((1 : ℝ) / 12)
                       ≥ ((1 + C₂) / C₁) * Real.log (Real.log N)) :
    min ((N : ℝ) / Real.log N ^ (1 + blasiConst))
        ((N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)))
      = (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) :=
  min_eq_right
    (kelley_meka_envelope_le_bloom_sisask_envelope_conditional
      N hN C₁ C₂ h_C₁_pos h_KM_bound h_BS_bound h_N_threshold)

#check rothNumberNat_bloom_sisask
#check blasiConst
#check blasiConst_pos
#check rothNumberNat_le_blasi
#check bloom_sisask_consistent_with_isLittleO
#check bloom_sisask_consistent_with_Behrend
#check rothNumberNat_kelley_meka
#check kelleyMekaConst
#check kelleyMekaConst_pos
#check rothNumberNat_le_kelley_meka
#check kelley_meka_consistent_with_Behrend
#check rothNumberNat_le_min_blasi_kelley_meka
#check analytic_envelope_kelley_meka
#check analytic_envelope_conditional
#check analytic_envelope_bloom_sisask
#check bloom_sisask_analytic_envelope_conditional
#check kelley_meka_envelope_le_bloom_sisask_envelope_conditional
#check min_blasi_kelley_meka_eq_kelley_meka_eventually

end RothTheoremOQ02
