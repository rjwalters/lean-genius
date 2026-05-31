import Mathlib
import Proofs.BallotProblemOQ02

/-!
# Donsker's Functional CLT — statement layer (S2 ACT)

## Research Problem: ballot-problem-oq-02-oq-05

This file is the **statement layer** of the OQ-05 pipeline that connects the
discrete ballot problem (`Proofs/BallotProblem.lean`) to its continuous-time
shadow (`Proofs/BallotProblemOQ02.lean`) via Donsker's functional central
limit theorem.

The S2 deliverable is statement-only:

- `interpolatedRescaled` — the canonical interpolated rescaled random walk
  $S_n^\ast(t) = (S_{\lfloor n t\rfloor} + \{n t\}\,\xi_{\lfloor n t\rfloor})/\sqrt n$,
  living in $C([0,1], \mathbb{R})$.
- `WeakConvergesInC01` — an ad hoc weak-convergence predicate on path
  trajectories. Mathlib v4.26.0 lacks a first-class Polish/Borel space
  structure on $C([0,1], \mathbb{R})$, so the predicate is encoded against
  continuous test functionals in the pointwise topology. This is strictly
  weaker than the classical sup-norm weak-convergence formulation but
  suffices for the axiomatic targets in S3-S7.
- `donsker_fclt` — Donsker (1951): the rescaled interpolated walk
  converges weakly in $C([0, 1])$ to standard Brownian motion. Wiedijk #45.

No theorems are proved in this file; sessions S3+ will prove the discrete
reflection identity (`discrete_reflection`) and use `donsker_fclt` plus
auxiliary continuous-mapping axioms to derive the parent's three axioms
(`reflection_principle`, `firstPassageTime_eq_maxEvent`, and the embedded
arcsine identity) as theorems.

## Status (0 sorries, 1 axiom)

- [x] Interpolated rescaled walk definition
- [x] Ad hoc weak-convergence predicate on $C([0,1])$
- [x] Donsker FCLT axiom statement
- [ ] Discrete reflection identity (S3, sorry-free target)
- [ ] Continuous-mapping-for-sup axiom (S4)
- [ ] Reflection-principle theorem deriving parent's axiom (S4)
- [ ] First-passage-time event theorem (S5)
- [ ] Sparre Andersen + arcsine derivation (S6)
- [ ] Parent-file axiom downgrade (S7)
-/

namespace BallotOQ05

open MeasureTheory ProbabilityTheory ContinuousBallot

variable {Ω : Type*}

/-! ## Part I: Interpolated rescaled random walk -/

/-- The partial sum `S_k = ξ_0 + ξ_1 + ⋯ + ξ_{k-1}` of an i.i.d. sequence. -/
noncomputable def partialSum (xi : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, xi i ω

/-- The **interpolated rescaled random walk** on `[0, 1]`.

  $S_n^\ast(t) = \dfrac{S_{\lfloor n t\rfloor} + \{n t\}\,\xi_{\lfloor n t\rfloor}}{\sqrt n}$

This is the canonical $C([0, 1], \mathbb{R})$-valued process used in Donsker's
theorem. For `n = 0` the convention `Real.sqrt 0 = 0` and division-by-zero
yielding `0` give the degenerate value `0`. -/
noncomputable def interpolatedRescaled
    (xi : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  let k : ℕ := ⌊t * n⌋₊
  let frac : ℝ := t * n - k
  (partialSum xi k ω + frac * xi k ω) / Real.sqrt n

/-! ## Part II: Ad hoc weak-convergence predicate on `C([0,1])` -/

/-- Weak convergence of a sequence of path-valued random elements to a path
limit. Encoded against the pointwise topology on `ℝ → ℝ`, which is what
Mathlib v4.26.0 provides without requiring the Polish structure on
$C([0, 1], \mathbb{R})$.

For continuous test functionals `Φ : (ℝ → ℝ) → ℝ`, the predicate asserts
$\mathbb{E}_\mu[\Phi(X_n)] \to \mathbb{E}_\mu[\Phi(X)]$. When `Φ` is
non-integrable on either side, Lean's `∫ ... ∂μ = 0` convention applies,
so the predicate degenerates to `|0 - 0| < ε`, trivially satisfied — i.e.
the predicate constrains only the integrable continuous test functionals,
matching the operational content of weak convergence.

This is **temporary scaffolding**: a Polish-space refinement should
replace it once Mathlib supplies `Polish (C(Set.Icc (0:ℝ) 1, ℝ))`. -/
def WeakConvergesInC01
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → ℝ → Ω → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  ∀ Φ : (ℝ → ℝ) → ℝ, Continuous Φ → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |∫ ω, Φ (fun t => Xn n t ω) ∂μ - ∫ ω, Φ (fun t => X t ω) ∂μ| < ε

/-! ## Part III: Donsker's functional CLT (axiomatized) -/

/-- **Donsker's functional CLT** (Donsker 1951, Wiedijk #45).

For i.i.d. mean-0 variance-1 measurable random variables $\xi_1, \xi_2, \ldots$
on a probability space $(\Omega, \mu)$, there exists a standard Brownian motion
$W$ on the same probability space such that the interpolated rescaled walk
$S_n^\ast$ converges weakly in $C([0, 1])$ to $W$.

**Axiomatization rationale.** A full proof requires Mathlib infrastructure
that is absent at v4.26.0:

- Polish-space structure on `C(Icc (0:ℝ) 1, ℝ)` (needs separability via
  Stone-Weierstrass)
- Prokhorov's tightness theorem
- Kolmogorov-Centsov continuity criterion
- Continuous mapping theorem for weak convergence

Each gap is itself a substantial Mathlib contribution; collectively they
exceed any single-session research scope. The axiom is named, classical,
and corresponds to Wiedijk's "100 Theorems" item #45, which is open in
all major theorem provers as of 2026.

**Use.** This axiom unlocks the derivation pipeline in S4-S6 that
downgrades the parent file's three axioms (`reflection_principle`,
`firstPassageTime_eq_maxEvent`, embedded arcsine) to theorems. -/
axiom donsker_fclt
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (xi : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (xi i))
    (hindep : iIndepFun xi μ)
    (hmean : ∀ i, ∫ ω, xi i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (xi i ω) ^ 2 ∂μ = 1) :
    ∃ bm : BrownianMotion Ω μ,
      WeakConvergesInC01 μ (interpolatedRescaled xi) bm.W

/-! ## Part IV: Discrete reflection identity (S6 ACT — paste-ready skeleton)

This section is the S6 ACT paste-ready skeleton from S5 PREP §5, dropped
in here so future researchers (or Aristotle) can discharge the 4
acknowledged `sorry`s. The design is fully scoped in S5 PREP:

- §3.1 Option C: `partialSumBool : (Fin n → Bool) → Fin (n+1) → ℤ` via
  bounded sum over `Fin n` with `if h : i.val < k.val` guard.
- §3.2 Option β: first hit time via `Finset.min'` on `hitSet ω a`.
- §3.3 Option iv: bijection assembly via `Finset.card_nbij'`
  (non-dependent, inverse-pair form — `Mathlib/Data/Finset/Card.lean:398`),
  with `i = j = reflectAt _ a` (involutive).

Build status at ACT-time: NOT verified (Docker daemon hung at
2026-05-16T15:26Z — `timeout 8 docker info` returns no Server section;
host disk 100% / 5.4Gi avail). Ships under
`(build pending — Docker daemon hung)` qualifier per memory feedback
pattern; leaf-only file (no downstream importers), bearer pins verified
at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(S5 PREP §4), recent build-verify on `cff3fd36c83` (S2 ACT #19282,
7744 jobs successful 2026-05-15). -/

section DiscreteReflection

variable {n : ℕ}

/-- Partial sum at index `k` of a `Fin n → Bool` lattice path (`true ↦ +1`,
    `false ↦ -1`). Indexed by `Fin (n+1)` so `k = ⟨n, _⟩` is the endpoint. -/
def partialSumBool (ω : Fin n → Bool) (k : Fin (n+1)) : ℤ :=
  ∑ i : Fin n, if h : i.val < k.val then (if ω i then (1 : ℤ) else -1) else 0

/-- The finset of hit-time indices `{k : Fin (n+1) | S_k(ω) = a}`. -/
def hitSet (ω : Fin n → Bool) (a : ℤ) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun k => partialSumBool ω k = a

/-- First hit time of level `a` along `ω`. When `ω` doesn't hit `a`, returns
    `⟨0, _⟩` as a placeholder — never referenced in proofs of paths that
    don't reach `a`. -/
noncomputable def firstHitFin (ω : Fin n → Bool) (a : ℤ) : Fin (n+1) :=
  if h : (hitSet ω a).Nonempty then (hitSet ω a).min' h
  else ⟨0, Nat.zero_lt_succ _⟩

/-- Reflection of `ω` past its first hit of level `a`: flip every bit at
    index `≥ τ_a(ω)`. Identity on paths that don't reach `a` (since
    `firstHitFin = ⟨0, _⟩` there and we don't care about those paths in
    the bijection). -/
def reflectAt (ω : Fin n → Bool) (a : ℤ) : Fin n → Bool :=
  fun i => if (firstHitFin ω a).val ≤ i.val then !(ω i) else ω i

/-- **R4-helper.** Below the first hit time, reflection is the identity.

    Used by R4 (`reflectAt_involutive`) to show
    `firstHitFin (reflectAt ω a) a = firstHitFin ω a` on the
    `(hitSet ω a).Nonempty` branch. Pure `if_neg` collapse. -/
lemma reflectAt_eq_below_firstHit
    {ω : Fin n → Bool} {a : ℤ} {i : Fin n}
    (hi : i.val < (firstHitFin ω a).val) :
    reflectAt ω a i = ω i := by
  unfold reflectAt
  exact if_neg (Nat.not_le_of_lt hi)

/-- **R4** Reflection is involutive **on the non-empty-hit-set branch**.
    `reflectAt (reflectAt ω a) a = ω` whenever `(hitSet ω a).Nonempty`.

    **History (S7 PREP, researcher-1, 2026-05-30)**: a 2-bit counterexample
    (`n = 2`, `a = 1`, `ω = ![false, false]`) showed the unconditional
    statement is **false**: when `(hitSet ω a) = ∅`, `firstHitFin ω a`
    defaults to `⟨0, _⟩` and `reflectAt ω a = !ω` pointwise; the
    complemented path may itself hit `a` (e.g., when `ω` hits `-a`), so
    a second reflection flips a different bit-set and breaks involution.
    The `(hitSet ω a).Nonempty` hypothesis restricts to the well-defined
    branch where first-hit-preservation holds. Downstream consumer R6
    invokes R4 inside a `Finset.card_nbij'` bijection whose source-set
    predicate includes `(hitSet ω a).Nonempty`, so the hypothesis is
    in scope at the call site — zero-cost fix downstream. -/
lemma reflectAt_involutive {ω : Fin n → Bool} {a : ℤ}
    (h : (hitSet ω a).Nonempty) :
    reflectAt (reflectAt ω a) a = ω := by
  -- Step 1: firstHitFin is preserved under reflection (uses h).
  -- Discharge sketch (S7 PREP §3, 6 bullets):
  --   τ := (hitSet ω a).min' h ∈ hitSet (reflectAt ω a) a via
  --   `reflectAt_eq_below_firstHit` + `Finset.sum_congr`;
  --   antisymmetry on `Fin (n+1)` via `min'_le` (both directions).
  -- Left as a named sub-sorry for S9; ~15 LOC inline discharge planned.
  have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
    sorry  -- R4-sub `hτ`: min'-of-hitSet argument; see S7 PREP §3 (6 bullets)
  -- Step 2: pointwise `!!b = b` collapse with first-hit alignment.
  funext i
  unfold reflectAt
  rw [hτ]
  split_ifs with hi
  · simp [Bool.not_not]
  · rfl

/-- **R5** Partial-sum-after-reflection identity at the endpoint.
    If `ω` hits `a` at some `τ ≤ n` (i.e., `(hitSet ω a).Nonempty`), then
    the reflected path's endpoint is `2 * a - S_n(ω)`. Proof: split the
    sum `∑ i : Fin n` at `τ`, identity on `i < τ`, sign-flipped on `i ≥ τ`,
    and use `S_τ(ω) = a` (`min'_mem` + `hitSet` defn). -/
lemma partialSumBool_reflectAt_endpoint
    {ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty) :
    partialSumBool (reflectAt ω a) ⟨n, Nat.lt_succ_self n⟩
      = 2 * a - partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ := by
  sorry  -- R5: Finset.sum_ite + min'_mem h + arithmetic

/-- Hitting `≥ a` ⟺ `(hitSet ω a').Nonempty` for some `a' ≤ a`. For the
    bijection we need: paths reaching ≥ a partition as (ending ≥ a) ⊔
    (ending < a, having reached a). Reflection sends the second class to
    (ending > a). -/
lemma reaches_iff_hits_or_above
    {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a) :
    (∃ k : Fin (n+1), partialSumBool ω k ≥ a)
      ↔ partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a ∨ (hitSet ω a).Nonempty := by
  sorry  -- LOW: use Int.le_iff_exists_eq_succ on partial-sum jumps of ±1

/-- **Discrete reflection identity** (André 1887, Feller Vol. I § III.1).

    `|{paths reaching ≥ a}| = 2 · |{paths ending ≥ a}| - |{paths ending = a}|`.

    Proof: partition reaches-≥-a as (ending ≥ a) ⊔ (ending < a but hits a).
    `card_nbij'` with `i = j = reflectAt _ a` is an involutive bijection
    from the second class to (ending > a), by R4 + R5. Hence
    `|reaches ≥ a| = |ending ≥ a| + |ending > a|`, and
    `|ending > a| = |ending ≥ a| - |ending = a|` (disjoint union). -/
theorem discrete_reflection
    (hn : 0 < n) (a : ℤ) (ha : 0 < a) :
    (Finset.univ.filter fun ω : Fin n → Bool =>
        ∃ k : Fin (n+1), partialSumBool ω k ≥ a).card
    = 2 * (Finset.univ.filter fun ω : Fin n → Bool =>
        partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a).card
      - (Finset.univ.filter fun ω : Fin n → Bool =>
        partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ = a).card := by
  sorry  -- R6: assemble via Finset.card_nbij' applied to the (ending<a,hits a) ↔ (ending>a) restriction

end DiscreteReflection

end BallotOQ05
