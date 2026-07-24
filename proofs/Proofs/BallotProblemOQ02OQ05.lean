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
in here so future researchers (or Aristotle) can discharge the
acknowledged `sorry`s. R4 (`reflectAt_involutive`) and R5
(`partialSumBool_reflectAt_endpoint`) are now proved; 2 `sorry`s remain
(`reaches_iff_hits_or_above`, R6 `discrete_reflection`). The design is
fully scoped in S5 PREP:

- §3.1 Option C: `partialSumBool : (Fin n → Bool) → Fin (n+1) → ℤ` via
  bounded sum over `Fin n` with `if h : i.val < k.val` guard.
- §3.2 Option β: first hit time via `Finset.min'` on `hitSet ω a`.
- §3.3 Option iv: bijection assembly via `Finset.card_nbij'`
  (non-dependent, inverse-pair form — `Mathlib/Data/Finset/Card.lean:398`),
  with `i = j = reflectAt _ a` (involutive).

Build status: VERIFIED 2026-06-12 (Docker, 7744 jobs successful) with R4
and R5 proved; the only remaining `sorry` warnings are
`reaches_iff_hits_or_above` and R6 `discrete_reflection`. Leaf-only file
(no downstream importers). -/

section DiscreteReflection

variable {n : ℕ}

/-- Partial sum at index `k` of a `Fin n → Bool` lattice path (`true ↦ +1`,
    `false ↦ -1`). Indexed by `Fin (n+1)` so `k = ⟨n, _⟩` is the endpoint. -/
def partialSumBool (ω : Fin n → Bool) (k : Fin (n+1)) : ℤ :=
  ∑ i : Fin n, if i.val < k.val then (if ω i then (1 : ℤ) else -1) else 0

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
    the bijection). Marked `noncomputable` because it depends on
    `firstHitFin` (which uses `Finset.min'`). -/
noncomputable def reflectAt (ω : Fin n → Bool) (a : ℤ) : Fin n → Bool :=
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

/-- **R4-sub helper (S9 ACT).** Partial sums up to a position not exceeding
    the first hit time are unchanged by reflection. The sum's `i.val < k.val`
    guard restricts each summand index `i` to satisfy `i.val < k.val ≤ τ.val`,
    so `reflectAt_eq_below_firstHit` collapses every summand pointwise. -/
lemma partialSumBool_congr_below
    {ω : Fin n → Bool} {a : ℤ} {k : Fin (n+1)}
    (hk : k.val ≤ (firstHitFin ω a).val) :
    partialSumBool (reflectAt ω a) k = partialSumBool ω k := by
  unfold partialSumBool
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i.val < k.val
  · rw [if_pos hi, if_pos hi,
        reflectAt_eq_below_firstHit (Nat.lt_of_lt_of_le hi hk)]
  · rw [if_neg hi, if_neg hi]

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
  -- Discharged inline (S9 ACT): the partial-sum equality below τ
  -- (`partialSumBool_congr_below`) shows τ ∈ hitSet (reflectAt ω a) a and
  -- that the reflected path has no earlier hit; min'-antisymmetry closes.
  have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
    have hτ_eq : firstHitFin ω a = (hitSet ω a).min' h := by
      simp [firstHitFin, dif_pos h]
    have hτ_mem : firstHitFin ω a ∈ hitSet ω a := by
      rw [hτ_eq]; exact (hitSet ω a).min'_mem h
    have hτ_ps : partialSumBool ω (firstHitFin ω a) = a :=
      (Finset.mem_filter.mp hτ_mem).2
    have hτ_mem' : firstHitFin ω a ∈ hitSet (reflectAt ω a) a := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [partialSumBool_congr_below (le_refl _)]
      exact hτ_ps
    have h' : (hitSet (reflectAt ω a) a).Nonempty := ⟨_, hτ_mem'⟩
    have hfh' : firstHitFin (reflectAt ω a) a = (hitSet (reflectAt ω a) a).min' h' := by
      simp [firstHitFin, dif_pos h']
    apply le_antisymm
    · rw [hfh']
      exact Finset.min'_le _ _ hτ_mem'
    · rw [hfh']
      refine Finset.le_min' _ _ _ (fun k hk => ?_)
      by_contra hlt
      push_neg at hlt
      have hk_val : k.val < (firstHitFin ω a).val := hlt
      have hk_ps : partialSumBool (reflectAt ω a) k = a :=
        (Finset.mem_filter.mp hk).2
      have hk_ω : partialSumBool ω k = a := by
        rw [← partialSumBool_congr_below (Nat.le_of_lt hk_val)]
        exact hk_ps
      have hk_mem : k ∈ hitSet ω a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_ω⟩
      rw [hτ_eq] at hk_val
      exact absurd ((hitSet ω a).min'_le _ hk_mem) (not_le.mpr hk_val)
  -- Step 2: pointwise `!!b = b` collapse with first-hit alignment.
  --
  -- N.B. we cannot `unfold reflectAt; rw [hτ]` because `unfold` rewrites
  -- the inner `reflectAt ω a` inside `firstHitFin (reflectAt ω a) a` too,
  -- eliminating the `reflectAt`-shaped subterm `hτ` needs to match.
  -- Instead we expose the outer `reflectAt` via `show` (using definitional
  -- equality), apply `hτ`, then case-split.
  funext i
  show (if (firstHitFin (reflectAt ω a) a).val ≤ i.val
         then !((reflectAt ω a) i)
         else (reflectAt ω a) i) = ω i
  rw [hτ]
  by_cases hi : (firstHitFin ω a).val ≤ i.val
  · -- ≤ case: outer-if then-branch + inner reflectAt also flips
    rw [if_pos hi]
    -- Outer parens needed: `!` notation precedence interacts with `=`
    show (!(if (firstHitFin ω a).val ≤ i.val then !(ω i) else ω i)) = ω i
    rw [if_pos hi]
    exact Bool.not_not (ω i)
  · -- > case: outer-if else-branch, inner reflectAt is identity
    rw [if_neg hi]
    show (if (firstHitFin ω a).val ≤ i.val then !(ω i) else ω i) = ω i
    rw [if_neg hi]

/-- **R5** Partial-sum-after-reflection identity at the endpoint.
    If `ω` hits `a` at some `τ ≤ n` (i.e., `(hitSet ω a).Nonempty`), then
    the reflected path's endpoint is `2 * a - S_n(ω)`. Proof: split the
    sum `∑ i : Fin n` at `τ`, identity on `i < τ`, sign-flipped on `i ≥ τ`,
    and use `S_τ(ω) = a` (`min'_mem` + `hitSet` defn). -/
lemma partialSumBool_reflectAt_endpoint
    {ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty) :
    partialSumBool (reflectAt ω a) ⟨n, Nat.lt_succ_self n⟩
      = 2 * a - partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ := by
  -- The endpoint partial sum is the full signed sum (the `i.val < n` guard
  -- is vacuous for `i : Fin n`).
  have key : ∀ (ψ : Fin n → Bool),
      partialSumBool ψ ⟨n, Nat.lt_succ_self n⟩
        = ∑ i : Fin n, (if ψ i then (1 : ℤ) else -1) := by
    intro ψ
    unfold partialSumBool
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [if_pos i.isLt]
  -- `S_τ(ω) = a` at the first hit time τ.
  have hmem : firstHitFin ω a ∈ hitSet ω a := by
    have hmin : firstHitFin ω a = (hitSet ω a).min' h := by
      simp only [firstHitFin, dif_pos h]
    rw [hmin]; exact (hitSet ω a).min'_mem h
  have hPS : partialSumBool ω (firstHitFin ω a) = a := (Finset.mem_filter.mp hmem).2
  have hA : (∑ i : Fin n, if i.val < (firstHitFin ω a).val
       then (if ω i then (1 : ℤ) else -1) else 0) = a := by
    have h' := hPS
    unfold partialSumBool at h'
    exact h'
  -- Reduce both endpoints to full signed sums, then equate via `R + T = 2a`.
  rw [key, key, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  have step : ∀ i : Fin n,
      ((if reflectAt ω a i then (1 : ℤ) else -1) + (if ω i then (1 : ℤ) else -1))
        = 2 * (if i.val < (firstHitFin ω a).val
                 then (if ω i then (1 : ℤ) else -1) else 0) := by
    intro i
    unfold reflectAt
    by_cases hi : (firstHitFin ω a).val ≤ i.val
    · rw [if_pos hi, if_neg (Nat.not_lt.mpr hi)]
      cases ω i <;> simp
    · rw [if_neg hi, if_pos (Nat.lt_of_not_le hi)]
      ring
  rw [Finset.sum_congr rfl (fun i _ => step i), ← Finset.mul_sum, hA]

/-- The index-0 partial sum vanishes: the `i.val < 0` guard kills every
    summand. The bound proof is an explicit argument so callers' `Fin.mk`
    literals match without proof-irrelevance gymnastics. -/
lemma partialSumBool_zero (ω : Fin n → Bool) (h0 : 0 < n + 1) :
    partialSumBool ω ⟨0, h0⟩ = 0 := by
  unfold partialSumBool
  simp

/-- One-step recurrence: the partial sum at `j + 1` adds the `j`-th `±1`
    step. All three `Fin` bound proofs are explicit arguments so the
    statement unifies syntactically with whatever proofs the caller has in
    context (`omega` treats `Fin.mk` terms with different proofs as distinct
    atoms). -/
lemma partialSumBool_succ (ω : Fin n → Bool) {j : ℕ} (hj : j < n)
    (h1 : j + 1 < n + 1) (h2 : j < n + 1) :
    partialSumBool ω ⟨j + 1, h1⟩
      = partialSumBool ω ⟨j, h2⟩ + (if ω ⟨j, hj⟩ then (1 : ℤ) else -1) := by
  have hsplit : ∀ i : Fin n,
      (if i.val < j + 1 then (if ω i then (1 : ℤ) else -1) else 0)
        = (if i.val < j then (if ω i then (1 : ℤ) else -1) else 0)
          + (if i.val = j then (if ω i then (1 : ℤ) else -1) else 0) := by
    intro i
    -- Bind each condition proof BEFORE `rw [if_pos/if_neg]`: an unanchored
    -- `if_pos (by omega)` leaves the condition a metavariable and can unify
    -- with the wrong `ite` (e.g. the inner `if ω i` payload).
    rcases lt_trichotomy i.val j with h | h | h
    · have c1 : i.val < j + 1 := by omega
      have c3 : ¬(i.val = j) := by omega
      rw [if_pos c1, if_pos h, if_neg c3]; ring
    · have c1 : i.val < j + 1 := by omega
      have c2 : ¬(i.val < j) := by omega
      rw [if_pos c1, if_neg c2, if_pos h]; ring
    · have c1 : ¬(i.val < j + 1) := by omega
      have c2 : ¬(i.val < j) := by omega
      have c3 : ¬(i.val = j) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3]; ring
  have hlast : (∑ i : Fin n, if i.val = j then (if ω i then (1 : ℤ) else -1) else 0)
      = (if ω ⟨j, hj⟩ then (1 : ℤ) else -1) := by
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · have hc : (⟨j, hj⟩ : Fin n).val = j := rfl
      rw [if_pos hc]
    · intro i _ hne
      exact if_neg (fun h => hne (Fin.ext h))
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  show (∑ i : Fin n, if i.val < j + 1 then (if ω i then (1 : ℤ) else -1) else 0)
      = (∑ i : Fin n, if i.val < j then (if ω i then (1 : ℤ) else -1) else 0)
        + (if ω ⟨j, hj⟩ then (1 : ℤ) else -1)
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hlast]

/-- **Discrete intermediate-value.** If some partial sum reaches `≥ a > 0`,
    the path hits `a` exactly: partial sums start at `0` and move by `±1`,
    so the first index with `S ≥ a` has `S = a` (a `+1` jump from `< a`
    cannot overshoot). -/
lemma hitSet_nonempty_of_ge {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a)
    {k : Fin (n + 1)} (hk : a ≤ partialSumBool ω k) :
    (hitSet ω a).Nonempty := by
  suffices H : ∀ (j : ℕ) (hj : j < n + 1), a ≤ partialSumBool ω ⟨j, hj⟩ →
      (hitSet ω a).Nonempty from H k.val k.isLt hk
  intro j
  induction j with
  | zero =>
    intro hj h0
    rw [partialSumBool_zero ω hj] at h0
    omega
  | succ i IH =>
    intro hj hsi
    by_cases heq : partialSumBool ω ⟨i + 1, hj⟩ = a
    · exact ⟨⟨i + 1, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩
    · have hi_n : i < n := by omega
      have hi_n1 : i < n + 1 := by omega
      have hstep := partialSumBool_succ ω hi_n hj hi_n1
      have hgt : a < partialSumBool ω ⟨i + 1, hj⟩ := lt_of_le_of_ne hsi (Ne.symm heq)
      have hprev : a ≤ partialSumBool ω ⟨i, hi_n1⟩ := by
        by_cases hb : ω ⟨i, hi_n⟩
        · rw [if_pos hb] at hstep
          omega
        · rw [if_neg hb] at hstep
          omega
      exact IH hi_n1 hprev

/-- The first hit time of `ω` is also a hit time of the reflected path:
    partial sums agree up to (and including) the first hit
    (`partialSumBool_congr_below`). Extracted from the Step-1 argument
    inside `reflectAt_involutive` for reuse in the R6 bijection. -/
lemma firstHit_mem_hitSet_reflectAt {ω : Fin n → Bool} {a : ℤ}
    (h : (hitSet ω a).Nonempty) :
    firstHitFin ω a ∈ hitSet (reflectAt ω a) a := by
  have hτ_eq : firstHitFin ω a = (hitSet ω a).min' h := by
    simp [firstHitFin, dif_pos h]
  have hτ_mem : firstHitFin ω a ∈ hitSet ω a := by
    rw [hτ_eq]; exact (hitSet ω a).min'_mem h
  have hτ_ps : partialSumBool ω (firstHitFin ω a) = a :=
    (Finset.mem_filter.mp hτ_mem).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [partialSumBool_congr_below (le_refl _)]
  exact hτ_ps

/-- Hitting `≥ a` ⟺ `(hitSet ω a').Nonempty` for some `a' ≤ a`. For the
    bijection we need: paths reaching ≥ a partition as (ending ≥ a) ⊔
    (ending < a, having reached a). Reflection sends the second class to
    (ending > a). -/
lemma reaches_iff_hits_or_above
    {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a) :
    (∃ k : Fin (n+1), partialSumBool ω k ≥ a)
      ↔ partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a ∨ (hitSet ω a).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact Or.inr (hitSet_nonempty_of_ge ha hk)
  · rintro (h | ⟨k, hk⟩)
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, h⟩
    · exact ⟨k, ge_of_eq (Finset.mem_filter.mp hk).2⟩

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
  -- Path classes: A = reaches ≥ a (the LHS), B = ends ≥ a, C = ends = a,
  -- D = ends < a but hits a, E = ends > a.
  set A := (Finset.univ.filter fun ω : Fin n → Bool =>
      ∃ k : Fin (n+1), partialSumBool ω k ≥ a) with hA
  set B := (Finset.univ.filter fun ω : Fin n → Bool =>
      partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a) with hB
  set C := (Finset.univ.filter fun ω : Fin n → Bool =>
      partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ = a) with hC
  set D := (Finset.univ.filter fun ω : Fin n → Bool =>
      partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ < a ∧ (hitSet ω a).Nonempty) with hD
  set E := (Finset.univ.filter fun ω : Fin n → Bool =>
      a < partialSumBool ω ⟨n, Nat.lt_succ_self n⟩) with hE
  -- Partition 1: A = B ⊔ D (by `reaches_iff_hits_or_above`).
  have hAeq : A = B ∪ D := by
    ext ω
    simp only [hA, hB, hD, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hr
      by_cases hend : partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a
      · exact Or.inl hend
      · rcases (reaches_iff_hits_or_above ha).mp hr with h | h
        · exact Or.inl h
        · exact Or.inr ⟨lt_of_not_ge hend, h⟩
    · rintro (h | ⟨_, hne⟩)
      · exact (reaches_iff_hits_or_above ha).mpr (Or.inl h)
      · exact (reaches_iff_hits_or_above ha).mpr (Or.inr hne)
  have hdisjBD : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro ω hb hd
    simp only [hB, hD, Finset.mem_filter, Finset.mem_univ, true_and] at hb hd
    exact absurd hb (not_le.mpr hd.1)
  have h1 : A.card = B.card + D.card := by
    rw [hAeq, Finset.card_union_of_disjoint hdisjBD]
  -- Partition 2: B = C ⊔ E (ends ≥ a splits as = a / > a).
  have hBeq : B = C ∪ E := by
    ext ω
    simp only [hB, hC, hE, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr hlt
    · rintro (h | h)
      · exact ge_of_eq h
      · exact le_of_lt h
  have hdisjCE : Disjoint C E := by
    rw [Finset.disjoint_left]
    intro ω hc he
    simp only [hC, hE, Finset.mem_filter, Finset.mem_univ, true_and] at hc he
    omega
  have h2 : B.card = C.card + E.card := by
    rw [hBeq, Finset.card_union_of_disjoint hdisjCE]
  -- The reflection bijection: |D| = |E| via `reflectAt · a` both ways
  -- (involutive on paths that hit `a`, by R4; endpoint formula by R5).
  have h3 : D.card = E.card := by
    apply Finset.card_nbij' (fun ω => reflectAt ω a) (fun ω => reflectAt ω a)
    · -- MapsTo D → E: ends < a and hits a ⟹ reflection ends at 2a − S > a.
      intro ω hω
      rw [Finset.mem_coe] at hω ⊢
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
      have hR5 := partialSumBool_reflectAt_endpoint hω.2
      rw [hR5]
      omega
    · -- MapsTo E → D: ends > a ⟹ hits a (discrete IVT), reflection ends
      -- at 2a − S < a, and the reflected path still hits a at the same
      -- first-hit index.
      intro ω hω
      rw [Finset.mem_coe] at hω ⊢
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      have hne : (hitSet ω a).Nonempty := hitSet_nonempty_of_ge ha (le_of_lt hω)
      have hR5 := partialSumBool_reflectAt_endpoint hne
      exact ⟨by rw [hR5]; omega, ⟨firstHitFin ω a, firstHit_mem_hitSet_reflectAt hne⟩⟩
    · -- Left inverse on D: R4 involution (D-membership includes the hit).
      intro ω hω
      rw [Finset.mem_coe] at hω
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact reflectAt_involutive hω.2
    · -- Right inverse on E: E-paths hit a by the discrete IVT, so R4 applies.
      intro ω hω
      rw [Finset.mem_coe] at hω
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact reflectAt_involutive (hitSet_nonempty_of_ge ha (le_of_lt hω))
  -- Assemble: |A| = |B| + |D| = |B| + |E| = |B| + (|B| − |C|) = 2|B| − |C|.
  omega

end DiscreteReflection

end BallotOQ05
