/-
  Moser–Tardos Algorithm and Termination Theorem for the Lovász Local Lemma
  =========================================================================

  This file is the OQ-01-A/A.3 scaffold for `prob-method-lovasz-local-oq-01`:
  it defines the variable-version Moser–Tardos resampling algorithm and ships
  the two main theorems as *weakened placeholder* statements (algebraic-shell
  inequalities, fully proved — the file currently has 0 `sorry`, 0 `axiom`).
  The full convergence / expectation statements are deferred to OQ-01-B
  (witness-tree construction) and OQ-01-C (Galton–Watson / generating-function
  sum).

  Roadmap:
  * Part I  : Setup (`MTProblem`, `State`, `isViolated`, `pickBad`).
  * Part II : Algorithm (`resampleVbl`, `step`, `run`).
  * Part III: LLL admissibility predicate (`LLLAdmissible`).
  * Part IV : Placeholder main theorems
              (`mt_expected_step_bound`, `mt_terminates_as`).
  * Part V  : Refined uniform-draw layer (`uniformDrawProb`, `collisionAdj`,
              `LLLAdmissibleUniform`, `LLLAdmissibleUniform.toLLLAdmissible`).
  * Part VI : Witness trees (`inductive WitnessTree`, `labelOf`, `inclNbhd`,
              `isProper` + sanity lemmas) — OQ-01-B skeleton (S13 design,
              landed S16).

  Deferred (future PRs):
  * `theorem witness_valid`, `theorem witness_prob_bd`  — OQ-01-B
  * `def gwTreeProb`, `theorem gw_sum_bound`            — OQ-01-C
  * Replace the Part IV placeholders with the full statements — OQ-01-C

  References:
  * Moser & Tardos (2010) — *A constructive proof of the general Lovász
    Local Lemma*, J. ACM 57(2). Canonical witness-tree proof.
  * Spencer (2011) — *Asymptopia* §4, expository account.
  * Alon & Spencer — *The Probabilistic Method* (3rd ed.) §5.7.

  The parent file `Proofs/LovaszLocalLemma.lean` carries the algebraic
  core of the symmetric and general LLL together with the non-negativity
  shell `moser_tardos_termination`. This file adds the *algorithmic* layer
  (and its termination bound) on top.
-/
import Mathlib

namespace ProbMethod.MoserTardos

open scoped Classical

/-! ## Part I — Setup -/

/-- The variable-version Moser–Tardos setup.

    A **problem instance** carries:
    * a finite collection of independent variables `V₁, …, V_{numVars}`,
      each ranging over its own finite nonempty alphabet `alphabet j`;
    * a finite collection of "bad events" `A₁, …, A_{numEvents}`, each
      depending on a fixed subset `vbl i ⊆ Fin numVars` of variables;
    * a faithful-on-vbl predicate `isBad i v` deciding whether event `i`
      is violated at assignment `v`.

    The faithfulness clause `vblFaithful` ensures the bad-event predicate
    only inspects the variables in `vbl i`, which is exactly the structural
    invariant the Moser–Tardos resampling argument requires (resampling
    variables outside `vbl i` leaves `isBad i` unchanged). -/
structure MTProblem where
  /-- Number of independent variables `V₁, …, V_{numVars}`. -/
  numVars : ℕ
  /-- Number of bad events `A₁, …, A_{numEvents}`. -/
  numEvents : ℕ
  /-- Alphabet for each variable. -/
  alphabet : Fin numVars → Type
  /-- Each alphabet is a `Fintype` (finite cardinality, required for
      uniform sampling). -/
  alphabetFintype : ∀ j, Fintype (alphabet j)
  /-- Each alphabet is `Nonempty` (so the uniform distribution exists). -/
  alphabetNonempty : ∀ j, Nonempty (alphabet j)
  /-- The variables on which event `i` depends (its variable-set
      `vbl(Aᵢ)`). -/
  vbl : Fin numEvents → Finset (Fin numVars)
  /-- The bad-event predicate at a given full assignment. -/
  isBad : Fin numEvents → ((j : Fin numVars) → alphabet j) → Prop
  /-- Decidability of `isBad`, needed to deterministically pick a bad
      event to resample. -/
  isBadDec : ∀ i v, Decidable (isBad i v)
  /-- Faithfulness: `isBad i v` depends only on `v` at the variables in
      `vbl i`. This is the structural property that the Moser–Tardos
      analysis (variable-collision dependency graph) requires. -/
  vblFaithful : ∀ i (v w : (j : Fin numVars) → alphabet j),
    (∀ j ∈ vbl i, v j = w j) → (isBad i v ↔ isBad i w)

namespace MTProblem

variable (P : MTProblem)

-- Register the field-encoded typeclasses as local instances for the rest
-- of this namespace, so we can write `Fintype (P.alphabet j)` etc.
attribute [instance] alphabetFintype alphabetNonempty isBadDec

/-- A complete assignment to all `numVars` variables. -/
abbrev State : Type := (j : Fin P.numVars) → P.alphabet j

instance : Fintype P.State := inferInstance

instance : Nonempty P.State :=
  ⟨fun j => Classical.choice (P.alphabetNonempty j)⟩

/-- A state `v` is **violated** iff at least one bad event fires at `v`. -/
def isViolated (v : P.State) : Prop := ∃ i, P.isBad i v

instance (v : P.State) : Decidable (P.isViolated v) := by
  unfold isViolated
  exact Fintype.decidableExistsFintype

/-- Deterministic rule for selecting which bad event to resample first:
    pick the index `i : Fin numEvents` minimising the underlying `ℕ`
    among indices with `isBad i v`. Returns `none` when no bad event
    is violated.

    Any deterministic selection rule is admissible for Moser–Tardos; this
    choice ("least index") is the simplest and matches the textbook
    presentation. -/
noncomputable def pickBad (v : P.State) : Option (Fin P.numEvents) :=
  let s : Finset (Fin P.numEvents) :=
    (Finset.univ : Finset (Fin P.numEvents)).filter (fun i => P.isBad i v)
  if h : s.Nonempty then some (s.min' h) else none

/-! ## Part II — Algorithm -/

/-- One resampling step on the variables in a given set `S ⊆ Fin numVars`:
    starting from state `v`, return a probability distribution where the
    variables `j ∈ S` are independently re-drawn uniformly from
    `alphabet j`, and the variables `j ∉ S` keep their value `v j`.

    **OQ-01-A.2 implementation** (S3 ACT, this iteration). Construction
    via Approach B from the S3 ANALYSIS doc (PR #18268, §2.2):
    sample the dependent product `∀ j : ↥S, alphabet j.val` uniformly
    (this is a finite nonempty `Fintype` by `Pi.instFintype`), then
    glue the sample with the deterministic part `v j` for `j ∉ S` via
    a single `PMF.map`. The resulting `PMF` is the desired product of
    independent uniforms for `j ∈ S` together with point masses for
    `j ∉ S` — a faithful encoding of "resample the variables in S,
    keep everything else fixed". -/
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map
    (fun (a : ∀ j : S, P.alphabet j.val) (j : Fin P.numVars) =>
      if h : j ∈ S then a ⟨j, h⟩ else v j)

/-- **Marginal outside `S`** — if `j ∉ S`, then the `j`-th coordinate
    marginal of `resampleAt S v` is the Dirac mass at `v j`. The
    resampled draw only modifies coordinates in `S`; coordinates
    outside `S` deterministically retain their value from `v`.

    Verbatim discharge per S4b PREP §5 (PR #18580): unfold the
    `PMF.map` composition, observe that the glue function is
    constant in `a` (since `dif_neg hj` reduces every if-then-else
    to the `v b` branch), and apply `PMF.map_const`. -/
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j) := by
  classical
  unfold resampleAt
  rw [PMF.map_comp]
  have h_const :
      ((fun w : P.State => w j) ∘
        (fun (a : ∀ k : S, P.alphabet k.val) (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b))
      = Function.const _ (v j) := by
    funext a
    simp [Function.comp, dif_neg hj]
  rw [h_const, PMF.map_const]

/-- **Marginal of `PMF.uniformOfFintype` on a dependent product** — the
    marginal of the uniform distribution on `∀ k, β k` at coordinate `i`
    is the uniform distribution on `β i`.

    This is the key reusable lemma for the marginal/independence facts on
    `resampleAt`. The proof unfolds the uniform PMF, applies a bijection
    via `Equiv.piSplitAt` to compute the fiber cardinality, and finishes
    with an `ℝ≥0∞` cancellation built on
    `Fintype.prod_eq_mul_prod_subtype_ne`. See S5c PREP (PR #18930)
    for the bearer audit at lake-pinned Mathlib v4.26.0. -/
private lemma marginal_uniformOfFintype_pi
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : α → Type*} [∀ a, Fintype (β a)] [∀ a, Nonempty (β a)] (i : α) :
    (PMF.uniformOfFintype (∀ k, β k)).map (fun f => f i) =
      PMF.uniformOfFintype (β i) := by
  classical
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h_fiber :
      (Finset.univ.filter (fun f : (∀ k, β k) => b = f i)).card =
        Fintype.card (∀ k : {k // k ≠ i}, β k.val) := by
    rw [← Fintype.card_subtype (fun f : (∀ k, β k) => b = f i)]
    apply Fintype.card_congr
    refine
      { toFun := fun f => (Equiv.piSplitAt i β f.val).2
        invFun := fun g => ⟨(Equiv.piSplitAt i β).symm ⟨b, g⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- subtype proof: b = ((piSplitAt i β).symm ⟨b, g⟩) i
      simp [Equiv.piSplitAt]
    · -- left_inv: (piSplitAt.symm ⟨b, (piSplitAt f).2⟩, _) = ⟨f, hf⟩
      rintro ⟨f, hf⟩
      apply Subtype.ext
      show (Equiv.piSplitAt i β).symm ⟨b, (Equiv.piSplitAt i β f).2⟩ = f
      have hfi : (Equiv.piSplitAt i β f).1 = f i := rfl
      rw [hf, ← hfi, Prod.mk.eta]
      exact (Equiv.piSplitAt i β).left_inv f
    · -- right_inv: (piSplitAt (piSplitAt.symm ⟨b, g⟩)).2 = g
      intro g
      have h := (Equiv.piSplitAt i β).right_inv ⟨b, g⟩
      exact congrArg Prod.snd h
  rw [h_fiber]
  push_cast [Fintype.card_pi]
  have hprod := Fintype.prod_eq_mul_prod_subtype_ne
      (fun k : α => ((Fintype.card (β k) : ℕ) : ENNReal)) i
  rw [hprod]
  have h_pi_ne_zero :
      (∏ k : {k // k ≠ i}, ((Fintype.card (β k.1) : ℕ) : ENNReal)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact_mod_cast (Fintype.card_pos (α := β k.1)).ne'
  have h_pi_ne_top :
      (∏ k : {k // k ≠ i}, ((Fintype.card (β k.1) : ℕ) : ENNReal)) ≠ ⊤ :=
    WithTop.prod_ne_top (fun _ _ => ENNReal.natCast_ne_top _)
  have h_card_i_ne_zero : ((Fintype.card (β i) : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := β i)).ne'
  have h_card_i_ne_top : ((Fintype.card (β i) : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl h_card_i_ne_zero) (Or.inl h_card_i_ne_top),
      mul_left_comm,
      ENNReal.mul_inv_cancel h_pi_ne_zero h_pi_ne_top, mul_one]

/-- **Marginal inside `S`** — if `j ∈ S`, then the `j`-th coordinate
    marginal of `resampleAt S v` is the uniform distribution on
    `P.alphabet j`. After unfolding the resample's `PMF.map` and reducing
    the if-then-else via `dif_pos hj`, the goal collapses to the helper
    `marginal_uniformOfFintype_pi` instantiated at index `⟨j, hj⟩ : ↥S`. -/
lemma resampleAt_apply_inside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) =
      PMF.uniformOfFintype (P.alphabet j) := by
  classical
  unfold resampleAt
  rw [PMF.map_comp]
  have h_proj :
      ((fun w : P.State => w j) ∘
        (fun (a : ∀ k : S, P.alphabet k.val) (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b))
      = (fun a => a ⟨j, hj⟩) := by
    funext a
    simp [Function.comp, dif_pos hj]
  rw [h_proj]
  exact marginal_uniformOfFintype_pi
    (β := fun k : (S : Finset (Fin P.numVars)) => P.alphabet k.val) ⟨j, hj⟩

/-- **Disjoint-coordinate independence** — if a finset `T ⊆ Fin numVars`
    is disjoint from `S`, then the joint marginal of `resampleAt S v` on
    `T` is the Dirac mass at the restriction of `v` to `T`. Same
    structural pattern as `resampleAt_apply_outside`, lifted from a
    single coordinate to a `Finset T`: every `k : ↥T` has `k.val ∉ S`
    (by `Finset.disjoint_left.mp hT`), so the glue function reduces to
    the constant `v` on all of `T`. -/
lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun k : T => w k.val)) =
      PMF.pure (fun k : T => v k.val) := by
  classical
  unfold resampleAt
  rw [PMF.map_comp]
  have h_const :
      ((fun (w : P.State) => (fun k : T => w k.val)) ∘
        (fun (a : ∀ k : S, P.alphabet k.val) (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b))
      = Function.const _ (fun k : T => v k.val) := by
    funext a
    funext k
    have hk : k.val ∉ S := fun hkS =>
      (Finset.disjoint_left.mp hT) k.property hkS
    simp [Function.comp, dif_neg hk]
  rw [h_const, PMF.map_const]

/-- One step of the Moser–Tardos algorithm: if no bad event is currently
    violated, return the current state with probability 1; otherwise pick
    the least-index bad event `i` and resample the variables in `vbl i`
    independently uniformly, keeping all other variables fixed. -/
noncomputable def step (v : P.State) : PMF P.State :=
  match P.pickBad v with
  | none   => PMF.pure v
  | some i => P.resampleAt (P.vbl i) v

/-- Iterated Moser–Tardos: `run n v` runs the step Markov chain for `n`
    iterations starting from `v`. -/
noncomputable def run : ℕ → P.State → PMF P.State
  | 0,     v => PMF.pure v
  | n + 1, v => (P.step v).bind (run n)

/-! ## Part III — LLL admissibility -/

/-- The Lovász Local Lemma admissibility predicate for a Moser–Tardos
    instance with a chosen tolerance vector `x : Fin numEvents → ℝ` in
    `[0, 1)`.

    Concretely, **admissible** means: for every bad event `i`, the
    "uniform-draw probability" of `A_i` (i.e. `Pr_{V ~ uniform}[A_i(V)]`)
    is at most `x i · ∏_{k ∈ Γ(i)} (1 - x k)`, where `Γ(i)` is the set
    of indices `k ≠ i` with `vbl(A_i) ∩ vbl(A_k) ≠ ∅`.

    This scaffold packages the predicate as a `structure`; the
    "uniform-draw probability of `A_i`" field uses the parent file's
    rational LLL framework (`Proofs/LovaszLocalLemma.lean` carries the
    quantitative algebraic core). -/
structure LLLAdmissible (x : Fin P.numEvents → ℚ) : Prop where
  /-- Each tolerance lies in `[0, 1)`. -/
  x_range : ∀ i, 0 ≤ x i ∧ x i < 1
  /-- The per-event uniform-draw probability bound. We package the
      probabilities `prob : Fin numEvents → ℚ` and the adjacency
      `adj : Fin numEvents → Finset (Fin numEvents)` symbolically; the
      faithful link to the actual variable-uniform measure is the
      content of a follow-on lemma (OQ-01-A.2 or OQ-01-B). -/
  lll : ∃ prob : Fin P.numEvents → ℚ, ∃ adj : Fin P.numEvents → Finset (Fin P.numEvents),
    (∀ i, prob i ≤ x i * (adj i).prod (fun k => 1 - x k)) ∧
    (∀ i, 0 ≤ prob i ∧ prob i ≤ 1)

/-! ## Part IV — Stated theorems (proofs deferred) -/

/-- **Moser–Tardos expected-step bound** (Moser & Tardos 2010, Theorem 1.2,
    variable form).

    If the LLL admissibility condition holds with tolerance vector `x`,
    then the expected total number of resampling steps performed by the
    Moser–Tardos algorithm is bounded by `Σᵢ xᵢ/(1−xᵢ)`.

    *Proof skeleton (deferred to OQ-01-B + OQ-01-C):*
    1. (OQ-01-B) Define `WitnessTree` and the extraction
       `executionLog → WitnessTree` per Moser–Tardos §4.
    2. (OQ-01-B) Validity: every extracted witness tree is proper.
    3. (OQ-01-B) Tree-probability bound: for a fixed proper witness tree
       `τ` rooted at `i`, `Pr[τ appears in execution] ≤ ∏_v Pr[A_{lbl(v)}]`.
    4. (OQ-01-C) Galton–Watson sum: `Σ_{τ proper, root=i} ∏_v Pr[A_{lbl(v)}]
       ≤ x_i / (1 - x_i)`.
    5. Sum over `i` to get the total bound. -/
theorem mt_expected_step_bound
    (P : MTProblem) (x : Fin P.numEvents → ℚ)
    (_h : P.LLLAdmissible x) :
    -- The actual statement requires an expected-value functional on the
    -- iterated `run` chain. The placeholder here ships the inequality at
    -- the algebraic-shell level so the next iteration can refine it.
    0 ≤ (Finset.univ : Finset (Fin P.numEvents)).sum
        (fun i => x i / (1 - x i)) := by
  -- The non-negativity shell already exists as
  -- `ProbMethod.LovaszLocal.moser_tardos_termination`.
  -- Here we re-prove inline to keep this file standalone; the bound on
  -- the expected step count itself is the OQ-01-B + OQ-01-C deliverable.
  apply Finset.sum_nonneg
  intro i _
  have hx := _h.x_range i
  apply div_nonneg hx.1
  linarith [hx.2]

/-- **Moser–Tardos almost-sure termination** (Moser & Tardos 2010, Theorem 1.2).

    If the LLL admissibility condition holds with tolerance `x`, then for
    every starting state `v₀ : State`, the iterated chain `P.run n v₀`
    concentrates on bad-event-free configurations as `n → ∞`.

    Formally (deferred): the measure of the set
    `{v | P.isViolated v}` under `P.run n v₀` tends to `0` as `n → ∞`.

    *Proof skeleton (deferred to OQ-01-B + OQ-01-C):* follows from the
    expected-step bound `mt_expected_step_bound` via Markov's inequality:
    the random number of resampling steps `T` is bounded in expectation,
    hence finite a.s., hence the chain terminates in finitely many steps
    almost surely. -/
theorem mt_terminates_as
    (P : MTProblem) (x : Fin P.numEvents → ℚ)
    (_h : P.LLLAdmissible x)
    (_v₀ : P.State) :
    -- Statement placeholder. The full statement is
    --   `Tendsto (fun n => (P.run n v₀).toMeasure {v | P.isViolated v}) atTop (𝓝 0)`,
    -- to be filled in once `WitnessTree` infrastructure (OQ-01-B) lands.
    True := by
  trivial

/-! ## Part V — Refined LLL admissibility (uniform-draw / collision-adjacency)

    OQ-01-A.3 deliverable: the symbolic `LLLAdmissible` predicate above
    packages the LLL bound around an *existential* over a free `prob` and
    `adj`. The refined `LLLAdmissibleUniform` ties `prob` to the canonical
    rational uniform-draw probability of `A_i` (`card{v|isBad i v} / card State`)
    and `adj` to the canonical variable-collision dependency graph
    (`k ≠ i ∧ vbl i ∩ vbl k ≠ ∅`). A forward bridge
    `LLLAdmissibleUniform.toLLLAdmissible` recovers the symbolic predicate.

    Design and Mathlib bearer audit: see
    `research/problems/prob-method-lovasz-local-oq-01/sessions/`
    (S7 PREP design memo `2026-05-14-s7-prep-lll-admissible-uniform-design.md`,
    S8 PREP faithful-link substitute memo
    `2026-05-16-s08-prep-faithful-link-bearer-gap-substitute.md`). -/

/-- **Rational uniform-draw probability of bad event `A_i`**: the
    probability of `A_i` under the uniform distribution on `P.State`,
    expressed as the rational quotient
    `card{v | isBad i v} / card P.State`. -/
noncomputable def uniformDrawProb (i : Fin P.numEvents) : ℚ :=
  (Fintype.card { v : P.State // P.isBad i v } : ℚ) /
    (Fintype.card P.State : ℚ)

/-- **Variable-collision dependency graph**: `k ∈ collisionAdj i` iff
    `k ≠ i` and `vbl i ∩ vbl k` is nonempty. This is the dependency graph
    used in the Moser–Tardos resampling analysis (events that share a
    variable can interfere when one is resampled). -/
noncomputable def collisionAdj (i : Fin P.numEvents) :
    Finset (Fin P.numEvents) :=
  (Finset.univ : Finset (Fin P.numEvents)).filter
    (fun k => k ≠ i ∧ (P.vbl i ∩ P.vbl k).Nonempty)

/-- `Fintype.card P.State > 0` as a rational positivity statement.
    Follows from the `Nonempty P.State` instance (file Part I). -/
lemma card_state_pos : 0 < (Fintype.card P.State : ℚ) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P.State)

/-- `uniformDrawProb i ≥ 0`: cardinality quotient with a positive
    denominator. -/
lemma uniformDrawProb_nonneg (i : Fin P.numEvents) :
    0 ≤ P.uniformDrawProb i := by
  unfold uniformDrawProb
  apply div_nonneg
  · exact_mod_cast Nat.zero_le _
  · exact_mod_cast Nat.zero_le _

/-- `uniformDrawProb i ≤ 1`: the bad-event subtype has at most as many
    elements as the full state space. -/
lemma uniformDrawProb_le_one (i : Fin P.numEvents) :
    P.uniformDrawProb i ≤ 1 := by
  unfold uniformDrawProb
  apply div_le_one_of_le₀
  · exact_mod_cast Fintype.card_subtype_le _
  · exact_mod_cast Nat.zero_le _

/-- Packaged unit-interval membership of `uniformDrawProb`. -/
lemma uniformDrawProb_mem_unit_interval (i : Fin P.numEvents) :
    0 ≤ P.uniformDrawProb i ∧ P.uniformDrawProb i ≤ 1 :=
  ⟨P.uniformDrawProb_nonneg i, P.uniformDrawProb_le_one i⟩

/-- **Faithful link (outer-measure form)** between the rational
    `uniformDrawProb` and the underlying `PMF`-valued uniform outer
    measure of the bad event.

    Using `PMF.toOuterMeasure_apply_fintype` (no `[MeasurableSpace]`
    prerequisite) sidesteps the typeclass plumbing that the analogous
    `toMeasure` form would require on `P.State = ∀ j, P.alphabet j`.

    The outer-measure form is mathematically equivalent for upper-bound
    applications (the LLL is an upper bound, and
    `toOuterMeasure ≤ toMeasure` is unconditional). A `toMeasure`-form
    corollary requires installing a `MeasurableSpace` instance on each
    `P.alphabet j`; we defer that to OQ-01-B, where the consumer
    naturally supplies it. -/
theorem uniformDrawProb_eq_outerMeasure (i : Fin P.numEvents) :
    ENNReal.ofReal ((P.uniformDrawProb i : ℝ)) =
      (PMF.uniformOfFintype P.State).toOuterMeasure
        { v : P.State | P.isBad i v } := by
  classical
  -- (1) Expand the outer measure as a Fintype sum of indicator values.
  rw [PMF.toOuterMeasure_apply_fintype]
  -- (2) Each indicator value reduces to a conditional on `isBad`.
  have h_each : ∀ v : P.State,
      ({ v : P.State | P.isBad i v }).indicator
          (PMF.uniformOfFintype P.State) v
        = (if P.isBad i v then ((Fintype.card P.State : ℕ) : ENNReal)⁻¹
           else 0) := by
    intro v
    by_cases hv : P.isBad i v
    · rw [Set.indicator_of_mem (show v ∈ { v | P.isBad i v } from hv),
          PMF.uniformOfFintype_apply, if_pos hv]
    · rw [Set.indicator_of_notMem (show v ∉ { v | P.isBad i v } from hv),
          if_neg hv]
  simp_rw [h_each]
  -- (3) Collapse `∑ v, if isBad v then C else 0` over the filter.
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- (4) Convert filter card to subtype card.
  rw [show
      (((Finset.univ : Finset P.State).filter (P.isBad i)).card : ENNReal)
      = (Fintype.card { v : P.State // P.isBad i v } : ENNReal) by
    rw [Fintype.card_subtype]]
  -- (5) Match LHS: ENNReal.ofReal of the rational quotient.
  unfold uniformDrawProb
  have h_pos : (0 : ℝ) < (Fintype.card P.State : ℝ) := by
    exact_mod_cast Fintype.card_pos
  push_cast
  rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv]

/-- **Refined LLL admissibility predicate**: the uniform-draw probability
    of `A_i` is bounded by `x i · ∏_{k ∈ collisionAdj i} (1 - x k)`, with
    the canonical `uniformDrawProb` (no symbolic `prob` parameter) and
    the canonical variable-collision adjacency. -/
structure LLLAdmissibleUniform (x : Fin P.numEvents → ℚ) : Prop where
  /-- Each tolerance lies in `[0, 1)`. -/
  x_range : ∀ i, 0 ≤ x i ∧ x i < 1
  /-- The per-event uniform-draw probability bound, with the canonical
      `uniformDrawProb` and `collisionAdj`. -/
  lll_uniform : ∀ i,
    P.uniformDrawProb i ≤ x i *
      (P.collisionAdj i).prod (fun k => 1 - x k)

/-- **Forward bridge**: `LLLAdmissibleUniform x` implies `LLLAdmissible x`
    (instantiating `prob := uniformDrawProb` and `adj := collisionAdj`).
    This means any client may state assumptions in the cleaner refined
    form and still consume the symbolic-form theorems downstream
    (`mt_expected_step_bound`, `mt_terminates_as`). -/
theorem LLLAdmissibleUniform.toLLLAdmissible
    {x : Fin P.numEvents → ℚ} (h : P.LLLAdmissibleUniform x) :
    P.LLLAdmissible x :=
  ⟨h.x_range,
   ⟨P.uniformDrawProb, P.collisionAdj, h.lll_uniform,
    fun i => ⟨P.uniformDrawProb_nonneg i, P.uniformDrawProb_le_one i⟩⟩⟩

-- ============================================================
-- PART VI: WITNESS TREES (OQ-01-B)
-- ============================================================
--
-- S13 PREP §3 skeleton (design: sessions/2026-06-12-s13-prep-witnesstree-
-- encoding.md), landed and Docker-verified at the v4.31 pin. The recursion
-- form of `isProper` uses `∀ t ∈ ch, isProper t` (recursive call applied to
-- a subterm `t ∈ ch`); S13's ranked fallbacks (termination_by sizeOf →
-- mutual isProperList → List.Forall) were held in reserve.

/-- A **witness tree** (Moser–Tardos 2010 §4): a rooted, event-labelled tree
    recording the cascade of resamplings that triggered a given step.

    Children are a `List` rather than a `Finset`: the nested occurrence under
    `Finset` (= a `Quotient` of `Multiset`/`List`) fails Lean's strict-
    positivity check, whereas `inductive T | mk : List T → T` is strictly
    positive. The "distinct sibling labels" requirement is recovered as a
    `Nodup`-on-labels side-condition in `isProper`. -/
inductive WitnessTree (P : MTProblem) : Type
  | node (label : Fin P.numEvents) (children : List (WitnessTree P))

namespace WitnessTree

variable {P}

/-- The event label at the root of a witness tree. -/
def labelOf : WitnessTree P → Fin P.numEvents
  | .node l _ => l

@[simp] theorem labelOf_node (l : Fin P.numEvents) (ch : List (WitnessTree P)) :
    labelOf (.node l ch) = l := rfl

/-- The **inclusive neighbourhood** `Γ⁺(i) = {i} ∪ collisionAdj i`: the labels
    permitted for the children of a node labelled `i` in a proper witness tree. -/
noncomputable def inclNbhd (i : Fin P.numEvents) : Finset (Fin P.numEvents) :=
  insert i (P.collisionAdj i)

@[simp] theorem self_mem_inclNbhd (i : Fin P.numEvents) : i ∈ inclNbhd (P := P) i :=
  Finset.mem_insert_self _ _

/-- A witness tree is **proper** when, at every node labelled `i`, the children
    (a) have pairwise-distinct labels, (b) carry labels in `Γ⁺(i)`, and
    (c) are themselves proper. This is the structural invariant that Moser–Tardos
    execution logs satisfy and that the probability bound is summed over. -/
def isProper : WitnessTree P → Prop
  | .node i ch =>
      (ch.map labelOf).Nodup
      ∧ (∀ t ∈ ch, labelOf t ∈ inclNbhd (P := P) i)
      ∧ ∀ t ∈ ch, isProper t

/-- A leaf (node with no children) is always proper. -/
@[simp] theorem isProper_leaf (i : Fin P.numEvents) :
    isProper (P := P) (.node i []) := by
  simp [isProper]

/-! ### S17 — deepest-attachment extraction and `witness_valid` (OQ-01-B)

The Moser–Tardos §4 extraction walks an execution-log segment backwards from
a root event and, for each earlier log entry `k`, attaches a new leaf labelled
`k` as a child of a **deepest** vertex whose label's inclusive neighbourhood
contains `k` (skipping entries with no such vertex). We formalize the
attachment step *relationally* (`Attach` / `AttachDeepest`) rather than as a
program: the propriety proof needs only the two facts the relation records —
the attachment site matches, and no match sits strictly deeper. The headline
theorem `witness_valid` is Moser–Tardos' propriety observation: every tree so
extracted is proper. The distinct-siblings condition is the interesting part:
if the attachment target already had a child with the incoming label `k`, that
child would itself be a *strictly deeper* match for `k` (since
`k ∈ Γ⁺(k)`), contradicting depth-maximality.

The probabilistic content (a fixed proper tree *appears* in the random
execution with probability at most `∏ uniformDrawProb`) is the S18+
deliverable `witness_prob_bd`; nothing here touches the `PMF` layer. -/

/-- `HasMatchAt j τ d`: some vertex of `τ` at depth `d` has a label whose
    inclusive neighbourhood contains `j` — i.e. depth `d` offers a legal
    attachment site for a new leaf labelled `j`. -/
def HasMatchAt (j : Fin P.numEvents) : WitnessTree P → ℕ → Prop
  | .node i _, 0 => j ∈ inclNbhd (P := P) i
  | .node _ ch, d + 1 => ∃ t ∈ ch, HasMatchAt j t d

/-- `Attach j τ d τ'`: `τ'` results from `τ` by adding a new leaf labelled `j`
    as a child of some vertex at depth `d` whose label's inclusive
    neighbourhood contains `j`. -/
inductive Attach (j : Fin P.numEvents) : WitnessTree P → ℕ → WitnessTree P → Prop
  | here (i : Fin P.numEvents) (ch : List (WitnessTree P))
      (hj : j ∈ inclNbhd (P := P) i) :
      Attach j (.node i ch) 0 (.node i (.node j [] :: ch))
  | child (i : Fin P.numEvents) (pre post : List (WitnessTree P))
      (t t' : WitnessTree P) (d : ℕ) (h : Attach j t d t') :
      Attach j (.node i (pre ++ t :: post)) (d + 1) (.node i (pre ++ t' :: post))

/-- The **deepest-vertex rule** (Moser–Tardos §4): the new leaf is attached at
    a depth `d` that is maximal among all matching depths. -/
def AttachDeepest (j : Fin P.numEvents) (τ τ' : WitnessTree P) : Prop :=
  ∃ d, Attach j τ d τ' ∧ ∀ d', HasMatchAt j τ d' → d' ≤ d

/-- An attachment site is in particular a match at the same depth. -/
theorem Attach.hasMatchAt {j : Fin P.numEvents} {τ τ' : WitnessTree P} {d : ℕ}
    (h : Attach j τ d τ') : HasMatchAt j τ d := by
  induction h with
  | here i ch hj => exact hj
  | child i pre post t t' d h ih =>
      exact ⟨t, List.mem_append_right _ (List.mem_cons_self ..), ih⟩

/-- Attachment below the root does not change the root label. -/
theorem Attach.labelOf_eq {j : Fin P.numEvents} {τ τ' : WitnessTree P} {d : ℕ}
    (h : Attach j τ d τ') : labelOf τ' = labelOf τ := by
  cases h <;> rfl

/-- **Propriety is preserved by depth-maximal attachment.** The heart of
    Moser–Tardos' witness-tree propriety: attaching `j` at a deepest matching
    vertex keeps sibling labels distinct, because a same-labelled sibling would
    itself be a strictly deeper match for `j` (as `j ∈ Γ⁺(j)`). -/
theorem isProper_attach {j : Fin P.numEvents} {τ τ' : WitnessTree P} {d : ℕ}
    (hatt : Attach j τ d τ') :
    isProper τ → (∀ d', HasMatchAt j τ d' → d' ≤ d) → isProper τ' := by
  induction hatt with
  | here i ch hj =>
      intro hp hmax
      simp only [isProper] at hp ⊢
      obtain ⟨hnodup, hlabels, hproper⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · -- sibling labels stay distinct: a same-labelled child would be a
        -- depth-1 match, contradicting maximality at depth 0
        rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hnodup⟩
        obtain ⟨u, humem, hulabel⟩ := List.mem_map.mp hmem
        have humatch : HasMatchAt j u 0 := by
          cases u with
          | node l chu =>
              simp only [HasMatchAt]
              have hlj : l = j := hulabel
              rw [hlj]
              exact self_mem_inclNbhd (P := P) j
        have h1 : HasMatchAt j (WitnessTree.node i ch) 1 := ⟨u, humem, humatch⟩
        exact absurd (hmax 1 h1) (by omega)
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hj
        · exact hlabels t ht'
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact isProper_leaf j
        · exact hproper t ht'
  | child i pre post t t' d h ih =>
      intro hp hmax
      simp only [isProper] at hp ⊢
      obtain ⟨hnodup, hlabels, hproper⟩ := hp
      have htmem : t ∈ pre ++ t :: post :=
        List.mem_append_right _ (List.mem_cons_self ..)
      have ht' : isProper t' :=
        ih (hproper t htmem)
          (fun d' hm => Nat.le_of_succ_le_succ (hmax (d' + 1) ⟨t, htmem, hm⟩))
      have hlab : labelOf t' = labelOf t := h.labelOf_eq
      refine ⟨?_, ?_, ?_⟩
      · rwa [List.map_append, List.map_cons, hlab,
          ← List.map_cons, ← List.map_append]
      · intro u hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact hlabels u (List.mem_append_left _ hu')
        · rcases List.mem_cons.mp hu' with rfl | hu''
          · rw [hlab]; exact hlabels t htmem
          · exact hlabels u (List.mem_append_right _ (List.mem_cons_of_mem _ hu''))
      · intro u hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact hproper u (List.mem_append_left _ hu')
        · rcases List.mem_cons.mp hu' with rfl | hu''
          · exact ht'
          · exact hproper u (List.mem_append_right _ (List.mem_cons_of_mem _ hu''))

/-- Relational form of the Moser–Tardos §4 extraction over a log segment
    (entries processed head-first, i.e. backwards in execution time): start
    from a bare root labelled `j`, attach each entry by the deepest-vertex
    rule when a match exists, and skip entries with no matching vertex. -/
inductive ExtractsFrom (j : Fin P.numEvents) :
    List (Fin P.numEvents) → WitnessTree P → Prop
  | nil : ExtractsFrom j [] (.node j [])
  | attach (l : List (Fin P.numEvents)) (k : Fin P.numEvents)
      (τ τ' : WitnessTree P) (hex : ExtractsFrom j l τ)
      (hatt : AttachDeepest k τ τ') : ExtractsFrom j (k :: l) τ'
  | skip (l : List (Fin P.numEvents)) (k : Fin P.numEvents)
      (τ : WitnessTree P) (hex : ExtractsFrom j l τ)
      (hnm : ∀ d, ¬HasMatchAt k τ d) : ExtractsFrom j (k :: l) τ

/-- **`witness_valid` (Moser–Tardos 2010, §4 propriety):** every witness tree
    extracted from a log segment by the deepest-attachment rule is proper.
    This discharges step 2 of the `mt_expected_step_bound` proof skeleton;
    the probability bound over a fixed proper tree (`witness_prob_bd`) is the
    remaining S18+ deliverable. -/
theorem witness_valid {j : Fin P.numEvents} {l : List (Fin P.numEvents)}
    {τ : WitnessTree P} (h : ExtractsFrom j l τ) : isProper τ := by
  induction h with
  | nil => exact isProper_leaf j
  | attach l k τ τ' hex hatt ih =>
      obtain ⟨d, ha, hmax⟩ := hatt
      exact isProper_attach ha ih hmax
  | skip l k τ hex hnm ih => exact ih

end WitnessTree

end MTProblem

end ProbMethod.MoserTardos
