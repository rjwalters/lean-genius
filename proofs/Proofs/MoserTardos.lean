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
  * Part I   : Setup (`MTProblem`, `State`, `isViolated`, `pickBad`).
  * Part II  : Algorithm (`resampleAt`, `step`, `run`).
  * Part III : LLL admissibility predicate (`LLLAdmissible`).
  * Part IV  : Placeholder main theorems
               (`mt_expected_step_bound`, `mt_terminates_as`).
  * Part V   : Refined uniform-draw layer (`uniformDrawProb`, `collisionAdj`,
               `LLLAdmissibleUniform`, `LLLAdmissibleUniform.toLLLAdmissible`).
  * Part VI  : Witness trees (`inductive WitnessTree`, `labelOf`, `inclNbhd`,
               `isProper`) — OQ-01-B skeleton (landed S16) — plus the
               deepest-attachment extraction (`Attach`, `ExtractsFrom`) and
               the propriety theorem `witness_valid` (landed S17).
  * Part VII : Instrumented runner `stepLog` / `runLog` emitting the resample
               log in execution order, with conservativity over `step` / `run`
               (landed S18-prep; log order fixed S18a).
  * Part VIII: Uniform initialization `mtRun` and the witness-tree weight
               `WitnessTree.weight` — the two statement-level ingredients of
               `witness_prob_bd` (landed S18a).

  Deferred (future PRs):
  * `theorem witness_prob_bd` (resample-table coupling)  — OQ-01-B
  * `def gwTreeProb`, `theorem gw_sum_bound`             — OQ-01-C
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

/-- Relational form of the Moser–Tardos §4 extraction over a log segment.

    The list is expected in **execution order** — oldest resample at the
    head, as emitted by `runLog` (Part VII). Because the `attach`/`skip`
    constructors recurse on the tail *before* handling the head, a
    derivation attaches entries starting from the **end** of the list, i.e.
    most recent resample first — exactly the backward pass of Moser–Tardos
    §4: start from a bare root labelled `j`, walk the log backwards in
    time, attach each entry at a deepest matching vertex when a match
    exists, and skip entries with no matching vertex. -/
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

/-! ## Part VII — Instrumented runner: the resample log (S18 prep)

The remaining probabilistic deliverable `witness_prob_bd` (a fixed proper
witness tree *appears* in the random execution with probability at most
`∏ uniformDrawProb` over its vertices) couples the Moser–Tardos run with the
**log** of resampled event indices — the list Part VI's `ExtractsFrom`
relation consumes. This part instruments the Part II runner with that log
and proves the instrumentation conservative:

* `stepLog` / `runLog` — the Part II chain, additionally emitting the
  indices of the resampled events in **execution order** (oldest entry
  first). Part VI's `ExtractsFrom` consumes such a list from the tail
  forward — most recent entry first — which is the Moser–Tardos §4
  backward pass (see the S18a session memo for why the opposite emission
  order would extract the wrong trees);
* `stepLog_map_fst` / `runLog_map_fst` — projecting the log away recovers
  `step` / `run` on the nose, so `runLog` is the *same* random process
  carrying extra bookkeeping;
* `runLog_length_le` — a run of `n` steps logs at most `n` resamples;
* `runLog_of_pickBad_none` — from a good state the run is silent;
* `pickBad_isBad` / `mem_log_pickBad` — every logged index was returned by
  `pickBad` at some state, hence names an event violated at its resample.

Nothing here yet assigns probabilities to trees: this is the state/log
plumbing that `witness_prob_bd` will quantify over. -/

section RunLog

/-- One Moser–Tardos step, additionally reporting which event (if any) was
    resampled: from a good state, stay put and report `none`; otherwise
    resample the least-index violated event `i` and report `some i`. -/
noncomputable def stepLog (v : P.State) :
    PMF (P.State × Option (Fin P.numEvents)) :=
  match P.pickBad v with
  | none   => PMF.pure (v, none)
  | some i => (P.resampleAt (P.vbl i) v).map (fun w => (w, some i))

/-- Instrumented runner: `runLog n v` runs `n` Moser–Tardos steps from `v`
    and returns the final state together with the log of resampled event
    indices in **execution order** (oldest entry first).

    Part VI's `ExtractsFrom` recurses on the tail of its list before
    handling the head, so on an execution-order log it attaches the most
    recent resample first — the Moser–Tardos §4 backward pass. (S18a fix:
    an earlier revision emitted the log most-recent-first, under which
    `ExtractsFrom` would have attached entries *oldest*-first — the reverse
    of MT §4; the S18a session memo records a two-event counterexample
    where the two orders extract genuinely different trees.) -/
noncomputable def runLog : ℕ → P.State → PMF (P.State × List (Fin P.numEvents))
  | 0, v => PMF.pure (v, [])
  | n + 1, v =>
      (P.stepLog v).bind fun p =>
        (runLog n p.1).map fun q => (q.1, p.2.toList ++ q.2)

/-- Projecting the log away from one instrumented step recovers `step`. -/
theorem stepLog_map_fst (v : P.State) :
    (P.stepLog v).map Prod.fst = P.step v := by
  cases h : P.pickBad v with
  | none => simp [stepLog, step, h, PMF.pure_map]
  | some i =>
      simp only [stepLog, step, h, PMF.map_comp]
      have hcomp : (Prod.fst ∘ fun w : P.State => (w, some i)) = id := rfl
      rw [hcomp, PMF.map_id]

/-- **The instrumentation is conservative**: projecting the log away from
    `runLog` recovers `run` exactly — the instrumented runner is the same
    random process as the Part II chain. -/
theorem runLog_map_fst (n : ℕ) (v : P.State) :
    (P.runLog n v).map Prod.fst = P.run n v := by
  induction n generalizing v with
  | zero => simp [runLog, run, PMF.pure_map]
  | succ n ih =>
      simp only [runLog, run, PMF.map_bind]
      have hinner : ∀ p : P.State × Option (Fin P.numEvents),
          ((P.runLog n p.1).map fun q => (q.1, p.2.toList ++ q.2)).map Prod.fst
            = P.run n p.1 := by
        intro p
        rw [PMF.map_comp]
        have hcomp :
            (Prod.fst ∘ fun q : P.State × List (Fin P.numEvents) =>
              (q.1, p.2.toList ++ q.2)) = Prod.fst := rfl
        rw [hcomp, ih p.1]
      simp only [hinner]
      rw [← P.stepLog_map_fst v, PMF.bind_map]
      rfl

/-- A run of `n` steps logs at most `n` resamples. -/
theorem runLog_length_le (n : ℕ) (v : P.State) :
    ∀ wl ∈ (P.runLog n v).support, wl.2.length ≤ n := by
  induction n generalizing v with
  | zero =>
      intro wl hwl
      simp only [runLog, PMF.mem_support_pure_iff] at hwl
      simp [hwl]
  | succ n ih =>
      intro wl hwl
      simp only [runLog, PMF.mem_support_bind_iff] at hwl
      obtain ⟨p, _hp, hwl⟩ := hwl
      rw [PMF.mem_support_map_iff] at hwl
      obtain ⟨q, hq, rfl⟩ := hwl
      have h1 := ih p.1 q hq
      have h2 : p.2.toList.length ≤ 1 := by cases p.2 <;> simp
      simp only [List.length_append]
      omega

/-- From a good state (no violated event) the instrumented run is silent:
    it stays put and logs nothing. -/
theorem runLog_of_pickBad_none {v : P.State} (h : P.pickBad v = none) :
    ∀ n, P.runLog n v = PMF.pure (v, []) := by
  intro n
  induction n with
  | zero => simp [runLog]
  | succ n ih =>
      simp only [runLog, stepLog, h, PMF.pure_bind]
      rw [ih, PMF.pure_map]
      simp

/-- `pickBad` only returns genuinely violated events. -/
theorem pickBad_isBad {v : P.State} {i : Fin P.numEvents}
    (h : P.pickBad v = some i) : P.isBad i v := by
  classical
  simp only [pickBad] at h
  split at h
  · rename_i hne
    obtain rfl : _ = i := Option.some.inj h
    have hmem := Finset.min'_mem _ hne
    exact (Finset.mem_filter.mp hmem).2
  · exact absurd h (by simp)

/-- **Provenance of log entries**: every index in the log was returned by
    `pickBad` at some state of the run — in particular it names an event
    that was violated at the moment it was resampled. -/
theorem mem_log_pickBad (n : ℕ) (v : P.State) :
    ∀ wl ∈ (P.runLog n v).support, ∀ k ∈ wl.2,
      ∃ w : P.State, P.pickBad w = some k ∧ P.isBad k w := by
  induction n generalizing v with
  | zero =>
      intro wl hwl k hk
      simp only [runLog, PMF.mem_support_pure_iff] at hwl
      subst hwl
      simp at hk
  | succ n ih =>
      intro wl hwl k hk
      simp only [runLog, PMF.mem_support_bind_iff] at hwl
      obtain ⟨p, hp, hwl⟩ := hwl
      rw [PMF.mem_support_map_iff] at hwl
      obtain ⟨q, hq, rfl⟩ := hwl
      rcases List.mem_append.mp hk with hk' | hk'
      · -- `k` was reported by this step
        revert hp
        cases hpb : P.pickBad v with
        | none =>
            simp only [stepLog, hpb, PMF.mem_support_pure_iff]
            rintro rfl
            simp at hk'
        | some i =>
            simp only [stepLog, hpb, PMF.mem_support_map_iff]
            rintro ⟨w, _hw, rfl⟩
            simp only [Option.toList_some, List.mem_singleton] at hk'
            subst hk'
            exact ⟨v, hpb, P.pickBad_isBad hpb⟩
      · exact ih p.1 q hq k hk'

end RunLog

/-! ## Part VIII — Uniform initialization and tree weight (S18a)

Statement-level preparation for the witness-tree probability bound
`witness_prob_bd`, driven by two observations recorded in the S18a session
memo:

* **Random initialization is part of the statement.** Moser–Tardos sample
  the initial assignment uniformly at random, and the per-tree bound is
  genuinely false over a *fixed* initial state: with a single 2-valued
  variable, one bad event `A = {v = 0}` and a violated fixed start, the
  path tree on `m + 1` vertices is extracted from the run's log with
  probability `2⁻ᵐ`, exceeding the would-be bound
  `∏_v uniformDrawProb = 2⁻⁽ᵐ⁺¹⁾`. Under uniform initialization the same
  computation gives exactly `2⁻⁽ᵐ⁺¹⁾` — the bound holds with equality, so
  it is also as sharp as it can be. `mtRun` packages the
  uniformly-initialized chain that `witness_prob_bd` quantifies over.

* **Tree weight.** `WitnessTree.weight τ = ∏_{v ∈ τ} uniformDrawProb
  (labelOf v)` is the right-hand side of `witness_prob_bd`, defined by
  structural recursion over the nested tree; its unit-interval bounds
  follow from the Part V bounds on `uniformDrawProb`. -/

section MTRun

/-- The **full Moser–Tardos process**: sample the initial assignment
    uniformly at random (`PMF.uniformOfFintype` on the finite product state
    space — i.e. every variable independently uniform on its alphabet),
    then run `n` instrumented steps, returning the final state and the
    resample log in execution order. `witness_prob_bd` is a statement about
    this process; see the Part VIII header for why the initial sample
    cannot be fixed. -/
noncomputable def mtRun (n : ℕ) : PMF (P.State × List (Fin P.numEvents)) :=
  (PMF.uniformOfFintype P.State).bind (P.runLog n)

/-- Projecting the log away recovers the uninstrumented uniformly-initialized
    chain: `mtRun` is the Part II process with random initialization plus
    bookkeeping. -/
theorem mtRun_map_fst (n : ℕ) :
    (P.mtRun n).map Prod.fst
      = (PMF.uniformOfFintype P.State).bind (P.run n) := by
  simp only [mtRun, PMF.map_bind, runLog_map_fst]

end MTRun

namespace WitnessTree

variable {P}

/-- The **weight** of a witness tree: the product, over all vertices `v` of
    the tree, of the uniform-draw probabilities of their labels,
    `∏_{v ∈ τ} uniformDrawProb (labelOf v)`.

    This is the right-hand side of the Moser–Tardos per-tree probability
    bound `witness_prob_bd` (Moser–Tardos 2010, §5): a fixed proper tree is
    extracted from the uniformly-initialized run with probability at most
    its weight. -/
noncomputable def weight : WitnessTree P → ℚ
  | .node i ch => P.uniformDrawProb i * (ch.map weight).prod

@[simp] theorem weight_node (i : Fin P.numEvents)
    (ch : List (WitnessTree P)) :
    weight (.node i ch) = P.uniformDrawProb i * (ch.map weight).prod := by
  simp [weight]

/-- Auxiliary: a product of rationals from `[0, 1]` stays in `[0, 1]`. -/
private lemma list_prod_mem_unit_interval {l : List ℚ}
    (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) : 0 ≤ l.prod ∧ l.prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 0 ≤ a ∧ a ≤ 1 := h a (by simp)
      have hl : 0 ≤ l.prod ∧ l.prod ≤ 1 :=
        ih fun x hx => h x (by simp [hx])
      simp only [List.prod_cons]
      refine ⟨mul_nonneg ha.1 hl.1, ?_⟩
      calc a * l.prod ≤ 1 * 1 := mul_le_mul ha.2 hl.2 hl.1 zero_le_one
        _ = 1 := one_mul 1

/-- The weight of a witness tree lies in `[0, 1]` — the sanity bound needed
    before `weight` can appear as a probability upper bound. -/
theorem weight_mem_unit_interval :
    ∀ τ : WitnessTree P, 0 ≤ weight τ ∧ weight τ ≤ 1
  | .node i ch => by
      have hch : ∀ x ∈ ch.map weight, 0 ≤ x ∧ x ≤ 1 := by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        exact weight_mem_unit_interval t
      obtain ⟨hp0, hp1⟩ := list_prod_mem_unit_interval hch
      obtain ⟨hu0, hu1⟩ := P.uniformDrawProb_mem_unit_interval i
      rw [weight_node]
      refine ⟨mul_nonneg hu0 hp0, ?_⟩
      calc P.uniformDrawProb i * (ch.map weight).prod
          ≤ 1 * 1 := mul_le_mul hu1 hp1 hp0 zero_le_one
        _ = 1 := one_mul 1

/-- Weight is non-negative. -/
theorem weight_nonneg (τ : WitnessTree P) : 0 ≤ weight τ :=
  (weight_mem_unit_interval τ).1

/-- Weight is at most one. -/
theorem weight_le_one (τ : WitnessTree P) : weight τ ≤ 1 :=
  (weight_mem_unit_interval τ).2

end WitnessTree

/-! ## Part IX — The resample table and the coupling (S18b)

Moser–Tardos §5 re-presents the randomness of the algorithm as a
**pre-sampled table**: for each variable an independent column of fresh
uniform draws, with column entry `0` the initialization and entry `t` the
value the variable receives at its `t`-th resampling. Running the algorithm
against the table is then *deterministic* — each resample of event `i` reads,
for each `j ∈ vbl i`, the next unused cell of column `j` — and the coupling
lemma `map_runTable` states that this deterministic runner, pushed forward
along the uniform table distribution, **is** the instrumented random runner
of Part VII. Consequences downstream (S18c): any event of the run — in
particular "the log extracts witness tree τ" — can be computed on the table
side, where the per-vertex resample values sit in *pairwise-disjoint,
independent* table cells indexed by data of τ alone (the slot invariant).

Design notes:

* Cells are addressed by `ℕ` counters via `readCell`, with a junk fallback
  (`Classical.arbitrary`) above row `n`; the coupling hypothesis
  `c j + m ≤ n + 1` guarantees the fallback is never consumed, and the
  table type stays the *finite* product the uniform PMF needs.
* The randomness bookkeeping is one splitting lemma
  (`uniform_table_overwrite`): overwriting one fresh cell per variable of
  `S` in a uniform table with an independent uniform draw reproduces the
  uniform table. Together with read-locality (`runTable_congr`: the runner
  never looks below its counters) this peels one resample off the run, and
  the peeled factor is *definitionally* `resampleAt` — the same
  subtype-product glue. -/

section TableCoupling

/-- A **resample table** with `n + 1` rows: for each variable `j`, a column
    of `n + 1` pre-sampled values of `alphabet j`. Row `0` is the
    initialization; row `t ≥ 1` is the value `j` receives at its `t`-th
    resampling. -/
abbrev Table (n : ℕ) : Type :=
  (j : Fin P.numVars) → Fin (n + 1) → P.alphabet j

instance (n : ℕ) : Nonempty (P.Table n) :=
  ⟨fun j _ => Classical.arbitrary (P.alphabet j)⟩

variable {n : ℕ}

/-- Read the table cell in column `j` at row `x : ℕ`, with a junk fallback
    above row `n` (never consumed under the coupling's counter bounds). -/
noncomputable def readCell (T : P.Table n) (j : Fin P.numVars) (x : ℕ) :
    P.alphabet j :=
  if h : x < n + 1 then T j ⟨x, h⟩ else Classical.arbitrary (P.alphabet j)

/-- One deterministic Moser–Tardos step against the table. The runner state
    is the current assignment together with one **write counter** per
    variable (the row index of that variable's next unused cell). From a
    good state, stay put and report `none`; otherwise resample the
    least-index violated event `i` by reading, for each `j ∈ vbl i`, the
    cell at `j`'s counter, then bump exactly those counters. -/
noncomputable def stepTable (T : P.Table n)
    (s : P.State × (Fin P.numVars → ℕ)) :
    (P.State × (Fin P.numVars → ℕ)) × Option (Fin P.numEvents) :=
  match P.pickBad s.1 with
  | none => (s, none)
  | some i =>
      ((fun j => if j ∈ P.vbl i then P.readCell T j (s.2 j) else s.1 j,
        fun j => if j ∈ P.vbl i then s.2 j + 1 else s.2 j), some i)

/-- The deterministic instrumented runner against the table: `m` steps from
    runner state `s`, returning the final runner state and the resample log
    in execution order (mirroring `runLog`). -/
noncomputable def runTable (T : P.Table n) :
    ℕ → P.State × (Fin P.numVars → ℕ) →
      (P.State × (Fin P.numVars → ℕ)) × List (Fin P.numEvents)
  | 0, s => (s, [])
  | m + 1, s =>
      ((runTable T m (P.stepTable T s).1).1,
        (P.stepTable T s).2.toList ++ (runTable T m (P.stepTable T s).1).2)

/-- **Read-locality, one step**: a table step from runner state `s` only
    reads cells at the current counters, so tables agreeing at all rows
    `≥ s.2 j` of each column `j` step identically. -/
private lemma stepTable_congr {T T' : P.Table n}
    (s : P.State × (Fin P.numVars → ℕ))
    (h : ∀ j (x : Fin (n + 1)), s.2 j ≤ (x : ℕ) → T j x = T' j x) :
    P.stepTable T s = P.stepTable T' s := by
  cases hpb : P.pickBad s.1 with
  | none => simp [stepTable, hpb]
  | some i =>
      simp only [stepTable, hpb]
      refine congrArg (fun w => ((w, _), _)) ?_
      funext j
      by_cases hj : j ∈ P.vbl i
      · simp only [if_pos hj, readCell]
        by_cases hlt : s.2 j < n + 1
        · rw [dif_pos hlt, dif_pos hlt, h j ⟨s.2 j, hlt⟩ (le_refl _)]
        · rw [dif_neg hlt, dif_neg hlt]
      · simp only [if_neg hj]

/-- Counters never decrease along a step. -/
private lemma stepTable_counter_le (T : P.Table n)
    (s : P.State × (Fin P.numVars → ℕ)) (j : Fin P.numVars) :
    s.2 j ≤ (P.stepTable T s).1.2 j := by
  cases hpb : P.pickBad s.1 with
  | none => simp [stepTable, hpb]
  | some i =>
      simp only [stepTable, hpb]
      by_cases hj : j ∈ P.vbl i <;> simp [hj]

/-- **Read-locality**: the runner never reads a cell below its counters, so
    tables agreeing at all rows `≥ s.2 j` of each column produce identical
    runs from `s`. -/
private lemma runTable_congr (m : ℕ) :
    ∀ (s : P.State × (Fin P.numVars → ℕ)) {T T' : P.Table n},
      (∀ j (x : Fin (n + 1)), s.2 j ≤ (x : ℕ) → T j x = T' j x) →
      P.runTable T m s = P.runTable T' m s := by
  induction m with
  | zero => intro s T T' _; rfl
  | succ m ih =>
      intro s T T' h
      have hstep : P.stepTable T s = P.stepTable T' s := P.stepTable_congr s h
      have hrec : P.runTable T m (P.stepTable T s).1
          = P.runTable T' m (P.stepTable T s).1 :=
        ih _ fun j x hx =>
          h j x (le_trans (P.stepTable_counter_le T s j) hx)
      simp only [runTable]
      rw [← hstep, hrec]

/-- **The splitting lemma**: overwriting, in a uniform table, one designated
    cell per variable of `S` (column `j`, row `c j`, in bounds) with an
    independent uniform draw reproduces the uniform table. This is the
    product-structure fact that peels one resample's worth of fresh
    randomness off the table; the overwriting draw lives on exactly the
    subtype product `resampleAt` samples. -/
private lemma uniform_table_overwrite (n : ℕ) (S : Finset (Fin P.numVars))
    (c : Fin P.numVars → ℕ) (hc : ∀ j ∈ S, c j < n + 1) :
    PMF.uniformOfFintype (P.Table n) =
      (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).bind fun a =>
        (PMF.uniformOfFintype (P.Table n)).map fun T j (x : Fin (n + 1)) =>
          if h : j ∈ S ∧ (x : ℕ) = c j then a ⟨j, h.1⟩ else T j x := by
  classical
  ext T₀
  rw [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  -- the unique compatible overwrite draw: the values T₀ takes at the cells
  set a₀ : ∀ j : S, P.alphabet j.val :=
    fun j => T₀ j.val ⟨c j.val, hc j.val j.property⟩ with ha₀
  rw [Finset.sum_eq_single a₀]
  · -- the surviving term: count the fiber of the overwrite map over T₀
    rw [PMF.map_apply, tsum_fintype, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have h_fiber :
        (Finset.univ.filter (fun T : P.Table n => T₀ =
            fun j (x : Fin (n + 1)) => if h : j ∈ S ∧ (x : ℕ) = c j
              then a₀ ⟨j, h.1⟩ else T j x)).card
          = Fintype.card (∀ j : S, P.alphabet j.val) := by
      rw [← Fintype.card_subtype]
      apply Fintype.card_congr
      refine
        { toFun := fun T => fun j : S =>
            T.val j.val ⟨c j.val, hc j.val j.property⟩
          invFun := fun b =>
            ⟨fun j (x : Fin (n + 1)) => if h : j ∈ S ∧ (x : ℕ) = c j
              then b ⟨j, h.1⟩ else T₀ j x, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · -- the reconstructed table lies in the fiber
        funext j x
        by_cases h : j ∈ S ∧ (x : ℕ) = c j
        · rw [dif_pos h, dif_pos h, ha₀]
          have hx : x = ⟨c j, hc j h.1⟩ := Fin.ext h.2
          rw [hx]
        · rw [dif_pos h, dif_neg h]
          exact absurd h (by simp)
      · -- left inverse
        rintro ⟨T, hT⟩
        apply Subtype.ext
        funext j x
        by_cases h : j ∈ S ∧ (x : ℕ) = c j
        · rw [dif_pos h]
          have hx : x = ⟨c j, hc j h.1⟩ := Fin.ext h.2
          rw [hx]
        · rw [dif_neg h]
          have := congrFun (congrFun hT j) x
          rw [dif_neg h] at this
          exact this
      · -- right inverse
        intro b
        funext j
        rw [dif_pos ⟨j.property, rfl⟩]
    rw [h_fiber]
    have h_ne_zero :
        ((Fintype.card (∀ j : S, P.alphabet j.val) : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos
        (α := ∀ j : S, P.alphabet j.val)).ne'
    have h_ne_top :
        ((Fintype.card (∀ j : S, P.alphabet j.val) : ℕ) : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, ← mul_assoc,
      ENNReal.inv_mul_cancel h_ne_zero h_ne_top, one_mul]
  · -- any other draw is incompatible: the fiber is empty
    intro a _ ha
    rw [PMF.map_apply, tsum_fintype]
    rw [Finset.sum_eq_zero, mul_zero]
    intro T _
    rw [if_neg]
    intro hT
    refine ha ?_
    funext j
    have := congrFun (congrFun hT j.val) ⟨c j.val, hc j.val j.property⟩
    rw [dif_pos ⟨j.property, rfl⟩] at this
    rw [ha₀]
    exact this
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The coupling, running form**: pushing the uniform table forward along
    `m` deterministic table steps from assignment `v` — with counters `c`
    leaving enough fresh rows (`c j + m ≤ n + 1`) — reproduces the
    instrumented random runner `runLog m v` exactly (final assignment and
    log; the counters are projected away). One resample is peeled per
    induction step: the splitting lemma makes the read cells an independent
    uniform draw on the `resampleAt` subtype product, and read-locality
    lets the recursive run forget the consumed cells. -/
private lemma map_runTable (m : ℕ) :
    ∀ (v : P.State) (c : Fin P.numVars → ℕ), (∀ j, c j + m ≤ n + 1) →
      (PMF.uniformOfFintype (P.Table n)).map
          (fun T => ((P.runTable T m (v, c)).1.1, (P.runTable T m (v, c)).2))
        = P.runLog m v := by
  induction m with
  | zero =>
      intro v c _
      have hconst : (fun T : P.Table n =>
          ((P.runTable T 0 (v, c)).1.1, (P.runTable T 0 (v, c)).2))
          = Function.const _ (v, ([] : List (Fin P.numEvents))) := rfl
      rw [hconst, PMF.map_const]
      rfl
  | succ m ih =>
      intro v c hc
      cases hpb : P.pickBad v with
      | none =>
          -- silent step on both sides
          have hfun : (fun T : P.Table n =>
              ((P.runTable T (m + 1) (v, c)).1.1,
                (P.runTable T (m + 1) (v, c)).2))
              = fun T => ((P.runTable T m (v, c)).1.1,
                (P.runTable T m (v, c)).2) := by
            funext T
            simp only [runTable, stepTable, hpb, Option.toList_none,
              List.nil_append]
          rw [hfun, ih v c fun j => le_trans (by omega) (hc j)]
          simp only [runLog, stepLog, hpb, PMF.pure_bind]
          have hid : (fun q : P.State × List (Fin P.numEvents) =>
              (q.1, (none : Option (Fin P.numEvents)).toList ++ q.2)) = id := by
            funext q
            simp
          rw [hid, PMF.map_id]
      | some i =>
          -- resampling step: peel the read cells off the uniform table
          have hbound : ∀ j ∈ P.vbl i, c j < n + 1 := fun j _ => by
            have := hc j; omega
          rw [P.uniform_table_overwrite n (P.vbl i) c hbound, PMF.map_bind]
          -- reduce the runLog side to a bind over the same subtype draw
          simp only [runLog, stepLog, hpb]
          rw [show P.resampleAt (P.vbl i) v =
              (PMF.uniformOfFintype (∀ j : (P.vbl i : Finset (Fin P.numVars)),
                P.alphabet j.val)).map
                (fun a (j : Fin P.numVars) =>
                  if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j) from rfl,
            PMF.map_comp, PMF.bind_map]
          refine congrArg _ (funext fun a => ?_)
          -- fixed draw `a`: the overwritten table steps to the glued
          -- assignment and never re-reads the consumed cells
          rw [PMF.map_comp]
          have hpoint : ((fun T : P.Table n =>
              ((P.runTable T (m + 1) (v, c)).1.1,
                (P.runTable T (m + 1) (v, c)).2)) ∘
              (fun T j (x : Fin (n + 1)) =>
                if h : j ∈ P.vbl i ∧ (x : ℕ) = c j
                then a ⟨j, h.1⟩ else T j x))
              = fun T =>
                  ((P.runTable T m
                    ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                      fun j => if j ∈ P.vbl i then c j + 1 else c j)).1.1,
                    i :: (P.runTable T m
                    ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                      fun j => if j ∈ P.vbl i then c j + 1 else c j)).2) := by
            funext T
            simp only [Function.comp_apply, runTable]
            set Tw : P.Table n :=
              fun j (x : Fin (n + 1)) =>
                if h : j ∈ P.vbl i ∧ (x : ℕ) = c j
                then a ⟨j, h.1⟩ else T j x with hTw
            have hstep : P.stepTable Tw (v, c) =
                (((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j), some i) := by
              simp only [stepTable, hpb]
              refine congrArg (fun w => ((w, _), _)) ?_
              funext j
              by_cases hj : j ∈ P.vbl i
              · rw [if_pos hj, dif_pos hj]
                simp only [readCell, dif_pos (hbound j hj), hTw]
                rw [dif_pos ⟨hj, rfl⟩]
              · rw [if_neg hj, dif_neg hj]
            have h1 : (P.stepTable Tw (v, c)).1 =
                ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j) := by
              rw [hstep]
            have h2 : (P.stepTable Tw (v, c)).2 = some i := by rw [hstep]
            rw [h1, h2]
            have hforget : P.runTable Tw m
                ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j)
                = P.runTable T m
                ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j) := by
              refine P.runTable_congr m _ fun j x hx => ?_
              have hcell : ¬ (j ∈ P.vbl i ∧ (x : ℕ) = c j) := by
                rintro ⟨hj, hxc⟩
                simp only [if_pos hj] at hx
                omega
              simp only [hTw, dif_neg hcell]
            rw [hforget]
            simp
          rw [hpoint]
          have hc' : ∀ j, (if j ∈ P.vbl i then c j + 1 else c j) + m ≤ n + 1 := by
            intro j
            have := hc j
            by_cases hj : j ∈ P.vbl i <;> simp [hj] <;> omega
          rw [show (fun T : P.Table n =>
              ((P.runTable T m
                ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j)).1.1,
                i :: (P.runTable T m
                ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                  fun j => if j ∈ P.vbl i then c j + 1 else c j)).2))
              = (fun q : P.State × List (Fin P.numEvents) => (q.1, i :: q.2)) ∘
                (fun T => ((P.runTable T m
                  ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                    fun j => if j ∈ P.vbl i then c j + 1 else c j)).1.1,
                  (P.runTable T m
                  ((fun j => if h : j ∈ P.vbl i then a ⟨j, h⟩ else v j),
                    fun j => if j ∈ P.vbl i then c j + 1 else c j)).2)) from rfl,
            ← PMF.map_comp,
            ih _ _ hc']
          simp

end TableCoupling

end MTProblem

end ProbMethod.MoserTardos
