/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5c298404-bda6-4a69-902d-23d99d0943e4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem tsum_prob_norm_gt_lt_top_of_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ⊤

- theorem integrable_of_tsum_prob_norm_gt_lt_top
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (htsum : (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ∞) :
    Integrable X μ

- theorem tsum_prob_norm_gt_eq_top_of_not_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : ¬ Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤

- theorem slln_necessity_statement
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds c)) :
    MeasureTheory.Integrable (X 0) μ

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
  Aristotle targets for Laws of Large Numbers OQ-01
  Supporting lemmas for the slln_necessity proof (Borel-Cantelli approach).
  See LawsOfLargeNumbersOQ01.lean for the main formalization.

  The Missing Piece: slln_necessity

  LawsOfLargeNumbersOQ01.lean has `slln_necessity` as an axiom:
    If SLLN holds (sample mean → c a.s.), then E[|X₀|] < ∞.

  Proof Blueprint (for future formalization)

  By contradiction: assume SLLN holds but E[|X₀|] = ∞. Then:
  1. Xₙ/n → 0 a.s. (from SLLN, by Cesàro)
  2. Σ P(‖X₀‖ > n) = ∞ (layer cake: E[‖X‖] = ∞ ↔ Σ P(‖X‖ > n) = ∞)
  3. Σ P(‖Xₙ‖ > n) = ∞ (from 2, by identical distribution)
  4. P(‖Xₙ‖ > n i.o.) = 1 (BC2: ProbabilityTheory.measure_limsup_eq_one)
  5. But from (1): P(‖Xₙ‖ > n i.o.) = 0 — contradiction!

  Key Mathlib tools available:
  - ProbabilityTheory.measure_limsup_eq_one (BC2, from Mathlib.Probability.BorelCantelli)
  - ProbabilityTheory.tsum_prob_mem_Ioi_lt_top (L¹ → Σ P(X > n) < ∞)

  Criteria for inclusion:
  - NOT the main open conjecture
  - No axioms (use theorem ... := by sorry instead)
  - No definition sorries
-/
import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

open MeasureTheory ProbabilityTheory Filter ENNReal

namespace LawsOfLargeNumbersOQ01

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Routine Lemma 1: Measurability of tail events.
   The events {ω | n < ‖Xₙ(ω)‖} are measurable (needed for applying BC2). -/

/-- The tail event {ω | n < ‖X n ω‖} is measurable for each n. -/
theorem measurableSet_tail_event
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (n : ℕ) :
    MeasurableSet {ω : Ω | (↑n : ℝ) < ‖X n ω‖} :=
  measurableSet_lt measurable_const (hmeas n).norm

/- Routine Lemma 2: IdentDistrib preserves tail probabilities.
   If X₀ and Xₙ have identical distributions, then P(‖Xₙ‖ > t) = P(‖X₀‖ > t). -/

omit [IsProbabilityMeasure μ] in
/-- Identical distributions preserve tail probabilities. -/
theorem identDistrib_meas_norm_gt
    (X Y : Ω → ℝ)
    (hXY : ProbabilityTheory.IdentDistrib X Y μ μ)
    (t : ℝ) :
    μ {ω : Ω | t < ‖X ω‖} = μ {ω : Ω | t < ‖Y ω‖} :=
  hXY.measure_mem_eq (measurableSet_lt measurable_const measurable_norm)

/- Routine Lemma 3: i.i.d. tail sum equals X₀ tail sum.
   Σₙ P(‖Xₙ‖ > n) = Σₙ P(‖X₀‖ > n) when X₀, X₁, ... are identically distributed. -/

omit [IsProbabilityMeasure μ] in
/-- For an i.i.d. sequence, the tail sum Σ P(‖Xₙ‖ > n) equals Σ P(‖X₀‖ > n). -/
theorem tsum_prob_norm_gt_iid_eq
    (X : ℕ → Ω → ℝ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    (∑' n : ℕ, μ {ω : Ω | (↑n : ℝ) < ‖X n ω‖}) =
    (∑' n : ℕ, μ {ω : Ω | (↑n : ℝ) < ‖X 0 ω‖}) := by
  congr 1
  ext n
  exact identDistrib_meas_norm_gt (X n) (X 0) (hident n) n

/- Routine Lemma 4: Integrability implies finite tail sum.
   If E[‖X‖] < ∞, then Σₙ P(‖X‖ > n) < ∞.
   Uses ProbabilityTheory.tsum_prob_mem_Ioi_lt_top (requires MeasureSpace). -/

/-- Integrability implies finite tail sum: E[‖X‖] < ∞ → Σ P(‖X‖ > n) < ∞. -/
theorem tsum_prob_norm_gt_lt_top_of_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ⊤ := by
  have h_summable : ∑' k : ℕ, (μ {ω | ‖X ω‖ > (k : ℝ)}) = ∫⁻ ω, (∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0)) ∂μ := by
    rw [ MeasureTheory.lintegral_tsum ];
    · congr! 2 with k ; erw [ MeasureTheory.lintegral_indicator ] ; aesop;
      exact measurableSet_lt measurable_const ( hmeas.norm );
    · exact fun n => Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_lt measurable_const ( hmeas.norm ) ) measurable_const measurable_const );
  -- The inner sum is bounded by ‖X ω‖ + 1.
  have h_inner_bound : ∀ ω : Ω, ∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0) ≤ ‖X ω‖ + 1 := by
    intro ω
    have h_inner_bound : ∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0) ≤ ∑ k ∈ Finset.range (Nat.floor (‖X ω‖) + 1), (1 : ℝ) := by
      rw [ tsum_eq_sum ];
      exacts [ Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num, fun n hn => if_neg <| by exact fun h => hn <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| mod_cast h.le ];
    exact h_inner_bound.trans ( by simpa using Nat.floor_le ( norm_nonneg ( X ω ) ) );
  -- Using the bound, we can show that the integral is finite.
  have h_integral_finite : ∫⁻ ω, (∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0)) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (‖X ω‖ + 1) ∂μ := by
    refine' MeasureTheory.lintegral_mono fun ω => _;
    convert ENNReal.ofReal_le_ofReal ( h_inner_bound ω ) using 1 ; norm_num [ ENNReal.ofReal ];
    rw [ tsum_eq_sum ];
    any_goals exact Finset.range ( ⌊|X ω|⌋₊ + 1 );
    · rw [ tsum_eq_sum ] ; aesop;
      exact fun n hn => if_neg fun h => hn <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| mod_cast h.le;
    · exact fun n hn => if_neg fun h => hn <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| mod_cast h.le;
  refine' h_summable ▸ lt_of_le_of_lt h_integral_finite _;
  convert MeasureTheory.Integrable.lintegral_lt_top _;
  exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.norm ‹_› ) ( MeasureTheory.integrable_const _ )

/- Routine Lemma 5: Layer cake converse.
   If Σ P(‖X‖ > n) < ∞, then X is integrable.
   This follows from E[‖X‖] ≤ 1 + Σ P(‖X‖ > n). -/

/-- If the tail sum Σ P(‖X‖ > n) is finite, then X is integrable.

    Proof sketch: E[‖X‖] ≤ 1 + Σ P(‖X‖ > n) by layer cake formula. -/
theorem integrable_of_tsum_prob_norm_gt_lt_top
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (htsum : (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ∞) :
    Integrable X μ := by
  contrapose htsum;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∫⁻ (ω : Ω), ⌈‖X ω‖⌉₊ ∂μ = ∑' (n : ℕ), μ {ω | ‖X ω‖ > n} := by
    have h_fubini : ∫⁻ (ω : Ω), ⌈‖X ω‖⌉₊ ∂μ = ∫⁻ (ω : Ω), ∑' (n : ℕ), (if n < ‖X ω‖ then 1 else 0) ∂μ := by
      congr with ω;
      rw [ tsum_eq_sum ];
      any_goals exact Finset.range ⌈‖X ω‖⌉₊;
      · rw [ Finset.sum_congr rfl fun i hi => if_pos <| Nat.lt_ceil.mp <| Finset.mem_range.mp hi ] ; aesop;
      · aesop;
    rw [ h_fubini, MeasureTheory.lintegral_tsum ];
    · congr with n ; erw [ MeasureTheory.lintegral_indicator ] ; aesop;
      exact measurableSet_lt measurable_const ( hmeas.norm );
    · exact fun n => Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_lt measurable_const ( hmeas.norm ) ) measurable_const measurable_const );
  contrapose! htsum; have := hmeas.norm; simp_all +decide [ MeasureTheory.Integrable ] ; (
  refine' ⟨ hmeas.aestronglyMeasurable, _ ⟩;
  simp_all +decide [ MeasureTheory.hasFiniteIntegral_iff_norm ];
  refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) ( h_fubini.symm ▸ htsum );
  rw [ ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num [ Nat.le_ceil ]);

/- Routine Lemma 6: Non-integrable → tail sum is infinite.
   Contrapositive of Lemma 5. -/

/-- If X is not integrable, then the tail sum Σ P(‖X‖ > n) = ∞. -/
theorem tsum_prob_norm_gt_eq_top_of_not_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : ¬ Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤ := by
  -- By definition of integrability, if X is not integrable, then the integral of ‖X‖ over Ω is infinite.
  by_contra h_contra;
  apply_rules [ integrable_of_tsum_prob_norm_gt_lt_top ];
  exact lt_top_iff_ne_top.mpr h_contra

/- Main Target: slln_necessity (the key open gap).
   Converts the axiom to a sorry theorem for potential future proof. -/

/- slln_necessity — converse of Kolmogorov's SLLN.

    If the sample mean of i.i.d. random variables converges a.s. to some limit,
    then the random variables must have finite first moment.

    Status: Completes Kolmogorov's characterization: SLLN ⟺ E[‖X₀‖] < ∞

    Proof gaps:
    1. Cesàro argument: SLLN → Xₙ/n → 0 a.s.
    2. Layer cake converse: ¬ Integrable → Σ P(‖X‖ > n) = ∞
    3. Full mutual independence of {‖Xₙ‖ > n} for BC2 -/
noncomputable section AristotleLemmas

/-
If the Cesàro mean of a sequence converges, then the terms divided by n converge to 0.
-/
theorem tendsto_zero_div_of_tendsto_sum_div
    {u : ℕ → ℝ} {c : ℝ}
    (h : Filter.Tendsto (fun (n : ℕ) => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, u i) Filter.atTop (nhds c)) :
    Filter.Tendsto (fun (n : ℕ) => (↑n : ℝ)⁻¹ • u n) Filter.atTop (nhds 0) := by
      -- Let $S_n = \sum_{i=0}^{n-1} u_i$. We are given that $S_n/n \to c$.
      set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, u i
      have hS : Filter.Tendsto (fun n => S n / (n : ℝ)) Filter.atTop (nhds c) := by
        simpa [ div_eq_inv_mul ] using h;
      -- We want to show that $u_n/n \to 0$. Note that $u_n = S_{n+1} - S_n$.
      have h_diff : Filter.Tendsto (fun n => (S (n + 1) - S n) / (n : ℝ)) Filter.atTop (nhds 0) := by
        have h_diff : Filter.Tendsto (fun n => (S (n + 1) / (n + 1 : ℝ)) * ((n + 1 : ℝ) / (n : ℝ)) - (S n / (n : ℝ))) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.sub ( Filter.Tendsto.mul ( hS.comp ( Filter.tendsto_add_atTop_nat 1 ) ) ( show Filter.Tendsto ( fun n : ℕ => ( n + 1 : ℝ ) / n ) Filter.atTop ( nhds 1 ) from by simpa [ add_div ] using tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat ) |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ) hS;
        refine h_diff.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_mul_div_cancel₀ ( by positivity ) ] ; ring );
      simp +zetaDelta at *;
      simpa [ div_eq_inv_mul, Finset.sum_range_succ ] using h_diff

/-
If random variables are pairwise independent, then events defined by them are pairwise independent.
-/
theorem indepSet_of_indepFun_pairwise
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (A : ℕ → Set ℝ)
    (hA : ∀ i, MeasurableSet (A i)) :
    Pairwise (fun i j => ProbabilityTheory.IndepSet {ω | X i ω ∈ A i} {ω | X j ω ∈ A j} μ) := by
      intro i j hij
      have h_indep : ProbabilityTheory.IndepFun (X i) (X j) μ := by
        exact hindep hij
      generalize_proofs at *;
      rw [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ] at h_indep
      generalize_proofs at *;
      exact?

/-
The variance of the sum of indicators of pairwise independent sets is bounded by the sum of their probabilities.
-/
theorem variance_sum_indicator_le
    {ι : Type*} {t : Finset ι}
    {s : ι → Set Ω}
    (hmeas : ∀ i ∈ t, MeasurableSet (s i))
    (hindep : Set.Pairwise t (fun i j => ProbabilityTheory.IndepSet (s i) (s j) μ)) :
    variance (∑ i ∈ t, (s i).indicator (fun _ => 1)) μ ≤ ∑ i ∈ t, (μ (s i)).toReal := by
      -- By definition of variance, we know that
      have h_var : ProbabilityTheory.variance (∑ i ∈ t, (s i).indicator (fun _ => (1 : ℝ))) μ = ∑ i ∈ t, ∑ j ∈ t, ProbabilityTheory.covariance ((s i).indicator (fun _ => (1 : ℝ))) ((s j).indicator (fun _ => (1 : ℝ))) μ := by
        have h_var : ∀ (f : ι → Ω → ℝ), (∀ i ∈ t, MeasureTheory.Integrable (f i) μ) → (∀ i ∈ t, MeasureTheory.Integrable (fun ω => (f i ω) ^ 2) μ) → ProbabilityTheory.variance (∑ i ∈ t, f i) μ = ∑ i ∈ t, ∑ j ∈ t, ProbabilityTheory.covariance (f i) (f j) μ := by
          intro f hf_int hf_sq_int
          have h_var_def : ProbabilityTheory.variance (∑ i ∈ t, f i) μ = ∑ i ∈ t, ∑ j ∈ t, ProbabilityTheory.covariance (f i) (f j) μ := by
            have h_var_def : ProbabilityTheory.variance (∑ i ∈ t, f i) μ = ∑ i ∈ t, ∑ j ∈ t, (∫ ω, (f i ω - ∫ ω, f i ω ∂μ) * (f j ω - ∫ ω, f j ω ∂μ) ∂μ) := by
              have h_var_def : ProbabilityTheory.variance (∑ i ∈ t, f i) μ = ∫ ω, (∑ i ∈ t, (f i ω - ∫ ω, f i ω ∂μ)) ^ 2 ∂μ := by
                rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
                · simp +decide [ Finset.sum_sub_distrib, MeasureTheory.integral_finset_sum _ fun i hi => hf_int i hi ];
                · exact Filter.Eventually.of_forall fun ω => sq_nonneg _;
                · exact MeasureTheory.AEStronglyMeasurable.pow ( MeasureTheory.AEStronglyMeasurable.sub ( Finset.aestronglyMeasurable_sum _ fun i hi => hf_int i hi |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) _;
              simp +decide only [h_var_def, sq, Finset.mul_sum _ _ _, mul_comm];
              rw [ MeasureTheory.integral_finset_sum ];
              · refine' Finset.sum_congr rfl fun i hi => MeasureTheory.integral_finset_sum _ fun j hj => _;
                refine' MeasureTheory.Integrable.mono' _ _ _;
                exact fun ω => ( f i ω - ∫ ω, f i ω ∂μ ) ^ 2 + ( f j ω - ∫ ω, f j ω ∂μ ) ^ 2;
                · simp_rw +decide [ sub_sq ];
                  exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( MeasureTheory.Integrable.sub ( hf_sq_int i hi ) ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf_int i hi ) _ ) _ ) ) ( MeasureTheory.integrable_const _ ) ) ( MeasureTheory.Integrable.add ( MeasureTheory.Integrable.sub ( hf_sq_int j hj ) ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf_int j hj ) _ ) _ ) ) ( MeasureTheory.integrable_const _ ) );
                · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.sub ( hf_int i hi |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) ( MeasureTheory.AEStronglyMeasurable.sub ( hf_int j hj |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) );
                · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
              · intro i hi
                have h_integrable : ∀ j ∈ t, MeasureTheory.Integrable (fun ω => (f i ω - ∫ ω, f i ω ∂μ) * (f j ω - ∫ ω, f j ω ∂μ)) μ := by
                  intro j hj
                  have h_integrable : MeasureTheory.Integrable (fun ω => (f i ω - ∫ ω, f i ω ∂μ) ^ 2) μ ∧ MeasureTheory.Integrable (fun ω => (f j ω - ∫ ω, f j ω ∂μ) ^ 2) μ := by
                    simp_all +decide [ sub_sq ];
                    exact ⟨ MeasureTheory.Integrable.sub ( hf_sq_int i hi ) ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf_int i hi ) _ ) _ ), MeasureTheory.Integrable.sub ( hf_sq_int j hj ) ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf_int j hj ) _ ) _ ) ⟩;
                  refine' MeasureTheory.Integrable.mono' ( h_integrable.1.add h_integrable.2 ) _ _;
                  · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.sub ( hf_int i hi |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) ) ( MeasureTheory.AEStronglyMeasurable.sub ( hf_int j hj |> MeasureTheory.Integrable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) );
                  · filter_upwards [ ] with ω using abs_le.mpr ⟨ by norm_num; nlinarith only, by norm_num; nlinarith only ⟩
                exact MeasureTheory.integrable_finset_sum _ fun j hj => h_integrable j hj
            exact h_var_def.trans ( Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => rfl )
          exact h_var_def;
        apply h_var; intro i hi; exact (by
        exact MeasureTheory.integrable_indicator_iff ( hmeas i hi ) |>.2 ( MeasureTheory.integrable_const _ )); intro i hi; exact (by
        refine' MeasureTheory.Integrable.mono' _ _ _ <;> norm_num [ Set.indicator ];
        exacts [ fun _ => 1, MeasureTheory.integrable_const _, Measurable.aestronglyMeasurable ( by exact Measurable.ite ( hmeas i hi ) measurable_const measurable_const ), Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num ]);
      -- Since the sets are pairwise independent, the covariance between any two distinct indicators is zero.
      have h_cov_zero : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ProbabilityTheory.covariance ((s i).indicator (fun _ => (1 : ℝ))) ((s j).indicator (fun _ => (1 : ℝ))) μ = 0 := by
        intro i hi j hj hij; specialize hindep hi hj hij; simp_all +decide [ ProbabilityTheory.IndepSet ] ;
        rw [ ProbabilityTheory.covariance ] ; simp_all +decide [ Set.indicator_apply ] ; ring;
        rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ] <;> norm_num [ MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, MeasureTheory.integral_indicator, hmeas i hi, hmeas j hj ] ; ring!;
        · rw [ MeasureTheory.integral_sub ] <;> norm_num [ MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, MeasureTheory.integral_indicator, hmeas i hi, hmeas j hj ] ; ring!;
          · rw [ sub_eq_zero, mul_comm ];
            convert hindep.measure_inter_eq_mul using 1;
            rw [ show ( fun a => ( s i ).indicator ( fun _ => 1 : Ω → ℝ ) a * ( s j ).indicator ( fun _ => 1 : Ω → ℝ ) a ) = ( s i ∩ s j ).indicator ( fun _ => 1 : Ω → ℝ ) by ext; by_cases hi : ‹_› ∈ s i <;> by_cases hj : ‹_› ∈ s j <;> simp +decide [ hi, hj ] ] ; rw [ MeasureTheory.integral_indicator ( hmeas i hi |> MeasurableSet.inter <| hmeas j hj ) ] ; simp +decide [ MeasureTheory.measureReal_def ] ;
            rw [ ← ENNReal.toReal_eq_toReal ] <;> norm_num [ ENNReal.toReal_mul ];
            exact ENNReal.mul_ne_top ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_ne_top _ _ );
          · refine' MeasureTheory.Integrable.neg _;
            refine' MeasureTheory.Integrable.mul_const _ _;
            exact MeasureTheory.integrable_indicator_iff ( hmeas i hi ) |>.2 ( MeasureTheory.integrable_const _ );
          · refine' MeasureTheory.Integrable.const_mul _ _;
            exact MeasureTheory.integrable_indicator_iff ( hmeas j hj ) |>.2 ( MeasureTheory.integrable_const _ );
        · refine' MeasureTheory.Integrable.mono' _ _ _ <;> norm_num [ Set.indicator ];
          exacts [ fun _ => 1, MeasureTheory.integrable_const _, Measurable.aestronglyMeasurable ( by exact Measurable.ite ( hmeas j hj ) ( Measurable.ite ( hmeas i hi ) measurable_const measurable_const ) measurable_const ), Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num ];
        · refine' MeasureTheory.Integrable.sub _ _;
          · refine' MeasureTheory.Integrable.neg _;
            refine' MeasureTheory.Integrable.mul_const _ _;
            exact MeasureTheory.integrable_indicator_iff ( hmeas i hi ) |>.2 ( MeasureTheory.integrable_const _ );
          · refine' MeasureTheory.Integrable.const_mul _ _;
            exact MeasureTheory.integrable_indicator_iff ( hmeas j hj ) |>.2 ( MeasureTheory.integrable_const _ );
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.mono' _ _ _ <;> norm_num [ Set.indicator ];
            refine' fun ω => 1;
            · norm_num;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( hmeas j hj ) ( Measurable.ite ( hmeas i hi ) measurable_const measurable_const ) measurable_const );
            · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
          · refine' MeasureTheory.Integrable.sub _ _;
            · refine' MeasureTheory.Integrable.neg _;
              refine' MeasureTheory.Integrable.mul_const _ _;
              exact MeasureTheory.integrable_indicator_iff ( hmeas i hi ) |>.2 ( MeasureTheory.integrable_const _ );
            · refine' MeasureTheory.Integrable.const_mul _ _;
              exact MeasureTheory.integrable_indicator_iff ( hmeas j hj ) |>.2 ( MeasureTheory.integrable_const _ );
        · exact MeasureTheory.integrable_const _;
      rw [ h_var, Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ( fun j hj => by by_cases hij : i = j <;> aesop ) ( by aesop ) ];
      refine' Finset.sum_le_sum fun i hi => _;
      rw [ ProbabilityTheory.covariance_self ];
      · refine' le_trans ( ProbabilityTheory.variance_le_expectation_sq _ ) _;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.indicator measurable_const ( hmeas i hi ) );
        · simp +decide [ Set.indicator, sq ];
          erw [ MeasureTheory.integral_indicator ( hmeas i hi ) ] ; aesop;
      · exact Measurable.aemeasurable ( by exact Measurable.indicator measurable_const ( hmeas i hi ) )

/-
If a non-decreasing sequence of random variables has probability of being bounded by M going to 0 for all M, then it diverges to infinity almost surely.
-/
theorem tendsto_infinity_ae_of_monotone_tendsto_measure_le_zero
    (X : ℕ → Ω → ℝ)
    (hmono : ∀ n ω, X n ω ≤ X (n + 1) ω)
    (hmeas : ∀ n, Measurable (X n))
    (hlim : ∀ M : ℝ, Filter.Tendsto (fun n => μ {ω | X n ω ≤ M}) Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop Filter.atTop := by
      -- Let $E_M = \{ \omega \mid \sup_n X_n(\omega) \le M \}$.
      set EM : ℝ → Set Ω := fun M => {ω | ∀ n, X n ω ≤ M};
      -- By continuity of measure from above (since $\mu$ is finite), $\mu(E_M) = \lim_n \mu \{ X_n \le M \}$.
      have hEM_zero : ∀ M, μ (EM M) = 0 := by
        intro M
        have hEM_eq : EM M = ⋂ n, {ω | X n ω ≤ M} := by
          aesop
        rw [hEM_eq] at *;
        have hEM_zero : Filter.Tendsto (fun n => μ {ω | X n ω ≤ M}) Filter.atTop (nhds 0) := hlim M
        exact (by
        exact le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds hEM_zero fun n => MeasureTheory.measure_mono <| Set.iInter_subset _ _ ) bot_le); -- Apply the continuity of measure from above to conclude that the measure of the intersection is zero. This follows from the fact that the measure of the intersection is the limit of the measures of the individual sets. Hence, μ (⋂ n, {ω | X n ω ≤ M}) = 0.;
      -- The event $\{ \sup_n X_n < \infty \}$ is $\bigcup_{k \in \mathbb{N}} \{ \sup_n X_n \le k \}$.
      have h_union_zero : μ (⋃ k : ℕ, EM (k : ℝ)) = 0 := by
        exact MeasureTheory.measure_iUnion_null fun k => hEM_zero _;
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_union_zero ] with ω hω;
      simp +zetaDelta at *;
      exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases hω ⌈x⌉₊ with ⟨ n, hn ⟩ ; exact ⟨ n, fun m hm => le_trans ( Nat.le_ceil _ ) ( le_trans hn.le ( show X m ω ≥ X n ω from by exact monotone_nat_of_le_succ ( fun n => hmono n ω ) hm ) ) ⟩ ;

/-
If a non-decreasing sequence of random variables has expectation tending to infinity and variance bounded by expectation, then it diverges to infinity almost surely.
-/
theorem tendsto_infinity_ae_of_monotone_variance_le_expectation
    (X : ℕ → Ω → ℝ)
    (hmono : ∀ n ω, X n ω ≤ X (n + 1) ω)
    (hmeas : ∀ n, Measurable (X n))
    (hint : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (hexp_tendsto : Filter.Tendsto (fun n => ∫ ω, X n ω ∂μ) Filter.atTop Filter.atTop)
    (hvar : ∀ n, ProbabilityTheory.variance (X n) μ ≤ ∫ ω, X n ω ∂μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop Filter.atTop := by
      apply_rules [ tendsto_infinity_ae_of_monotone_tendsto_measure_le_zero ];
      intro M
      have hM : ∀ᶠ n in Filter.atTop, (∫ ω, X n ω ∂μ) > 2 * M := by
        exact hexp_tendsto.eventually_gt_atTop _
      have hM' : ∀ᶠ n in Filter.atTop, (μ {ω | X n ω ≤ M}) ≤ (ENNReal.ofReal (4 / (∫ ω, X n ω ∂μ))) := by
        filter_upwards [ hM, hexp_tendsto.eventually_gt_atTop 0 ] with n hn hn';
        have h_chebyshev : μ {ω | |X n ω - ∫ ω, X n ω ∂μ| ≥ (∫ ω, X n ω ∂μ) / 2} ≤ ENNReal.ofReal (4 / (∫ ω, X n ω ∂μ)) := by
          have := @meas_ge_le_variance_div_sq Ω _ μ;
          refine' le_trans ( this ( ‹∀ n, MeasureTheory.MemLp ( X n ) 2 μ› n ) ( half_pos hn' ) ) _;
          exact ENNReal.ofReal_le_ofReal ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hvar n ] );
        refine' le_trans ( MeasureTheory.measure_mono _ ) h_chebyshev;
        exact fun ω hω => by rw [ Set.mem_setOf_eq ] at *; cases abs_cases ( X n ω - ∫ ω, X n ω ∂μ ) <;> linarith;
      have hM'' : Filter.Tendsto (fun n => ENNReal.ofReal (4 / (∫ ω, X n ω ∂μ))) Filter.atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal ( tendsto_const_nhds.div_atTop hexp_tendsto ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
      exact (by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM'' ( Filter.eventually_of_mem hM' fun n hn => zero_le _ ) ( Filter.eventually_of_mem hM' fun n hn => hn )); -- replace this with the proper infer instance proof.

/-
The second Borel-Cantelli lemma holds for pairwise independent events: if the sum of probabilities diverges, the events occur infinitely often with probability 1.
-/
theorem borel_cantelli_of_pairwise_independent
    {s : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (s n))
    (hindep : Pairwise (fun i j => ProbabilityTheory.IndepSet (s i) (s j) μ))
    (hsum : ∑' n, μ (s n) = ⊤) :
    μ (Filter.limsup s Filter.atTop) = 1 := by
      -- Let $S_N = \sum_{n < N} \mathbf{1}_{s_n}$.
      set S : ℕ → Ω → ℝ := fun N ω => ∑ n ∈ Finset.range N, (s n).indicator (fun _ => 1) ω;
      have hS_mono : ∀ N ω, S N ω ≤ S (N + 1) ω := by
        exact fun N ω => Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => Set.indicator_nonneg ( fun _ _ => zero_le_one ) _;;
      have hS_measurable : ∀ N, Measurable (S N) := by
        exact fun N => Finset.measurable_sum _ fun n _ => Measurable.indicator measurable_const ( hmeas n );
      have hS_L2 : ∀ N, MeasureTheory.MemLp (S N) 2 μ := by
        intro N
        have hS_L2_aux : ∀ n, MeasureTheory.MemLp ((s n).indicator (fun _ => 1) : Ω → ℝ) 2 μ := by
          intro n; exact (by
          refine' MeasureTheory.MemLp.indicator _ _ <;> norm_num [ hmeas ];
          exact MeasureTheory.memLp_const _)
          skip
        generalize_proofs at *; (
        exact MeasureTheory.memLp_finset_sum _ fun n _ => hS_L2_aux n)
      generalize_proofs at *; (
      -- By `tendsto_infinity_ae_of_monotone_variance_le_expectation`, $S_N \to \infty$ almost surely.
      have hS_tendsto_infty : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => S N ω) Filter.atTop Filter.atTop := by
        apply_rules [ tendsto_infinity_ae_of_monotone_variance_le_expectation ];
        · -- By definition of $S$, we know that $\mathbb{E}[S_N] = \sum_{n=0}^{N-1} \mathbb{P}(s_n)$.
          have hS_exp : ∀ N, ∫ ω, S N ω ∂μ = ∑ n ∈ Finset.range N, (μ (s n)).toReal := by
            intro N; rw [ MeasureTheory.integral_finset_sum ] ; aesop;
            exact fun n _ => MeasureTheory.integrable_indicator_iff ( hmeas n ) |>.2 ( MeasureTheory.integrable_const _ )
          generalize_proofs at *; (
          have hS_exp_tendsto : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (μ (s n)).toReal) Filter.atTop Filter.atTop := by
            have h_sum_inf : ¬ Summable (fun n => (μ (s n)).toReal) := by
              intro h_summable
              have h_sum_finite : ∑' n, (μ (s n)) = ENNReal.ofReal (∑' n, (μ (s n)).toReal) := by
                rw [ ENNReal.ofReal_tsum_of_nonneg ] <;> aesop
                skip
              generalize_proofs at *; (
              aesop)
            exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => ENNReal.toReal_nonneg ) |>.1 h_sum_inf
          generalize_proofs at *; (
          simpa only [ hS_exp ] using hS_exp_tendsto));
        · intro N
          generalize_proofs at *; (
          have h_var_le_exp : ProbabilityTheory.variance (∑ n ∈ Finset.range N, (s n).indicator (fun _ => 1)) μ ≤ ∑ n ∈ Finset.range N, (μ (s n)).toReal := by
            convert variance_sum_indicator_le _ _ using 1
            generalize_proofs at *; (
            infer_instance);
            · exact?;
            · exact fun i hi j hj hij => hindep hij
          generalize_proofs at *; (
          convert h_var_le_exp using 1
          generalize_proofs at *; (
          congr! 1
          generalize_proofs at *; (
          exact?));
          rw [ MeasureTheory.integral_finset_sum ];
          · simp +decide [ MeasureTheory.integral_indicator ( hmeas _ ) ];
            rfl;
          · exact fun n _ => MeasureTheory.integrable_indicator_iff ( hmeas n ) |>.2 ( MeasureTheory.integrable_const _ )))
      generalize_proofs at *; (
      -- Since $S_N \to \infty$ almost surely, we have $\omega \in \limsup s_n$ for almost every $\omega$.
      have h_lim_sup : ∀ᵐ ω ∂μ, ω ∈ Filter.limsup s Filter.atTop := by
        filter_upwards [ hS_tendsto_infty ] with ω hω
        have h_lim_sup : ∀ N, ∃ n ≥ N, ω ∈ s n := by
          intro N
          by_contra h_contra
          push_neg at h_contra
          generalize_proofs at *; (
          have h_finite : ∀ n ≥ N, S n ω = S N ω := by
            intro n hn; induction hn <;> simp_all +decide [ Finset.sum_range_succ ] ;
            simp +zetaDelta at *;
            simp_all +decide [ Finset.sum_range_succ, Set.indicator_apply ]
          generalize_proofs at *; (
          exact absurd ( hω.eventually_gt_atTop ( S N ω ) ) fun h => by have := h.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ n, hn₁, hn₂ ⟩ := this.exists; linarith [ h_finite n hn₂ ] ;))
        generalize_proofs at *; (
        simp +decide [ Filter.limsup_eq_iInf_iSup_of_nat, h_lim_sup ])
      generalize_proofs at *; (
      rw [ MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ ] ; aesop;)))

end AristotleLemmas

theorem slln_necessity_statement
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds c)) :
    MeasureTheory.Integrable (X 0) μ := by
  by_contra h_not_integrable;
  -- By the Borel-Cantelli lemma, since the sum of the probabilities is infinite, the events {ω | ‖X n ω‖ > n} occur infinitely often almost surely.
  have h_borel_cantelli : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∃ n ≥ N, ‖X n ω‖ > n := by
    have h_borel_cantelli : μ (Filter.limsup (fun n => {ω | ‖X n ω‖ > n}) Filter.atTop) = 1 := by
      apply_rules [ borel_cantelli_of_pairwise_independent ];
      · exact fun n => measurableSet_lt measurable_const ( hmeas n |> Measurable.norm );
      · intro i j hij; specialize hindep hij; simp_all +decide [ ProbabilityTheory.IndepFun, ProbabilityTheory.IndepSet ] ;
        rw [ ProbabilityTheory.Kernel.indepSet_iff_measure_inter_eq_mul ] at *;
        · rw [ ProbabilityTheory.Kernel.indepFun_iff_measure_inter_preimage_eq_mul ] at hindep;
          convert hindep { x : ℝ | ( i : ℝ ) < |x| } { x : ℝ | ( j : ℝ ) < |x| } ( measurableSet_lt measurable_const ( measurable_norm ) ) ( measurableSet_lt measurable_const ( measurable_norm ) ) using 1;
        · exact measurableSet_lt measurable_const ( hmeas i |> Measurable.norm );
        · exact measurableSet_lt measurable_const ( hmeas j |> Measurable.norm );
      · convert tsum_prob_norm_gt_eq_top_of_not_integrable ( X 0 ) ( hmeas 0 ) h_not_integrable using 1;
        exact tsum_prob_norm_gt_iid_eq X hident ▸ rfl;
    simp_all +decide [ Filter.limsup_eq_iInf_iSup_of_nat ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( show μ ( ⋂ n : ℕ, ⋃ i : ℕ, ⋃ ( _ : n ≤ i ), { ω : Ω | ( i : ℝ ) < |X i ω| } )ᶜ = 0 from by rw [ MeasureTheory.measure_compl ( by exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const ( hmeas _ |> Measurable.norm ) ) ( by exact MeasureTheory.measure_ne_top _ _ ) ] ; aesop ) ] with ω hω N ; aesop;
  -- This contradicts the assumption that the sample mean converges almost surely.
  obtain ⟨c, hc⟩ := hslln
  have h_contradiction : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (X n ω : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
    filter_upwards [ hc ] with ω hω;
    have := tendsto_zero_div_of_tendsto_sum_div ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) ⁻¹ • ∑ i ∈ Finset.range n, X i ω ) Filter.atTop ( nhds c ) from hω );
    simpa [ div_eq_inv_mul ] using this;
  have h_contradiction : ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, ‖X n ω‖ ≤ n := by
    filter_upwards [ h_contradiction ] with ω hω using by rcases Metric.tendsto_atTop.mp hω 1 zero_lt_one with ⟨ N, hN ⟩ ; exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ dist_zero_right ] at this; rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ] at *; rw [ div_lt_one ( by norm_cast; linarith ) ] at *; linarith ⟩ ;
  exact absurd ( h_borel_cantelli.and h_contradiction ) ( by intro H; obtain ⟨ ω, hω₁, hω₂ ⟩ := H.exists; obtain ⟨ N, hN ⟩ := hω₂; obtain ⟨ n, hn₁, hn₂ ⟩ := hω₁ N; exact hn₂.not_le ( hN n hn₁ ) )

end LawsOfLargeNumbersOQ01