/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2f46a68b-3f4e-4af2-952a-28a2a86a1202

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem elemSymmA_succ_castSucc {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) :
    elemSymmA (k + 1) x =
    elemSymmA (k + 1) (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymmA k (x ∘ Fin.castSucc)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
  Aristotle targets for amgm-inequality-oq-02 (Maclaurin Inequalities)
  Routine supporting lemmas for automated proof search.
  See AmgmInequalityOQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Maclaurin chain M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ)
  - NOT the axiomatized deep results (Newton log-concavity, Maclaurin step)
  - Known classical results provable from Mathlib

  Main target: h_binom — the binomial expansion identity
    (∑ i : Fin n, x i) ^ 2 = ∑ i, (x i) ^ 2 + 2 * elemSymm 2 x

  This is the ONLY remaining sorry in AmgmInequalityOQ02.lean.
  Once proved, it closes `maclaurin_sq_m1_ge_m2_general` completely
  (the rest of that proof is already written and compiles).

  Proof strategy for h_binom:
  - Induction on n using the elemSymm recurrence
  - elemSymm 2 (x ∘ Fin.castSucc ++ [a]) = elemSymm 2 (x ∘ Fin.castSucc) + a * elemSymm 1 (x ∘ Fin.castSucc)
  - Base: n=0 trivial; n=1 trivial (no 2-element subsets)
  - Step: (S'+a)² = S'² + 2S'a + a² = (S₂'+2e₂') + 2S'a + a² = (S₂'+a²) + 2(e₂'+aS')
-/
import Mathlib


import Batteries.Tactic.GeneralizeProofs

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option pp.fullNames true
set_option pp.structureInstances true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option linter.all false

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
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

open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
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

open Finset Real

noncomputable def elemSymmA {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, x i

/-- e₀ = 1 (empty product) -/
theorem elemSymmA_zero {n : ℕ} (x : Fin n → ℝ) : elemSymmA 0 x = 1 := by
  simp [elemSymmA, powersetCard_zero]

/-- e₁ = ∑ xᵢ -/
theorem elemSymmA_one {n : ℕ} (x : Fin n → ℝ) : elemSymmA 1 x = ∑ i, x i := by
  simp [elemSymmA, powersetCard_one, sum_map, prod_singleton]

/-- Recurrence: eₖ₊₁(x₀,...,xₙ) = eₖ₊₁(x₀,...,xₙ₋₁) + xₙ · eₖ(x₀,...,xₙ₋₁)
    This is the fundamental recurrence for elementary symmetric polynomials. -/
theorem elemSymmA_succ_castSucc {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) :
    elemSymmA (k + 1) x =
    elemSymmA (k + 1) (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymmA k (x ∘ Fin.castSucc) := by
  unfold elemSymmA;
  have h_split : Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin (n + 1))) = Finset.image (fun s => Finset.image (fun i => Fin.castSucc i) s) (Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin n))) ∪ Finset.image (fun s => Finset.image (fun i => Fin.castSucc i) s ∪ {Fin.last n}) (Finset.powersetCard k (Finset.univ : Finset (Fin n))) := by
    ext s
    simp [Finset.mem_union, Finset.mem_image];
    constructor <;> intro hs
    all_goals generalize_proofs at *;
    · by_cases h : Fin.last n ∈ s;
      · refine' Or.inr ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ s, _, _ ⟩;
        · have h_sum : ∑ i : Fin (n + 1), (if i ∈ s then 1 else 0) = k + 1 := by
            aesop;
          rw [ Fin.sum_univ_castSucc ] at h_sum ; aesop;
        · ext i; cases i using Fin.lastCases <;> aesop;
      · refine' Or.inl ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ s, _, _ ⟩;
        · rw [ ← hs, Finset.card_filter ];
          rw [ Finset.card_eq_sum_ones, eq_comm ];
          rw [ ← Finset.sum_filter ];
          refine' Finset.sum_bij ( fun i hi => ⟨ i.val, by
            exact lt_of_le_of_ne ( Nat.le_of_lt_succ i.2 ) fun con => h <| by convert hi; aesop; ⟩ ) _ _ _ _ <;> simp_all +decide [ Fin.ext_iff ];
          exact fun b hb => ⟨ _, hb, rfl ⟩;
        · -- To prove equality of finite sets, we show each set is a subset of the other.
          apply Finset.ext
          intro y
          simp [Finset.mem_image];
          exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun hy => by cases y using Fin.lastCases <;> aesop ⟩;
    · rcases hs with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp +decide [ Finset.card_image_of_injective, Function.Injective, ha ];
  rw [ h_split, Finset.sum_union, Finset.sum_image, Finset.sum_image ];
  · simp +decide [ Finset.prod_union, Finset.prod_singleton, mul_comm, Finset.mul_sum _ _ _ ];
  · intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff ] ;
    intro a; specialize h_eq ( Fin.castSucc a ) ; aesop;
  · intro s hs t ht h_eq; ext i; replace h_eq := Finset.ext_iff.mp h_eq ( Fin.castSucc i ) ; aesop;
  · norm_num [ Finset.disjoint_right ];
    intro a ha b hb; intro H; replace H := Finset.ext_iff.mp H ( Fin.last n ) ; aesop;

-- follows from Finset.powersetCard_succ_insert applied to Fin.last n ∉ image Fin.castSucc

/-- elemSymm 2 of n+1 variables decomposes as:
    e₂(x₀,...,xₙ) = e₂(x₀,...,xₙ₋₁) + xₙ · (∑ᵢ xᵢ) -/
theorem elemSymmA_two_succ {n : ℕ} (x : Fin (n + 1) → ℝ) :
    elemSymmA 2 x =
    elemSymmA 2 (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymmA 1 (x ∘ Fin.castSucc) := by
  exact elemSymmA_succ_castSucc 1 x

/-- The key binomial identity: (∑xᵢ)² = ∑xᵢ² + 2·e₂
    This is the MAIN target for Aristotle to close. -/
theorem sq_sum_eq_sum_sq_add_two_esymm {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 = ∑ i : Fin n, (x i) ^ 2 + 2 * elemSymmA 2 x := by
  induction n with
  | zero =>
    have h : elemSymmA 2 x = 0 := by
      simp only [elemSymmA]
      apply Finset.sum_eq_zero; intro s hs
      have hmem := Finset.mem_powersetCard.mp hs
      have huniv : (univ : Finset (Fin 0)).card = 0 := by simp
      have hle : s.card ≤ 0 := (Finset.card_le_card hmem.1).trans_eq huniv
      omega
    simp [h]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, elemSymmA_two_succ, elemSymmA_one]
    have hih := ih (x ∘ Fin.castSucc)
    simp only [Function.comp_apply] at hih ⊢
    nlinarith [hih, sq_nonneg (∑ i : Fin k, x (Fin.castSucc i)),
               sq_nonneg (x (Fin.last k))]

/-- The Cauchy-Schwarz inequality for finite sums: n·∑xᵢ² ≥ (∑xᵢ)² -/
theorem cauchy_schwarz_sum_A {n : ℕ} (x : Fin n → ℝ) :
    (n : ℝ) * ∑ i : Fin n, (x i) ^ 2 ≥ (∑ i : Fin n, x i) ^ 2 := by
  have h_nn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 =
      2 * ((n : ℝ) * ∑ i, (x i) ^ 2 - (∑ i, x i) ^ 2) := by
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib]
    have h1 : ∑ i : Fin n, ∑ _j : Fin n, (x i) ^ 2 = (n : ℝ) * ∑ i, (x i) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h2 : ∑ _i : Fin n, ∑ j : Fin n, (x j) ^ 2 = (n : ℝ) * ∑ j, (x j) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h3 : ∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j = 2 * (∑ i, x i) ^ 2 := by
      rw [sq, sum_mul]; simp_rw [mul_sum]; congr 1; ext i; ring
    rw [h1, h2, h3]; ring
  linarith
