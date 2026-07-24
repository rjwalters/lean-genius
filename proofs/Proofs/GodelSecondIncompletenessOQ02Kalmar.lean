/-
  # Kalmár completeness for the box-free fragment of GL — and consistency of GL

  S19 of `godel-second-incompleteness-oq02-oq-02`: metatheory of the S8 GL
  Hilbert system (`GodelSecondIncompletenessOQ02GLSyntax`), fully
  constructive, with no imports beyond the GL files themselves (no Mathlib —
  like S8/S18).

  ## What is proved

  Boolean semantics `eval v` (atoms by `v`, `⊥ ↦ false`, `→` material,
  `□ ↦ true` — the one-world Kripke model with no successors) gives:

  * **Soundness** (`eval_of_GL_proves`): every GL theorem evaluates true
    under every valuation.  All five constructors — including K and Löb —
    are validated because `□` is constantly true on a world with no
    successors.
  * **`GL_consistent : ¬ GL_proves ⊥`** — machine-checked consistency of the
    S8 system — and `GL_proves_no_atom`.
  * **Kalmár completeness** (`kalmar`): every **box-free** boolean tautology
    is GL-derivable.  The classical Kalmár argument, run constructively
    through a hypothesis-context layer:
    - `PDeriv Γ φ` — derivability from a finite hypothesis list (cited GL
      theorems + modus ponens), with weakening;
    - the **deduction theorem** (`PDeriv.deduction`), by induction on the
      derivation, using only the k1/k2 schemas;
    - classical glue derived inside the Hilbert system via the deduction
      theorem: `dne` (`⊢ ¬¬p → p`, via k3) and
      `case_split : ⊢ (χ→φ) → ((χ→⊥)→φ) → φ`;
    - the Kalmár main lemma (`kalmar_main`): under the literal context of a
      valuation `v`, every box-free `φ` derives its own literal `lit v φ`;
    - atom elimination (`elim_atoms`): case-splitting on each atom via the
      updated valuations `v[a := true]` / `v[a := false]`.  The elimination
      is duplicate-tolerant (weakening absorbs repeated atoms), so no
      `Nodup`/`dedup` machinery is needed.
  * **`boxfree_characterization`**: for box-free `φ`,
    `GL_proves φ ↔ ∀ v, eval v φ = true` — the propositional fragment of GL
    is EXACTLY classical propositional logic.  Propositional obligations
    about the S8 system (the `Htaut`-style hypotheses of S16) thereby reduce
    on the GL side to truth-table checks.

  ## Relation to the recorded plan

  This is option (a) of the S18 handoff ("Kalmár completeness for the →/⊥
  GLFormula fragment"), the tractable next step after the S18 `4`-schema
  derivation.  The blocked `Hk` route (meta/object confusion; waits on the
  Σ₁ `Provable` rebuild) is untouched, per the tracker's blocked-route
  registry.

  Reference: Kalmár (1935); Boolos, *The Logic of Provability*, ch. 1.
-/
import Proofs.GodelSecondIncompletenessOQ02GLSyntax
import Proofs.GodelSecondIncompletenessOQ02GLFour

namespace GodelSecondKalmar

open GodelSecondGLSyntax GodelSecondGLFour

local infixr:55 " ⟶ " => GLFormula.impl
local prefix:75 "□" => GLFormula.box
local notation "⊥ₘ" => GLFormula.falsum

-- ============================================================
-- PART 1: boolean semantics, soundness, consistency
-- ============================================================

/-- Boolean evaluation of GL formulas: the one-world Kripke model with no
successors (`□ ↦ true`).  On the box-free fragment this is ordinary
classical truth-table semantics. -/
def eval (v : PropAtom → Bool) : GLFormula → Bool
  | .atom p => v p
  | .falsum => false
  | .impl p q => !(eval v p) || eval v q
  | .box _ => true

/-- **Soundness of GL for the boolean semantics**: every GL theorem
evaluates to `true` under every valuation.  K and Löb hold because `□` is
constantly true on a successor-free world. -/
theorem eval_of_GL_proves {φ : GLFormula} (h : GL_proves φ) (v : PropAtom → Bool) :
    eval v φ = true := by
  induction h with
  | taut hax =>
      cases hax with
      | k1 p q =>
          simp only [eval]
          cases hp : eval v p <;> cases hq : eval v q <;> rfl
      | k2 p q r =>
          simp only [eval]
          cases hp : eval v p <;> cases hq : eval v q <;> cases hr : eval v r <;> rfl
      | k3 p q =>
          simp only [eval]
          cases hp : eval v p <;> cases hq : eval v q <;> rfl
  | k p q => simp [eval]
  | lob p => simp [eval]
  | mp h₁ h₂ ih₁ ih₂ =>
      simp only [eval, ih₂, Bool.not_true, Bool.false_or] at ih₁
      exact ih₁
  | nec h ih => simp [eval]

/-- **GL is consistent**: the S8 Hilbert system does not derive `⊥`. -/
theorem GL_consistent : ¬ GL_proves ⊥ₘ := fun h => by
  simpa [eval] using eval_of_GL_proves h fun _ => true

/-- GL derives no atomic formula. -/
theorem GL_proves_no_atom (p : PropAtom) : ¬ GL_proves (.atom p) := fun h => by
  simpa [eval] using eval_of_GL_proves h fun _ => false

-- ============================================================
-- PART 2: derivability from hypotheses and the deduction theorem
-- ============================================================

/-- Derivability from a finite list of hypotheses: hypotheses, cited GL
theorems, and modus ponens.  (No necessitation under hypotheses — this is
the propositional layer, which is all Kalmár needs; cited GL theorems may
of course be modal.) -/
inductive PDeriv : List GLFormula → GLFormula → Prop where
  | hyp {Γ : List GLFormula} {φ : GLFormula} (h : φ ∈ Γ) : PDeriv Γ φ
  | thm {Γ : List GLFormula} {φ : GLFormula} (h : GL_proves φ) : PDeriv Γ φ
  | mp {Γ : List GLFormula} {φ ψ : GLFormula}
      (h₁ : PDeriv Γ (φ ⟶ ψ)) (h₂ : PDeriv Γ φ) : PDeriv Γ ψ

/-- Weakening: derivability is monotone in the hypothesis list (as a set —
duplicates and order are irrelevant). -/
theorem PDeriv.weaken {Γ Γ' : List GLFormula} {φ : GLFormula}
    (hsub : ∀ x ∈ Γ, x ∈ Γ') (h : PDeriv Γ φ) : PDeriv Γ' φ := by
  induction h with
  | hyp h => exact .hyp (hsub _ h)
  | thm h => exact .thm h
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- **The deduction theorem** for the propositional layer: from `Γ, χ ⊢ φ`
conclude `Γ ⊢ χ → φ`.  Induction on the derivation, using only k1/k2. -/
theorem PDeriv.deduction {Γ : List GLFormula} {χ φ : GLFormula}
    (h : PDeriv (χ :: Γ) φ) : PDeriv Γ (χ ⟶ φ) := by
  have key : ∀ {Δ : List GLFormula} {ψ : GLFormula}, PDeriv Δ ψ →
      Δ = χ :: Γ → PDeriv Γ (χ ⟶ ψ) := by
    intro Δ ψ hd
    induction hd with
    | hyp h =>
        rintro rfl
        rcases List.mem_cons.mp h with rfl | h
        · exact .thm (imp_id _)
        · exact .mp (.thm (ax1 _ χ)) (.hyp h)
    | thm h =>
        intro _
        exact .mp (.thm (ax1 _ χ)) (.thm h)
    | mp _ _ ih₁ ih₂ =>
        rintro rfl
        exact .mp (.mp (.thm (ax2 χ _ _)) (ih₁ rfl)) (ih₂ rfl)
  exact key h rfl

/-- Closed derivations are GL theorems. -/
theorem PDeriv.toGL {φ : GLFormula} (h : PDeriv [] φ) : GL_proves φ := by
  induction h with
  | hyp h => cases h
  | thm h => exact h
  | mp _ _ ih₁ ih₂ => exact ih₁.mp ih₂

-- ============================================================
-- PART 3: classical glue, derived via the deduction theorem
-- ============================================================

/-- Double-negation elimination `⊢ ¬¬p → p`, from the k3 schema.  Derived
inside `PDeriv` and closed by the deduction theorem. -/
theorem dne (p : GLFormula) : GL_proves (((p ⟶ ⊥ₘ) ⟶ ⊥ₘ) ⟶ p) := by
  apply PDeriv.toGL
  apply PDeriv.deduction
  -- context: [¬¬p] ⊢ p
  have hnp : PDeriv [(p ⟶ ⊥ₘ), ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] (p ⟶ ⊥ₘ) := .hyp (by simp)
  have hnnp : PDeriv [(p ⟶ ⊥ₘ), ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ) :=
    .hyp (by simp)
  have hfal : PDeriv [(p ⟶ ⊥ₘ), ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] ⊥ₘ := .mp hnnp hnp
  have hstep : PDeriv [(p ⟶ ⊥ₘ), ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] ((p ⟶ p) ⟶ ⊥ₘ) :=
    .mp (.thm (efq _)) hfal
  have hneg : PDeriv [((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] ((p ⟶ ⊥ₘ) ⟶ ((p ⟶ p) ⟶ ⊥ₘ)) :=
    hstep.deduction
  have hk3 : PDeriv [((p ⟶ ⊥ₘ) ⟶ ⊥ₘ)] ((p ⟶ p) ⟶ p) :=
    .mp (.thm (ax3 p (p ⟶ p))) hneg
  exact hk3.mp (.thm (imp_id p))

/-- The classical case split `⊢ (χ → φ) → ((χ → ⊥) → φ) → φ`, derived via
the deduction theorem and `dne`. -/
theorem case_split (χ φ : GLFormula) :
    GL_proves ((χ ⟶ φ) ⟶ ((χ ⟶ ⊥ₘ) ⟶ φ) ⟶ φ) := by
  apply PDeriv.toGL
  apply PDeriv.deduction
  apply PDeriv.deduction
  -- context: [(χ→⊥)→φ, χ→φ] ⊢ φ, via ¬¬φ and dne
  have hnχ : PDeriv [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)] (χ ⟶ ⊥ₘ) := by
    apply PDeriv.deduction
    -- context: [χ, ¬φ, (χ→⊥)→φ, χ→φ] ⊢ ⊥
    have hχ : PDeriv (χ :: [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)]) χ :=
      .hyp (by simp)
    have hχφ : PDeriv (χ :: [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)]) (χ ⟶ φ) :=
      .hyp (by simp)
    have hnφ : PDeriv (χ :: [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)]) (φ ⟶ ⊥ₘ) :=
      .hyp (by simp)
    exact .mp hnφ (.mp hχφ hχ)
  have himp : PDeriv [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)] ((χ ⟶ ⊥ₘ) ⟶ φ) :=
    .hyp (by simp)
  have hnφ' : PDeriv [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)] (φ ⟶ ⊥ₘ) :=
    .hyp (by simp)
  have hbot : PDeriv [(φ ⟶ ⊥ₘ), ((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)] ⊥ₘ :=
    .mp hnφ' (.mp himp hnχ)
  have hnn : PDeriv [((χ ⟶ ⊥ₘ) ⟶ φ), (χ ⟶ φ)] ((φ ⟶ ⊥ₘ) ⟶ ⊥ₘ) :=
    hbot.deduction
  exact PDeriv.mp (.thm (dne φ)) hnn

-- ============================================================
-- PART 4: the Kalmár argument
-- ============================================================

/-- Box-freeness: the purely propositional (`→`/`⊥`/atoms) fragment. -/
def BoxFree : GLFormula → Prop
  | .atom _ => True
  | .falsum => True
  | .impl p q => BoxFree p ∧ BoxFree q
  | .box _ => False

/-- The atoms occurring in a formula (with multiplicity — harmless). -/
def atoms : GLFormula → List PropAtom
  | .atom p => [p]
  | .falsum => []
  | .impl p q => atoms p ++ atoms q
  | .box _ => []

/-- The literal of `φ` under `v`: `φ` itself if it evaluates true, else `¬φ`. -/
def lit (v : PropAtom → Bool) (φ : GLFormula) : GLFormula :=
  if eval v φ then φ else φ ⟶ ⊥ₘ

/-- The literal of an atom under `v`. -/
def litAtom (v : PropAtom → Bool) (a : PropAtom) : GLFormula :=
  if v a then .atom a else .atom a ⟶ ⊥ₘ

/-- **Kalmár's main lemma**: under any hypothesis list containing the
`v`-literals of its atoms, a box-free formula derives its own `v`-literal. -/
theorem kalmar_main (v : PropAtom → Bool) {φ : GLFormula} :
    BoxFree φ → ∀ {Γ : List GLFormula},
      (∀ a ∈ atoms φ, litAtom v a ∈ Γ) → PDeriv Γ (lit v φ) := by
  induction φ with
  | atom p =>
      intro _ Γ hΓ
      have hmem : litAtom v p ∈ Γ := hΓ p (by simp [atoms])
      have heq : lit v (.atom p) = litAtom v p := rfl
      rw [heq]
      exact .hyp hmem
  | falsum =>
      intro _ Γ _
      have heq : lit v ⊥ₘ = (⊥ₘ ⟶ ⊥ₘ) := by simp [lit, eval]
      rw [heq]
      exact .thm (imp_id ⊥ₘ)
  | impl p q ihp ihq =>
      intro hbf Γ hΓ
      obtain ⟨hbp, hbq⟩ := hbf
      have hΓp : ∀ a ∈ atoms p, litAtom v a ∈ Γ := fun a ha =>
        hΓ a (by simp [atoms, ha])
      have hΓq : ∀ a ∈ atoms q, litAtom v a ∈ Γ := fun a ha =>
        hΓ a (by simp [atoms, ha])
      have hp := ihp hbp hΓp
      have hq := ihq hbq hΓq
      cases hevq : eval v q with
      | true =>
          -- q true: `p → q` from `q` by k1
          have hq' : PDeriv Γ q := by simpa [lit, hevq] using hq
          have heq : lit v (p ⟶ q) = (p ⟶ q) := by
            simp [lit, eval, hevq]
          rw [heq]
          exact .mp (.thm (ax1 q p)) hq'
      | false =>
          cases hevp : eval v p with
          | false =>
              -- p false: `p → q` from `¬p` by ex falso
              have hp' : PDeriv Γ (p ⟶ ⊥ₘ) := by simpa [lit, hevp] using hp
              have heq : lit v (p ⟶ q) = (p ⟶ q) := by
                simp [lit, eval, hevp]
              rw [heq]
              have hbot : PDeriv (p :: Γ) ⊥ₘ :=
                .mp (hp'.weaken fun x hx => List.mem_cons_of_mem _ hx)
                  (.hyp (by simp))
              exact PDeriv.deduction (.mp (.thm (efq q)) hbot)
          | true =>
              -- p true, q false: `¬(p → q)`
              have hp' : PDeriv Γ p := by simpa [lit, hevp] using hp
              have hq' : PDeriv Γ (q ⟶ ⊥ₘ) := by simpa [lit, hevq] using hq
              have heq : lit v (p ⟶ q) = ((p ⟶ q) ⟶ ⊥ₘ) := by
                simp [lit, eval, hevp, hevq]
              rw [heq]
              have hw : ∀ x ∈ Γ, x ∈ (p ⟶ q) :: Γ := fun x hx =>
                List.mem_cons_of_mem _ hx
              have hhead : PDeriv ((p ⟶ q) :: Γ) (p ⟶ q) := .hyp (by simp)
              have hbot : PDeriv ((p ⟶ q) :: Γ) ⊥ₘ :=
                .mp (hq'.weaken hw) (.mp hhead (hp'.weaken hw))
              exact hbot.deduction
  | box p ih =>
      intro hbf
      simp [BoxFree] at hbf

/-- Atom elimination: if `φ` is derivable from the `v`-literal context of a
list of atoms for EVERY valuation `v`, it is a GL theorem.  Case-split on
each atom in turn via `case_split`; duplicate atoms are absorbed by
weakening. -/
theorem elim_atoms (φ : GLFormula) :
    ∀ L : List PropAtom, (∀ v, PDeriv (L.map (litAtom v)) φ) → GL_proves φ := by
  intro L
  induction L with
  | nil =>
      intro h
      exact (h fun _ => true).toGL
  | cons a L ih =>
      intro h
      apply ih
      intro v
      have h₁ := h fun x => if x = a then true else v x
      have h₂ := h fun x => if x = a then false else v x
      -- weaken both into a clean head over the untouched tail context
      have hmap₁ : ∀ b ∈ a :: L,
          litAtom (fun x => if x = a then true else v x) b
            ∈ (GLFormula.atom a) :: L.map (litAtom v) := by
        intro b hb
        by_cases hba : b = a
        · subst hba
          have heq : litAtom (fun x => if x = b then true else v x) b
              = .atom b := by simp [litAtom]
          rw [heq]
          exact List.mem_cons.mpr (Or.inl rfl)
        · have heq : litAtom (fun x => if x = a then true else v x) b
              = litAtom v b := by simp [litAtom, hba]
          rw [heq]
          rcases List.mem_cons.mp hb with rfl | hbL
          · exact absurd rfl hba
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨b, hbL, rfl⟩))
      have hmap₂ : ∀ b ∈ a :: L,
          litAtom (fun x => if x = a then false else v x) b
            ∈ (GLFormula.atom a ⟶ ⊥ₘ) :: L.map (litAtom v) := by
        intro b hb
        by_cases hba : b = a
        · subst hba
          have heq : litAtom (fun x => if x = b then false else v x) b
              = (.atom b ⟶ ⊥ₘ) := by simp [litAtom]
          rw [heq]
          exact List.mem_cons.mpr (Or.inl rfl)
        · have heq : litAtom (fun x => if x = a then false else v x) b
              = litAtom v b := by simp [litAtom, hba]
          rw [heq]
          rcases List.mem_cons.mp hb with rfl | hbL
          · exact absurd rfl hba
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨b, hbL, rfl⟩))
      have hw₁ : PDeriv ((GLFormula.atom a) :: L.map (litAtom v)) φ := by
        refine h₁.weaken ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
        exact hmap₁ b hb
      have hw₂ : PDeriv ((GLFormula.atom a ⟶ ⊥ₘ) :: L.map (litAtom v)) φ := by
        refine h₂.weaken ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
        exact hmap₂ b hb
      exact PDeriv.mp
        (PDeriv.mp (.thm (case_split (.atom a) φ)) hw₁.deduction)
        hw₂.deduction

/-- **Kalmár completeness for the box-free fragment**: every box-free
boolean tautology is a GL theorem. -/
theorem kalmar {φ : GLFormula} (hbf : BoxFree φ)
    (htaut : ∀ v, eval v φ = true) : GL_proves φ := by
  apply elim_atoms φ (atoms φ)
  intro v
  have hlit := kalmar_main v hbf
    (Γ := (atoms φ).map (litAtom v)) fun a ha => List.mem_map.mpr ⟨a, ha, rfl⟩
  simpa [lit, htaut v] using hlit

/-- **The box-free fragment of GL is exactly classical propositional
logic**: for box-free `φ`, derivability coincides with being a boolean
tautology.  (Soundness needs no box-freeness; completeness is Kalmár.) -/
theorem boxfree_characterization {φ : GLFormula} (hbf : BoxFree φ) :
    GL_proves φ ↔ ∀ v, eval v φ = true :=
  ⟨eval_of_GL_proves, kalmar hbf⟩

#check @eval_of_GL_proves
#check @GL_consistent
#check @PDeriv.deduction
#check @kalmar
#check @boxfree_characterization

end GodelSecondKalmar
