import Proofs.GodelSecondIncompletenessOQ02GLSyntax
import Proofs.GodelSecondIncompletenessOQ02GLFour
import Proofs.GodelSecondIncompletenessOQ02Kalmar

/-!
# GL finite Lindenbaum layer — S22a: FMP groundwork for Segerberg completeness

S22a of `godel-second-incompleteness-oq02-oq-02` (Solovay's arithmetical
completeness for GL). The mapped S22 goal is **full GL decidability via the
finite model property** (Segerberg filtration / canonical finite model over
the S20 `Kripke.lean` frames). This file delivers the world-construction
layer that every canonical-model session needs, and nothing speculative
beyond it:

* **Finite consistency calculus** over the S19 hypothesis layer `PDeriv`:
  `Consistent Γ := ¬ PDeriv Γ ⊥`, monotonicity (`Consistent.of_subset`),
  the deduction-theorem bridge `deriv_neg_of_inconsistent`, the classical
  splitting lemma `consistent_cons_or`, and `consistent_cons_of_deriv`.
* **Subformula closure**: `subf φ` (a finite list), `self_mem_subf`, and
  transitivity `subf_closed` — the closure sets over which canonical worlds
  live.
* **Finite Lindenbaum lemma** (`lindenbaum`): every consistent list of
  formulas inside a closure list `L` extends to a subset of `L` that is
  *maximal consistent in `L`* (`MaximalIn`). The extension is the classical
  one-pass sweep `extend` (add each candidate iff consistency survives),
  so no Zorn/Mathlib machinery is needed — everything stays Lean-core.
* **Maximal-set toolkit** — the exact lemmas the future truth lemma
  consumes: derivability closure (`MaximalIn.mem_of_deriv`,
  `MaximalIn.deriv_iff_mem`), negation completeness relative to `L`
  (`MaximalIn.neg_deriv_of_not_mem`, `MaximalIn.not_mem_of_neg_deriv`),
  `MaximalIn.falsum_not_mem`, and the implication membership
  characterization `MaximalIn.impl_mem_iff` (the `→`-case of the truth
  lemma, discharged here once and for all).
* **Root-world capstone** (`exists_root_world`): if `GL ⊬ φ` then there is
  a maximal consistent subset of `subf (¬φ)` containing `¬φ` — the root of
  the future canonical countermodel.

## What this is NOT

Completeness itself (the canonical accessibility relation, the box case of
the truth lemma via Löb's axiom + the S18 `4` schema, and the resulting
FMP/decidability) is **not** claimed here — that is the next stage (S22b),
which imports this file.

## Design notes

* Mathlib-free like S8/S18/S19/S20/S21: the only classical ingredients are
  `Classical.byContradiction` and the `Classical.propDecidable` instance
  (scoped, used only inside `extend`), so the file's axiom footprint is the
  foundational trio only. 0 sorries, 0 `axiom` declarations.
* `Consistent` is defined for **lists** (the ambient hypothesis-context
  type of S19's `PDeriv`), with all set-like reasoning done through
  membership — duplicates and order are irrelevant by `PDeriv.weaken`.

## References

- Boolos, G. (1993). *The Logic of Provability*. Cambridge University
  Press, Ch. 5 (the finite canonical model for GL).
- Segerberg, K. (1971). *An Essay in Classical Modal Logic*. Uppsala.
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer, §2.
-/

namespace GodelSecondLindenbaum

open GodelSecondGLSyntax GodelSecondGLFour GodelSecondKalmar

local infixr:55 " ⟶ " => GLFormula.impl
local prefix:75 "□" => GLFormula.box
local notation "⊥ₘ" => GLFormula.falsum

-- ============================================================
-- PART 1: the finite consistency calculus
-- ============================================================

/-- A finite hypothesis list is **consistent** when it does not derive `⊥`
in the S19 propositional layer (hypotheses + cited GL theorems + mp). -/
def Consistent (Γ : List GLFormula) : Prop := ¬ PDeriv Γ ⊥ₘ

/-- Consistency is antitone in the hypothesis list (as a set). -/
theorem Consistent.of_subset {Γ' Γ : List GLFormula} (h : Consistent Γ')
    (hsub : ∀ x ∈ Γ, x ∈ Γ') : Consistent Γ := fun hd => h (hd.weaken hsub)

/-- If adjoining `ψ` breaks consistency, the context refutes `ψ`.
The deduction-theorem bridge used throughout the maximality toolkit. -/
theorem deriv_neg_of_inconsistent {Γ : List GLFormula} {ψ : GLFormula}
    (h : ¬ Consistent (ψ :: Γ)) : PDeriv Γ (ψ ⟶ ⊥ₘ) :=
  (Classical.byContradiction h).deduction

/-- Classical splitting: a consistent context stays consistent after
adjoining `ψ` or after adjoining `¬ψ` (at least one of the two). -/
theorem consistent_cons_or {Γ : List GLFormula} (h : Consistent Γ)
    (ψ : GLFormula) :
    Consistent (ψ :: Γ) ∨ Consistent ((ψ ⟶ ⊥ₘ) :: Γ) :=
  Classical.byContradiction fun hcon =>
    h ((deriv_neg_of_inconsistent fun hc => hcon (Or.inr hc)).mp
       (deriv_neg_of_inconsistent fun hc => hcon (Or.inl hc)))

/-- Adjoining a derivable formula preserves consistency. -/
theorem consistent_cons_of_deriv {Γ : List GLFormula} {ψ : GLFormula}
    (hc : Consistent Γ) (hd : PDeriv Γ ψ) : Consistent (ψ :: Γ) :=
  fun hbot => hc (hbot.deduction.mp hd)

-- ============================================================
-- PART 2: subformula closure
-- ============================================================

/-- The (finite) list of subformulas of a GL formula, including the
formula itself. Canonical worlds live inside `subf` of the target. -/
def subf : GLFormula → List GLFormula
  | .atom p   => [.atom p]
  | .falsum   => [.falsum]
  | .impl p q => .impl p q :: (subf p ++ subf q)
  | .box p    => .box p :: subf p

theorem self_mem_subf (φ : GLFormula) : φ ∈ subf φ := by
  cases φ <;> simp [subf]

/-- Subformula closure is transitive: `subf φ` is closed under `subf`. -/
theorem subf_closed : ∀ (φ ψ : GLFormula), ψ ∈ subf φ →
    ∀ χ ∈ subf ψ, χ ∈ subf φ := by
  intro φ
  induction φ with
  | atom p =>
    intro ψ hψ χ hχ
    simp only [subf, List.mem_singleton] at hψ
    subst hψ; exact hχ
  | falsum =>
    intro ψ hψ χ hχ
    simp only [subf, List.mem_singleton] at hψ
    subst hψ; exact hχ
  | impl p q ihp ihq =>
    intro ψ hψ χ hχ
    simp only [subf, List.mem_cons, List.mem_append] at hψ
    rcases hψ with rfl | hp | hq
    · exact hχ
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihp _ hp _ hχ)))
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihq _ hq _ hχ)))
  | box p ih =>
    intro ψ hψ χ hχ
    simp only [subf, List.mem_cons] at hψ
    rcases hψ with rfl | hp
    · exact hχ
    · exact List.mem_cons_of_mem _ (ih _ hp _ hχ)

-- ============================================================
-- PART 3: the finite Lindenbaum extension
-- ============================================================

/-- One-pass Lindenbaum sweep: walk the closure list `L`, adjoining each
candidate formula to the accumulating context iff consistency survives.
Classical (`Classical.propDecidable`) but requires no choice beyond it —
the closure is a finite list, so no Zorn is needed. -/
open Classical in
noncomputable def extend : List GLFormula → List GLFormula → List GLFormula
  | Γ, [] => Γ
  | Γ, ψ :: L => if Consistent (ψ :: Γ) then extend (ψ :: Γ) L else extend Γ L

theorem extend_nil (Γ : List GLFormula) : extend Γ [] = Γ := by
  simp only [extend]

theorem extend_cons_pos {Γ L : List GLFormula} {ψ : GLFormula}
    (h : Consistent (ψ :: Γ)) : extend Γ (ψ :: L) = extend (ψ :: Γ) L := by
  simp only [extend]
  rw [if_pos h]

theorem extend_cons_neg {Γ L : List GLFormula} {ψ : GLFormula}
    (h : ¬ Consistent (ψ :: Γ)) : extend Γ (ψ :: L) = extend Γ L := by
  simp only [extend]
  rw [if_neg h]

/-- The sweep preserves consistency. -/
theorem consistent_extend : ∀ (L : List GLFormula) {Γ : List GLFormula},
    Consistent Γ → Consistent (extend Γ L) := by
  intro L
  induction L with
  | nil => intro Γ h; rw [extend_nil]; exact h
  | cons ψ L ih =>
    intro Γ h
    by_cases hc : Consistent (ψ :: Γ)
    · rw [extend_cons_pos hc]; exact ih hc
    · rw [extend_cons_neg hc]; exact ih h

/-- The sweep only ever grows the context. -/
theorem subset_extend : ∀ (L : List GLFormula) {Γ : List GLFormula}
    {x : GLFormula}, x ∈ Γ → x ∈ extend Γ L := by
  intro L
  induction L with
  | nil => intro Γ x hx; rw [extend_nil]; exact hx
  | cons ψ L ih =>
    intro Γ x hx
    by_cases hc : Consistent (ψ :: Γ)
    · rw [extend_cons_pos hc]; exact ih (List.mem_cons_of_mem _ hx)
    · rw [extend_cons_neg hc]; exact ih hx

/-- Everything in the sweep's output came from the seed or the closure. -/
theorem mem_or_of_mem_extend : ∀ (L : List GLFormula) {Γ : List GLFormula}
    {x : GLFormula}, x ∈ extend Γ L → x ∈ Γ ∨ x ∈ L := by
  intro L
  induction L with
  | nil => intro Γ x hx; rw [extend_nil] at hx; exact Or.inl hx
  | cons ψ L ih =>
    intro Γ x hx
    by_cases hc : Consistent (ψ :: Γ)
    · rw [extend_cons_pos hc] at hx
      rcases ih hx with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [extend_cons_neg hc] at hx
      rcases ih hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Maximality of the sweep: any closure formula that could still be
consistently adjoined to the *final* context was in fact adjoined. (If it
was skipped, its stage context was a subset of the final one, so skipping
was forced by inconsistency — which weakening transports to the end.) -/
theorem mem_extend_of_consistent : ∀ (L : List GLFormula) {Γ : List GLFormula}
    {ψ : GLFormula}, ψ ∈ L → Consistent (ψ :: extend Γ L) →
    ψ ∈ extend Γ L := by
  intro L
  induction L with
  | nil => intro Γ ψ h _; exact absurd h (by simp)
  | cons ψ' L ih =>
    intro Γ ψ hmem hcons
    by_cases hc : Consistent (ψ' :: Γ)
    · rw [extend_cons_pos hc] at hcons ⊢
      rcases List.mem_cons.mp hmem with rfl | hL
      · exact subset_extend L (List.mem_cons.mpr (Or.inl rfl))
      · exact ih hL hcons
    · rw [extend_cons_neg hc] at hcons ⊢
      rcases List.mem_cons.mp hmem with rfl | hL
      · refine absurd (hcons.of_subset fun x hx => ?_) hc
        rcases List.mem_cons.mp hx with rfl | hxΓ
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (subset_extend L hxΓ)
      · exact ih hL hcons

-- ============================================================
-- PART 4: maximal consistent subsets of a closure
-- ============================================================

/-- `Δ` is a **maximal consistent subset of `L`**: consistent, contained in
`L`, and containing every member of `L` it could consistently absorb.
These are the worlds of the future canonical model. -/
structure MaximalIn (L Δ : List GLFormula) : Prop where
  consistent : Consistent Δ
  subset : ∀ ψ ∈ Δ, ψ ∈ L
  maximal : ∀ ψ ∈ L, Consistent (ψ :: Δ) → ψ ∈ Δ

/-- **Finite Lindenbaum lemma**: every consistent list inside a closure
list `L` extends to a maximal consistent subset of `L`. -/
theorem lindenbaum {Γ L : List GLFormula} (hΓL : ∀ x ∈ Γ, x ∈ L)
    (hc : Consistent Γ) :
    ∃ Δ, MaximalIn L Δ ∧ ∀ x ∈ Γ, x ∈ Δ := by
  refine ⟨extend Γ L, ⟨consistent_extend L hc, ?_, fun ψ hψ => mem_extend_of_consistent L hψ⟩,
    fun x hx => subset_extend L hx⟩
  intro ψ hψ
  rcases mem_or_of_mem_extend L hψ with h | h
  · exact hΓL _ h
  · exact h

/-- Derivability closure: a maximal set contains every closure formula it
derives. -/
theorem MaximalIn.mem_of_deriv {L Δ : List GLFormula} (h : MaximalIn L Δ)
    {ψ : GLFormula} (hψL : ψ ∈ L) (hd : PDeriv Δ ψ) : ψ ∈ Δ :=
  h.maximal ψ hψL (consistent_cons_of_deriv h.consistent hd)

/-- For closure formulas, membership and derivability coincide. -/
theorem MaximalIn.deriv_iff_mem {L Δ : List GLFormula} (h : MaximalIn L Δ)
    {ψ : GLFormula} (hψL : ψ ∈ L) : PDeriv Δ ψ ↔ ψ ∈ Δ :=
  ⟨h.mem_of_deriv hψL, fun hm => .hyp hm⟩

/-- Negation completeness relative to the closure: a maximal set refutes
every closure formula it omits. -/
theorem MaximalIn.neg_deriv_of_not_mem {L Δ : List GLFormula}
    (h : MaximalIn L Δ) {ψ : GLFormula} (hψL : ψ ∈ L) (hn : ψ ∉ Δ) :
    PDeriv Δ (ψ ⟶ ⊥ₘ) :=
  deriv_neg_of_inconsistent fun hc => hn (h.maximal ψ hψL hc)

/-- Conversely, a refuted formula cannot be a member. -/
theorem MaximalIn.not_mem_of_neg_deriv {L Δ : List GLFormula}
    (h : MaximalIn L Δ) {ψ : GLFormula} (hd : PDeriv Δ (ψ ⟶ ⊥ₘ)) : ψ ∉ Δ :=
  fun hm => h.consistent (hd.mp (.hyp hm))

/-- `⊥` never belongs to a maximal consistent set. -/
theorem MaximalIn.falsum_not_mem {L Δ : List GLFormula} (h : MaximalIn L Δ) :
    ⊥ₘ ∉ Δ := fun hm => h.consistent (.hyp hm)

/-- **Implication membership characterization** — the `→`-case of the
future truth lemma: for closure formulas, `p ⟶ q ∈ Δ` iff membership of
`p` implies membership of `q`. Forward: modus ponens + derivability
closure. Backward: case on `p ∈ Δ` — either lift `q` by `k1`, or refute
`p` and use ex falso under the deduction theorem. -/
theorem MaximalIn.impl_mem_iff {L Δ : List GLFormula} (h : MaximalIn L Δ)
    {p q : GLFormula} (hpq : (p ⟶ q) ∈ L) (hpL : p ∈ L) (hqL : q ∈ L) :
    (p ⟶ q) ∈ Δ ↔ (p ∈ Δ → q ∈ Δ) := by
  constructor
  · intro hmem hp
    exact h.mem_of_deriv hqL (PDeriv.mp (.hyp hmem) (.hyp hp))
  · intro himp
    by_cases hp : p ∈ Δ
    · exact h.mem_of_deriv hpq (PDeriv.mp (.thm (ax1 q p)) (.hyp (himp hp)))
    · have hnp : PDeriv Δ (p ⟶ ⊥ₘ) := h.neg_deriv_of_not_mem hpL hp
      have hbot : PDeriv (p :: Δ) ⊥ₘ :=
        .mp (hnp.weaken fun x hx => List.mem_cons_of_mem _ hx)
          (.hyp (List.mem_cons.mpr (Or.inl rfl)))
      exact h.mem_of_deriv hpq (PDeriv.deduction (.mp (.thm (efq q)) hbot))

-- ============================================================
-- PART 5: the root world of a countermodel
-- ============================================================

/-- If `GL ⊬ φ` then `{¬φ}` is consistent: a `PDeriv`-refutation of `¬φ`
would close (deduction theorem) to a GL proof of `¬¬φ`, whence `φ` by
double-negation elimination. -/
theorem consistent_singleton_neg {φ : GLFormula} (h : ¬ GL_proves φ) :
    Consistent [φ ⟶ ⊥ₘ] := fun hd =>
  h (GL_proves.mp (dne φ) hd.deduction.toGL)

/-- **Root-world existence**: every GL-unprovable formula `φ` admits a
maximal consistent subset of `subf (¬φ)` containing `¬φ` — the root of the
future canonical countermodel for `φ`. -/
theorem exists_root_world {φ : GLFormula} (h : ¬ GL_proves φ) :
    ∃ Δ, MaximalIn (subf (φ ⟶ ⊥ₘ)) Δ ∧ (φ ⟶ ⊥ₘ) ∈ Δ := by
  have hseed : ∀ x ∈ [φ ⟶ ⊥ₘ], x ∈ subf (φ ⟶ ⊥ₘ) := by
    intro x hx
    have hx' : x = (φ ⟶ ⊥ₘ) := by simpa using hx
    rw [hx']
    exact self_mem_subf _
  obtain ⟨Δ, hmax, hsub⟩ := lindenbaum hseed (consistent_singleton_neg h)
  exact ⟨Δ, hmax, hsub _ (by simp)⟩

#check @lindenbaum
#check @MaximalIn.impl_mem_iff
#check @exists_root_world

end GodelSecondLindenbaum
