import Proofs.GodelSecondIncompletenessOQ02GLSyntax
import Proofs.GodelSecondIncompletenessOQ02GLFour
import Proofs.GodelSecondIncompletenessOQ02Kalmar
import Proofs.GodelSecondIncompletenessOQ02Lindenbaum
import Proofs.GodelSecondIncompletenessOQ02Kripke

/-!
# GL canonical finite model — S22b: Segerberg completeness

S22b of `godel-second-incompleteness-oq02-oq-02` (Solovay's arithmetical
completeness for GL). S22a (`Lindenbaum.lean`) built the world-construction
layer: maximal consistent subsets of a finite closure list, with the
implication case of the truth lemma discharged once and for all. This file
finishes the modal completeness theorem, Boolos *The Logic of Provability*
Ch. 5:

* **Curried premise lists** (`imps`): `imps [x₁,…,xₙ] B = x₁ ⟶ ⋯ ⟶ xₙ ⟶ B`.
  Working with curried implications instead of a defined list conjunction
  keeps every step inside the S18 propositional toolkit: closing a `PDeriv`
  derivation into a GL theorem (`imps_of_pderiv`), boxing it premise-wise
  through the `K` axiom (`box_imps`), and re-discharging the boxed premises
  against a world (`pderiv_imps_discharge`).
* **The Löb step** (`consistent_lob_seed`): if `□p ∉ Δ` for a world `Δ`,
  then `{¬p, □p} ∪ {q, □q : □q ∈ Δ}` is consistent. An inconsistency would
  yield `GL ⊢ q₁ ⟶ □q₁ ⟶ ⋯ ⟶ (□p ⟶ p)`; necessitation, `K`-distribution
  (`box_imps`), **Löb's axiom** at the tail, the S18 `4` schema `□q ⟶ □□q`
  on the premises, and derivability closure of `Δ` force `□p ∈ Δ`. This is
  the box case of the truth lemma, and the only place Löb is used.
* **Negation-augmented closure** (`negClosure φ = subf φ ++ ¬·subf φ`):
  worlds are maximal consistent subsets of `negClosure φ₀`; the extra
  negations let the Lindenbaum seed of a box-case successor contain `¬p`
  while the truth lemma itself only ever visits genuine subformulas of
  `φ₀`.
* **The canonical frame** (`canonicalFrame`): worlds as above,
  `Δ R Θ  ↔  (∀ □q ∈ Δ, q ∈ Θ ∧ □q ∈ Θ) ∧ (∃ □q ∈ Θ, □q ∉ Δ)`.
  Transitivity is immediate; converse well-foundedness holds because the
  number of boxed members (`bcount`) strictly increases along `R` and is
  bounded by the closure length — the frame is a genuine `GLFrame` in the
  sense of the S20 `Kripke.lean`, with no infinite ascending chains.
* **Truth lemma** (`truth_lemma`): for `ψ ∈ subf φ₀` and any world `w`,
  `Forces w ψ ↔ ψ ∈ w`. Atom and falsum are definitional, implication is
  S22a's `MaximalIn.impl_mem_iff`, and the box case combines
  `consistent_lob_seed` with the S22a Lindenbaum lemma to manufacture the
  refuting successor.
* **Completeness capstones**: `exists_countermodel` (every GL-unprovable
  formula fails at a world of its canonical frame),
  `not_valid_of_not_provable`, `gl_complete : Valid φ → GL_proves φ`, and
  the headline equivalence `gl_proves_iff_valid : GL_proves φ ↔ Valid φ`
  (soundness direction from the S20 `valid_of_GL_proves`).

## What this is NOT

The worlds of `canonicalFrame φ₀` are list-valued: only finitely many
world *sets* occur, but the Lean subtype has many list representatives per
set, so the finite-model property *as a finite Lean type* (and with it
S22c decidability) still requires a canonical-representative quotient.
That packaging is deliberately left to S22c; nothing here claims it.

## Design notes

* Mathlib-free like the whole S8–S22a chain. Classical ingredients enter
  only through the imported S22a layer (`Consistent` splitting, `extend`);
  everything added here is constructive over it except `Classical`-free —
  the file adds **no** new classical axiom use of its own. 0 sorries,
  0 `axiom` declarations.
* `nat_lt_wf` is proved locally (10 lines) rather than imported, keeping
  the file independent of Mathlib's well-founded-order lemma names.

## References

- Boolos, G. (1993). *The Logic of Provability*. Cambridge University
  Press, Ch. 5.
- Segerberg, K. (1971). *An Essay in Classical Modal Logic*. Uppsala.
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer, §2.
-/

namespace GodelSecondCanonical

open GodelSecondGLSyntax GodelSecondGLFour GodelSecondKalmar
open GodelSecondLindenbaum GodelSecondGLKripke

local infixr:55 " ⟶ " => GLFormula.impl
local prefix:75 "□" => GLFormula.box
local notation "⊥ₘ" => GLFormula.falsum

-- ============================================================
-- PART 1: curried premise lists
-- ============================================================

/-- `imps [x₁,…,xₙ] B = x₁ ⟶ x₂ ⟶ ⋯ ⟶ xₙ ⟶ B`: a hypothesis list as a
curried implication. All "conjunction of a context" reasoning in the
completeness proof is done in this currying, so only `k1`/`k2`-level
combinators are ever needed. -/
def imps : List GLFormula → GLFormula → GLFormula
  | [], B => B
  | x :: Γ, B => x ⟶ imps Γ B

/-- Right monotonicity of implication under a fixed antecedent: from
`⊢ x ⟶ y` conclude `⊢ (a ⟶ x) ⟶ (a ⟶ y)`. -/
theorem imp_mono_right {a x y : GLFormula} (h : GL_proves (x ⟶ y)) :
    GL_proves ((a ⟶ x) ⟶ (a ⟶ y)) :=
  (ax2 a x y).mp ((ax1 (x ⟶ y) a).mp h)

/-- Exchange: a premise appearing after a curried prefix can be rotated to
the front, `⊢ imps Γ (x ⟶ B) ⟶ (x ⟶ imps Γ B)`. -/
theorem imps_exchange : ∀ (Γ : List GLFormula) (x B : GLFormula),
    GL_proves (imps Γ (x ⟶ B) ⟶ (x ⟶ imps Γ B))
  | [], x, B => imp_id (x ⟶ B)
  | a :: Γ, x, B =>
      imp_trans (imp_mono_right (imps_exchange Γ x B))
        (imp_swap a x (imps Γ B))

/-- Closing a hypothesis-level derivation into a GL theorem: from
`Γ ⊢ B` (in `PDeriv`) conclude `⊢ imps Γ B`. Iterated deduction theorem,
with `imps_exchange` repairing the premise order at each step. -/
theorem imps_of_pderiv : ∀ {Γ : List GLFormula} {B : GLFormula},
    PDeriv Γ B → GL_proves (imps Γ B)
  | [], _, h => h.toGL
  | _ :: Γ, _, h => (imps_exchange Γ _ _).mp (imps_of_pderiv h.deduction)

/-- Conclusion monotonicity: from `⊢ B ⟶ C` conclude
`⊢ imps Γ B ⟶ imps Γ C`. -/
theorem imps_mono_concl {B C : GLFormula} (h : GL_proves (B ⟶ C)) :
    ∀ Γ : List GLFormula, GL_proves (imps Γ B ⟶ imps Γ C)
  | [] => h
  | _ :: Γ => imp_mono_right (imps_mono_concl h Γ)

/-- Premise-wise `K`-distribution: `⊢ □(imps Γ B) ⟶ imps (Γ.map □) (□B)`.
Each step is one instance of the `K` axiom composed under the boxed
premise. -/
theorem box_imps (B : GLFormula) : ∀ Γ : List GLFormula,
    GL_proves (□(imps Γ B) ⟶ imps (Γ.map GLFormula.box) (□B))
  | [] => imp_id (□B)
  | x :: Γ =>
      imp_trans (GL_proves.k x (imps Γ B)) (imp_mono_right (box_imps B Γ))

/-- Discharging a curried theorem against a context: if `Δ ⊢ imps Γ B` and
`Δ` derives every member of `Γ`, then `Δ ⊢ B`. -/
theorem pderiv_imps_discharge {Δ : List GLFormula} :
    ∀ {Γ : List GLFormula} {B : GLFormula}, PDeriv Δ (imps Γ B) →
      (∀ x ∈ Γ, PDeriv Δ x) → PDeriv Δ B
  | [], _, h, _ => h
  | x :: _, _, h, hall =>
      pderiv_imps_discharge (h.mp (hall x (List.mem_cons_self)))
        (fun y hy => hall y (List.mem_cons_of_mem _ hy))

-- ============================================================
-- PART 2: the boxed content of a world
-- ============================================================

/-- `unbox Δ` lists, for each boxed member `□q ∈ Δ`, both `q` and `□q` —
the formulas every `R`-successor of `Δ` must contain. -/
def unbox : List GLFormula → List GLFormula
  | [] => []
  | GLFormula.box q :: Γ => q :: GLFormula.box q :: unbox Γ
  | _ :: Γ => unbox Γ

theorem unbox_subset_cons (ψ : GLFormula) (Γ : List GLFormula) :
    ∀ x ∈ unbox Γ, x ∈ unbox (ψ :: Γ) := by
  intro x hx
  cases ψ with
  | box q =>
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
  | atom p => exact hx
  | falsum => exact hx
  | impl p q => exact hx

/-- Forward: each boxed member of `Δ` contributes both `q` and `□q` to
`unbox Δ`. -/
theorem mem_unbox_of_box_mem : ∀ {Γ : List GLFormula} {q : GLFormula},
    (□q) ∈ Γ → q ∈ unbox Γ ∧ (□q) ∈ unbox Γ := by
  intro Γ
  induction Γ with
  | nil => intro q h; cases h
  | cons ψ Γ ih =>
    intro q h
    rcases List.mem_cons.mp h with heq | hmem
    · rw [← heq]
      refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_cons_self)⟩
    · obtain ⟨h1, h2⟩ := ih hmem
      exact ⟨unbox_subset_cons ψ Γ _ h1, unbox_subset_cons ψ Γ _ h2⟩

/-- Backward: every member of `unbox Δ` is `q` or `□q` for some boxed
member `□q ∈ Δ`. -/
theorem unbox_sound : ∀ {Γ : List GLFormula} {x : GLFormula},
    x ∈ unbox Γ → ∃ q, (□q) ∈ Γ ∧ (x = q ∨ x = □q) := by
  intro Γ
  induction Γ with
  | nil => intro x h; cases h
  | cons ψ Γ ih =>
    intro x h
    cases ψ with
    | box q =>
      rcases List.mem_cons.mp h with heq | h'
      · exact ⟨q, List.mem_cons_self, Or.inl heq⟩
      · rcases List.mem_cons.mp h' with heq | h''
        · exact ⟨q, List.mem_cons_self, Or.inr heq⟩
        · obtain ⟨r, hr, hx⟩ := ih h''
          exact ⟨r, List.mem_cons_of_mem _ hr, hx⟩
    | atom p =>
      obtain ⟨r, hr, hx⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, hx⟩
    | falsum =>
      obtain ⟨r, hr, hx⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, hx⟩
    | impl p q =>
      obtain ⟨r, hr, hx⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, hx⟩

-- ============================================================
-- PART 3: the Löb step
-- ============================================================

/-- **The box case of the truth lemma, syntactic half.** If `Δ` is maximal
consistent in `L`, `□p ∈ L` and `□p ∉ Δ`, then
`{¬p, □p} ∪ {q, □q : □q ∈ Δ}` is consistent.

If not, the deduction theorem gives `unbox Δ ⊢ □p ⟶ p`, hence
`⊢ imps (unbox Δ) (□p ⟶ p)`. Necessitating and distributing `K`
premise-wise (`box_imps`) yields `⊢ imps (□·unbox Δ) (□(□p ⟶ p))`;
**Löb's axiom** at the conclusion gives `⊢ imps (□·unbox Δ) (□p)`. Every
boxed premise is derivable from `Δ` — `□q` is a hypothesis and `□□q`
follows by the S18 `4` schema — so `Δ ⊢ □p`, and derivability closure of
the maximal set forces `□p ∈ Δ`, a contradiction. -/
theorem consistent_lob_seed {L Δ : List GLFormula} (hmax : MaximalIn L Δ)
    {p : GLFormula} (hpL : (□p) ∈ L) (hnp : (□p) ∉ Δ) :
    Consistent ((p ⟶ ⊥ₘ) :: □p :: unbox Δ) := by
  intro hbot
  apply hnp
  apply hmax.mem_of_deriv hpL
  have h1 : PDeriv (□p :: unbox Δ) ((p ⟶ ⊥ₘ) ⟶ ⊥ₘ) := hbot.deduction
  have h2 : PDeriv (□p :: unbox Δ) p := .mp (.thm (dne p)) h1
  have h3 : PDeriv (unbox Δ) (□p ⟶ p) := h2.deduction
  have h4 : GL_proves (imps (unbox Δ) (□p ⟶ p)) := imps_of_pderiv h3
  have h5 : GL_proves (imps ((unbox Δ).map GLFormula.box) (□(□p ⟶ p))) :=
    (box_imps _ _).mp (.nec h4)
  have h6 : GL_proves (imps ((unbox Δ).map GLFormula.box) (□p)) :=
    (imps_mono_concl (GL_proves.lob p) _).mp h5
  refine pderiv_imps_discharge (.thm h6) ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hqΔ, hy'⟩ := unbox_sound hy
  rcases hy' with rfl | rfl
  · exact .hyp hqΔ
  · exact .mp (.thm (four q)) (.hyp hqΔ)

-- ============================================================
-- PART 4: the negation-augmented closure
-- ============================================================

/-- The closure list over which canonical worlds live: all subformulas of
`φ`, plus the negation of each. The negations are needed only so that the
box-case Lindenbaum seed `¬p :: □p :: unbox Δ` stays inside the closure;
the truth lemma itself only visits `subf φ`. -/
def negClosure (φ : GLFormula) : List GLFormula :=
  subf φ ++ (subf φ).map fun ψ => ψ ⟶ ⊥ₘ

theorem mem_negClosure_of_subf {φ ψ : GLFormula} (h : ψ ∈ subf φ) :
    ψ ∈ negClosure φ :=
  List.mem_append.mpr (Or.inl h)

theorem neg_mem_negClosure {φ ψ : GLFormula} (h : ψ ∈ subf φ) :
    (ψ ⟶ ⊥ₘ) ∈ negClosure φ :=
  List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ψ, h, rfl⟩))

/-- Boxed members of the closure are genuine subformulas: the appended
negations are `⟶`-shaped, never `□`-shaped. -/
theorem box_mem_subf_of_mem_negClosure {φ q : GLFormula}
    (h : (□q) ∈ negClosure φ) : (□q) ∈ subf φ := by
  rcases List.mem_append.mp h with h | h
  · exact h
  · obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    cases ha

theorem mem_subf_of_impl_left {φ p q : GLFormula} (h : (p ⟶ q) ∈ subf φ) :
    p ∈ subf φ := by
  apply subf_closed φ _ h
  simp only [subf, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (self_mem_subf p))

theorem mem_subf_of_impl_right {φ p q : GLFormula} (h : (p ⟶ q) ∈ subf φ) :
    q ∈ subf φ := by
  apply subf_closed φ _ h
  simp only [subf, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (self_mem_subf q))

theorem mem_subf_of_box {φ p : GLFormula} (h : (□p) ∈ subf φ) :
    p ∈ subf φ := by
  apply subf_closed φ _ h
  simp only [subf, List.mem_cons]
  exact Or.inr (self_mem_subf p)

-- ============================================================
-- PART 5: counting boxed members — the well-foundedness measure
-- ============================================================

/-- Weight of one closure position: `1` if it is a boxed formula belonging
to `Δ`, else `0`. -/
def boxWeight (Δ : List GLFormula) (ψ : GLFormula) : Nat :=
  match ψ with
  | GLFormula.box _ => if ψ ∈ Δ then 1 else 0
  | _ => 0

/-- The number of positions of `L` holding a boxed member of `Δ`. -/
def bcount (Δ : List GLFormula) : List GLFormula → Nat
  | [] => 0
  | ψ :: L => boxWeight Δ ψ + bcount Δ L

theorem boxWeight_le_one (Δ : List GLFormula) (ψ : GLFormula) :
    boxWeight Δ ψ ≤ 1 := by
  cases ψ with
  | box q =>
      simp only [boxWeight]
      split <;> omega
  | atom p => exact Nat.zero_le 1
  | falsum => exact Nat.zero_le 1
  | impl p q => exact Nat.zero_le 1

theorem bcount_le_length (Δ : List GLFormula) :
    ∀ L : List GLFormula, bcount Δ L ≤ L.length := by
  intro L
  induction L with
  | nil => exact Nat.le_refl 0
  | cons ψ L ih =>
    have h := boxWeight_le_one Δ ψ
    simp only [bcount, List.length_cons]
    omega

theorem boxWeight_mono {Δ Θ : List GLFormula}
    (h : ∀ q, (□q) ∈ Δ → (□q) ∈ Θ) (ψ : GLFormula) :
    boxWeight Δ ψ ≤ boxWeight Θ ψ := by
  cases ψ with
  | box q =>
      simp only [boxWeight]
      by_cases hq : (□q) ∈ Δ
      · rw [if_pos hq, if_pos (h q hq)]
        exact Nat.le_refl 1
      · rw [if_neg hq]
        exact Nat.zero_le _
  | atom p => exact Nat.le_refl 0
  | falsum => exact Nat.le_refl 0
  | impl p q => exact Nat.le_refl 0

theorem bcount_mono {Δ Θ : List GLFormula}
    (h : ∀ q, (□q) ∈ Δ → (□q) ∈ Θ) :
    ∀ L : List GLFormula, bcount Δ L ≤ bcount Θ L := by
  intro L
  induction L with
  | nil => exact Nat.le_refl 0
  | cons ψ L ih =>
    have hw := boxWeight_mono h ψ
    simp only [bcount]
    omega

/-- Strict growth: if the boxed members of `Δ` all persist into `Θ` and
`Θ` holds a boxed formula of `L` that `Δ` lacks, the count strictly
increases. -/
theorem bcount_lt {Δ Θ : List GLFormula}
    (h : ∀ q, (□q) ∈ Δ → (□q) ∈ Θ) {w : GLFormula}
    (hΘ : (□w) ∈ Θ) (hΔ : (□w) ∉ Δ) :
    ∀ {L : List GLFormula}, (□w) ∈ L → bcount Δ L < bcount Θ L := by
  intro L
  induction L with
  | nil => intro hmem; cases hmem
  | cons ψ L ih =>
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · have hwΔ : boxWeight Δ ψ = 0 := by
        rw [← heq]
        simp only [boxWeight]
        rw [if_neg hΔ]
      have hwΘ : boxWeight Θ ψ = 1 := by
        rw [← heq]
        simp only [boxWeight]
        rw [if_pos hΘ]
      have htail := bcount_mono h L
      simp only [bcount]
      omega
    · have hw := boxWeight_mono h ψ
      have htail := ih hmem'
      simp only [bcount]
      omega

/-- `WellFounded Nat.lt`, proved locally to keep the file free of external
well-founded-order lemma names. -/
theorem nat_lt_wf : WellFounded (fun a b : Nat => a < b) := by
  constructor
  intro n
  induction n with
  | zero =>
    constructor
    intro m hm
    exact absurd hm (Nat.not_lt_zero m)
  | succ k ih =>
    constructor
    intro m hm
    have : m < k ∨ m = k := by omega
    rcases this with h | rfl
    · exact ih.inv h
    · exact ih

-- ============================================================
-- PART 6: the canonical frame
-- ============================================================

/-- The canonical accessibility relation (Boolos Ch. 5): `Θ` sees all of
`Δ`'s boxed commitments (both `q` and `□q`, the latter via the `4`
schema built into the relation), and holds strictly more boxed formulas.
The strictness clause is what makes the relation converse well-founded —
Löb's axiom is sound on the resulting frame. -/
def CanR (Δ Θ : List GLFormula) : Prop :=
  (∀ q, (□q) ∈ Δ → q ∈ Θ ∧ (□q) ∈ Θ) ∧ (∃ q, (□q) ∈ Θ ∧ (□q) ∉ Δ)

/-- Worlds of the canonical model for `φ₀`: maximal consistent subsets of
the negation-augmented subformula closure. -/
abbrev CanWorld (φ₀ : GLFormula) :=
  {Δ : List GLFormula // MaximalIn (negClosure φ₀) Δ}

/-- **The canonical frame** — a genuine `GLFrame`: transitive, and
converse well-founded via the strictly increasing boxed-member count. -/
def canonicalFrame (φ₀ : GLFormula) : GLFrame where
  World := CanWorld φ₀
  R w u := CanR w.val u.val
  trans := by
    rintro x y z ⟨hxy1, _⟩ ⟨hyz1, q, hqz, hqy⟩
    refine ⟨fun r hr => hyz1 r (hxy1 r hr).2, q, hqz, fun hqx => hqy (hxy1 q hqx).2⟩
  cwf := by
    have hwf : WellFounded
        (InvImage (fun a b : Nat => a < b)
          (fun w : CanWorld φ₀ =>
            (negClosure φ₀).length - bcount w.val (negClosure φ₀))) :=
      InvImage.wf _ nat_lt_wf
    refine Subrelation.wf (fun {x y} hxy => ?_) hwf
    obtain ⟨h1, q, hqx, hqy⟩ := hxy
    have hboxes : ∀ r, (□r) ∈ y.val → (□r) ∈ x.val := fun r hr => (h1 r hr).2
    have hqL : (□q) ∈ negClosure φ₀ := x.property.subset _ hqx
    have hlt : bcount y.val (negClosure φ₀) < bcount x.val (negClosure φ₀) :=
      bcount_lt hboxes hqx hqy hqL
    have hle : bcount x.val (negClosure φ₀) ≤ (negClosure φ₀).length :=
      bcount_le_length _ _
    show (negClosure φ₀).length - bcount x.val (negClosure φ₀) <
      (negClosure φ₀).length - bcount y.val (negClosure φ₀)
    omega

/-- The canonical valuation: an atom holds at a world iff it is a member. -/
def canonicalVal (φ₀ : GLFormula) :
    PropAtom → (canonicalFrame φ₀).World → Prop :=
  fun p w => (GLFormula.atom p) ∈ w.val

-- ============================================================
-- PART 7: the truth lemma
-- ============================================================

/-- **Truth lemma** (Boolos Ch. 5): for subformulas of `φ₀`, forcing at a
canonical world is membership. Implication is S22a's
`MaximalIn.impl_mem_iff`; the box case builds the refuting successor from
`consistent_lob_seed` + the finite Lindenbaum lemma. -/
theorem truth_lemma (φ₀ : GLFormula) :
    ∀ ψ : GLFormula, ψ ∈ subf φ₀ → ∀ w : (canonicalFrame φ₀).World,
      (Forces (canonicalFrame φ₀) (canonicalVal φ₀) w ψ ↔ ψ ∈ w.val) := by
  intro ψ
  induction ψ with
  | atom p => intro _ w; exact Iff.rfl
  | falsum =>
    intro _ w
    exact ⟨fun h => (h : False).elim, fun h => absurd h w.property.falsum_not_mem⟩
  | impl p q ihp ihq =>
    intro hmem w
    have hp : p ∈ subf φ₀ := mem_subf_of_impl_left hmem
    have hq : q ∈ subf φ₀ := mem_subf_of_impl_right hmem
    have hiff := w.property.impl_mem_iff (mem_negClosure_of_subf hmem)
      (mem_negClosure_of_subf hp) (mem_negClosure_of_subf hq)
    constructor
    · intro hf
      exact hiff.mpr fun hpmem => (ihq hq w).mp (hf ((ihp hp w).mpr hpmem))
    · intro hmem' hfp
      exact (ihq hq w).mpr (hiff.mp hmem' ((ihp hp w).mp hfp))
  | box p ihp =>
    intro hmem w
    have hpsub : p ∈ subf φ₀ := mem_subf_of_box hmem
    constructor
    · intro hf
      refine Classical.byContradiction fun hnmem => ?_
      have hcons : Consistent ((p ⟶ ⊥ₘ) :: □p :: unbox w.val) :=
        consistent_lob_seed w.property (mem_negClosure_of_subf hmem) hnmem
      have hseedsub : ∀ x ∈ (p ⟶ ⊥ₘ) :: □p :: unbox w.val,
          x ∈ negClosure φ₀ := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact neg_mem_negClosure hpsub
        rcases List.mem_cons.mp hx' with rfl | hx''
        · exact mem_negClosure_of_subf hmem
        · obtain ⟨q, hqΔ, hor⟩ := unbox_sound hx''
          have hqsub : (□q) ∈ subf φ₀ :=
            box_mem_subf_of_mem_negClosure (w.property.subset _ hqΔ)
          rcases hor with rfl | rfl
          · exact mem_negClosure_of_subf (mem_subf_of_box hqsub)
          · exact mem_negClosure_of_subf hqsub
      obtain ⟨Θ, hΘmax, hΘsub⟩ := lindenbaum hseedsub hcons
      have hRu : CanR w.val Θ := by
        constructor
        · intro q hq
          obtain ⟨h1, h2⟩ := mem_unbox_of_box_mem hq
          exact ⟨hΘsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)),
            hΘsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2))⟩
        · exact ⟨p, hΘsub _ (List.mem_cons_of_mem _ (List.mem_cons_self)),
            hnmem⟩
      have hnegΘ : (p ⟶ ⊥ₘ) ∈ Θ := hΘsub _ (List.mem_cons_self)
      have hpΘ : p ∉ Θ := fun hpΘ =>
        hΘmax.consistent (.mp (.hyp hnegΘ) (.hyp hpΘ))
      exact hpΘ ((ihp hpsub ⟨Θ, hΘmax⟩).mp (hf ⟨Θ, hΘmax⟩ hRu))
    · intro hmem' u hRu
      exact (ihp hpsub u).mpr (hRu.1 p hmem').1

-- ============================================================
-- PART 8: completeness
-- ============================================================

/-- **Countermodel existence**: every GL-unprovable formula fails at some
world of its own canonical frame. The root world extends the consistent
seed `{¬φ}` (S22a `consistent_singleton_neg`) inside `negClosure φ`. -/
theorem exists_countermodel {φ : GLFormula} (h : ¬ GL_proves φ) :
    ∃ w : (canonicalFrame φ).World,
      ¬ Forces (canonicalFrame φ) (canonicalVal φ) w φ := by
  have hseed : ∀ x ∈ [φ ⟶ ⊥ₘ], x ∈ negClosure φ := by
    intro x hx
    have hx' : x = (φ ⟶ ⊥ₘ) := by simpa using hx
    rw [hx']
    exact neg_mem_negClosure (self_mem_subf φ)
  obtain ⟨Δ, hmax, hsub⟩ := lindenbaum hseed (consistent_singleton_neg h)
  refine ⟨⟨Δ, hmax⟩, fun hf => ?_⟩
  have hφΔ : φ ∈ Δ := (truth_lemma φ φ (self_mem_subf φ) ⟨Δ, hmax⟩).mp hf
  have hnegΔ : (φ ⟶ ⊥ₘ) ∈ Δ := hsub _ (by simp)
  exact hmax.consistent (.mp (.hyp hnegΔ) (.hyp hφΔ))

/-- Unprovable formulas are not valid: contrapositive packaging of
`exists_countermodel` against the S20 `Valid`. -/
theorem not_valid_of_not_provable {φ : GLFormula} (h : ¬ GL_proves φ) :
    ¬ Valid φ := fun hv =>
  (exists_countermodel h).elim fun w hw => hw (hv _ _ w)

/-- **Kripke completeness of GL** (Segerberg): every formula valid on all
transitive converse-wellfounded frames is a GL theorem. -/
theorem gl_complete {φ : GLFormula} (h : Valid φ) : GL_proves φ :=
  Classical.byContradiction fun hn => not_valid_of_not_provable hn h

/-- **The headline equivalence**: GL proves exactly the formulas valid on
all GL frames. Soundness is the S20 `valid_of_GL_proves`; completeness is
the canonical model of this file. -/
theorem gl_proves_iff_valid (φ : GLFormula) : GL_proves φ ↔ Valid φ :=
  ⟨valid_of_GL_proves, gl_complete⟩

#check @consistent_lob_seed
#check @truth_lemma
#check @exists_countermodel
#check @gl_complete
#check @gl_proves_iff_valid

end GodelSecondCanonical
