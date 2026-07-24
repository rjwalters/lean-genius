/-
  # Self-duality of Desargues's theorem, made explicit

  *Question* (`desargues-theorem-oq-02-oq-02`): can we formalize the
  **self-duality** property of Desargues's theorem explicitly?

  Plane projective duality exchanges points with lines, "lies on" with "passes
  through", collinearity with concurrency.  Desargues's theorem

  > **(D)** two triangles centrally perspective (the three joins `AA'`, `BB'`,
  > `CC'` concurrent in a center `O`) are axially perspective (the three
  > meets `AB·A'B'`, `BC·B'C'`, `CA·C'A'` collinear on an axis `ℓ`)

  dualizes term-by-term to

  > **(D\*)** two triangles axially perspective are centrally perspective

  — exactly the **converse** of (D).  So Desargues's theorem is *its own dual =
  its own converse*.  This file machine-checks that dictionary at two layers.

  ## Layer 1 — the finite Desargues configuration `10₃` is self-dual

  The ten points and ten lines of a Desargues configuration are the classical
  `10₃` configuration.  In the standard combinatorial model both points and
  lines are labelled by the 2-element subsets of a 5-element set, with
  incidence = **disjointness**; disjointness is symmetric, so the label-
  preserving swap of points and lines is an incidence-reversing bijection — an
  explicit **polarity**.  We fix the geometric dictionary

  | node | pair | node | pair |
  |------|------|------|------|
  | `O` (center) = pt 0 | `{0,1}` | axis `ℓ` = ln 0 | `{0,1}` |
  | `A` = pt 1 | `{0,2}` | `la = OAA'` = ln 1 | `{3,4}` |
  | `B` = pt 2 | `{0,3}` | `lb = OBB'` = ln 2 | `{2,4}` |
  | `C` = pt 3 | `{0,4}` | `lc = OCC'` = ln 3 | `{2,3}` |
  | `A'` = pt 4 | `{1,2}` | `ab = ABP` = ln 4 | `{1,4}` |
  | `B'` = pt 5 | `{1,3}` | `ab' = A'B'P` = ln 5 | `{0,4}` |
  | `C'` = pt 6 | `{1,4}` | `bc = BCQ` = ln 6 | `{1,2}` |
  | `P = AB·A'B'` = pt 7 | `{2,3}` | `bc' = B'C'Q` = ln 7 | `{0,2}` |
  | `Q = BC·B'C'` = pt 8 | `{3,4}` | `ca = CARᵣ` = ln 8 | `{1,3}` |
  | `R = CA·C'A'` = pt 9 | `{2,4}` | `ca' = C'A'R` = ln 9 | `{0,3}` |

  and verify by kernel `decide`: it is a genuine `10₃` configuration
  (`inc_point_card_three`, `inc_line_card_three`), all 30 Desargues role
  incidences hold (`desargues_roles_*`), and the explicit permutation pair
  `ptToLn`/`lnToPt` is an incidence-reversing bijection
  (`polarity_reverses`, `lnToPt_ptToLn`, `ptToLn_lnToPt`).  The polarity sends
  the center `O` to the axis `ℓ`, each vertex to the *opposite* side of the
  *other* triangle (`A ↦ B'C'`, …), and each perspectivity line to an axis
  point (`la ↦ Q`, …) — the classical self-duality of the configuration.

  ## Layer 2 — the Desarguesian property dualizes to the converse property

  On a bare incidence structure `[Membership P L]` (the layer at which
  Mathlib's `Configuration.Dual` operates) we define

  * `PointsCollinear P L p₁ p₂ p₃` / `LinesConcurrent P L l₁ l₂ l₃`,
  * `IsDesarguesian P L` — the universal incidence form of (D): for every
    labelled Desargues configuration (27 incidence hypotheses + 12
    nondegeneracy inequalities), the three axis candidate points are
    collinear;
  * `IsConverseDesarguesian P L` — the universal form of (D\*): given the
    axis (3 incidences) and the same sides/joins data, the three joins are
    concurrent.

  The nondegeneracy schema is chosen **closed under the polarity** (the 12
  inequalities `A ≠ A', B ≠ B', C ≠ C', p,q,r pairwise distinct, la,lb,lc
  pairwise distinct, ab ≠ ab', bc ≠ bc', ca ≠ ca'` map onto each other), so
  duality is an exact statement swap:

  * `pointsCollinear_dual_iff` / `linesConcurrent_dual_iff` — collinear and
    concurrent are exchanged by `Configuration.Dual` **definitionally**
    (`Iff.rfl`);
  * **`isDesarguesian_dual_iff : IsDesarguesian (Dual L) (Dual P) ↔
    IsConverseDesarguesian P L`** — the dual plane satisfies Desargues iff
    the plane satisfies the converse: *Desargues's theorem is its own dual =
    its own converse*, stated and proved explicitly;
  * `isConverseDesarguesian_dual_iff` — the mirror statement, obtained from
    the previous one because `Dual` is definitionally involutive;
  * `desargues_package_self_dual` — the full package (theorem ∧ converse) is
    invariant under dualization.

  The type-order gotcha is respected throughout: the dual of the plane
  `(P, L)` is `(Dual L, Dual P)` — dual *points* are the original *lines*.

  ## Honest scope

  * Desargues is NOT a theorem of the projective-plane axioms (the parent
    entry's Moulton plane is a non-Desarguesian counterexample), so
    self-duality is necessarily a statement about the *Desarguesian property*,
    not a proof of (D) itself.  Nothing here claims any particular plane is
    Desarguesian.
  * The *intra-plane* implication "a projective plane satisfying (D) also
    satisfies (D\*)" is a genuine geometric theorem (apply (D) to a derived
    configuration); it is NOT purely formal duality and is left open here.
  * The parent's Moulton model is affine, and affine planes are not self-dual
    (parallels have no point-dual); this file therefore lives at the abstract
    incidence layer, one level above its parent, as recorded in the survey.

  ## Verification status: verified (axiom-free)

  All finite checks are kernel `decide` on `Fin 10`/`Fin 5` data (no
  `native_decide`); the abstract layer is constructive shuffling of incidence
  hypotheses along `Configuration.Dual`.  0 sorries, 0 axioms.
-/
import Mathlib

namespace DesarguesTheoremOQ02OQ02

/- ## Layer 1: the finite Desargues configuration and its explicit polarity -/

/-- The ten POINTS of the Desargues configuration, encoded by 2-element
subsets of `Fin 5` (order: `O, A, B, C, A', B', C', P, Q, R`). -/
def pairOf : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {3, 4}, {2, 4}]

/-- The ten LINES of the Desargues configuration, same encoding (order:
`axis, la = OAA', lb = OBB', lc = OCC', ab, ab', bc, bc', ca, ca'`). -/
def lineOf : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {3, 4}, {2, 4}, {2, 3}, {1, 4}, {0, 4}, {1, 2}, {0, 2}, {1, 3}, {0, 3}]

/-- Incidence: a point lies on a line iff their label pairs are disjoint —
the classical combinatorial model of the Desargues `10₃` configuration. -/
def Inc (p l : Fin 10) : Prop := pairOf p ∩ lineOf l = ∅

instance (p l : Fin 10) : Decidable (Inc p l) := by unfold Inc; infer_instance

/-- Each line passes through exactly 3 points: the `10₃` line condition. -/
theorem inc_line_card_three :
    ∀ l : Fin 10, ((Finset.univ : Finset (Fin 10)).filter fun p => Inc p l).card = 3 := by
  decide

/-- Each point lies on exactly 3 lines: the `10₃` point condition. -/
theorem inc_point_card_three :
    ∀ p : Fin 10, ((Finset.univ : Finset (Fin 10)).filter fun l => Inc p l).card = 3 := by
  decide

/-- Central perspectivity in the model: the center `O` (pt 0) lies on all
three perspectivity lines `la, lb, lc` (ln 1, 2, 3), which carry the
corresponding vertex pairs `A,A'`, `B,B'`, `C,C'`. -/
theorem desargues_roles_central :
    Inc 0 1 ∧ Inc 1 1 ∧ Inc 4 1 ∧
    Inc 0 2 ∧ Inc 2 2 ∧ Inc 5 2 ∧
    Inc 0 3 ∧ Inc 3 3 ∧ Inc 6 3 := by decide

/-- The six sides carry their two vertices and the matching axis point:
`ab = {A, B, P}`, `ab' = {A', B', P}`, `bc = {B, C, Q}`, `bc' = {B', C', Q}`,
`ca = {C, A, R}`, `ca' = {C', A', R}`. -/
theorem desargues_roles_sides :
    Inc 1 4 ∧ Inc 2 4 ∧ Inc 7 4 ∧
    Inc 4 5 ∧ Inc 5 5 ∧ Inc 7 5 ∧
    Inc 2 6 ∧ Inc 3 6 ∧ Inc 8 6 ∧
    Inc 5 7 ∧ Inc 6 7 ∧ Inc 8 7 ∧
    Inc 3 8 ∧ Inc 1 8 ∧ Inc 9 8 ∧
    Inc 6 9 ∧ Inc 4 9 ∧ Inc 9 9 := by decide

/-- Axial perspectivity in the model: the three axis points `P, Q, R`
(pts 7, 8, 9) all lie on the axis (ln 0) — the conclusion of Desargues's
theorem holds in the configuration. -/
theorem desargues_roles_axis : Inc 7 0 ∧ Inc 8 0 ∧ Inc 9 0 := by decide

/-- The polarity, point-to-line half: each point maps to the line carrying the
same label pair.  Geometrically: `O ↦ axis`, each vertex to the opposite side
of the other triangle (`A ↦ bc' = B'C'`, `B ↦ ca' = C'A'`, `C ↦ ab' = A'B'`,
`A' ↦ bc = BCQ`, `B' ↦ ca`, `C' ↦ ab`), each axis point to a perspectivity
line (`P ↦ lc`, `Q ↦ la`, `R ↦ lb`). -/
def ptToLn : Fin 10 → Fin 10 := ![0, 7, 9, 5, 6, 8, 4, 3, 1, 2]

/-- The polarity, line-to-point half (the inverse table). -/
def lnToPt : Fin 10 → Fin 10 := ![0, 8, 9, 7, 6, 3, 4, 1, 5, 2]

/-- The two halves are mutually inverse: the polarity is a bijection. -/
theorem lnToPt_ptToLn : ∀ p, lnToPt (ptToLn p) = p := by decide

theorem ptToLn_lnToPt : ∀ l, ptToLn (lnToPt l) = l := by decide

/-- **The Desargues configuration is self-dual**: the explicit polarity
reverses incidence — `p` lies on `l` iff the dual point `lnToPt l` lies on
the dual line `ptToLn p`.  (In the pair model this is just symmetry of
disjointness, transported through the label tables.) -/
theorem polarity_reverses : ∀ p l, Inc p l ↔ Inc (lnToPt l) (ptToLn p) := by decide

/- ## Layer 2: duality exchanges the Desarguesian and converse-Desarguesian
     properties -/

open Configuration

section Abstract

variable (P L : Type*) [Membership P L]

/-- Three points are collinear: some line passes through all three. -/
def PointsCollinear (p₁ p₂ p₃ : P) : Prop :=
  ∃ l : L, p₁ ∈ l ∧ p₂ ∈ l ∧ p₃ ∈ l

/-- Three lines are concurrent: some point lies on all three. -/
def LinesConcurrent (l₁ l₂ l₃ : L) : Prop :=
  ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ ∧ p ∈ l₃

/-- Collinearity in the dual plane IS concurrency in the original plane —
definitionally (note the type order: dual points are original lines). -/
theorem pointsCollinear_dual_iff (l₁ l₂ l₃ : L) :
    PointsCollinear (Dual L) (Dual P) l₁ l₂ l₃ ↔ LinesConcurrent P L l₁ l₂ l₃ :=
  Iff.rfl

/-- Concurrency in the dual plane IS collinearity in the original plane —
definitionally. -/
theorem linesConcurrent_dual_iff (p₁ p₂ p₃ : P) :
    LinesConcurrent (Dual L) (Dual P) p₁ p₂ p₃ ↔ PointsCollinear P L p₁ p₂ p₃ :=
  Iff.rfl

/-- **The Desarguesian property**, in universal incidence form: for every
labelled Desargues configuration — center `o`, vertices `A B C` / `A' B' C'`,
axis candidates `p q r`, perspectivity lines `la lb lc`, sides
`ab ab' bc bc' ca ca'`, subject to the polarity-symmetric nondegeneracy
schema (12 inequalities) and the 27 incidence hypotheses of central
perspectivity — the axis candidates are collinear.

The hypothesis schema is chosen to be exactly interchanged with that of
`IsConverseDesarguesian` under plane duality; see `isDesarguesian_dual_iff`. -/
def IsDesarguesian : Prop :=
  ∀ (o A B C A' B' C' p q r : P) (la lb lc ab ab' bc bc' ca ca' : L),
    A ≠ A' → B ≠ B' → C ≠ C' →
    p ≠ q → p ≠ r → q ≠ r →
    la ≠ lb → la ≠ lc → lb ≠ lc →
    ab ≠ ab' → bc ≠ bc' → ca ≠ ca' →
    o ∈ la → o ∈ lb → o ∈ lc →
    A ∈ la → A' ∈ la → B ∈ lb → B' ∈ lb → C ∈ lc → C' ∈ lc →
    A ∈ ab → B ∈ ab → p ∈ ab → A' ∈ ab' → B' ∈ ab' → p ∈ ab' →
    B ∈ bc → C ∈ bc → q ∈ bc → B' ∈ bc' → C' ∈ bc' → q ∈ bc' →
    C ∈ ca → A ∈ ca → r ∈ ca → C' ∈ ca' → A' ∈ ca' → r ∈ ca' →
    PointsCollinear P L p q r

/-- **The converse-Desarguesian property** (axial ⟹ central), in the same
universal incidence form: given the axis `ℓ` through `p q r` and the same
sides/joins data (27 incidence hypotheses in total, 12 nondegeneracy
inequalities), the three joins `la lb lc` are concurrent. -/
def IsConverseDesarguesian : Prop :=
  ∀ (A B C A' B' C' p q r : P) (ℓ la lb lc ab ab' bc bc' ca ca' : L),
    A ≠ A' → B ≠ B' → C ≠ C' →
    p ≠ q → p ≠ r → q ≠ r →
    la ≠ lb → la ≠ lc → lb ≠ lc →
    ab ≠ ab' → bc ≠ bc' → ca ≠ ca' →
    p ∈ ℓ → q ∈ ℓ → r ∈ ℓ →
    A ∈ la → A' ∈ la → B ∈ lb → B' ∈ lb → C ∈ lc → C' ∈ lc →
    A ∈ ab → B ∈ ab → p ∈ ab → A' ∈ ab' → B' ∈ ab' → p ∈ ab' →
    B ∈ bc → C ∈ bc → q ∈ bc → B' ∈ bc' → C' ∈ bc' → q ∈ bc' →
    C ∈ ca → A ∈ ca → r ∈ ca → C' ∈ ca' → A' ∈ ca' → r ∈ ca' →
    LinesConcurrent P L la lb lc

/-- **Self-duality of Desargues's theorem, class level**: the dual plane is
Desarguesian **iff** the original plane satisfies the *converse* of
Desargues.  The proof is the explicit statement swap along the polarity
dictionary (center ↔ axis, vertex ↔ opposite side of the other triangle,
perspectivity line ↔ axis point) — the same dictionary verified finitely by
`polarity_reverses`.  This is the precise sense in which Desargues's theorem
"is its own dual = its own converse". -/
theorem isDesarguesian_dual_iff :
    IsDesarguesian (Dual L) (Dual P) ↔ IsConverseDesarguesian P L := by
  constructor
  · -- Desargues in the dual plane ⟹ converse Desargues in `P`
    intro h A B C A' B' C' p q r ℓ la lb lc ab ab' bc bc' ca ca'
      hAA' hBB' hCC' hpq hpr hqr hlab hlac hlbc hab' hbc' hca'
      hpl hql hrl hAla hA'la hBlb hB'lb hClc hC'lc
      hAab hBab hpab hA'ab' hB'ab' hpab'
      hBbc hCbc hqbc hB'bc' hC'bc' hqbc'
      hCca hAca hrca hC'ca' hA'ca' hrca'
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      h ℓ bc' ca' ab' bc ca ab lc la lb q r p C' C A' A B' B
        hbc'.symm hca'.symm hab'.symm hlac.symm hlbc.symm hlab
        hqr hpq.symm hpr.symm hCC'.symm hAA'.symm hBB'.symm
        hql hrl hpl
        hqbc' hqbc hrca' hrca hpab' hpab
        hC'bc' hC'ca' hC'lc hCbc hCca hClc
        hA'ca' hA'ab' hA'la hAca hAab hAla
        hB'ab' hB'bc' hB'lb hBab hBbc hBlb
    exact ⟨x, hx2, hx3, hx1⟩
  · -- converse Desargues in `P` ⟹ Desargues in the dual plane
    intro h o A B C A' B' C' p q r la lb lc ab ab' bc bc' ca ca'
      hAA' hBB' hCC' hpq hpr hqr hlab hlac hlbc hab' hbc' hca'
      hola holb holc hAla hA'la hBlb hB'lb hClc hC'lc
      hAab hBab hpab hA'ab' hB'ab' hpab'
      hBbc hCbc hqbc hB'bc' hC'bc' hqbc'
      hCca hAca hrca hC'ca' hA'ca' hrca'
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      h bc' ca' ab' bc ca ab lc la lb o q r p C' C A' A B' B
        hbc'.symm hca'.symm hab'.symm hlac.symm hlbc.symm hlab
        hqr hpq.symm hpr.symm hCC'.symm hAA'.symm hBB'.symm
        holc hola holb
        hqbc' hqbc hrca' hrca hpab' hpab
        hC'bc' hC'ca' hC'lc hCbc hCca hClc
        hA'ca' hA'ab' hA'la hAca hAab hAla
        hB'ab' hB'bc' hB'lb hBab hBbc hBlb
    exact ⟨x, hx3, hx1, hx2⟩

/-- The mirror statement: the dual plane satisfies the *converse* of
Desargues iff the original plane is Desarguesian.  Follows from
`isDesarguesian_dual_iff` applied to the dual plane, because `Dual` is
definitionally involutive. -/
theorem isConverseDesarguesian_dual_iff :
    IsConverseDesarguesian (Dual L) (Dual P) ↔ IsDesarguesian P L :=
  (isDesarguesian_dual_iff (Dual L) (Dual P)).symm

/-- **The full Desargues package is self-dual**: a plane satisfies
(Desargues ∧ converse) iff its dual does.  In particular the class of planes
with the full package is closed under dualization. -/
theorem desargues_package_self_dual :
    IsDesarguesian P L ∧ IsConverseDesarguesian P L ↔
      IsDesarguesian (Dual L) (Dual P) ∧ IsConverseDesarguesian (Dual L) (Dual P) := by
  rw [isDesarguesian_dual_iff, isConverseDesarguesian_dual_iff]
  exact and_comm

/-- Context: Mathlib's duality principle — the dual of a projective plane is
a projective plane (with the point/line type order swapped), so all the
statements above genuinely live on projective planes and their duals. -/
example [ProjectivePlane P L] : ProjectivePlane (Dual L) (Dual P) := inferInstance

end Abstract

end DesarguesTheoremOQ02OQ02
