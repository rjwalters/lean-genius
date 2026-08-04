import Proofs.CycleDoubleCoverPort.CubicBridge
import Proofs.CycleDoubleCoverPort.EvenCover
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.CharP.Two

/-
# Cycle Double Cover port, step 3b: rotation systems and the vertex-ring expansion

Third slice of the port of the openai/cdc-lean development of the Cycle Double
Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery.
It corresponds to upstream `CDCLean/Expansion.lean`; see #37507 for the porting
order, #43625 for step 1 (`GeneralGraph.lean` / `CycleDecomposition.lean`),
#43626 for step 2 (`Basic.lean` / `EvenCover.lean`) and `CubicBridge.lean` in
this same slice for the general/cubic dictionary.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. Notable
differences in the arguments actually used:

* the two facts needed about `finRotate` are isolated as
  `exists_finRotate_iterate` and `finRotate_ne_self`, and the fixed-point-free
  statement is *deduced from* transitivity (a fixed point would make `Fin m` a
  subsingleton, forcing `m ≤ 1`) rather than proved by numeral arithmetic;
* conjugation and `Sigma`-iteration are factored out as the two standalone
  induction lemmas `Equiv.iterate_conj` and `iterate_sigmaCongrRight`, so
  `rotationPerm_fiberTransitive` becomes a three-step `calc` with no
  `Function.Semiconj` bookkeeping and no heterogeneous-equality manipulation;
* `expansionGraph_bridgeless` derives the invariance of `S` along `R.next` from
  a single `by_contra` against `Crosses`, and introduces the projected vertex
  set by `obtain` on its defining property rather than by unfolding a `let`;
* `projected_vertex_even` is a `Finset.sum_eq_zero` on the *fully assembled*
  three-term integrand, with the ring/previous-ring reindexing done once by
  `Equiv.sum_comp`.

## Mathematical content

The reduction of the theorem to the cubic case. Replace each vertex `v` of `G`
by a *ring*: its half-edges become new vertices, joined in a cycle by new "ring"
edges, and each keeps its original "spoke" edge. Every new vertex then has
degree exactly three — one spoke and two ring edges — so the expanded object is
cubic, and an even double cover of the expansion restricts along the spokes to
an even double cover of `G`.

Three things have to be checked, and each is a named result below.

1. **The rings exist.** A `RotationSystem` is a fixed-point-free permutation of
   the half-edges preserving the incident vertex and acting transitively on each
   vertex fibre — exactly a cyclic order on the half-edges at each vertex.
   `rotationSystemOfBridgeless` produces one for any bridgeless graph. The only
   obstruction is a degree-one vertex (a fibre of size one admits no
   fixed-point-free permutation), and `degree_ne_one_of_bridgeless` rules that
   out: the single edge at such a vertex would be a one-element cut.

2. **The expansion is cubic and bridgeless.** `cubicExpansion` packages the
   three slots at each new vertex as an explicit equivalence
   `(ExpandedVertex × Fin 3) ≃ (ExpandedEdge × Fin 2)`, and
   `expansionGraph_bridgeless` transfers bridgelessness. That transfer is the
   substantive step: a hypothetical one-edge cut of the expansion is either a
   ring edge — impossible, because the ring-crossing indicators telescope to `0`
   in `F₂` while a single crossing would make them sum to `1` — or a spoke, in
   which case no ring edge crosses, so membership of the cut side is constant on
   each fibre and the cut descends to a one-edge cut of `G`.

3. **Even double covers project.** `projected_vertex_even` shows the two ring
   contributions at each original vertex cancel in characteristic two, leaving
   exactly the parity condition for the spokes, and `projectEvenDoubleCover`
   assembles the restriction. Note that `coveredTwice` needs no work at all: an
   edge of `G` is literally a spoke of the expansion.

This file does **not** discharge
`CycleDoubleCover.cycleDoubleCover_of_bridgeless`; that is the final step of the
port.

## Deliberate omission: upstream `PathCut.lean`

The porting order in #37507 lists `PathCut.lean` alongside `Expansion.lean` and
`CubicBridge.lean` in step 3, but that grouping is not achievable: upstream's
`PathCut.lean` consists of three theorems (`integralPathCutDichotomy`,
`tutteFlowCardinalityInvariant`, `zmodEight_to_gamma_unconditional`) whose every
ingredient — `HasIntegerPath`, `hasCycleCorrection_of_integerPath`,
`IntegralPathCutDichotomy`, `FlowCardinalityInvariant`,
`flowCardinalityInvariant_of_pathCut`, `zmodEight_to_gamma` — is defined in the
692-line `FlowCount.lean`, which the issue schedules as step 5. `PathCut.lean`
is therefore deferred to the `FlowCount.lean` / `SixFlow.lean` slice, where it
belongs in the dependency order.
-/

namespace CycleDoubleCover

-- ============================================================
-- Generic iteration lemmas (no graph theory involved)
-- ============================================================

/-- Iterating a conjugated permutation is the conjugate of the iterate. Stated
for the concrete `Equiv.trans` shape in which `rotationPerm` and `fiberCycle`
are built, so that it applies by `rfl` after unfolding those definitions. -/
private theorem iterate_conj {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm β) :
    ∀ (n : ℕ) (x : α),
      ((e.trans (σ.trans e.symm) : Equiv.Perm α) : α → α)^[n] x
        = e.symm ((σ : β → β)^[n] (e x)) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      have hstep : e ((e.trans (σ.trans e.symm) : Equiv.Perm α) x) = σ (e x) := by
        simp [Equiv.trans_apply]
      rw [Function.iterate_succ_apply, ih, hstep, ← Function.iterate_succ_apply]

/-- Iterating a fibrewise permutation of a sigma type stays in its fibre. -/
private theorem iterate_sigmaCongrRight {ι : Type*} {β : ι → Type*}
    (f : ∀ i, Equiv.Perm (β i)) (i : ι) :
    ∀ (n : ℕ) (x : β i),
      ((Equiv.sigmaCongrRight f : Equiv.Perm ((j : ι) × β j)) :
          ((j : ι) × β j) → ((j : ι) × β j))^[n] ⟨i, x⟩
        = ⟨i, ((f i : β i → β i))^[n] x⟩ := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hstep : (Equiv.sigmaCongrRight f) (⟨i, x⟩ : (j : ι) × β j) = ⟨i, f i x⟩ := rfl
      rw [Function.iterate_succ_apply, hstep, ih, ← Function.iterate_succ_apply]

/-- `finRotate m` generates a transitive action on `Fin m`: any element can be
reached from any other by iterating. The witness is the translation distance,
via Mathlib's identification of `finCycle k` with the `k`-th iterate. -/
private theorem exists_finRotate_iterate {m : ℕ} (a b : Fin m) :
    ∃ j : ℕ, (finRotate m : Fin m → Fin m)^[j] a = b := by
  haveI : NeZero m := ⟨a.pos.ne'⟩
  refine ⟨(b - a).val, ?_⟩
  have h := congrFun (finCycle_eq_finRotate_iterate (n := m) (k := b - a)) a
  rw [← h, finCycle_apply]
  abel

/-- `finRotate m` has no fixed point unless `m = 1`. Proved from transitivity: a
fixed point is reachable from everything and equal to everything reachable, so
`Fin m` would be a subsingleton, which for `m ≠ 0` forces `m = 1`. -/
private theorem finRotate_ne_self {m : ℕ} (hm : m ≠ 1) (a : Fin m) :
    finRotate m a ≠ a := by
  intro hfix
  have hconst : ∀ j : ℕ, (finRotate m : Fin m → Fin m)^[j] a = a := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hall : ∀ b : Fin m, b = a := by
    intro b
    obtain ⟨j, hj⟩ := exists_finRotate_iterate a b
    rw [← hj, hconst j]
  have hm0 : m ≠ 0 := a.pos.ne'
  have h2 : 2 ≤ m := by omega
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := fun hEq =>
    Nat.zero_ne_one (congrArg Fin.val hEq)
  exact hne ((hall _).trans (hall _).symm)

/-- Distinctness of two propositions from a witness on one side. -/
private theorem prop_ne_of {P Q : Prop} (hP : P) (hQ : ¬ Q) : P ≠ Q :=
  fun hEq => hQ (cast hEq hP)

/-- Distinctness of two propositions from a witness on the other side. -/
private theorem prop_ne_of' {P Q : Prop} (hP : ¬ P) (hQ : Q) : P ≠ Q :=
  fun hEq => hP (cast hEq.symm hQ)

/-- The two elements of `Fin 2`, checked exhaustively by the kernel. -/
private theorem fin_two_cases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide

namespace FiniteGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

omit [DecidableEq V] [DecidableEq E] in
/-- Membership in a cut, unfolded once and for all. -/
theorem mem_cut {S : Finset V} {e : E} : e ∈ G.cut S ↔ G.Crosses S e := by
  classical
  simp [cut]

-- ============================================================
-- Rotation systems
-- ============================================================

/-- A cyclic successor on the half-edges at each vertex: a permutation of the
half-edges that keeps the incident vertex (`sameVertex`), has no fixed point
(`next_ne`, which is what stops the expanded rings from carrying loops) and
which sweeps out each vertex fibre (`fiberTransitive`, which is what makes
bridgelessness descend through the expansion). -/
structure RotationSystem where
  next : Equiv.Perm (HalfEdge E)
  sameVertex : ∀ h, G.vertex (next h) = G.vertex h
  next_ne : ∀ h, next h ≠ h
  fiberTransitive : ∀ h k, G.vertex h = G.vertex k →
    ∃ n : ℕ, (next : HalfEdge E → HalfEdge E)^[n] h = k

/-- The half-edges, sorted into their vertex fibres. -/
def halfEdgeSigmaEquiv : HalfEdge E ≃ (v : V) × G.halfEdgesAt v where
  toFun h := ⟨G.vertex h, h, rfl⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨h, rfl⟩⟩
    rfl

/-- A cyclic successor on a single vertex fibre, transported from `finRotate`
along any identification of the fibre with a `Fin`. -/
noncomputable def fiberCycle (v : V) : Equiv.Perm (G.halfEdgesAt v) :=
  (Fintype.equivFin (G.halfEdgesAt v)).trans
    ((finRotate (Fintype.card (G.halfEdgesAt v))).trans
      (Fintype.equivFin (G.halfEdgesAt v)).symm)

/-- All the fibre cycles at once, as a permutation of the half-edges. -/
noncomputable def rotationPerm : Equiv.Perm (HalfEdge E) :=
  (halfEdgeSigmaEquiv G).trans
    ((Equiv.sigmaCongrRight (fiberCycle G)).trans (halfEdgeSigmaEquiv G).symm)

omit [DecidableEq E] in
/-- Every fibre cycle sweeps out its fibre. -/
private theorem exists_fiberCycle_iterate (v : V) (x y : G.halfEdgesAt v) :
    ∃ n : ℕ, ((fiberCycle G v : G.halfEdgesAt v → G.halfEdgesAt v))^[n] x = y := by
  obtain ⟨n, hn⟩ := exists_finRotate_iterate
    (Fintype.equivFin (G.halfEdgesAt v) x) (Fintype.equivFin (G.halfEdgesAt v) y)
  refine ⟨n, ?_⟩
  have hunfold : ((fiberCycle G v : G.halfEdgesAt v → G.halfEdgesAt v))^[n] x
      = (((Fintype.equivFin (G.halfEdgesAt v)).trans
          ((finRotate (Fintype.card (G.halfEdgesAt v))).trans
            (Fintype.equivFin (G.halfEdgesAt v)).symm) :
              Equiv.Perm (G.halfEdgesAt v)) : G.halfEdgesAt v → G.halfEdgesAt v)^[n] x := rfl
  rw [hunfold, iterate_conj, hn, Equiv.symm_apply_apply]

omit [DecidableEq E] in
/-- The rotation permutation stays inside each vertex fibre. -/
theorem rotationPerm_sameVertex (h : HalfEdge E) :
    G.vertex (rotationPerm G h) = G.vertex h :=
  (fiberCycle G (G.vertex h) ⟨h, rfl⟩).2

omit [DecidableEq E] in
/-- The rotation permutation is fixed-point-free as soon as no vertex has degree
one, since a fibre with at least two elements is rotated nontrivially. -/
theorem rotationPerm_ne (hne : ∀ v : V, G.degree v ≠ 1) (h : HalfEdge E) :
    rotationPerm G h ≠ h := by
  intro hfix
  have hsub : fiberCycle G (G.vertex h) ⟨h, rfl⟩
      = (⟨h, rfl⟩ : G.halfEdgesAt (G.vertex h)) := Subtype.ext hfix
  have hfin : finRotate (Fintype.card (G.halfEdgesAt (G.vertex h)))
      (Fintype.equivFin (G.halfEdgesAt (G.vertex h)) ⟨h, rfl⟩)
      = Fintype.equivFin (G.halfEdgesAt (G.vertex h)) ⟨h, rfl⟩ := by
    have hcongr := congrArg (Fintype.equivFin (G.halfEdgesAt (G.vertex h))) hsub
    simpa [fiberCycle] using hcongr
  exact finRotate_ne_self (hne (G.vertex h)) _ hfin

omit [DecidableEq E] in
/-- The rotation permutation sweeps out each vertex fibre. -/
theorem rotationPerm_fiberTransitive (h k : HalfEdge E) (hvk : G.vertex h = G.vertex k) :
    ∃ n : ℕ, (rotationPerm G : HalfEdge E → HalfEdge E)^[n] h = k := by
  obtain ⟨n, hn⟩ :=
    exists_fiberCycle_iterate G (G.vertex h) ⟨h, rfl⟩ ⟨k, hvk.symm⟩
  refine ⟨n, ?_⟩
  have hunfold : (rotationPerm G : HalfEdge E → HalfEdge E)^[n] h
      = (((halfEdgeSigmaEquiv G).trans
          ((Equiv.sigmaCongrRight (fiberCycle G)).trans (halfEdgeSigmaEquiv G).symm) :
            Equiv.Perm (HalfEdge E)) : HalfEdge E → HalfEdge E)^[n] h := rfl
  calc (rotationPerm G : HalfEdge E → HalfEdge E)^[n] h
      = (halfEdgeSigmaEquiv G).symm
          ((Equiv.sigmaCongrRight (fiberCycle G) :
              ((v : V) × G.halfEdgesAt v) → ((v : V) × G.halfEdgesAt v))^[n]
            (halfEdgeSigmaEquiv G h)) := by
        rw [hunfold, iterate_conj]
    _ = (halfEdgeSigmaEquiv G).symm
          ⟨G.vertex h,
            ((fiberCycle G (G.vertex h) : G.halfEdgesAt (G.vertex h) →
              G.halfEdgesAt (G.vertex h)))^[n] ⟨h, rfl⟩⟩ :=
        iterate_sigmaCongrRight (fiberCycle G) (G.vertex h) n ⟨h, rfl⟩ ▸ rfl
    _ = (halfEdgeSigmaEquiv G).symm ⟨G.vertex h, ⟨k, hvk.symm⟩⟩ := by rw [hn]
    _ = k := rfl

/-- Every finite graph without a degree-one vertex carries a rotation system.
Fibres of size zero or at least two are rotated fixed-point-freely; size one is
the only obstruction. -/
noncomputable def rotationSystemOfDegreeNeOne (hne : ∀ v : V, G.degree v ≠ 1) :
    G.RotationSystem where
  next := rotationPerm G
  sameVertex := rotationPerm_sameVertex G
  next_ne := rotationPerm_ne G hne
  fiberTransitive := rotationPerm_fiberTransitive G

omit [DecidableEq E] in
/-- A bridgeless loopless graph has no degree-one vertex: the unique half-edge
at such a vertex would exhibit its edge as a one-element cut. -/
theorem degree_ne_one_of_bridgeless (hb : G.Bridgeless) (v : V) : G.degree v ≠ 1 := by
  classical
  intro hd
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hd
  have hcut : G.cut {v} = {u.1.1} := by
    ext k
    rw [G.mem_cut, Finset.mem_singleton]
    constructor
    · intro hk
      by_cases h0 : G.endAt k 0 = v
      · have huniq : (⟨(k, 0), h0⟩ : G.halfEdgesAt v) = u := hu _
        exact congrArg (fun w : G.halfEdgesAt v => w.1.1) huniq
      · have h1 : G.endAt k 1 = v := by
          by_contra h1'
          refine hk ?_
          rw [eq_false (show G.endAt k 0 ∉ ({v} : Finset V) by simpa using h0),
            eq_false (show G.endAt k 1 ∉ ({v} : Finset V) by simpa using h1')]
        have huniq : (⟨(k, 1), h1⟩ : G.halfEdgesAt v) = u := hu _
        exact congrArg (fun w : G.halfEdgesAt v => w.1.1) huniq
    · intro hk
      subst hk
      have hu2 : G.endAt u.1.1 u.1.2 = v := u.2
      rcases fin_two_cases u.1.2 with hj | hj
      · rw [hj] at hu2
        have hother : G.endAt u.1.1 1 ≠ v := fun hz =>
          G.loopless u.1.1 (hu2.trans hz.symm)
        exact prop_ne_of (by simp [hu2] : G.endAt u.1.1 0 ∈ ({v} : Finset V))
          (by simpa using hother)
      · rw [hj] at hu2
        have hother : G.endAt u.1.1 0 ≠ v := fun hz =>
          G.loopless u.1.1 (hz.trans hu2.symm)
        exact prop_ne_of' (by simpa using hother)
          (by simp [hu2] : G.endAt u.1.1 1 ∈ ({v} : Finset V))
  have hcard := hb {v}
  rw [hcut, Finset.card_singleton] at hcard
  exact hcard rfl

/-- The rotation system available on any bridgeless finite graph. -/
noncomputable def rotationSystemOfBridgeless (hb : G.Bridgeless) : G.RotationSystem :=
  rotationSystemOfDegreeNeOne G (degree_ne_one_of_bridgeless G hb)

-- ============================================================
-- The vertex-ring expansion
-- ============================================================

/-- Vertices of the expansion: the half-edges of the original graph. -/
abbrev ExpandedVertex (_G : FiniteGraph V E) := HalfEdge E

/-- Edges of the expansion: the original edges (*spokes*) together with one
*ring* edge for every half-edge, named by the half-edge it leaves. -/
abbrev ExpandedEdge (_G : FiniteGraph V E) := E ⊕ HalfEdge E

variable (R : G.RotationSystem)

/-- Slot `0` at an expanded vertex is its spoke, slot `1` the ring edge leaving
it, slot `2` the ring edge arriving at it. -/
private def expansionToEnd : (G.ExpandedVertex × Fin 3) → (G.ExpandedEdge × Fin 2) :=
  fun p =>
    if p.2 = 0 then (Sum.inl p.1.1, p.1.2)
    else if p.2 = 1 then (Sum.inr p.1, 0)
    else (Sum.inr (R.next.symm p.1), 1)

/-- The inverse assignment: an end of a spoke is a slot-`0`, and the two ends of
a ring edge are the slot-`1` of its name and the slot-`2` of its successor. -/
private def expansionFromEnd : (G.ExpandedEdge × Fin 2) → (G.ExpandedVertex × Fin 3)
  | (Sum.inl e, j) => ((e, j), 0)
  | (Sum.inr h, j) => if j = 0 then (h, 1) else (R.next h, 2)

omit [DecidableEq V] [DecidableEq E] in
private theorem expansionFromEnd_toEnd :
    Function.LeftInverse (expansionFromEnd G R) (expansionToEnd G R) := by
  rintro ⟨h, i⟩
  fin_cases i <;> simp [expansionToEnd, expansionFromEnd]

omit [DecidableEq V] [DecidableEq E] in
private theorem expansionToEnd_fromEnd :
    Function.RightInverse (expansionFromEnd G R) (expansionToEnd G R) := by
  rintro ⟨x, j⟩
  cases x with
  | inl e => simp [expansionToEnd, expansionFromEnd]
  | inr h => fin_cases j <;> simp [expansionToEnd, expansionFromEnd]

/-- Three local slots at every expanded vertex, matched with the two numbered
ends of every expanded edge. -/
def expansionIncidence : (G.ExpandedVertex × Fin 3) ≃ (G.ExpandedEdge × Fin 2) where
  toFun := expansionToEnd G R
  invFun := expansionFromEnd G R
  left_inv := expansionFromEnd_toEnd G R
  right_inv := expansionToEnd_fromEnd G R

/-- The vertex-ring expansion, as a cubic multigraph. -/
def cubicExpansion : CubicGraph G.ExpandedVertex G.ExpandedEdge where
  incidence := expansionIncidence G R
  loopless := by
    rintro (e | h)
    · intro hEq
      have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd hEq
      exact absurd h01 (by decide)
    · intro hEq
      exact R.next_ne h hEq.symm

/-- The same expansion presented directly as a loopless multigraph, with the two
ends of every edge written out. -/
def expansionGraph : FiniteGraph G.ExpandedVertex G.ExpandedEdge where
  endAt x j :=
    match x with
    | Sum.inl e => (e, j)
    | Sum.inr h => if j = 0 then h else R.next h
  loopless := by
    rintro (e | h)
    · intro hEq
      have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd hEq
      exact absurd h01 (by decide)
    · intro hEq
      exact R.next_ne h hEq.symm

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem expansionGraph_spoke_endAt (e : E) (j : Fin 2) :
    (expansionGraph G R).endAt (Sum.inl e) j = (e, j) := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem expansionGraph_ring_endAt_zero (h : G.ExpandedVertex) :
    (expansionGraph G R).endAt (Sum.inr h) 0 = h := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem expansionGraph_ring_endAt_one (h : G.ExpandedVertex) :
    (expansionGraph G R).endAt (Sum.inr h) 1 = R.next h := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem cubicExpansion_edgeAt_zero (h : G.ExpandedVertex) :
    (cubicExpansion G R).edgeAt h 0 = Sum.inl h.1 := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem cubicExpansion_edgeAt_one (h : G.ExpandedVertex) :
    (cubicExpansion G R).edgeAt h 1 = Sum.inr h := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem cubicExpansion_edgeAt_two (h : G.ExpandedVertex) :
    (cubicExpansion G R).edgeAt h 2 = Sum.inr (R.next.symm h) := rfl

/-- A loopless multigraph is determined by its endpoint map. -/
private theorem finiteGraph_ext {V' E' : Type*} [Fintype V'] [Fintype E']
    {A B : FiniteGraph V' E'} (hend : A.endAt = B.endAt) : A = B := by
  cases A
  cases B
  cases hend
  rfl

omit [DecidableEq V] [DecidableEq E] in
/-- Forgetting the cubic presentation of the expansion recovers the explicit
endpoint presentation. -/
theorem cubicExpansion_toFiniteGraph_eq :
    (cubicExpansion G R).toFiniteGraph = expansionGraph G R := by
  refine finiteGraph_ext ?_
  funext x j
  cases x with
  | inl e => rfl
  | inr h => rcases fin_two_cases j with hj | hj <;> rw [hj] <;> rfl

/-- **The expansion of a bridgeless graph is bridgeless.**

Suppose some one-element set `{x}` were a cut of the expansion. If `x` is a ring
edge, count crossings: writing `χ` for the `F₂`-indicator of the cut side, the
ring edge leaving `h` crosses exactly when `χ h + χ (R.next h) = 1`, and summing
that over all `h` gives `∑ χ + ∑ χ ∘ R.next = 2 ∑ χ = 0` because `R.next` is a
permutation — yet a single crossing ring edge would make the sum `1`.

So `x` must be a spoke. Then no ring edge crosses, i.e. membership of the cut
side is invariant under `R.next`, hence (by `fiberTransitive`) constant on each
vertex fibre. The set `T` of original vertices whose fibres lie inside the cut
side then has `G.cut T = {x}`, contradicting bridgelessness of `G`. -/
theorem expansionGraph_bridgeless (hb : G.Bridgeless) :
    (expansionGraph G R).Bridgeless := by
  classical
  intro S hcard
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hcross : ∀ y : G.ExpandedEdge,
      (expansionGraph G R).Crosses S y ↔ y = x := by
    intro y
    rw [← (expansionGraph G R).mem_cut, hx, Finset.mem_singleton]
  cases x with
  | inr h0 =>
      -- Ring-edge case: a parity count.
      have hpoint : ∀ h : G.ExpandedVertex,
          (if (expansionGraph G R).Crosses S (Sum.inr h) then (1 : F₂) else 0)
            = (if h ∈ S then 1 else 0) + (if R.next h ∈ S then 1 else 0) := by
        intro h
        by_cases hA : h ∈ S <;> by_cases hB : R.next h ∈ S
        · rw [if_neg (fun hc => hc (propext ⟨fun _ => hB, fun _ => hA⟩)), if_pos hA,
            if_pos hB]
          decide
        · rw [if_pos (show (expansionGraph G R).Crosses S (Sum.inr h) from prop_ne_of hA hB),
            if_pos hA, if_neg hB]
          decide
        · rw [if_pos (show (expansionGraph G R).Crosses S (Sum.inr h) from prop_ne_of' hA hB),
            if_neg hA, if_pos hB]
          decide
        · rw [if_neg (fun hc =>
              hc (propext ⟨fun hp => absurd hp hA, fun hq => absurd hq hB⟩)),
            if_neg hA, if_neg hB]
          decide
      have hzero : (∑ h : G.ExpandedVertex,
          (if (expansionGraph G R).Crosses S (Sum.inr h) then (1 : F₂) else 0)) = 0 := by
        have hshift : (∑ h : G.ExpandedVertex, (if R.next h ∈ S then (1 : F₂) else 0))
            = ∑ h : G.ExpandedVertex, (if h ∈ S then (1 : F₂) else 0) :=
          Equiv.sum_comp R.next (fun k : G.ExpandedVertex => if k ∈ S then (1 : F₂) else 0)
        calc (∑ h : G.ExpandedVertex,
                (if (expansionGraph G R).Crosses S (Sum.inr h) then (1 : F₂) else 0))
            = ∑ h : G.ExpandedVertex,
                ((if h ∈ S then (1 : F₂) else 0) + (if R.next h ∈ S then (1 : F₂) else 0)) :=
              Finset.sum_congr rfl fun h _ => hpoint h
          _ = (∑ h : G.ExpandedVertex, (if h ∈ S then (1 : F₂) else 0))
                + ∑ h : G.ExpandedVertex, (if R.next h ∈ S then (1 : F₂) else 0) :=
              Finset.sum_add_distrib
          _ = (∑ h : G.ExpandedVertex, (if h ∈ S then (1 : F₂) else 0))
                + ∑ h : G.ExpandedVertex, (if h ∈ S then (1 : F₂) else 0) := by rw [hshift]
          _ = 0 := CharTwo.add_self_eq_zero _
      have hone : (∑ h : G.ExpandedVertex,
          (if (expansionGraph G R).Crosses S (Sum.inr h) then (1 : F₂) else 0)) = 1 := by
        have hterm : ∀ h : G.ExpandedVertex,
            (if (expansionGraph G R).Crosses S (Sum.inr h) then (1 : F₂) else 0)
              = if h = h0 then 1 else 0 := by
          intro h
          by_cases hh : h = h0
          · rw [if_pos ((hcross _).mpr (by rw [hh])), if_pos hh]
          · rw [if_neg (fun hc => hh (Sum.inr_injective ((hcross _).mp hc))), if_neg hh]
        rw [Finset.sum_congr rfl
          fun h (_ : h ∈ (Finset.univ : Finset G.ExpandedVertex)) => hterm h]
        simp
      rw [hzero] at hone
      exact zero_ne_one hone
  | inl e0 =>
      -- Spoke case: the cut descends to the original graph.
      have hnoRing : ∀ h : G.ExpandedVertex,
          ¬ (expansionGraph G R).Crosses S (Sum.inr h) := by
        intro h hc
        exact Sum.inr_ne_inl ((hcross _).mp hc)
      have hnext : ∀ h : G.ExpandedVertex, (h ∈ S) = (R.next h ∈ S) := by
        intro h
        by_contra hne
        exact hnoRing h hne
      have hiter : ∀ (n : ℕ) (h : G.ExpandedVertex),
          (h ∈ S) = (((R.next : G.ExpandedVertex → G.ExpandedVertex)^[n] h) ∈ S) := by
        intro n
        induction n with
        | zero => intro h; rfl
        | succ n ih =>
            intro h
            rw [Function.iterate_succ_apply']
            exact (ih h).trans (hnext _)
      have hfibre : ∀ h k : G.ExpandedVertex,
          G.vertex h = G.vertex k → (h ∈ S) = (k ∈ S) := by
        intro h k hvk
        obtain ⟨n, hn⟩ := R.fiberTransitive h k hvk
        rw [← hn]
        exact hiter n h
      obtain ⟨T, hT⟩ : ∃ T : Finset V, ∀ h : G.ExpandedVertex, (G.vertex h ∈ T ↔ h ∈ S) := by
        refine ⟨Finset.univ.filter
          fun w => ∃ h : G.ExpandedVertex, G.vertex h = w ∧ h ∈ S, ?_⟩
        intro h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk, hkS⟩
          exact (hfibre k h hk).mp hkS
        · intro hh
          exact ⟨h, rfl, hh⟩
      have hbridge : ∀ e : E,
          G.Crosses T e ↔ (expansionGraph G R).Crosses S (Sum.inl e) := by
        intro e
        have p0 : (G.endAt e 0 ∈ T) = (((e, 0) : G.ExpandedVertex) ∈ S) :=
          propext (hT (e, 0))
        have p1 : (G.endAt e 1 ∈ T) = (((e, 1) : G.ExpandedVertex) ∈ S) :=
          propext (hT (e, 1))
        show ((G.endAt e 0 ∈ T) ≠ (G.endAt e 1 ∈ T)) ↔ _
        rw [p0, p1]
        exact Iff.rfl
      have horig : G.cut T = {e0} := by
        ext e
        rw [G.mem_cut, Finset.mem_singleton, hbridge e, hcross (Sum.inl e)]
        constructor
        · intro h
          exact Sum.inl_injective h
        · intro h
          rw [h]
      have hcardT := hb T
      rw [horig, Finset.card_singleton] at hcardT
      exact hcardT rfl

/-- Bridgelessness in exactly the shape consumed downstream: on the *forgotten*
cubic expansion. -/
theorem cubicExpansion_bridgeless (hb : G.Bridgeless) :
    (cubicExpansion G R).toFiniteGraph.Bridgeless := by
  rw [cubicExpansion_toFiniteGraph_eq G R]
  exact expansionGraph_bridgeless G R hb

-- ============================================================
-- Projecting an even double cover back along the spokes
-- ============================================================

/-- Around an original vertex the two ring contributions cancel in
characteristic two, leaving the parity condition for the spokes alone.

At each expanded vertex `h` the cubic evenness condition reads
`spoke h + ring h + ring (R.next.symm h) = 0`. Summing over the fibre of `v`,
the last two families are reindexed into each other by `R.next.symm` (which
preserves the incident vertex), so they cancel; what survives is the spoke
sum. -/
theorem projected_vertex_even
    (C : (cubicExpansion G R).IndexedEvenDoubleCover) (s : Gamma) (v : V) :
    ∑ e : E,
      ((if G.endAt e 0 = v then C.member s (Sum.inl e) else 0) +
       (if G.endAt e 1 = v then C.member s (Sum.inl e) else 0)) = 0 := by
  classical
  have hlocal : ∀ h : HalfEdge E,
      C.member s (Sum.inl h.1) + C.member s (Sum.inr h)
        + C.member s (Sum.inr (R.next.symm h)) = 0 := by
    intro h
    have hv := C.vertexEven s h
    rw [Fin.sum_univ_three, cubicExpansion_edgeAt_zero, cubicExpansion_edgeAt_one,
      cubicExpansion_edgeAt_two] at hv
    exact hv
  have hshift :
      (∑ h : HalfEdge E,
          (if G.endAt h.1 h.2 = v then C.member s (Sum.inr (R.next.symm h)) else 0))
        = ∑ h : HalfEdge E,
          (if G.endAt h.1 h.2 = v then C.member s (Sum.inr h) else 0) := by
    have hpoint : ∀ h : HalfEdge E,
        (if G.endAt h.1 h.2 = v then C.member s (Sum.inr (R.next.symm h)) else 0)
          = (fun k : HalfEdge E =>
              if G.endAt k.1 k.2 = v then C.member s (Sum.inr k) else 0) (R.next.symm h) := by
      intro h
      have hsame : G.endAt (R.next.symm h).1 (R.next.symm h).2 = G.endAt h.1 h.2 := by
        have hstep : G.vertex (R.next (R.next.symm h)) = G.vertex (R.next.symm h) :=
          R.sameVertex (R.next.symm h)
        rw [Equiv.apply_symm_apply] at hstep
        exact hstep.symm
      simp only
      rw [hsame]
    rw [Finset.sum_congr rfl fun h (_ : h ∈ (Finset.univ : Finset (HalfEdge E))) => hpoint h]
    exact Equiv.sum_comp R.next.symm
      (fun k : HalfEdge E => if G.endAt k.1 k.2 = v then C.member s (Sum.inr k) else 0)
  have htotal :
      (∑ h : HalfEdge E, (if G.endAt h.1 h.2 = v then C.member s (Sum.inl h.1) else 0))
        + ((∑ h : HalfEdge E, (if G.endAt h.1 h.2 = v then C.member s (Sum.inr h) else 0))
          + ∑ h : HalfEdge E,
              (if G.endAt h.1 h.2 = v then C.member s (Sum.inr (R.next.symm h)) else 0))
        = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun h _ => ?_
    by_cases hv : G.endAt h.1 h.2 = v
    · simp only [if_pos hv, ← add_assoc]
      exact hlocal h
    · simp only [if_neg hv, add_zero]
  rw [hshift, CharTwo.add_self_eq_zero, add_zero] at htotal
  calc ∑ e : E,
        ((if G.endAt e 0 = v then C.member s (Sum.inl e) else 0) +
         (if G.endAt e 1 = v then C.member s (Sum.inl e) else 0))
      = ∑ e : E, ∑ j : Fin 2, (if G.endAt e j = v then C.member s (Sum.inl e) else 0) :=
        Finset.sum_congr rfl fun e _ =>
          (Fin.sum_univ_two
            (fun j : Fin 2 => if G.endAt e j = v then C.member s (Sum.inl e) else 0)).symm
    _ = ∑ h : HalfEdge E, (if G.endAt h.1 h.2 = v then C.member s (Sum.inl h.1) else 0) :=
        (Fintype.sum_prod_type'
          (fun (e : E) (j : Fin 2) =>
            if G.endAt e j = v then C.member s (Sum.inl e) else 0)).symm
    _ = 0 := htotal

/-- Restricting an indexed even double cover of the expansion to the spokes
gives one on the original graph. `coveredTwice` is inherited verbatim, since an
original edge *is* a spoke. -/
def projectEvenDoubleCover (C : (cubicExpansion G R).IndexedEvenDoubleCover) :
    G.IndexedEvenDoubleCover where
  member s e := C.member s (Sum.inl e)
  vertexEven := projected_vertex_even G R C
  coveredTwice e := C.coveredTwice (Sum.inl e)

end FiniteGraph

end CycleDoubleCover
