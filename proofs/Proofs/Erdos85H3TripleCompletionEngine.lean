import Mathlib

/-!
# A sound completion engine for the order-49 three-high triple cell

This file is independent of the rest of the Erdős 85 development.  It fixes
the canonical `t = 1` labelling of the three-high stratum

* `0,1,2` high vertices,
* `3` triple support with high mask `7`,
* `4..24` singleton supports, seven per high colour,
* `25..48` empty supports,

and defines an executable three-phase search `dfs1 → dfs2 → dfs3` over
partial graphs (`St`).  The soundness theorem `search_sound` says: if the
search returns `true` on the initial state, no Boolean relation satisfying
the abstract `Model` axioms is compatible with that initial state.

The three phases are

1. `dfs1`: exactly-one colour clauses on the 22 nonempty low vertices, with
   twin (interchangeable-vertex) symmetry breaking;
2. `dfs2`: singleton/triple incidence of the empty vertices as colour
   transversal triples, named one fresh empty vertex at a time with a
   first-candidate ban;
3. `dfs3`: empty–empty edge completion with a counting gate.

Adapted from the H3 pair engine at `dc7f78d47d7017dcb8da5cc4aa200f1432a0f5df`.
The search and its proof retain the same structure; the support layout changes.
No exclusion computation is asserted in this file.
-/

namespace Erdos85
namespace H3TripleCompletion

abbrev V := Fin 49

/-- High-support mask of the canonical `t = 1` labelling. -/
def maskOf (v : V) : Nat :=
  if v.val < 3 then 0 else if v.val = 3 then 7 else if v.val < 11 then 1
  else if v.val < 18 then 2 else if v.val < 25 then 4 else 0

def col (v : V) (w : Fin 3) : Bool := (maskOf v).testBit w.val

def capOf (v : V) : Nat := if v.val < 3 then 8 else 7

def fiber0 : List V := [3, 4, 5, 6, 7, 8, 9, 10]
def fiber1 : List V := [3, 11, 12, 13, 14, 15, 16, 17]
def fiber2 : List V := [3, 18, 19, 20, 21, 22, 23, 24]

def fiberList (w : Fin 3) : List V :=
  match w with
  | 0 => fiber0
  | 1 => fiber1
  | 2 => fiber2

def fiberMask (w : Fin 3) : Nat :=
  match w with
  | 0 => 2040
  | 1 => 260104
  | 2 => 33292296

def highVerts : List V := [0, 1, 2]

def coreVerts : List V :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

def emptyVerts : List V :=
  [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47, 48]

def coreClauses : List (V × Fin 3) :=
  coreVerts.flatMap fun u => [(u, 0), (u, 1), (u, 2)]

def M49 : Nat := 2 ^ 49 - 1

/-! ## Finite facts about the labelling -/

theorem mem_fiberList : ∀ (v : V) (w : Fin 3), col v w = true → v ∈ fiberList w := by
  decide

theorem fiberList_col : ∀ (w : Fin 3) (v : V), v ∈ fiberList w → col v w = true := by
  decide

theorem col_low : ∀ (v : V) (w : Fin 3), col v w = true → 3 ≤ v.val ∧ v.val < 25 := by
  decide

theorem core_has_col : ∀ v : V, 3 ≤ v.val → v.val < 25 →
    ∃ w : Fin 3, col v w = true := by
  decide

theorem fiberMask_testBit : ∀ (v : V) (w : Fin 3),
    (fiberMask w).testBit v.val = col v w := by
  decide

theorem mem_highVerts : ∀ v : V, v.val < 3 → v ∈ highVerts := by
  decide

theorem mem_coreVerts : ∀ v : V, 3 ≤ v.val → v.val < 25 → v ∈ coreVerts := by
  decide

theorem mem_emptyVerts : ∀ v : V, 25 ≤ v.val → v ∈ emptyVerts := by
  decide

theorem maskOf_empty : ∀ v : V, 25 ≤ v.val → maskOf v = 0 := by
  decide

theorem cap_ge (v : V) : 7 ≤ capOf v := by
  unfold capOf
  split <;> omega

theorem capOf_low (v : V) (h : 3 ≤ v.val) : capOf v = 7 := by
  unfold capOf
  rw [if_neg (by omega)]

/-! ## Bit lemmas -/

theorem testBit_or_pow (r n m : Nat) :
    (r ||| 2 ^ n).testBit m = (r.testBit m || decide (n = m)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem and_bit_of_ne_zero {a b : Nat} (h : (((a &&& b) &&& M49) == 0) = false) :
    ∃ i, i < 49 ∧ a.testBit i = true ∧ b.testBit i = true := by
  by_contra hne
  have h0 : (a &&& b) &&& M49 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and]
    unfold M49
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 49
    · cases ha : a.testBit i
      · rfl
      · cases hb : b.testBit i
        · rfl
        · exact absurd ⟨i, hi, ha, hb⟩ hne
    · simp [hi]
  rw [h0] at h
  simp at h

theorem and_no_bit_of_eq_zero {a b : Nat} (h : (((a &&& b) &&& M49) == 0) = true)
    (i : Nat) (hi : i < 49) (ha : a.testBit i = true) (hb : b.testBit i = true) : False := by
  have h0 : (a &&& b) &&& M49 = 0 := by simpa using h
  have hbit : ((a &&& b) &&& M49).testBit i = true := by
    rw [Nat.testBit_and, Nat.testBit_and, ha, hb]
    unfold M49
    rw [Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [h0, Nat.zero_testBit] at hbit
  cases hbit

theorem length_le_of_nodup_subset {l₁ l₂ : List V} (d : l₁.Nodup)
    (h : ∀ y ∈ l₁, y ∈ l₂) : l₁.length ≤ l₂.length :=
  (List.subperm_of_subset d h).length_le

/-! ## Partial graphs -/

/-- A partial graph: a bit row and a neighbour list for each vertex. -/
structure St where
  rows : Vector Nat 49
  nbr : Vector (List V) 49

def St.adj (s : St) (a b : V) : Bool := (s.rows[a.val]).testBit b.val

def St.addEdge (s : St) (u x : V) : St where
  rows := (s.rows.set u.val (s.rows[u.val] ||| 2 ^ x.val)).set x.val
    (s.rows[x.val] ||| 2 ^ u.val)
  nbr := (s.nbr.set u.val (x :: s.nbr[u.val])).set x.val (u :: s.nbr[x.val])

theorem addEdge_adj_iff (s : St) (u x a b : V) (hux : u ≠ x) :
    (s.addEdge u x).adj a b = true ↔
      s.adj a b = true ∨ (a = u ∧ b = x) ∨ (a = x ∧ b = u) := by
  have hv : u.val ≠ x.val := fun h => hux (Fin.ext h)
  unfold St.adj St.addEdge
  simp only [Vector.getElem_set]
  by_cases hax : x.val = a.val
  · have hua : ¬ u.val = a.val := fun h => hv (h.trans hax.symm)
    rw [if_pos hax, testBit_or_pow]
    have hxa : a = x := Fin.ext hax.symm
    subst hxa
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨trivial, Fin.ext h.symm⟩)
    · rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
      · exact Or.inl h
      · exact absurd (congrArg Fin.val h1).symm hua
      · exact Or.inr (by rw [h2])
  · rw [if_neg hax]
    by_cases hua : u.val = a.val
    · rw [if_pos hua, testBit_or_pow]
      have hau : a = u := Fin.ext hua.symm
      subst hau
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨trivial, Fin.ext h.symm⟩)
      · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
        · exact Or.inl h
        · exact Or.inr (by rw [h2])
        · exact absurd (congrArg Fin.val h1).symm hax
    · rw [if_neg hua]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
        · exact h
        · exact absurd (congrArg Fin.val h1).symm hua
        · exact absurd (congrArg Fin.val h1).symm hax

theorem addEdge_nbr (s : St) (u x a : V) :
    (s.addEdge u x).nbr[a.val] =
      if x.val = a.val then u :: s.nbr[x.val]
      else if u.val = a.val then x :: s.nbr[u.val] else s.nbr[a.val] := by
  unfold St.addEdge
  simp only [Vector.getElem_set]

/-- Well-formedness: the bit rows are symmetric and the neighbour lists
enumerate them without repetition. -/
structure St.WF (s : St) : Prop where
  symm : ∀ a b : V, s.adj a b = s.adj b a
  nodup : ∀ a : V, (s.nbr[a.val]).Nodup
  mem : ∀ a b : V, b ∈ s.nbr[a.val] ↔ s.adj a b = true

theorem addEdge_wf {s : St} (hs : s.WF) {u x : V} (hux : u ≠ x)
    (hadj : s.adj u x = false) : (s.addEdge u x).WF := by
  have hxu : x ≠ u := fun h => hux h.symm
  have hadj' : s.adj x u = false := by rw [hs.symm x u]; exact hadj
  have hv : u.val ≠ x.val := fun h => hux (Fin.ext h)
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply Bool.eq_iff_iff.mpr
    rw [addEdge_adj_iff s u x a b hux, addEdge_adj_iff s u x b a hux, hs.symm a b]
    tauto
  · intro a
    rw [addEdge_nbr]
    by_cases hax : x.val = a.val
    · rw [if_pos hax]
      refine List.nodup_cons.mpr ⟨?_, hs.nodup x⟩
      intro hmem
      have := (hs.mem x u).mp hmem
      rw [hadj'] at this
      cases this
    · rw [if_neg hax]
      by_cases hua : u.val = a.val
      · rw [if_pos hua]
        refine List.nodup_cons.mpr ⟨?_, hs.nodup u⟩
        intro hmem
        have := (hs.mem u x).mp hmem
        rw [hadj] at this
        cases this
      · rw [if_neg hua]
        exact hs.nodup a
  · intro a b
    rw [addEdge_nbr, addEdge_adj_iff s u x a b hux]
    by_cases hax : x.val = a.val
    · have hxa : a = x := Fin.ext hax.symm
      subst hxa
      rw [if_pos rfl, List.mem_cons, hs.mem a b]
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inr ⟨rfl, h⟩)
        · exact Or.inl h
      · rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
        · exact Or.inr h
        · exact absurd h1 hxu
        · exact Or.inl h2
    · rw [if_neg hax]
      by_cases hua : u.val = a.val
      · have hau : a = u := Fin.ext hua.symm
        subst hau
        rw [if_pos rfl, List.mem_cons, hs.mem a b]
        constructor
        · rintro (h | h)
          · exact Or.inr (Or.inl ⟨rfl, h⟩)
          · exact Or.inl h
        · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
          · exact Or.inr h
          · exact Or.inl h2
          · exact absurd h1 hux
      · rw [if_neg hua, hs.mem a b]
        constructor
        · intro h
          exact Or.inl h
        · rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
          · exact h
          · exact absurd (congrArg Fin.val h1).symm hua
          · exact absurd (congrArg Fin.val h1).symm hax

/-! ## Models -/

/-- The abstract constraints on a complete adjacency relation.  They are the
relation-level order-49 constraints of the canonical `t = 1` three-high
labelling, restated without finsets. -/
structure Model (adj : V → V → Bool) : Prop where
  symm : ∀ a b, adj a b = adj b a
  irrefl : ∀ a, adj a a = false
  c4 : ∀ i j k l : V, i ≠ j → k ≠ l → adj i k = true → adj j k = true →
    adj i l = true → adj j l = true → False
  colEx : ∀ i : V, 3 ≤ i.val → ∀ w : Fin 3, ∃ k, adj i k = true ∧ col k w = true
  colUniq : ∀ i : V, 3 ≤ i.val → ∀ w : Fin 3, ∀ k l : V,
    adj i k = true → col k w = true → adj i l = true → col l w = true → k = l
  nb : ∀ i : V, ∃ L : List V, L.Nodup ∧ L.length = capOf i ∧
    ∀ j, j ∈ L ↔ adj i j = true

def Compat (s : St) (adj : V → V → Bool) : Prop :=
  ∀ a b, s.adj a b = true → adj a b = true

theorem cap_lt {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {u x : V} (hux : adj u x = true) (hsx : s.adj u x = false) :
    (s.nbr[u.val]).length < capOf u := by
  obtain ⟨L, hnd, hlen, hmem⟩ := M.nb u
  have hnd' : (x :: s.nbr[u.val]).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hs.nodup u⟩
    intro h
    have := (hs.mem u x).mp h
    rw [hsx] at this
    cases this
  have hsub : ∀ y ∈ x :: s.nbr[u.val], y ∈ L := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (hmem _).mpr hux
    · exact (hmem y).mpr (hc u y ((hs.mem u y).mp hy))
  have hle := length_le_of_nodup_subset hnd' hsub
  rw [List.length_cons, hlen] at hle
  omega

theorem exists_unknown_nbr {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    {u : V} (hdeg : (s.nbr[u.val]).length < capOf u) :
    ∃ x, adj u x = true ∧ s.adj u x = false := by
  obtain ⟨L, hnd, hlen, hmem⟩ := M.nb u
  by_contra hall
  have hsub : ∀ y ∈ L, y ∈ s.nbr[u.val] := by
    intro y hy
    apply (hs.mem u y).mpr
    by_contra hne
    apply hall
    refine ⟨y, (hmem y).mp hy, ?_⟩
    cases h : s.adj u y
    · rfl
    · exact absurd h hne
  have hle := length_le_of_nodup_subset hnd hsub
  omega

/-! ## Adding edges -/

def St.allowed (s : St) (u x : V) : Bool :=
  decide ((s.nbr[x.val]).length < capOf x) &&
    decide ((s.nbr[u.val]).length < capOf u) &&
    (s.nbr[u.val]).all fun y => ((s.rows[y.val] &&& s.rows[x.val]) &&& M49) == 0

theorem allowed_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {u x : V} (hux : adj u x = true) (hsx : s.adj u x = false) :
    s.allowed u x = true := by
  have hxu : adj x u = true := by rw [M.symm x u]; exact hux
  have hsxu : s.adj x u = false := by rw [hs.symm x u]; exact hsx
  unfold St.allowed
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨cap_lt hs M hc hxu hsxu, cap_lt hs M hc hux hsx⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro y hy
  have hsy : s.adj u y = true := (hs.mem u y).mp hy
  cases hbit : (((s.rows[y.val] &&& s.rows[x.val]) &&& M49) == 0)
  · exfalso
    obtain ⟨i, hi, hyi, hxi⟩ := and_bit_of_ne_zero hbit
    have hyz : s.adj y ⟨i, hi⟩ = true := hyi
    have hxz : s.adj x ⟨i, hi⟩ = true := hxi
    have hyx : y ≠ x := by
      intro h
      rw [h, hsx] at hsy
      cases hsy
    have huz : u ≠ ⟨i, hi⟩ := by
      intro h
      rw [← h, hsxu] at hxz
      cases hxz
    have hyu : adj y u = true := by rw [M.symm y u]; exact hc u y hsy
    exact M.c4 y x u ⟨i, hi⟩ hyx huz hyu hxu (hc _ _ hyz) (hc _ _ hxz)
  · rfl

def St.tryAdd (s : St) (u x : V) : Option St :=
  if u = x then none
  else if s.adj u x then some s
  else if s.allowed u x then some (s.addEdge u x) else none

theorem tryAdd_none {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {u x : V} (h : s.tryAdd u x = none) : adj u x = false := by
  unfold St.tryAdd at h
  split at h
  · rename_i hux
    rw [hux]
    exact M.irrefl x
  · split at h
    · cases h
    · rename_i hsx
      split at h
      · cases h
      · rename_i hal
        cases hux : adj u x
        · rfl
        · exfalso
          apply hal
          apply allowed_sound hs M hc hux
          cases hh : s.adj u x
          · rfl
          · exact absurd hh hsx

theorem tryAdd_some {s s' : St} {u x : V} (hs : s.WF) (h : s.tryAdd u x = some s') :
    s'.WF ∧ s'.adj u x = true ∧ (∀ a b, s.adj a b = true → s'.adj a b = true) ∧
    (∀ a b, s'.adj a b = true →
      s.adj a b = true ∨ (a = u ∧ b = x) ∨ (a = x ∧ b = u)) ∧
    (∀ adj, Model adj → Compat s adj → adj u x = true → Compat s' adj) := by
  unfold St.tryAdd at h
  split at h
  · cases h
  · rename_i hux
    split at h
    · rename_i hsx
      cases h
      exact ⟨hs, hsx, fun _ _ h => h, fun _ _ h => Or.inl h, fun _ _ hc _ => hc⟩
    · rename_i hsx
      have hsx' : s.adj u x = false := by
        cases hh : s.adj u x
        · rfl
        · exact absurd hh hsx
      split at h
      · cases h
        refine ⟨addEdge_wf hs hux hsx', ?_, ?_, ?_, ?_⟩
        · exact (addEdge_adj_iff s u x u x hux).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · intro a b hab
          exact (addEdge_adj_iff s u x a b hux).mpr (Or.inl hab)
        · intro a b hab
          exact (addEdge_adj_iff s u x a b hux).mp hab
        · intro adj M hc huxadj a b hab
          rcases (addEdge_adj_iff s u x a b hux).mp hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hc a b h
          · rw [h1, h2]
            exact huxadj
          · rw [h1, h2, M.symm x u]
            exact huxadj
      · cases h

/-! ## Twin transport -/

theorem swap_cases (x y a : V) :
    Equiv.swap x y a = a ∨ (a = x ∧ Equiv.swap x y a = y) ∨
      (a = y ∧ Equiv.swap x y a = x) := by
  by_cases hax : a = x
  · right
    left
    exact ⟨hax, by rw [hax, Equiv.swap_apply_left]⟩
  · by_cases hay : a = y
    · right
      right
      exact ⟨hay, by rw [hay, Equiv.swap_apply_right]⟩
    · left
      exact Equiv.swap_apply_of_ne_of_ne hax hay

/-- Swapping two low vertices with equal masks and equal known rows preserves
both the model axioms and compatibility with the partial graph. -/
theorem twin_transport {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) (x y : V) (hx : 3 ≤ x.val) (hy : 3 ≤ y.val)
    (hmask : maskOf x = maskOf y) (hrow : ∀ b, s.adj x b = s.adj y b) :
    Model (fun a b => adj (Equiv.swap x y a) (Equiv.swap x y b)) ∧
    Compat s (fun a b => adj (Equiv.swap x y a) (Equiv.swap x y b)) := by
  have hlow : ∀ a : V, 3 ≤ a.val → 3 ≤ (Equiv.swap x y a).val := by
    intro a ha
    rcases swap_cases x y a with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact ha
    · rw [h]; exact hy
    · rw [h]; exact hx
  have hcol : ∀ (a : V) (w : Fin 3), col (Equiv.swap x y a) w = col a w := by
    intro a w
    rcases swap_cases x y a with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · rw [h]
    · rw [h, h1]; unfold col; rw [hmask]
    · rw [h, h1]; unfold col; rw [hmask]
  have hcap : ∀ a : V, capOf (Equiv.swap x y a) = capOf a := by
    intro a
    rcases swap_cases x y a with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · rw [h]
    · rw [h, h1, capOf_low x hx, capOf_low y hy]
    · rw [h, h1, capOf_low x hx, capOf_low y hy]
  have hss : ∀ a : V, Equiv.swap x y (Equiv.swap x y a) = a :=
    fun a => Equiv.swap_apply_self x y a
  have hinj : Function.Injective (Equiv.swap x y) := (Equiv.swap x y).injective
  have hrow1 : ∀ a b : V, s.adj (Equiv.swap x y a) b = s.adj a b := by
    intro a b
    rcases swap_cases x y a with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · rw [h]
    · rw [h, h1]; exact (hrow b).symm
    · rw [h, h1]; exact hrow b
  have hrow2 : ∀ a b : V,
      s.adj (Equiv.swap x y a) (Equiv.swap x y b) = s.adj a b := by
    intro a b
    rw [hrow1, hs.symm, hrow1, hs.symm]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    exact M.symm _ _
  · intro a
    exact M.irrefl _
  · intro i j k l hij hkl h1 h2 h3 h4
    exact M.c4 _ _ _ _ (fun h => hij (hinj h)) (fun h => hkl (hinj h)) h1 h2 h3 h4
  · intro i hi w
    obtain ⟨k, hk, hkw⟩ := M.colEx (Equiv.swap x y i) (hlow i hi) w
    refine ⟨Equiv.swap x y k, ?_, ?_⟩
    · show adj (Equiv.swap x y i) (Equiv.swap x y (Equiv.swap x y k)) = true
      rw [hss]
      exact hk
    · rw [hcol]
      exact hkw
  · intro i hi w k l hk hkw hl hlw
    apply hinj
    exact M.colUniq (Equiv.swap x y i) (hlow i hi) w _ _ hk
      (by rw [hcol]; exact hkw) hl (by rw [hcol]; exact hlw)
  · intro i
    obtain ⟨L, hnd, hlen, hmem⟩ := M.nb (Equiv.swap x y i)
    refine ⟨L.map (Equiv.swap x y), hnd.map hinj, ?_, ?_⟩
    · rw [List.length_map, hlen, hcap]
    · intro j
      constructor
      · intro hj
        obtain ⟨a, ha, haj⟩ := List.mem_map.mp hj
        show adj (Equiv.swap x y i) (Equiv.swap x y j) = true
        rw [← haj, hss]
        exact (hmem a).mp ha
      · intro hj
        exact List.mem_map.mpr ⟨Equiv.swap x y j, (hmem _).mpr hj, hss j⟩
  · intro a b hab
    apply hc
    rw [hrow2]
    exact hab

/-! ## Phase 1: colour clauses on the nonempty low vertices -/

def clauseOpen (s : St) (u : V) (w : Fin 3) : Bool :=
  ((s.rows[u.val] &&& fiberMask w) &&& M49) == 0

theorem clauseOpen_not_adj {s : St} {u : V} {w : Fin 3} (h : clauseOpen s u w = true)
    {x : V} (hx : col x w = true) : s.adj u x = false := by
  cases hh : s.adj u x
  · rfl
  · exfalso
    exact and_no_bit_of_eq_zero h x.val x.isLt hh
      (by rw [fiberMask_testBit]; exact hx)

def twinSkip (s : St) (u : V) (w : Fin 3) (x : V) : Bool :=
  (fiberList w).any fun y =>
    decide (y.val < x.val) && decide (y ≠ u) &&
      decide (s.rows[y.val] = s.rows[x.val]) && decide (maskOf y = maskOf x)

def findClause (s : St) : Option (V × Fin 3) :=
  coreClauses.find? fun p => clauseOpen s p.1 p.2

def dfs1 (leaf : St → Bool) : Nat → St → Bool
  | 0, _ => false
  | fuel + 1, s =>
    match findClause s with
    | none => leaf s
    | some (u, w) =>
      decide (3 ≤ u.val) && clauseOpen s u w &&
        (fiberList w).all fun x =>
          decide (x = u) || twinSkip s u w x ||
            match s.tryAdd u x with
            | none => true
            | some s' => dfs1 leaf fuel s'

theorem dfs1_sound (leaf : St → Bool)
    (hleaf : ∀ s : St, s.WF → leaf s = true →
      ∀ adj, Model adj → Compat s adj → False) :
    ∀ (fuel : Nat) (s : St), s.WF → dfs1 leaf fuel s = true →
      ∀ adj, Model adj → Compat s adj → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ h
    simp [dfs1] at h
  | succ fuel ih =>
    intro s hs h adj M hc
    rw [dfs1] at h
    split at h
    · exact hleaf s hs h adj M hc
    · rename_i u w _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hu, hopen⟩, hall⟩ := h
      have key : ∀ (n : Nat) (k : V), k.val = n → ∀ adj, Model adj → Compat s adj →
          adj u k = true → col k w = true → False := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihn =>
          intro k hkn adj M hc huk hkw
          have hkmem : k ∈ fiberList w := mem_fiberList k w hkw
          have hk := (List.all_eq_true.mp hall) k hkmem
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
          have hku : k ≠ u := by
            intro h
            rw [h, M.irrefl] at huk
            cases huk
          rcases hk with (hk | hskip) | hchild
          · exact hku hk
          · unfold twinSkip at hskip
            obtain ⟨y, hy, hcond⟩ := List.any_eq_true.mp hskip
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨hlt, hyu⟩, hrows⟩, hmask⟩ := hcond
            have hyw : col y w = true := fiberList_col w y hy
            have hrow : ∀ b, s.adj y b = s.adj k b := by
              intro b
              unfold St.adj
              rw [hrows]
            obtain ⟨M', hc'⟩ := twin_transport hs M hc y k (col_low y w hyw).1
              (col_low k w hkw).1 hmask hrow
            refine ihn y.val (by omega) y rfl _ M' hc' ?_ hyw
            show adj (Equiv.swap y k u) (Equiv.swap y k y) = true
            rw [Equiv.swap_apply_left,
              Equiv.swap_apply_of_ne_of_ne (fun h => hyu h.symm) (fun h => hku h.symm)]
            exact huk
          · cases htry : s.tryAdd u k with
            | none =>
              have := tryAdd_none hs M hc htry
              rw [huk] at this
              cases this
            | some s' =>
              rw [htry] at hchild
              obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some hs htry
              exact ih s' hs' hchild adj M (hcompat adj M hc huk)
      obtain ⟨k, hk, hkw⟩ := M.colEx u hu w
      exact key k.val k rfl adj M hc hk hkw

/-! ## Phase 2: incidence triples of the empty vertices -/

abbrev Tri := V × V × V

def allTriples : List Tri :=
  fiber0.flatMap fun a => fiber1.flatMap fun b => fiber2.map fun c => (a, b, c)

def TriCol (t : Tri) : Prop :=
  col t.1 0 = true ∧ col t.2.1 1 = true ∧ col t.2.2 2 = true

def AdjAll (adj : V → V → Bool) (e : V) (t : Tri) : Prop :=
  adj e t.1 = true ∧ adj e t.2.1 = true ∧ adj e t.2.2 = true

def SFresh (s : St) (e : V) : Prop := ∀ b, s.adj e b = false

theorem sfresh_of_row_zero {s : St} {e : V} (h : s.rows[e.val] = 0) : SFresh s e := by
  intro b
  unfold St.adj
  rw [h, Nat.zero_testBit]

/-- Every fresh empty vertex has an incidence triple in the list. -/
def FreshWit (s : St) (adj : V → V → Bool) (avail : List Tri) : Prop :=
  ∀ e : V, 25 ≤ e.val → SFresh s e → ∃ t ∈ avail, AdjAll adj e t ∧ TriCol t

theorem mem_allTriples {a b c : V} (ha : col a 0 = true) (hb : col b 1 = true)
    (hcc : col c 2 = true) : (a, b, c) ∈ allTriples := by
  unfold allTriples
  refine List.mem_flatMap.mpr ⟨a, mem_fiberList a 0 ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, mem_fiberList b 1 hb, ?_⟩
  exact List.mem_map.mpr ⟨c, mem_fiberList c 2 hcc, rfl⟩

theorem freshWit_allTriples {s : St} {adj : V → V → Bool} (M : Model adj) :
    FreshWit s adj allTriples := by
  intro e he _
  have he3 : 3 ≤ e.val := by omega
  obtain ⟨a, ha, hac⟩ := M.colEx e he3 0
  obtain ⟨b, hb, hbc⟩ := M.colEx e he3 1
  obtain ⟨c, hcc, hccol⟩ := M.colEx e he3 2
  exact ⟨(a, b, c), mem_allTriples hac hbc hccol, ⟨ha, hb, hcc⟩, ⟨hac, hbc, hccol⟩⟩

def containsV (v : V) (t : Tri) : Bool :=
  (!col v 0 || decide (t.1 = v)) && (!col v 1 || decide (t.2.1 = v)) &&
    (!col v 2 || decide (t.2.2 = v))

theorem containsV_of_adj {adj : V → V → Bool} (M : Model adj) {e v : V} {t : Tri}
    (he : 3 ≤ e.val) (hev : adj e v = true) (ht : AdjAll adj e t) (hcol : TriCol t) :
    containsV v t = true := by
  unfold containsV
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · cases hv : col v 0
    · exact Or.inl rfl
    · exact Or.inr (M.colUniq e he 0 _ _ ht.1 hcol.1 hev hv)
  · cases hv : col v 1
    · exact Or.inl rfl
    · exact Or.inr (M.colUniq e he 1 _ _ ht.2.1 hcol.2.1 hev hv)
  · cases hv : col v 2
    · exact Or.inl rfl
    · exact Or.inr (M.colUniq e he 2 _ _ ht.2.2 hcol.2.2 hev hv)

def pairOK (s : St) (a b : V) : Bool :=
  decide (a = b) || (((s.rows[a.val] &&& s.rows[b.val]) &&& M49) == 0)

def insertable (s : St) (t : Tri) : Bool :=
  decide ((s.nbr[t.1.val]).length < capOf t.1) &&
    decide ((s.nbr[t.2.1.val]).length < capOf t.2.1) &&
    decide ((s.nbr[t.2.2.val]).length < capOf t.2.2) &&
    pairOK s t.1 t.2.1 && pairOK s t.1 t.2.2 && pairOK s t.2.1 t.2.2

theorem pairOK_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {e a b : V} (hfresh : SFresh s e)
    (ha : adj e a = true) (hb : adj e b = true) : pairOK s a b = true := by
  unfold pairOK
  by_cases hab : a = b
  · simp [hab]
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    cases hbit : (((s.rows[a.val] &&& s.rows[b.val]) &&& M49) == 0)
    · exfalso
      obtain ⟨i, hi, hai, hbi⟩ := and_bit_of_ne_zero hbit
      have haz : s.adj a ⟨i, hi⟩ = true := hai
      have hbz : s.adj b ⟨i, hi⟩ = true := hbi
      have hez : e ≠ ⟨i, hi⟩ := by
        intro h
        rw [← h, hs.symm a e, hfresh a] at haz
        cases haz
      have hae : adj a e = true := by rw [M.symm a e]; exact ha
      have hbe : adj b e = true := by rw [M.symm b e]; exact hb
      exact M.c4 a b e ⟨i, hi⟩ hab hez hae hbe (hc _ _ haz) (hc _ _ hbz)
    · rfl

theorem insertable_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {e : V} {t : Tri} (hfresh : SFresh s e)
    (ht : AdjAll adj e t) : insertable s t = true := by
  have hcap : ∀ a : V, adj e a = true → (s.nbr[a.val]).length < capOf a := by
    intro a ha
    have hae : adj a e = true := by rw [M.symm a e]; exact ha
    have hsae : s.adj a e = false := by rw [hs.symm a e]; exact hfresh a
    exact cap_lt hs M hc hae hsae
  unfold insertable
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hcap _ ht.1, hcap _ ht.2.1⟩, hcap _ ht.2.2⟩,
    pairOK_sound hs M hc hfresh ht.1 ht.2.1⟩,
    pairOK_sound hs M hc hfresh ht.1 ht.2.2⟩,
    pairOK_sound hs M hc hfresh ht.2.1 ht.2.2⟩

theorem freshWit_filter {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {avail : List Tri} (hw : FreshWit s adj avail) :
    FreshWit s adj (avail.filter (insertable s)) := by
  intro e he hfresh
  obtain ⟨t, ht, hadj, hcol⟩ := hw e he hfresh
  exact ⟨t, List.mem_filter.mpr ⟨ht, insertable_sound hs M hc hfresh hadj⟩, hadj, hcol⟩

def hasCol (s : St) (a : V) (w : Fin 3) : Bool :=
  !(((s.rows[a.val] &&& fiberMask w) &&& M49) == 0)

theorem hasCol_sound {s : St} {a : V} {w : Fin 3} (h : hasCol s a w = true) :
    ∃ y : V, s.adj a y = true ∧ col y w = true := by
  unfold hasCol at h
  have h' : (((s.rows[a.val] &&& fiberMask w) &&& M49) == 0) = false := by
    cases hh : (((s.rows[a.val] &&& fiberMask w) &&& M49) == 0)
    · rfl
    · rw [hh] at h
      cases h
  obtain ⟨i, hi, hai, hfi⟩ := and_bit_of_ne_zero h'
  refine ⟨⟨i, hi⟩, hai, ?_⟩
  rw [← fiberMask_testBit]
  exact hfi

def hasAllCols (s : St) (a : V) : Bool := hasCol s a 0 && hasCol s a 1 && hasCol s a 2

theorem hasAllCols_sound {s : St} {a : V} (h : hasAllCols s a = true) (w : Fin 3) :
    ∃ y : V, s.adj a y = true ∧ col y w = true := by
  unfold hasAllCols at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  match w with
  | 0 => exact hasCol_sound h0
  | 1 => exact hasCol_sound h1
  | 2 => exact hasCol_sound h2

/-- Runtime closure check used by phase 2: highs are full, nonempty low
vertices have all colour neighbours, and each empty vertex is either
untouched or has all colour neighbours. -/
def stateOK (s : St) : Bool :=
  (highVerts.all fun h => decide ((s.nbr[h.val]).length = capOf h)) &&
    (coreVerts.all fun a => hasAllCols s a) &&
    (emptyVerts.all fun e => (s.rows[e.val] == 0) || hasAllCols s e)

/-- The fibre masks already have no bits above 48. Cache the row and avoid
three redundant intersections with M49. -/
@[inline] def hasAllColsFast (s : St) (a : V) : Bool :=
  let row := s.rows[a.val]
  !((row &&& 2040) == 0) && !((row &&& 260104) == 0) &&
    !((row &&& 33292296) == 0)

theorem hasAllColsFast_eq (s : St) (a : V) :
    hasAllColsFast s a = hasAllCols s a := by
  unfold hasAllColsFast hasAllCols hasCol
  simp only [fiberMask, Nat.and_assoc]
  rfl

def stateOKFast (s : St) : Bool :=
  (highVerts.all fun h => decide ((s.nbr[h.val]).length = capOf h)) &&
    (coreVerts.all fun a => hasAllColsFast s a) &&
    (emptyVerts.all fun e => (s.rows[e.val] == 0) || hasAllColsFast s e)

theorem stateOKFast_eq (s : St) : stateOKFast s = stateOK s := by
  simp only [stateOKFast, stateOK, hasAllColsFast_eq]

theorem exists_fresh_nbr {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) (hok : stateOK s = true) {v : V} (hv3 : 3 ≤ v.val)
    (hv25 : v.val < 25) (hdeg : (s.nbr[v.val]).length < 7) :
    ∃ e : V, 25 ≤ e.val ∧ s.rows[e.val] = 0 ∧ adj v e = true := by
  unfold stateOK at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hhigh, hcore⟩, hempty⟩ := hok
  have hdeg' : (s.nbr[v.val]).length < capOf v := by
    rw [capOf_low v hv3]
    exact hdeg
  obtain ⟨x, hvx, hsvx⟩ := exists_unknown_nbr hs M hdeg'
  have hxv : adj x v = true := by rw [M.symm x v]; exact hvx
  have hsxv : s.adj x v = false := by rw [hs.symm x v]; exact hsvx
  by_cases hx3 : x.val < 3
  · exfalso
    have hfull := (List.all_eq_true.mp hhigh) x (mem_highVerts x hx3)
    simp only [decide_eq_true_eq] at hfull
    have := cap_lt hs M hc hxv hsxv
    omega
  · by_cases hx25 : x.val < 25
    · exfalso
      obtain ⟨w, hw⟩ := core_has_col x (by omega) hx25
      have hvall := (List.all_eq_true.mp hcore) v (mem_coreVerts v hv3 hv25)
      obtain ⟨y, hvy, hyw⟩ := hasAllCols_sound hvall w
      have hyx : y = x := M.colUniq v hv3 w y x (hc v y hvy) hyw hvx hw
      rw [hyx, hsvx] at hvy
      cases hvy
    · have hx25' : 25 ≤ x.val := by omega
      by_cases hrow : s.rows[x.val] = 0
      · exact ⟨x, hx25', hrow, hvx⟩
      · exfalso
        have hxe := (List.all_eq_true.mp hempty) x (mem_emptyVerts x hx25')
        simp only [Bool.or_eq_true, beq_iff_eq] at hxe
        rcases hxe with hxe | hxe
        · exact hrow hxe
        · obtain ⟨w, hw⟩ := core_has_col v hv3 hv25
          obtain ⟨y, hxy, hyw⟩ := hasAllCols_sound hxe w
          have hyv : y = v := M.colUniq x (by omega) w y v (hc x y hxy) hyw hxv hw
          rw [hyv, hsxv] at hxy
          cases hxy

/-- Occurrence counts of the vertices in a list of triples (heuristic only). -/
def triCounts (avail : List Tri) : Array Nat :=
  avail.foldl (fun cnt t =>
    let cnt := cnt.modify t.1.val (· + 1)
    let cnt := if t.2.1 = t.1 then cnt else cnt.modify t.2.1.val (· + 1)
    if t.2.2 = t.1 ∨ t.2.2 = t.2.1 then cnt else cnt.modify t.2.2.val (· + 1))
    (Array.replicate 49 0)

/-- Choose the deficient nonempty vertex minimizing candidate count divided by
remaining degree. Cross multiplication avoids division and preserves the first
vertex on ties. `dfs2` soundness is independent of this ordering. -/
def pickCore (s : St) (avail : List Tri) : Option V :=
  let cnt := triCounts avail
  (coreVerts.foldl (fun (best : Option (Nat × Nat × V)) v =>
    let need := 7 - (s.nbr[v.val]).length
    if 0 < need then
      let c := cnt[v.val]!
      match best with
      | none => some (c, need, v)
      | some (c', need', _) =>
        if c * need' < c' * need then some (c, need, v) else best
    else best) none).map fun p => p.2.2

def findFresh (s : St) : Option V :=
  emptyVerts.find? fun e => s.rows[e.val] == 0

def addTri (s : St) (n : V) (t : Tri) : Option St :=
  match s.tryAdd n t.1 with
  | none => none
  | some s1 =>
    match s1.tryAdd n t.2.1 with
    | none => none
    | some s2 => s2.tryAdd n t.2.2

theorem addTri_ne_none {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {n : V} {t : Tri} (ht : AdjAll adj n t) :
    addTri s n t ≠ none := by
  intro h
  unfold addTri at h
  cases h1 : s.tryAdd n t.1 with
  | none =>
    have := tryAdd_none hs M hc h1
    rw [ht.1] at this
    cases this
  | some s1 =>
    rw [h1] at h
    dsimp only at h
    obtain ⟨hs1, _, _, _, hc1⟩ := tryAdd_some hs h1
    have hc1' := hc1 adj M hc ht.1
    cases h2 : s1.tryAdd n t.2.1 with
    | none =>
      have := tryAdd_none hs1 M hc1' h2
      rw [ht.2.1] at this
      cases this
    | some s2 =>
      rw [h2] at h
      dsimp only at h
      obtain ⟨hs2, _, _, _, hc2⟩ := tryAdd_some hs1 h2
      have hc2' := hc2 adj M hc1' ht.2.1
      have := tryAdd_none hs2 M hc2' h
      rw [ht.2.2] at this
      cases this

theorem addTri_some {s s' : St} {n : V} {t : Tri} (hs : s.WF)
    (h : addTri s n t = some s') :
    s'.WF ∧ s'.adj n t.1 = true ∧ (∀ a b, s.adj a b = true → s'.adj a b = true) ∧
    (∀ adj, Model adj → Compat s adj → AdjAll adj n t → Compat s' adj) := by
  unfold addTri at h
  cases h1 : s.tryAdd n t.1 with
  | none =>
    rw [h1] at h
    cases h
  | some s1 =>
    rw [h1] at h
    dsimp only at h
    obtain ⟨hs1, he1, hm1, _, hc1⟩ := tryAdd_some hs h1
    cases h2 : s1.tryAdd n t.2.1 with
    | none =>
      rw [h2] at h
      cases h
    | some s2 =>
      rw [h2] at h
      dsimp only at h
      obtain ⟨hs2, _, hm2, _, hc2⟩ := tryAdd_some hs1 h2
      obtain ⟨hs3, _, hm3, _, hc3⟩ := tryAdd_some hs2 h
      refine ⟨hs3, hm3 _ _ (hm2 _ _ he1), fun a b hab => hm3 _ _ (hm2 _ _ (hm1 _ _ hab)), ?_⟩
      intro adj M hc ht
      exact hc3 adj M (hc2 adj M (hc1 adj M hc ht.1) ht.2.1) ht.2.2

def patLoop (f : Tri → List Tri → Bool) (pre : List Tri) : List Tri → Bool
  | [] => true
  | c :: rest => f c (pre ++ c :: rest) && patLoop f pre rest

theorem patLoop_sound {f : Tri → List Tri → Bool} {pre : List Tri}
    {Good : (V → V → Bool) → Prop} {Hit : (V → V → Bool) → Tri → Prop}
    {Wit : (V → V → Bool) → List Tri → Prop}
    (hnil : ∀ adj, Good adj → Wit adj pre → False)
    (hsplit : ∀ adj c l, Good adj → Wit adj (pre ++ c :: l) → ¬ Hit adj c →
      Wit adj (pre ++ l))
    (hchild : ∀ adj c av, Good adj → Wit adj av → Hit adj c → f c av = true → False) :
    ∀ cs, patLoop f pre cs = true → ∀ adj, Good adj → Wit adj (pre ++ cs) → False := by
  intro cs
  induction cs with
  | nil =>
    intro _ adj hg hw
    rw [List.append_nil] at hw
    exact hnil adj hg hw
  | cons c rest ih =>
    intro h adj hg hw
    rw [patLoop] at h
    simp only [Bool.and_eq_true] at h
    by_cases hit : Hit adj c
    · exact hchild adj c _ hg hw hit h.1
    · exact ih h.2 adj hg (hsplit adj c rest hg hw hit)

def containsM (m : Nat) (v : V) (t : Tri) : Bool :=
  (!m.testBit 0 || decide (t.1 = v)) && (!m.testBit 1 || decide (t.2.1 = v)) &&
    (!m.testBit 2 || decide (t.2.2 = v))

/-- `patLoop` on the available triples split by whether they contain `v`. -/
def patLoopSplit (f : Tri → List Tri → Bool) (v : V) (avail : List Tri) : Bool :=
  let m := maskOf v
  patLoop f (avail.filter fun t => !containsM m v t) (avail.filter fun t => containsM m v t)

theorem patLoopSplit_eq (f : Tri → List Tri → Bool) (v : V) (avail : List Tri) :
    patLoopSplit f v avail =
      patLoop f (avail.filter fun t => !containsV v t)
        (avail.filter fun t => containsV v t) := rfl

/-- One phase-2 node, with the recursive call abstracted. -/
def step2 (leaf : St → Bool) (rec : St → List Tri → Bool) (s : St)
    (avail : List Tri) : Bool :=
  match pickCore s avail with
  | none => leaf s
  | some v =>
    decide (3 ≤ v.val) && decide (v.val < 25) &&
      decide ((s.nbr[v.val]).length < 7) &&
      match findFresh s with
      | none => true
      | some n =>
        decide (25 ≤ n.val) && (s.rows[n.val] == 0) &&
          patLoopSplit
            (fun c av =>
              match addTri s n c with
              | none => true
              | some s' => rec s' av)
            v avail

def dfs2 (leaf : St → Bool) : Nat → St → List Tri → Bool
  | 0, _, _ => false
  | fuel + 1, s, avail0 =>
    stateOKFast s && step2 leaf (dfs2 leaf fuel) s (avail0.filter (insertable s))

theorem tri_fixed {x y : V} (hx : 25 ≤ x.val) (hy : 25 ≤ y.val) {a : V} {w : Fin 3}
    (ha : col a w = true) : Equiv.swap x y a = a := by
  have hlt := (col_low a w ha).2
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    rw [h] at hlt
    omega
  · intro h
    rw [h] at hlt
    omega

theorem dfs2_sound (leaf : St → Bool)
    (hleaf : ∀ s : St, s.WF → leaf s = true →
      ∀ adj, Model adj → Compat s adj → False) :
    ∀ (fuel : Nat) (s : St) (avail0 : List Tri), s.WF →
      dfs2 leaf fuel s avail0 = true →
      ∀ adj, Model adj → Compat s adj → FreshWit s adj avail0 → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s avail0 _ h
    simp [dfs2] at h
  | succ fuel ih =>
    intro s avail0 hs h adj M hc hw0
    rw [dfs2, stateOKFast_eq] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hok, h⟩ := h
    have hw := freshWit_filter hs M hc hw0
    generalize avail0.filter (insertable s) = avail at h hw
    unfold step2 at h
    split at h
    · exact hleaf s hs h adj M hc
    · rename_i v _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hv3, hv25⟩, hvdeg⟩, h⟩ := h
      split at h
      · rename_i hnone
        obtain ⟨e, he25, herow, _⟩ := exists_fresh_nbr hs M hc hok hv3 hv25 hvdeg
        have := (List.find?_eq_none.mp hnone) e (mem_emptyVerts e he25)
        apply this
        rw [herow]
        rfl
      · rename_i n _
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨hn25, hnrow⟩, hloop⟩ := h
        rw [patLoopSplit_eq] at hloop
        have hnfresh : SFresh s n := sfresh_of_row_zero hnrow
        refine patLoop_sound
          (Good := fun adj => Model adj ∧ Compat s adj)
          (Hit := fun adj c => ∃ e : V, 25 ≤ e.val ∧ SFresh s e ∧ AdjAll adj e c ∧ TriCol c)
          (Wit := fun adj av => FreshWit s adj av)
          ?_ ?_ ?_ _ hloop adj ⟨M, hc⟩ ?_
        · -- no candidate left
          rintro adj ⟨M, hc⟩ hw
          obtain ⟨e, he25, herow, hve⟩ := exists_fresh_nbr hs M hc hok hv3 hv25 hvdeg
          obtain ⟨t, ht, hadj, hcol⟩ := hw e he25 (sfresh_of_row_zero herow)
          have hcont : containsV v t = true :=
            containsV_of_adj M (by omega) (by rw [M.symm e v]; exact hve) hadj hcol
          have := (List.mem_filter.mp ht).2
          rw [hcont] at this
          cases this
        · -- skipping a candidate that no fresh vertex realises
          rintro adj c l ⟨M, hc⟩ hw hit e he hfresh
          obtain ⟨t, ht, hadj, hcol⟩ := hw e he hfresh
          refine ⟨t, ?_, hadj, hcol⟩
          rcases List.mem_append.mp ht with ht | ht
          · exact List.mem_append.mpr (Or.inl ht)
          · rcases List.mem_cons.mp ht with ht | ht
            · exfalso
              apply hit
              rw [← ht]
              exact ⟨e, he, hfresh, hadj, hcol⟩
            · exact List.mem_append.mpr (Or.inr ht)
        · -- the child realised by a fresh vertex
          rintro adj c av ⟨M, hc⟩ hw ⟨e, he25, hefresh, headj, hccol⟩ hf
          have hmask : maskOf e = maskOf n := by
            rw [maskOf_empty e he25, maskOf_empty n hn25]
          have hrow : ∀ b, s.adj e b = s.adj n b := by
            intro b
            rw [hefresh b, hnfresh b]
          obtain ⟨M', hc'⟩ := twin_transport hs M hc e n (by omega) (by omega) hmask hrow
          have hfix : ∀ (a : V) (w : Fin 3), col a w = true → Equiv.swap e n a = a :=
            fun a w ha => tri_fixed he25 hn25 ha
          have hadj' : AdjAll (fun a b => adj (Equiv.swap e n a) (Equiv.swap e n b)) n c := by
            refine ⟨?_, ?_, ?_⟩
            · show adj (Equiv.swap e n n) (Equiv.swap e n c.1) = true
              rw [Equiv.swap_apply_right, hfix _ 0 hccol.1]
              exact headj.1
            · show adj (Equiv.swap e n n) (Equiv.swap e n c.2.1) = true
              rw [Equiv.swap_apply_right, hfix _ 1 hccol.2.1]
              exact headj.2.1
            · show adj (Equiv.swap e n n) (Equiv.swap e n c.2.2) = true
              rw [Equiv.swap_apply_right, hfix _ 2 hccol.2.2]
              exact headj.2.2
          cases hadd : addTri s n c with
          | none => exact addTri_ne_none hs M' hc' hadj' hadd
          | some s' =>
            simp only [hadd] at hf
            obtain ⟨hs', hedge, hmono, hcompat⟩ := addTri_some hs hadd
            refine ih s' av hs' hf _ M' (hcompat _ M' hc' hadj') ?_
            intro e' he' hfresh'
            have hfresh_s : SFresh s e' := by
              intro b
              cases hh : s.adj e' b
              · rfl
              · have := hmono _ _ hh
                rw [hfresh' b] at this
                cases this
            have hne : e' ≠ n := by
              intro h
              rw [h] at hfresh'
              rw [hfresh' c.1] at hedge
              cases hedge
            have hswap : 25 ≤ (Equiv.swap e n e').val ∧ SFresh s (Equiv.swap e n e') := by
              rcases swap_cases e n e' with h | ⟨_, h⟩ | ⟨h1, _⟩
              · rw [h]
                exact ⟨he', hfresh_s⟩
              · rw [h]
                exact ⟨hn25, hnfresh⟩
              · exact absurd h1 hne
            obtain ⟨t, ht, htadj, htcol⟩ := hw _ hswap.1 hswap.2
            refine ⟨t, ht, ⟨?_, ?_, ?_⟩, htcol⟩
            · show adj (Equiv.swap e n e') (Equiv.swap e n t.1) = true
              rw [hfix _ 0 htcol.1]
              exact htadj.1
            · show adj (Equiv.swap e n e') (Equiv.swap e n t.2.1) = true
              rw [hfix _ 1 htcol.2.1]
              exact htadj.2.1
            · show adj (Equiv.swap e n e') (Equiv.swap e n t.2.2) = true
              rw [hfix _ 2 htcol.2.2]
              exact htadj.2.2
        · -- the split list still witnesses every fresh vertex
          intro e he hfresh
          obtain ⟨t, ht, hadj, hcol⟩ := hw e he hfresh
          refine ⟨t, ?_, hadj, hcol⟩
          cases hcv : containsV v t
          · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨ht, by rw [hcv]; rfl⟩))
          · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨ht, hcv⟩))

/-! ## Phase 3: empty–empty edges -/

def cands3 (s : St) (u : V) : List V :=
  (List.finRange 49).filter fun x => decide (x ≠ u) && !s.adj u x && s.allowed u x

def gate3 (s : St) : Bool :=
  emptyVerts.any fun u =>
    decide ((s.nbr[u.val]).length < 7) &&
      decide ((s.nbr[u.val]).length + (cands3 s u).length < 7)

def pick3 (s : St) : Option V :=
  (emptyVerts.foldl (fun (best : Option (Nat × V)) u =>
    if (s.nbr[u.val]).length < 7 then
      let cnt := (cands3 s u).length
      match best with
      | none => some (cnt, u)
      | some (c, _) => if cnt < c then some (cnt, u) else best
    else best) none).map fun p => p.2

theorem mem_cands3 {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {u x : V} (hux : adj u x = true) (hsx : s.adj u x = false) :
    x ∈ cands3 s u := by
  unfold cands3
  refine List.mem_filter.mpr ⟨List.mem_finRange x, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨?_, hsx⟩, allowed_sound hs M hc hux hsx⟩
  intro h
  rw [h, M.irrefl] at hux
  cases hux

theorem count_gate {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model adj)
    (hc : Compat s adj) {u : V}
    (h : (s.nbr[u.val]).length + (cands3 s u).length < 7) : False := by
  obtain ⟨L, hnd, hlen, hmem⟩ := M.nb u
  have hsub : ∀ y ∈ L, y ∈ s.nbr[u.val] ++ cands3 s u := by
    intro y hy
    have huy := (hmem y).mp hy
    cases hsy : s.adj u y
    · exact List.mem_append.mpr (Or.inr (mem_cands3 hs M hc huy hsy))
    · exact List.mem_append.mpr (Or.inl ((hs.mem u y).mpr hsy))
  have hle := length_le_of_nodup_subset hnd hsub
  rw [List.length_append, hlen] at hle
  have := cap_ge u
  omega

def addMany (s : St) (u : V) : List V → Option St
  | [] => some s
  | x :: xs =>
    match s.tryAdd u x with
    | none => none
    | some s' => addMany s' u xs

theorem addMany_ne_none {adj : V → V → Bool} (M : Model adj) {u : V} :
    ∀ (xs : List V) (s : St), s.WF → Compat s adj → (∀ x ∈ xs, adj u x = true) →
      addMany s u xs ≠ none := by
  intro xs
  induction xs with
  | nil =>
    intro s _ _ _ h
    simp [addMany] at h
  | cons x xs ih =>
    intro s hs hc hall h
    rw [addMany] at h
    have hx : adj u x = true := hall x (List.mem_cons_self ..)
    cases htry : s.tryAdd u x with
    | none =>
      have := tryAdd_none hs M hc htry
      rw [hx] at this
      cases this
    | some s' =>
      rw [htry] at h
      dsimp only at h
      obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some hs htry
      exact ih s' hs' (hcompat adj M hc hx)
        (fun y hy => hall y (List.mem_cons_of_mem _ hy)) h

theorem addMany_some {u : V} :
    ∀ (xs : List V) (s s' : St), s.WF → addMany s u xs = some s' →
      s'.WF ∧ ∀ adj, Model adj → Compat s adj → (∀ x ∈ xs, adj u x = true) →
        Compat s' adj := by
  intro xs
  induction xs with
  | nil =>
    intro s s' hs h
    rw [addMany] at h
    cases h
    exact ⟨hs, fun _ _ hc _ => hc⟩
  | cons x xs ih =>
    intro s s' hs h
    rw [addMany] at h
    cases htry : s.tryAdd u x with
    | none =>
      rw [htry] at h
      cases h
    | some s1 =>
      rw [htry] at h
      dsimp only at h
      obtain ⟨hs1, _, _, _, hcompat⟩ := tryAdd_some hs htry
      obtain ⟨hs', hc'⟩ := ih s1 s' hs1 h
      refine ⟨hs', ?_⟩
      intro adj M hc hall
      exact hc' adj M (hcompat adj M hc (hall x (List.mem_cons_self ..)))
        (fun y hy => hall y (List.mem_cons_of_mem _ hy))

def dfs3 : Nat → St → Bool
  | 0, _ => false
  | fuel + 1, s =>
    gate3 s ||
      match pick3 s with
      | none => false
      | some u =>
        (List.sublistsLen (capOf u - (s.nbr[u.val]).length) (cands3 s u)).all fun B =>
          match addMany s u B with
          | none => true
          | some s' => dfs3 fuel s'

theorem dfs3_sound :
    ∀ (fuel : Nat) (s : St), s.WF → dfs3 fuel s = true →
      ∀ adj, Model adj → Compat s adj → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ h
    simp [dfs3] at h
  | succ fuel ih =>
    intro s hs h adj M hc
    rw [dfs3] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hgate | h
    · unfold gate3 at hgate
      obtain ⟨u, _, hu⟩ := List.any_eq_true.mp hgate
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
      exact count_gate hs M hc hu.2
    · split at h
      · cases h
      · rename_i u _
        obtain ⟨L, hnd, hlen, hmem⟩ := M.nb u
        have hsub : ∀ y ∈ L, y ∈ s.nbr[u.val] ++
            (cands3 s u).filter (fun x => adj u x) := by
          intro y hy
          have huy := (hmem y).mp hy
          cases hsy : s.adj u y
          · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
              ⟨mem_cands3 hs M hc huy hsy, huy⟩))
          · exact List.mem_append.mpr (Or.inl ((hs.mem u y).mpr hsy))
        have hle := length_le_of_nodup_subset hnd hsub
        rw [List.length_append, hlen] at hle
        have hB : ((cands3 s u).filter (fun x => adj u x)).take
            (capOf u - (s.nbr[u.val]).length) ∈
            List.sublistsLen (capOf u - (s.nbr[u.val]).length) (cands3 s u) := by
          apply List.mem_sublistsLen.mpr
          refine ⟨(List.take_sublist _ _).trans List.filter_sublist, ?_⟩
          rw [List.length_take]
          omega
        have hall : ∀ x ∈ ((cands3 s u).filter (fun x => adj u x)).take
            (capOf u - (s.nbr[u.val]).length), adj u x = true := by
          intro x hx
          exact (List.mem_filter.mp (List.mem_of_mem_take hx)).2
        have hx := (List.all_eq_true.mp h) _ hB
        cases hadd : addMany s u (((cands3 s u).filter (fun x => adj u x)).take
            (capOf u - (s.nbr[u.val]).length)) with
        | none => exact addMany_ne_none M _ s hs hc hall hadd
        | some s' =>
          simp only [hadd] at hx
          obtain ⟨hs', hcompat⟩ := addMany_some _ s s' hs hadd
          exact ih s' hs' hx adj M (hcompat adj M hc hall)

/-! ## The composed search -/

def leaf2 (fuel3 : Nat) (s : St) : Bool := dfs3 fuel3 s

def leaf1 (fuel2 fuel3 : Nat) (s : St) : Bool :=
  dfs2 (leaf2 fuel3) fuel2 s allTriples

/-- The complete three-phase search from a given partial graph. -/
def search (fuel1 fuel2 fuel3 : Nat) (s : St) : Bool :=
  dfs1 (leaf1 fuel2 fuel3) fuel1 s

theorem leaf1_sound (fuel2 fuel3 : Nat) (s : St) (hs : s.WF)
    (h : leaf1 fuel2 fuel3 s = true) :
    ∀ adj, Model adj → Compat s adj → False := by
  intro adj M hc
  exact dfs2_sound (leaf2 fuel3)
    (fun s hs h adj M hc => dfs3_sound fuel3 s hs h adj M hc)
    fuel2 s allTriples hs h adj M hc (freshWit_allTriples M)

/-- Soundness of the composed search: a `true` result excludes every model
compatible with the partial graph. -/
theorem search_sound (fuel1 fuel2 fuel3 : Nat) (s : St) (hs : s.WF)
    (h : search fuel1 fuel2 fuel3 s = true) :
    ∀ adj, Model adj → Compat s adj → False :=
  dfs1_sound (leaf1 fuel2 fuel3) (leaf1_sound fuel2 fuel3) fuel1 s hs h

end H3TripleCompletion
end Erdos85

#print axioms Erdos85.H3TripleCompletion.search_sound
