import Proofs.Erdos85H3PairEngine

/-!
# A sound completion engine for the order-49 five-high cells

This file generalizes the pair-cell engine of `Erdos85H3PairEngine` to the
three canonical five-high labellings (`c = 0, 1, 2` triple supports):

* `0..4` high vertices,
* then the triple supports, the uncovered pair supports and the singleton
  supports grouped by high colour (the "core", indices `5 .. e0 c - 1`),
* `e0 c .. 48` empty supports.

The partial-graph type `St`, its edge insertion and well-formedness lemmas
are reused from the pair engine.  Everything that mentions the labelling
(`Model`, the three search phases and their soundness proofs) is restated
here with the cell index `c` as a parameter and five colours.

Differences from the pair engine:

* phase 1 takes its clause list as an argument and rejects a state as soon
  as some open colour clause has no admissible candidate (`clauseDead`);
* phase-1 soundness is proved once for a family of leaf tests
  (`dfs1_sound_fam`), which gives both the plain and the split form;
* phase-2 patterns are lists of vertices (one neighbour per colour) rather
  than triples.

No finite computation is asserted in this file.
-/

namespace Erdos85
namespace H5

open H3Pair (V St M49 Compat SFresh pairOK testBit_or_pow and_bit_of_ne_zero
  and_no_bit_of_eq_zero length_le_of_nodup_subset addEdge_adj_iff addEdge_nbr
  addEdge_wf swap_cases sfresh_of_row_zero)

/-! ## The three canonical labellings -/

def maskArr (c : Fin 3) : Array Nat :=
  match c with
  | 0 => #[0, 0, 0, 0, 0, 3, 5, 9, 17, 6, 10, 18, 12, 20, 24, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4, 8, 8, 8, 8, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => #[0, 0, 0, 0, 0, 7, 9, 17, 10, 18, 12, 20, 24, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8, 8, 8, 8, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => #[0, 0, 0, 0, 0, 7, 25, 10, 18, 12, 20, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def e0 (c : Fin 3) : Nat :=
  match c with
  | 0 => 35
  | 1 => 36
  | 2 => 37

def fiberList (c : Fin 3) (w : Fin 5) : List V :=
  match c, w with
  | 0, 0 => [5, 6, 7, 8, 15, 16, 17, 18]
  | 0, 1 => [5, 9, 10, 11, 19, 20, 21, 22]
  | 0, 2 => [6, 9, 12, 13, 23, 24, 25, 26]
  | 0, 3 => [7, 10, 12, 14, 27, 28, 29, 30]
  | 0, 4 => [8, 11, 13, 14, 31, 32, 33, 34]
  | 1, 0 => [5, 6, 7, 13, 14, 15, 16, 17]
  | 1, 1 => [5, 8, 9, 18, 19, 20, 21, 22]
  | 1, 2 => [5, 10, 11, 23, 24, 25, 26, 27]
  | 1, 3 => [6, 8, 10, 12, 28, 29, 30, 31]
  | 1, 4 => [7, 9, 11, 12, 32, 33, 34, 35]
  | 2, 0 => [5, 6, 11, 12, 13, 14, 15, 16]
  | 2, 1 => [5, 7, 8, 17, 18, 19, 20, 21]
  | 2, 2 => [5, 9, 10, 22, 23, 24, 25, 26]
  | 2, 3 => [6, 7, 9, 27, 28, 29, 30, 31]
  | 2, 4 => [6, 8, 10, 32, 33, 34, 35, 36]

def fiberMask (c : Fin 3) (w : Fin 5) : Nat :=
  match c, w with
  | 0, 0 => 492000
  | 0, 1 => 7867936
  | 0, 2 => 125841984
  | 0, 3 => 2013287552
  | 0, 4 => 32212281600
  | 1, 0 => 254176
  | 1, 1 => 8127264
  | 1, 2 => 260049952
  | 1, 3 => 4026537280
  | 1, 4 => 64424516224
  | 2, 0 => 129120
  | 2, 1 => 4063648
  | 2, 2 => 130024992
  | 2, 3 => 4160750272
  | 2, 4 => 133143987520

def coreVerts (c : Fin 3) : List V :=
  match c with
  | 0 => [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
  | 1 => [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
  | 2 => [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]

def emptyVerts (c : Fin 3) : List V :=
  match c with
  | 0 => [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]
  | 1 => [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]
  | 2 => [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]

def maskOf (c : Fin 3) (v : V) : Nat := (maskArr c).getD v.val 0

def col (c : Fin 3) (v : V) (w : Fin 5) : Bool := (maskOf c v).testBit w.val

def capOf (v : V) : Nat := if v.val < 5 then 8 else 7

def highVerts : List V := [0, 1, 2, 3, 4]

def clausesOf (vs : List V) : List (V × Fin 5) :=
  vs.flatMap fun u => [(u, 0), (u, 1), (u, 2), (u, 3), (u, 4)]

def coreClauses0 : List (V × Fin 5) := clausesOf (coreVerts 0)
def coreClauses1 : List (V × Fin 5) := clausesOf (coreVerts 1)
def coreClauses2 : List (V × Fin 5) := clausesOf (coreVerts 2)

/-- All colour clauses of the core vertices (a heuristic list: no lemma is
stated about it). -/
def coreClauses (c : Fin 3) : List (V × Fin 5) :=
  match c with
  | 0 => coreClauses0
  | 1 => coreClauses1
  | 2 => coreClauses2

/-! ## Finite facts about the labellings -/

theorem e0_ge (c : Fin 3) : 5 ≤ e0 c := by
  revert c
  decide

theorem mem_fiberList : ∀ (c : Fin 3) (v : V) (w : Fin 5),
    col c v w = true → v ∈ fiberList c w := by
  decide +kernel

theorem fiberList_col : ∀ (c : Fin 3) (w : Fin 5) (v : V),
    v ∈ fiberList c w → col c v w = true := by
  decide +kernel

theorem col_low : ∀ (c : Fin 3) (v : V) (w : Fin 5),
    col c v w = true → 5 ≤ v.val ∧ v.val < e0 c := by
  decide +kernel

theorem core_has_col : ∀ (c : Fin 3) (v : V), 5 ≤ v.val → v.val < e0 c →
    ∃ w : Fin 5, col c v w = true := by
  decide +kernel

theorem fiberMask_testBit : ∀ (c : Fin 3) (v : V) (w : Fin 5),
    (fiberMask c w).testBit v.val = col c v w := by
  decide +kernel

theorem mem_highVerts : ∀ v : V, v.val < 5 → v ∈ highVerts := by
  decide +kernel

theorem mem_coreVerts : ∀ (c : Fin 3) (v : V), 5 ≤ v.val → v.val < e0 c →
    v ∈ coreVerts c := by
  decide +kernel

theorem mem_emptyVerts : ∀ (c : Fin 3) (v : V), e0 c ≤ v.val → v ∈ emptyVerts c := by
  decide +kernel

theorem maskOf_empty : ∀ (c : Fin 3) (v : V), e0 c ≤ v.val → maskOf c v = 0 := by
  decide +kernel

theorem cap_ge (v : V) : 7 ≤ capOf v := by
  unfold capOf
  split <;> omega

theorem capOf_low (v : V) (h : 5 ≤ v.val) : capOf v = 7 := by
  unfold capOf
  rw [if_neg (by omega)]

/-! ## Models -/

/-- The abstract constraints on a complete adjacency relation: the
relation-level order-49 constraints of the canonical five-high labelling
`c`, restated without finsets. -/
structure Model (c : Fin 3) (adj : V → V → Bool) : Prop where
  symm : ∀ a b, adj a b = adj b a
  irrefl : ∀ a, adj a a = false
  c4 : ∀ i j k l : V, i ≠ j → k ≠ l → adj i k = true → adj j k = true →
    adj i l = true → adj j l = true → False
  colEx : ∀ i : V, 5 ≤ i.val → ∀ w : Fin 5, ∃ k, adj i k = true ∧ col c k w = true
  colUniq : ∀ i : V, 5 ≤ i.val → ∀ w : Fin 5, ∀ k l : V,
    adj i k = true → col c k w = true → adj i l = true → col c l w = true → k = l
  nb : ∀ i : V, ∃ L : List V, L.Nodup ∧ L.length = capOf i ∧
    ∀ j, j ∈ L ↔ adj i j = true

variable {c : Fin 3}

theorem cap_lt {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
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

theorem exists_unknown_nbr {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
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

def allowed (s : St) (u x : V) : Bool :=
  decide ((s.nbr[x.val]).length < capOf x) &&
    decide ((s.nbr[u.val]).length < capOf u) &&
    (s.nbr[u.val]).all fun y => ((s.rows[y.val] &&& s.rows[x.val]) &&& M49) == 0

theorem allowed_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {u x : V} (hux : adj u x = true) (hsx : s.adj u x = false) :
    allowed s u x = true := by
  have hxu : adj x u = true := by rw [M.symm x u]; exact hux
  have hsxu : s.adj x u = false := by rw [hs.symm x u]; exact hsx
  unfold allowed
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

def tryAdd (s : St) (u x : V) : Option St :=
  if u = x then none
  else if s.adj u x then some s
  else if allowed s u x then some (s.addEdge u x) else none

theorem tryAdd_none {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {u x : V} (h : tryAdd s u x = none) : adj u x = false := by
  unfold tryAdd at h
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

theorem tryAdd_some {s s' : St} {u x : V} (hs : s.WF) (h : tryAdd s u x = some s') :
    s'.WF ∧ s'.adj u x = true ∧ (∀ a b, s.adj a b = true → s'.adj a b = true) ∧
    (∀ a b, s'.adj a b = true →
      s.adj a b = true ∨ (a = u ∧ b = x) ∨ (a = x ∧ b = u)) ∧
    (∀ adj, Model c adj → Compat s adj → adj u x = true → Compat s' adj) := by
  unfold tryAdd at h
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

def addMany (s : St) (u : V) : List V → Option St
  | [] => some s
  | x :: xs =>
    match tryAdd s u x with
    | none => none
    | some s' => addMany s' u xs

theorem addMany_ne_none {adj : V → V → Bool} (M : Model c adj) {u : V} :
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
    cases htry : tryAdd s u x with
    | none =>
      have := tryAdd_none hs M hc htry
      rw [hx] at this
      cases this
    | some s' =>
      rw [htry] at h
      dsimp only at h
      obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some (c := c) hs htry
      exact ih s' hs' (hcompat adj M hc hx)
        (fun y hy => hall y (List.mem_cons_of_mem _ hy)) h

theorem addMany_some {u : V} :
    ∀ (xs : List V) (s s' : St), s.WF → addMany s u xs = some s' →
      s'.WF ∧ (∀ a b, s.adj a b = true → s'.adj a b = true) ∧
      (∀ x ∈ xs, s'.adj u x = true) ∧
      ∀ adj, Model c adj → Compat s adj → (∀ x ∈ xs, adj u x = true) →
        Compat s' adj := by
  intro xs
  induction xs with
  | nil =>
    intro s s' hs h
    rw [addMany] at h
    cases h
    exact ⟨hs, fun _ _ h => h, fun _ hx => absurd hx List.not_mem_nil, fun _ _ hc _ => hc⟩
  | cons x xs ih =>
    intro s s' hs h
    rw [addMany] at h
    cases htry : tryAdd s u x with
    | none =>
      rw [htry] at h
      cases h
    | some s1 =>
      rw [htry] at h
      dsimp only at h
      obtain ⟨hs1, he1, hm1, _, hcompat⟩ := tryAdd_some (c := c) hs htry
      obtain ⟨hs', hm', he', hc'⟩ := ih s1 s' hs1 h
      refine ⟨hs', fun a b hab => hm' a b (hm1 a b hab), ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · rw [hy]
          exact hm' u x he1
        · exact he' y hy
      · intro adj M hc hall
        exact hc' adj M (hcompat adj M hc (hall x (List.mem_cons_self ..)))
          (fun y hy => hall y (List.mem_cons_of_mem _ hy))

/-! ## Twin transport -/

/-- Swapping two low vertices with equal masks and equal known rows preserves
both the model axioms and compatibility with the partial graph. -/
theorem twin_transport {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) (x y : V) (hx : 5 ≤ x.val) (hy : 5 ≤ y.val)
    (hmask : maskOf c x = maskOf c y) (hrow : ∀ b, s.adj x b = s.adj y b) :
    Model c (fun a b => adj (Equiv.swap x y a) (Equiv.swap x y b)) ∧
    Compat s (fun a b => adj (Equiv.swap x y a) (Equiv.swap x y b)) := by
  have hlow : ∀ a : V, 5 ≤ a.val → 5 ≤ (Equiv.swap x y a).val := by
    intro a ha
    rcases swap_cases x y a with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact ha
    · rw [h]; exact hy
    · rw [h]; exact hx
  have hcol : ∀ (a : V) (w : Fin 5), col c (Equiv.swap x y a) w = col c a w := by
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

/-! ## Phase 1: colour clauses on the core vertices -/

def clauseOpen (c : Fin 3) (s : St) (u : V) (w : Fin 5) : Bool :=
  ((s.rows[u.val] &&& fiberMask c w) &&& M49) == 0

theorem clauseOpen_not_adj {s : St} {u : V} {w : Fin 5} (h : clauseOpen c s u w = true)
    {x : V} (hx : col c x w = true) : s.adj u x = false := by
  cases hh : s.adj u x
  · rfl
  · exfalso
    exact and_no_bit_of_eq_zero h x.val x.isLt hh
      (by rw [fiberMask_testBit]; exact hx)

/-- An open colour clause of a low vertex none of whose candidates can be
added. -/
def clauseDead (c : Fin 3) (s : St) (p : V × Fin 5) : Bool :=
  decide (5 ≤ p.1.val) && clauseOpen c s p.1 p.2 &&
    (fiberList c p.2).all fun x => decide (x = p.1) || !allowed s p.1 x

theorem clauseDead_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {p : V × Fin 5} (h : clauseDead c s p = true) : False := by
  unfold clauseDead at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hu, hopen⟩, hall⟩ := h
  obtain ⟨k, hk, hkw⟩ := M.colEx p.1 hu p.2
  have hx := (List.all_eq_true.mp hall) k (mem_fiberList c k p.2 hkw)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hx
  rcases hx with hx | hx
  · rw [hx, M.irrefl] at hk
    cases hk
  · rw [allowed_sound hs M hc hk (clauseOpen_not_adj hopen hkw)] at hx
    cases hx

def twinSkip (c : Fin 3) (s : St) (u : V) (w : Fin 5) (x : V) : Bool :=
  (fiberList c w).any fun y =>
    decide (y.val < x.val) && decide (y ≠ u) &&
      decide (s.rows[y.val] = s.rows[x.val]) && decide (maskOf c y = maskOf c x)

def findClause (c : Fin 3) (cl : List (V × Fin 5)) (s : St) : Option (V × Fin 5) :=
  cl.find? fun p => clauseOpen c s p.1 p.2

/-- Phase 1.  `fcl` is the list of clauses checked for dead ends, `cl` the
list of clauses branched on, in order.  Both are arbitrary: every property
of a chosen clause that soundness needs is re-checked at run time. -/
def dfs1 (c : Fin 3) (fcl cl : List (V × Fin 5)) (leaf : St → Bool) : Nat → St → Bool
  | 0, _ => false
  | fuel + 1, s =>
    fcl.any (clauseDead c s) ||
      match findClause c cl s with
      | none => leaf s
      | some (u, w) =>
        decide (5 ≤ u.val) && clauseOpen c s u w &&
          (fiberList c w).all fun x =>
            decide (x = u) || twinSkip c s u w x ||
              match tryAdd s u x with
              | none => true
              | some s' => dfs1 c fcl cl leaf fuel s'

theorem dfs1_succ (fcl cl : List (V × Fin 5)) (leaf : St → Bool) (fuel : Nat) (s : St) :
    dfs1 c fcl cl leaf (fuel + 1) s =
      (fcl.any (clauseDead c s) ||
        match findClause c cl s with
        | none => leaf s
        | some (u, w) =>
          decide (5 ≤ u.val) && clauseOpen c s u w &&
            (fiberList c w).all fun x =>
              decide (x = u) || twinSkip c s u w x ||
                match tryAdd s u x with
                | none => true
                | some s' => dfs1 c fcl cl leaf fuel s') := by
  rfl

/-- Soundness of phase 1 for a family of leaf tests.  Phase 1 does not
depend on the leaf test, so it suffices that at every state the leaf tests
of the family jointly exclude all models. -/
theorem dfs1_sound_fam {ι : Type} (i0 : ι) (fcl cl : List (V × Fin 5))
    (leaf : ι → St → Bool)
    (hleaf : ∀ s : St, s.WF → (∀ i, leaf i s = true) →
      ∀ adj, Model c adj → Compat s adj → False) :
    ∀ (fuel : Nat) (s : St), s.WF →
      (∀ i, dfs1 c fcl cl (leaf i) fuel s = true) →
      ∀ adj, Model c adj → Compat s adj → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ h
    have := h i0
    simp [dfs1] at this
  | succ fuel ih =>
    intro s hs h adj M hc
    cases hdead : fcl.any (clauseDead c s) with
    | true =>
      obtain ⟨p, _, hp⟩ := List.any_eq_true.mp hdead
      exact clauseDead_sound hs M hc hp
    | false =>
      cases hfc : findClause c cl s with
      | none =>
        refine hleaf s hs ?_ adj M hc
        intro i
        have hi := h i
        rw [dfs1_succ, hdead, hfc] at hi
        exact hi
      | some p =>
        obtain ⟨u, w⟩ := p
        have hall : ∀ i, 5 ≤ u.val ∧ ∀ x ∈ fiberList c w,
            (decide (x = u) || twinSkip c s u w x ||
              match tryAdd s u x with
              | none => true
              | some s' => dfs1 c fcl cl (leaf i) fuel s') = true := by
          intro i
          have hthis := h i
          rw [dfs1_succ, hdead, hfc] at hthis
          dsimp only at hthis
          try simp only [Bool.false_or] at hthis
          rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hthis
          exact ⟨hthis.1.1, List.all_eq_true.mp hthis.2⟩
        have hu : 5 ≤ u.val := (hall i0).1
        have key : ∀ (n : Nat) (k : V), k.val = n → ∀ adj, Model c adj → Compat s adj →
            adj u k = true → col c k w = true → False := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ihn =>
            intro k hkn adj M hc huk hkw
            have hkmem : k ∈ fiberList c w := mem_fiberList c k w hkw
            have hku : k ≠ u := by
              intro h
              rw [h, M.irrefl] at huk
              cases huk
            cases hskipc : twinSkip c s u w k with
            | true =>
              unfold twinSkip at hskipc
              obtain ⟨y, hy, hcond⟩ := List.any_eq_true.mp hskipc
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              obtain ⟨⟨⟨hlt, hyu⟩, hrows⟩, hmask⟩ := hcond
              have hyw : col c y w = true := fiberList_col c w y hy
              have hrow : ∀ b, s.adj y b = s.adj k b := by
                intro b
                unfold H3Pair.St.adj
                rw [hrows]
              obtain ⟨M', hc'⟩ := twin_transport hs M hc y k (col_low c y w hyw).1
                (col_low c k w hkw).1 hmask hrow
              refine ihn y.val (by omega) y rfl _ M' hc' ?_ hyw
              show adj (Equiv.swap y k u) (Equiv.swap y k y) = true
              rw [Equiv.swap_apply_left,
                Equiv.swap_apply_of_ne_of_ne (fun h => hyu h.symm) (fun h => hku h.symm)]
              exact huk
            | false =>
              cases htry : tryAdd s u k with
              | none =>
                have := tryAdd_none hs M hc htry
                rw [huk] at this
                cases this
              | some s' =>
                obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some (c := c) hs htry
                refine ih s' hs' ?_ adj M (hcompat adj M hc huk)
                intro i
                have hk := (hall i).2 k hkmem
                rw [hskipc, htry] at hk
                dsimp only at hk
                simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true,
                  or_false] at hk
                rcases hk with hk | hk
                · exact absurd hk hku
                · exact hk
        obtain ⟨k, hk, hkw⟩ := M.colEx u hu w
        exact key k.val k rfl adj M hc hk hkw

theorem dfs1_sound (fcl cl : List (V × Fin 5)) (leaf : St → Bool)
    (hleaf : ∀ s : St, s.WF → leaf s = true →
      ∀ adj, Model c adj → Compat s adj → False) :
    ∀ (fuel : Nat) (s : St), s.WF → dfs1 c fcl cl leaf fuel s = true →
      ∀ adj, Model c adj → Compat s adj → False := by
  intro fuel s hs h
  exact dfs1_sound_fam (ι := Unit) () fcl cl (fun _ => leaf)
    (fun s hs h => hleaf s hs (h ())) fuel s hs (fun _ => h)

/-! ## Phase 2: core neighbourhoods of the empty vertices -/

/-- A pattern: the core neighbours of an empty vertex, one per colour
(repetitions allowed). -/
abbrev Pat := List V

def allPats (c : Fin 3) : List Pat :=
  (fiberList c 0).flatMap fun a => (fiberList c 1).flatMap fun b =>
    (fiberList c 2).flatMap fun d => (fiberList c 3).flatMap fun g =>
      (fiberList c 4).map fun f => [a, b, d, g, f]

/-- `t` lists core neighbours of `e` and meets every colour. -/
def PatOf (c : Fin 3) (adj : V → V → Bool) (e : V) (t : Pat) : Prop :=
  (∀ x ∈ t, adj e x = true ∧ x.val < e0 c) ∧ ∀ w : Fin 5, ∃ x ∈ t, col c x w = true

/-- Every fresh empty vertex has a pattern in the list. -/
def FreshWit (c : Fin 3) (s : St) (adj : V → V → Bool) (avail : List Pat) : Prop :=
  ∀ e : V, e0 c ≤ e.val → SFresh s e → ∃ t ∈ avail, PatOf c adj e t

theorem freshWit_allPats {s : St} {adj : V → V → Bool} (M : Model c adj) :
    FreshWit c s adj (allPats c) := by
  intro e he _
  have he5 : 5 ≤ e.val := (e0_ge c).trans he
  obtain ⟨a, ha, hac⟩ := M.colEx e he5 0
  obtain ⟨b, hb, hbc⟩ := M.colEx e he5 1
  obtain ⟨d, hd, hdc⟩ := M.colEx e he5 2
  obtain ⟨g, hg, hgc⟩ := M.colEx e he5 3
  obtain ⟨f, hf, hfc⟩ := M.colEx e he5 4
  refine ⟨[a, b, d, g, f], ?_, ?_, ?_⟩
  · unfold allPats
    refine List.mem_flatMap.mpr ⟨a, mem_fiberList c a 0 hac, ?_⟩
    refine List.mem_flatMap.mpr ⟨b, mem_fiberList c b 1 hbc, ?_⟩
    refine List.mem_flatMap.mpr ⟨d, mem_fiberList c d 2 hdc, ?_⟩
    refine List.mem_flatMap.mpr ⟨g, mem_fiberList c g 3 hgc, ?_⟩
    exact List.mem_map.mpr ⟨f, mem_fiberList c f 4 hfc, rfl⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h
    · rw [h]; exact ⟨ha, (col_low c a 0 hac).2⟩
    · rw [h]; exact ⟨hb, (col_low c b 1 hbc).2⟩
    · rw [h]; exact ⟨hd, (col_low c d 2 hdc).2⟩
    · rw [h]; exact ⟨hg, (col_low c g 3 hgc).2⟩
    · rw [h]; exact ⟨hf, (col_low c f 4 hfc).2⟩
  · intro w
    match w with
    | 0 => exact ⟨a, by simp, hac⟩
    | 1 => exact ⟨b, by simp, hbc⟩
    | 2 => exact ⟨d, by simp, hdc⟩
    | 3 => exact ⟨g, by simp, hgc⟩
    | 4 => exact ⟨f, by simp, hfc⟩

theorem mem_pat_of_adj {adj : V → V → Bool} (M : Model c adj) {e v : V} {t : Pat}
    (he : 5 ≤ e.val) {w : Fin 5} (hvw : col c v w = true) (hev : adj e v = true)
    (ht : PatOf c adj e t) : v ∈ t := by
  obtain ⟨x, hx, hxw⟩ := ht.2 w
  have hxv : x = v := M.colUniq e he w x v (ht.1 x hx).1 hxw hev hvw
  rw [← hxv]
  exact hx

theorem pairOK_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
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

def insertable (s : St) (t : Pat) : Bool :=
  t.all fun a => decide ((s.nbr[a.val]).length < capOf a) && t.all fun b => pairOK s a b

theorem insertable_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {e : V} {t : Pat} (hfresh : SFresh s e)
    (ht : ∀ x ∈ t, adj e x = true) : insertable s t = true := by
  have hcap : ∀ a : V, adj e a = true → (s.nbr[a.val]).length < capOf a := by
    intro a ha
    have hae : adj a e = true := by rw [M.symm a e]; exact ha
    have hsae : s.adj a e = false := by rw [hs.symm a e]; exact hfresh a
    exact cap_lt hs M hc hae hsae
  unfold insertable
  apply List.all_eq_true.mpr
  intro a ha
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hcap a (ht a ha), ?_⟩
  apply List.all_eq_true.mpr
  intro b hb
  exact pairOK_sound hs M hc hfresh (ht a ha) (ht b hb)

theorem freshWit_filter {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {avail : List Pat} (hw : FreshWit c s adj avail) :
    FreshWit c s adj (avail.filter (insertable s)) := by
  intro e he hfresh
  obtain ⟨t, ht, hpat⟩ := hw e he hfresh
  exact ⟨t, List.mem_filter.mpr
    ⟨ht, insertable_sound hs M hc hfresh (fun x hx => (hpat.1 x hx).1)⟩, hpat⟩

def hasCol (c : Fin 3) (s : St) (a : V) (w : Fin 5) : Bool :=
  !(((s.rows[a.val] &&& fiberMask c w) &&& M49) == 0)

theorem hasCol_sound {s : St} {a : V} {w : Fin 5} (h : hasCol c s a w = true) :
    ∃ y : V, s.adj a y = true ∧ col c y w = true := by
  unfold hasCol at h
  have h' : (((s.rows[a.val] &&& fiberMask c w) &&& M49) == 0) = false := by
    cases hh : (((s.rows[a.val] &&& fiberMask c w) &&& M49) == 0)
    · rfl
    · rw [hh] at h
      cases h
  obtain ⟨i, hi, hai, hfi⟩ := and_bit_of_ne_zero h'
  refine ⟨⟨i, hi⟩, hai, ?_⟩
  rw [← fiberMask_testBit]
  exact hfi

def hasAllCols (c : Fin 3) (s : St) (a : V) : Bool :=
  (List.finRange 5).all fun w => hasCol c s a w

theorem hasAllCols_sound {s : St} {a : V} (h : hasAllCols c s a = true) (w : Fin 5) :
    ∃ y : V, s.adj a y = true ∧ col c y w = true :=
  hasCol_sound ((List.all_eq_true.mp h) w (List.mem_finRange w))

/-- Runtime closure check used by phase 2: highs are full, core vertices
have all colour neighbours, and each empty vertex is either untouched or
has all colour neighbours. -/
def stateOK (c : Fin 3) (s : St) : Bool :=
  (highVerts.all fun h => decide ((s.nbr[h.val]).length = capOf h)) &&
    ((coreVerts c).all fun a => hasAllCols c s a) &&
    ((emptyVerts c).all fun e => (s.rows[e.val] == 0) || hasAllCols c s e)

theorem exists_fresh_nbr {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) (hok : stateOK c s = true) {v : V} (hv5 : 5 ≤ v.val)
    (hve : v.val < e0 c) (hdeg : (s.nbr[v.val]).length < 7) :
    ∃ e : V, e0 c ≤ e.val ∧ s.rows[e.val] = 0 ∧ adj v e = true := by
  unfold stateOK at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hhigh, hcore⟩, hempty⟩ := hok
  have hdeg' : (s.nbr[v.val]).length < capOf v := by
    rw [capOf_low v hv5]
    exact hdeg
  obtain ⟨x, hvx, hsvx⟩ := exists_unknown_nbr hs M hdeg'
  have hxv : adj x v = true := by rw [M.symm x v]; exact hvx
  have hsxv : s.adj x v = false := by rw [hs.symm x v]; exact hsvx
  by_cases hx5 : x.val < 5
  · exfalso
    have hfull := (List.all_eq_true.mp hhigh) x (mem_highVerts x hx5)
    simp only [decide_eq_true_eq] at hfull
    have := cap_lt hs M hc hxv hsxv
    omega
  · by_cases hxe : x.val < e0 c
    · exfalso
      obtain ⟨w, hw⟩ := core_has_col c x (by omega) hxe
      have hvall := (List.all_eq_true.mp hcore) v (mem_coreVerts c v hv5 hve)
      obtain ⟨y, hvy, hyw⟩ := hasAllCols_sound hvall w
      have hyx : y = x := M.colUniq v hv5 w y x (hc v y hvy) hyw hvx hw
      rw [hyx, hsvx] at hvy
      cases hvy
    · have hxe' : e0 c ≤ x.val := by omega
      by_cases hrow : s.rows[x.val] = 0
      · exact ⟨x, hxe', hrow, hvx⟩
      · exfalso
        have hxall := (List.all_eq_true.mp hempty) x (mem_emptyVerts c x hxe')
        simp only [Bool.or_eq_true, beq_iff_eq] at hxall
        rcases hxall with hxall | hxall
        · exact hrow hxall
        · obtain ⟨w, hw⟩ := core_has_col c v hv5 hve
          obtain ⟨y, hxy, hyw⟩ := hasAllCols_sound hxall w
          have hyv : y = v := M.colUniq x (by omega) w y v (hc x y hxy) hyw hxv hw
          rw [hyv, hsxv] at hxy
          cases hxy

/-- Occurrence counts of the vertices in a list of patterns (heuristic only). -/
def patCounts (avail : List Pat) : Array Nat :=
  avail.foldl (fun cnt t => t.foldl (fun cnt x => cnt.modify x.val (· + 1)) cnt)
    (Array.replicate 49 0)

/-- Heuristic choice of the next deficient core vertex.  Soundness of `dfs2`
does not depend on this function. -/
def pickCore (c : Fin 3) (s : St) (avail : List Pat) : Option V :=
  let cnt := patCounts avail
  ((coreVerts c).foldl (fun (best : Option (Nat × V)) v =>
    if (s.nbr[v.val]).length < 7 then
      let k := cnt[v.val]!
      match best with
      | none => some (k, v)
      | some (k', _) => if k < k' then some (k, v) else best
    else best) none).map fun p => p.2

def findFresh (c : Fin 3) (s : St) : Option V :=
  (emptyVerts c).find? fun e => s.rows[e.val] == 0

def patLoop (f : Pat → List Pat → Bool) (pre : List Pat) : List Pat → Bool
  | [] => true
  | p :: rest => f p (pre ++ p :: rest) && patLoop f pre rest

theorem patLoop_sound {f : Pat → List Pat → Bool} {pre : List Pat}
    {Good : (V → V → Bool) → Prop} {Hit : (V → V → Bool) → Pat → Prop}
    {Wit : (V → V → Bool) → List Pat → Prop}
    (hnil : ∀ adj, Good adj → Wit adj pre → False)
    (hsplit : ∀ adj p l, Good adj → Wit adj (pre ++ p :: l) → ¬ Hit adj p →
      Wit adj (pre ++ l))
    (hchild : ∀ adj p av, Good adj → Wit adj av → Hit adj p → f p av = true → False) :
    ∀ cs, patLoop f pre cs = true → ∀ adj, Good adj → Wit adj (pre ++ cs) → False := by
  intro cs
  induction cs with
  | nil =>
    intro _ adj hg hw
    rw [List.append_nil] at hw
    exact hnil adj hg hw
  | cons p rest ih =>
    intro h adj hg hw
    rw [patLoop] at h
    simp only [Bool.and_eq_true] at h
    by_cases hit : Hit adj p
    · exact hchild adj p _ hg hw hit h.1
    · exact ih h.2 adj hg (hsplit adj p rest hg hw hit)

/-- `patLoop` on the available patterns split by whether they contain `v`. -/
def patLoopSplit (f : Pat → List Pat → Bool) (v : V) (avail : List Pat) : Bool :=
  patLoop f (avail.filter fun t => !decide (v ∈ t)) (avail.filter fun t => decide (v ∈ t))

/-- One phase-2 node, with the recursive call abstracted. -/
def step2 (c : Fin 3) (leaf : St → Bool) (rec : St → List Pat → Bool) (s : St)
    (avail : List Pat) : Bool :=
  match pickCore c s avail with
  | none => leaf s
  | some v =>
    decide (5 ≤ v.val) && decide (v.val < e0 c) &&
      decide ((s.nbr[v.val]).length < 7) &&
      match findFresh c s with
      | none => true
      | some n =>
        decide (e0 c ≤ n.val) && (s.rows[n.val] == 0) &&
          patLoopSplit
            (fun p av =>
              match addMany s n p with
              | none => true
              | some s' => rec s' av)
            v avail

def dfs2 (c : Fin 3) (leaf : St → Bool) : Nat → St → List Pat → Bool
  | 0, _, _ => false
  | fuel + 1, s, avail0 =>
    stateOK c s && step2 c leaf (dfs2 c leaf fuel) s (avail0.filter (insertable s))

theorem swap_fixed {x y a : V} {n : Nat} (hx : n ≤ x.val) (hy : n ≤ y.val)
    (ha : a.val < n) : Equiv.swap x y a = a := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    rw [h] at ha
    omega
  · intro h
    rw [h] at ha
    omega

theorem dfs2_sound (leaf : St → Bool)
    (hleaf : ∀ s : St, s.WF → leaf s = true →
      ∀ adj, Model c adj → Compat s adj → False) :
    ∀ (fuel : Nat) (s : St) (avail0 : List Pat), s.WF →
      dfs2 c leaf fuel s avail0 = true →
      ∀ adj, Model c adj → Compat s adj → FreshWit c s adj avail0 → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s avail0 _ h
    simp [dfs2] at h
  | succ fuel ih =>
    intro s avail0 hs h adj M hc hw0
    rw [dfs2] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hok, h⟩ := h
    have hw := freshWit_filter hs M hc hw0
    generalize avail0.filter (insertable s) = avail at h hw
    unfold step2 at h
    split at h
    · exact hleaf s hs h adj M hc
    · rename_i v _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hv5, hve⟩, hvdeg⟩, h⟩ := h
      split at h
      · rename_i hnone
        obtain ⟨e, hee, herow, _⟩ := exists_fresh_nbr hs M hc hok hv5 hve hvdeg
        have := (List.find?_eq_none.mp hnone) e (mem_emptyVerts c e hee)
        apply this
        rw [herow]
        rfl
      · rename_i n _
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨hne, hnrow⟩, hloop⟩ := h
        unfold patLoopSplit at hloop
        have hnfresh : SFresh s n := sfresh_of_row_zero hnrow
        obtain ⟨wv, hwv⟩ := core_has_col c v hv5 hve
        refine patLoop_sound
          (Good := fun adj => Model c adj ∧ Compat s adj)
          (Hit := fun adj p => ∃ e : V, e0 c ≤ e.val ∧ SFresh s e ∧ PatOf c adj e p)
          (Wit := fun adj av => FreshWit c s adj av)
          ?_ ?_ ?_ _ hloop adj ⟨M, hc⟩ ?_
        · -- no candidate left
          rintro adj ⟨M, hc⟩ hw
          obtain ⟨e, hee, herow, hve'⟩ := exists_fresh_nbr hs M hc hok hv5 hve hvdeg
          obtain ⟨t, ht, hpat⟩ := hw e hee (sfresh_of_row_zero herow)
          have hcont : v ∈ t :=
            mem_pat_of_adj M ((e0_ge c).trans hee) hwv (by rw [M.symm e v]; exact hve') hpat
          have := (List.mem_filter.mp ht).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
          exact this hcont
        · -- skipping a candidate that no fresh vertex realises
          rintro adj p l ⟨M, hc⟩ hw hit e he hfresh
          obtain ⟨t, ht, hpat⟩ := hw e he hfresh
          refine ⟨t, ?_, hpat⟩
          rcases List.mem_append.mp ht with ht | ht
          · exact List.mem_append.mpr (Or.inl ht)
          · rcases List.mem_cons.mp ht with ht | ht
            · exfalso
              apply hit
              rw [← ht]
              exact ⟨e, he, hfresh, hpat⟩
            · exact List.mem_append.mpr (Or.inr ht)
        · -- the child realised by a fresh vertex
          rintro adj p av ⟨M, hc⟩ hw ⟨e, hee, hefresh, hpat⟩ hf
          have hmask : maskOf c e = maskOf c n := by
            rw [maskOf_empty c e hee, maskOf_empty c n hne]
          have hrow : ∀ b, s.adj e b = s.adj n b := by
            intro b
            rw [hefresh b, hnfresh b]
          have he5 : 5 ≤ e.val := (e0_ge c).trans hee
          have hn5 : 5 ≤ n.val := (e0_ge c).trans hne
          obtain ⟨M', hc'⟩ := twin_transport hs M hc e n he5 hn5 hmask hrow
          have hfix : ∀ a : V, a.val < e0 c → Equiv.swap e n a = a :=
            fun a ha => swap_fixed hee hne ha
          have hall' : ∀ x ∈ p,
              (fun a b => adj (Equiv.swap e n a) (Equiv.swap e n b)) n x = true := by
            intro x hx
            show adj (Equiv.swap e n n) (Equiv.swap e n x) = true
            rw [Equiv.swap_apply_right, hfix x (hpat.1 x hx).2]
            exact (hpat.1 x hx).1
          cases hadd : addMany s n p with
          | none => exact addMany_ne_none M' p s hs hc' hall' hadd
          | some s' =>
            simp only [hadd] at hf
            obtain ⟨hs', hmono, hedge, hcompat⟩ := addMany_some (c := c) p s s' hs hadd
            refine ih s' av hs' hf _ M' (hcompat _ M' hc' hall') ?_
            intro e' he' hfresh'
            have hfresh_s : SFresh s e' := by
              intro b
              cases hh : s.adj e' b
              · rfl
              · have := hmono _ _ hh
                rw [hfresh' b] at this
                cases this
            have hne' : e' ≠ n := by
              intro h
              obtain ⟨x, hx, _⟩ := hpat.2 0
              have := hedge x hx
              rw [← h, hfresh' x] at this
              cases this
            have hswap : e0 c ≤ (Equiv.swap e n e').val ∧ SFresh s (Equiv.swap e n e') := by
              rcases swap_cases e n e' with h | ⟨_, h⟩ | ⟨h1, _⟩
              · rw [h]
                exact ⟨he', hfresh_s⟩
              · rw [h]
                exact ⟨hne, hnfresh⟩
              · exact absurd h1 hne'
            obtain ⟨t, ht, htpat⟩ := hw _ hswap.1 hswap.2
            refine ⟨t, ht, ?_, htpat.2⟩
            intro x hx
            refine ⟨?_, (htpat.1 x hx).2⟩
            show adj (Equiv.swap e n e') (Equiv.swap e n x) = true
            rw [hfix x (htpat.1 x hx).2]
            exact (htpat.1 x hx).1
        · -- the split list still witnesses every fresh vertex
          intro e he hfresh
          obtain ⟨t, ht, hpat⟩ := hw e he hfresh
          refine ⟨t, ?_, hpat⟩
          by_cases hcv : v ∈ t
          · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨ht, by simpa using hcv⟩))
          · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨ht, by simpa using hcv⟩))

/-! ## Phase 3: empty–empty edges -/

def cands3 (s : St) (u : V) : List V :=
  (List.finRange 49).filter fun x => decide (x ≠ u) && !s.adj u x && allowed s u x

def gate3 (c : Fin 3) (s : St) : Bool :=
  (emptyVerts c).any fun u =>
    decide ((s.nbr[u.val]).length < 7) &&
      decide ((s.nbr[u.val]).length + (cands3 s u).length < 7)

def pick3 (c : Fin 3) (s : St) : Option V :=
  ((emptyVerts c).foldl (fun (best : Option (Nat × V)) u =>
    if (s.nbr[u.val]).length < 7 then
      let cnt := (cands3 s u).length
      match best with
      | none => some (cnt, u)
      | some (k, _) => if cnt < k then some (cnt, u) else best
    else best) none).map fun p => p.2

theorem mem_cands3 {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {u x : V} (hux : adj u x = true) (hsx : s.adj u x = false) :
    x ∈ cands3 s u := by
  unfold cands3
  refine List.mem_filter.mpr ⟨List.mem_finRange x, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨?_, hsx⟩, allowed_sound hs M hc hux hsx⟩
  intro h
  rw [h, M.irrefl] at hux
  cases hux

theorem count_gate {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
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

def dfs3 (c : Fin 3) : Nat → St → Bool
  | 0, _ => false
  | fuel + 1, s =>
    gate3 c s ||
      match pick3 c s with
      | none => false
      | some u =>
        (List.sublistsLen (capOf u - (s.nbr[u.val]).length) (cands3 s u)).all fun B =>
          match addMany s u B with
          | none => true
          | some s' => dfs3 c fuel s'

theorem dfs3_sound :
    ∀ (fuel : Nat) (s : St), s.WF → dfs3 c fuel s = true →
      ∀ adj, Model c adj → Compat s adj → False := by
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
          obtain ⟨hs', _, _, hcompat⟩ := addMany_some (c := c) _ s s' hs hadd
          exact ih s' hs' hx adj M (hcompat adj M hc hall)

/-! ## The composed search -/

/-- Phases 2 and 3 from a phase-1 leaf. -/
def leaf1 (c : Fin 3) (fuel2 fuel3 : Nat) (s : St) : Bool :=
  dfs2 c (dfs3 c fuel3) fuel2 s (allPats c)

theorem leaf1_sound (fuel2 fuel3 : Nat) (s : St) (hs : s.WF)
    (h : leaf1 c fuel2 fuel3 s = true) :
    ∀ adj, Model c adj → Compat s adj → False := by
  intro adj M hc
  exact dfs2_sound (dfs3 c fuel3)
    (fun s hs h adj M hc => dfs3_sound fuel3 s hs h adj M hc)
    fuel2 s (allPats c) hs h adj M hc (freshWit_allPats M)

/-- The complete three-phase search from a given partial graph. -/
def search (c : Fin 3) (fuel1 fuel2 fuel3 : Nat) (s : St) : Bool :=
  dfs1 c (coreClauses c) (coreClauses c) (leaf1 c fuel2 fuel3) fuel1 s

/-- Soundness of the composed search: a `true` result excludes every model
compatible with the partial graph. -/
theorem search_sound (fuel1 fuel2 fuel3 : Nat) (s : St) (hs : s.WF)
    (h : search c fuel1 fuel2 fuel3 s = true) :
    ∀ adj, Model c adj → Compat s adj → False :=
  dfs1_sound (coreClauses c) (coreClauses c) (leaf1 c fuel2 fuel3)
    (leaf1_sound fuel2 fuel3) fuel1 s hs h

/-! ## Splitting phase 1 -/

/-- A cheap key of a partial graph, used only to distribute the work. -/
def stKey (s : St) : Nat :=
  s.rows.toArray.foldl (fun acc r => (acc * 31 + r % 1000003) % 1000003) 0

/-- Leaf test of part `r` of `m`: states with another key are accepted
without search; the others continue with the full search. -/
def leafPart (c : Fin 3) (m r : Nat) (s : St) : Bool :=
  decide (stKey s % m ≠ r) || search c 170 20 20 s

/-- Part `r` of the `m`-way split of the search from `s`: phase 1 on the
clauses of the first `k` core vertices, then the key test, then the full
search. -/
def part (c : Fin 3) (k m r : Nat) (s : St) : Bool :=
  dfs1 c (coreClauses c) ((coreClauses c).take (5 * k)) (leafPart c m r) 170 s

/-- If all `m` parts return `true`, no model is compatible with the state. -/
theorem parts_sound (k m : Nat) (hm : 0 < m) (s : St) (hs : s.WF)
    (h : ∀ r, r < m → part c k m r s = true) :
    ∀ adj, Model c adj → Compat s adj → False := by
  refine dfs1_sound_fam (ι := Fin m) ⟨0, hm⟩ (coreClauses c)
    ((coreClauses c).take (5 * k)) (fun r => leafPart c m r.val) ?_ 170 s hs
    (fun r => h r.val r.isLt)
  intro s hs hall adj M hc
  have hr : leafPart c m (stKey s % m) s = true := hall ⟨stKey s % m, Nat.mod_lt _ hm⟩
  unfold leafPart at hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with hr | hr
  · exact hr rfl
  · exact search_sound 170 20 20 s hs hr adj M hc

end H5
end Erdos85

#print axioms Erdos85.H5.search_sound
#print axioms Erdos85.H5.parts_sound
