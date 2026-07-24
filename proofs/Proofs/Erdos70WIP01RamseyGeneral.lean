import Mathlib
import Proofs.Erdos70WIP01

/-
# Erdős #70 — the infinite Ramsey theorem for every uniformity and colour count
# (erdos-70-wip-01, r-uniform k-colour generalization of the triples engine)

## What This File Contains

`Proofs/Erdos70WIP01.lean` proved the infinite Ramsey theorem for 2-colourings
of 3-element subsets (`infiniteRamsey3_holds`) by an iterated ultrafilter-majority
argument with three hand-coded majority levels (`pairMaj`, `pointMaj`, `topMaj`).
That was the single missing ingredient for the formalized (cardinality-surrogate)
Erdős #70 conjecture.  The registered next step on this node is to generalize the
engine to arbitrary uniformity `r` and arbitrary finite colour count — reusable
partition-calculus infrastructure absent from Mathlib v4.31 (whose combinatorics
library stops at finite Ramsey-type results: Hales–Jewett, Hindman, pigeonhole).

This file delivers the full generalization:

1. `majColorK` — the `U`-majority colour of a `Fin (k+1)`-valued function on `ℕ`,
   `U` = the hyperfilter (an ultrafilter extending the cofinite filter); an
   ultrafilter selects exactly one cell of any finite partition.
2. `listMaj` — the recursive majority tower, generalizing the three hand-coded
   levels at once: on a list `L` of fewer than `r` points it is the majority over
   one-point extensions, and at `r` points it is the honest colour.  This single
   definition makes every goodness condition *definitionally* `U`-large, so the
   choice invariant (`RamseyInv`) of the 3-uniform proof disappears entirely.
3. `genSeq` — the recursively chosen homogeneous sequence: each term is the least
   member of the (`U`-large, hence nonempty) good set of its predecessors.
4. `ramsey_nat_general` — **infinite Ramsey on `ℕ`, every `r`, every `k + 1`
   colours**: any colouring of the `r`-subsets of `ℕ` by `k + 1` colours admits
   an infinite homogeneous set.
5. `infiniteRamsey_general` — the same over an arbitrary infinite type, by
   pulling the colouring back along `ℕ ↪ S` and pushing the homogeneous set
   forward.
6. `infiniteRamsey3_of_general` — sanity bridge: the parent file's
   `InfiniteRamsey3` is the special case `r = 3`, `k + 1 = 2`.

## Honesty note

This is *infrastructure*: it generalizes the ingredient that already settled the
formalized (cardinality-surrogate) conjecture.  The genuine Erdős #70 partition
relation `𝔠 → (β, n)₂³` with true order type `β ≥ ω²` remains open and blocked on
Erdős–Rado order-type-preserving machinery (see the node's registered blocker).
-/

set_option linter.unusedVariables false

namespace Erdos70

section RamseyGeneral

open Filter

/-! ## Part 1: `k+1`-colour ultrafilter majority -/

/-- An ultrafilter selects a cell of every finite partition: some colour class of
a `Fin (k+1)`-valued function is `U`-large.  (For `Fin 2` this is the case split
inside `majColor`; here it is a genuine finite pigeonhole over the ultrafilter.) -/
theorem exists_majority {k : ℕ} (f : ℕ → Fin (k + 1)) :
    ∃ i : Fin (k + 1), {n | f n = i} ∈ hyperfilter ℕ := by
  by_contra h
  have h' : ∀ i : Fin (k + 1), {n | f n = i} ∉ hyperfilter ℕ := not_exists.mp h
  have hc : ∀ i : Fin (k + 1), {n | f n = i}ᶜ ∈ hyperfilter ℕ := fun i =>
    Ultrafilter.compl_mem_iff_notMem.mpr (h' i)
  have hint : (⋂ i : Fin (k + 1), {n | f n = i}ᶜ) ∈ hyperfilter ℕ :=
    Filter.iInter_mem.mpr hc
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem hint
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq] at hn
  exact hn (f n) rfl

/-- The `U`-majority colour of a `Fin (k+1)`-valued function on `ℕ`. -/
noncomputable def majColorK {k : ℕ} (f : ℕ → Fin (k + 1)) : Fin (k + 1) :=
  Classical.choose (exists_majority f)

/-- The defining property: the majority colour is attained on a `U`-large set. -/
theorem majColorK_mem {k : ℕ} (f : ℕ → Fin (k + 1)) :
    {n | f n = majColorK f} ∈ hyperfilter ℕ :=
  Classical.choose_spec (exists_majority f)

/-- Polymorphic finite-conjunction lemma (the parent file's `list_forall_large`
with an arbitrary index type, needed here to index conditions by *lists*): a
conjunction of `U`-large conditions over a finite list is `U`-large. -/
theorem list_forall_large' {α : Type*} {P : α → ℕ → Prop} (L : List α)
    (h : ∀ a ∈ L, {m | P a m} ∈ hyperfilter ℕ) :
    {m | ∀ a ∈ L, P a m} ∈ hyperfilter ℕ := by
  induction L with
  | nil =>
    have huniv : {m : ℕ | ∀ a ∈ ([] : List α), P a m} = Set.univ := by
      ext m; simp
    rw [huniv]
    exact Filter.univ_mem
  | cons a L ih =>
    have h1 : {m | P a m} ∈ hyperfilter ℕ := h a (by simp)
    have h2 : {m | ∀ b ∈ L, P b m} ∈ hyperfilter ℕ :=
      ih fun b hb => h b (List.mem_cons_of_mem a hb)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro m ⟨hm1, hm2⟩ b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hm1
    · exact hm2 b hb'

/-! ## Part 2: the recursive majority tower -/

/-- The recursive majority tower, all levels of the 3-uniform proof's
`pairMaj`/`pointMaj`/`topMaj` at once.  On a list of at least `r` points, the
honest colour of the underlying finset (junk `0` on collisions); on fewer, the
`U`-majority over one-point extensions. -/
noncomputable def listMaj (r k : ℕ) (c : Coloring ℕ r (k + 1)) (L : List ℕ) :
    Fin (k + 1) :=
  if h : r ≤ L.length then
    if hc : L.toFinset.card = r then c ⟨L.toFinset, hc⟩ else 0
  else
    majColorK (fun z => listMaj r k c (L ++ [z]))
termination_by r - L.length
decreasing_by
  simp only [List.length_append, List.length_singleton]
  omega

/-- Below the top level, `listMaj` is the majority of its one-point extensions. -/
theorem listMaj_of_length_lt {r k : ℕ} (c : Coloring ℕ r (k + 1)) {L : List ℕ}
    (h : L.length < r) :
    listMaj r k c L = majColorK (fun z => listMaj r k c (L ++ [z])) := by
  rw [listMaj]
  exact dif_neg (not_le.mpr h)

/-- At the top level, `listMaj` computes the honest colour. -/
theorem listMaj_eq_color {r k : ℕ} (c : Coloring ℕ r (k + 1)) {L : List ℕ}
    (hlen : r ≤ L.length) (hc : L.toFinset.card = r) :
    listMaj r k c L = c ⟨L.toFinset, hc⟩ := by
  rw [listMaj]
  rw [dif_pos hlen, dif_pos hc]

/-- The heart of the simplification: extending any short list by its majority
colour is a `U`-large condition — *definitionally*, with no invariant needed. -/
theorem listMaj_extend_large {r k : ℕ} (c : Coloring ℕ r (k + 1)) {L : List ℕ}
    (h : L.length < r) :
    {m | listMaj r k c (L ++ [m]) = listMaj r k c L} ∈ hyperfilter ℕ := by
  have hmem := majColorK_mem (fun z => listMaj r k c (L ++ [z]))
  rwa [← listMaj_of_length_lt c h] at hmem

/-! ## Part 3: the good set and the homogeneous sequence -/

/-- The set of viable next elements after the finite prefix `L`: larger than all
of `L`, and preserving the majority tower along every short sublist of `L`. -/
def goodSetK (r k : ℕ) (c : Coloring ℕ r (k + 1)) (L : List ℕ) : Set ℕ :=
  {m | (∀ a ∈ L, a < m) ∧
    ∀ S ∈ L.sublists, S.length < r →
      listMaj r k c (S ++ [m]) = listMaj r k c S}

/-- The good set is `U`-large — with *no* hypotheses on `L`: every clause is
`U`-large by `listMaj_extend_large` (definitional) or cofiniteness of tails. -/
theorem goodSetK_mem (r k : ℕ) (c : Coloring ℕ r (k + 1)) (L : List ℕ) :
    goodSetK r k c L ∈ hyperfilter ℕ := by
  have hA : {m | ∀ a ∈ L, a < m} ∈ hyperfilter ℕ :=
    list_forall_large' L (fun a _ => gt_large a)
  have hB : {m | ∀ S ∈ L.sublists, S.length < r →
      listMaj r k c (S ++ [m]) = listMaj r k c S} ∈ hyperfilter ℕ := by
    apply list_forall_large'
    intro S hS
    by_cases hlen : S.length < r
    · exact Filter.mem_of_superset (listMaj_extend_large c hlen)
        fun m hm _ => hm
    · exact Filter.mem_of_superset Filter.univ_mem
        fun m _ hlen' => absurd hlen' hlen
  exact Filter.inter_mem hA hB

/-- The increasing prefix lists of the homogeneous sequence: each new term is the
least member of the good set of its predecessors. -/
noncomputable def genPrefix (r k : ℕ) (c : Coloring ℕ r (k + 1)) : ℕ → List ℕ
  | 0 => []
  | n + 1 => genPrefix r k c n ++ [sInf (goodSetK r k c (genPrefix r k c n))]

/-- The homogeneous sequence itself. -/
noncomputable def genSeq (r k : ℕ) (c : Coloring ℕ r (k + 1)) (n : ℕ) : ℕ :=
  sInf (goodSetK r k c (genPrefix r k c n))

theorem genPrefix_succ (r k : ℕ) (c : Coloring ℕ r (k + 1)) (n : ℕ) :
    genPrefix r k c (n + 1) = genPrefix r k c n ++ [genSeq r k c n] := rfl

/-- Each term really lies in the good set of its predecessors (which is
`U`-large, hence nonempty).  No induction needed — `goodSetK_mem` is
unconditional. -/
theorem genSeq_mem_goodSet (r k : ℕ) (c : Coloring ℕ r (k + 1)) (n : ℕ) :
    genSeq r k c n ∈ goodSetK r k c (genPrefix r k c n) :=
  Nat.sInf_mem (Ultrafilter.nonempty_of_mem (goodSetK_mem r k c _))

/-- The prefix list is the sequence over an initial segment of indices. -/
theorem genPrefix_eq_map (r k : ℕ) (c : Coloring ℕ r (k + 1)) (n : ℕ) :
    genPrefix r k c n = (List.range n).map (genSeq r k c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [genPrefix_succ, ih, List.range_succ, List.map_append, List.map_singleton]

theorem mem_genPrefix_iff (r k : ℕ) (c : Coloring ℕ r (k + 1)) {a n : ℕ} :
    a ∈ genPrefix r k c n ↔ ∃ j, j < n ∧ genSeq r k c j = a := by
  rw [genPrefix_eq_map]
  simp [List.mem_map, List.mem_range]

theorem genSeq_strictMono (r k : ℕ) (c : Coloring ℕ r (k + 1)) :
    StrictMono (genSeq r k c) := by
  intro i j hij
  have hmem : genSeq r k c i ∈ genPrefix r k c j :=
    (mem_genPrefix_iff r k c).mpr ⟨i, hij, rfl⟩
  exact (genSeq_mem_goodSet r k c j).1 _ hmem

/-! ## Part 4: homogeneity by telescoping the majority tower -/

/-- A strictly increasing list of naturals bounded by `n` is a sublist of
`range n`.  (The index-bookkeeping lemma behind the telescope.) -/
theorem sorted_lt_sublist_range {ps : List ℕ} :
    ∀ {n : ℕ}, ps.Pairwise (· < ·) → (∀ x ∈ ps, x < n) →
      ps.Sublist (List.range n) := by
  induction ps using List.reverseRecOn with
  | nil => intro n _ _; exact List.nil_sublist _
  | append_singleton ps x ih =>
    intro n hs hb
    have hpair := List.pairwise_append.mp hs
    have h1 : ps.Sublist (List.range x) :=
      ih hpair.1 (fun a ha => hpair.2.2 a ha x (List.mem_singleton_self x))
    have h2 : (ps ++ [x]).Sublist (List.range x ++ [x]) :=
      h1.append (List.Sublist.refl [x])
    rw [← List.range_succ] at h2
    exact h2.trans (List.range_sublist.mpr (hb x (by simp)))

/-- **The telescope.**  Along any strictly increasing index list of length at
most `r`, the majority tower over the corresponding sequence values collapses
to its base `listMaj r k c []`: the largest point was chosen good for a prefix
containing all the others, so each step peels one point off the top. -/
theorem listMaj_map_eq_base (r k : ℕ) (c : Coloring ℕ r (k + 1)) :
    ∀ ps : List ℕ, ps.Pairwise (· < ·) → ps.length ≤ r →
      listMaj r k c (ps.map (genSeq r k c)) = listMaj r k c [] := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _ _; rfl
  | append_singleton ps p ih =>
    intro hs hlen
    have hpair := List.pairwise_append.mp hs
    have hps_lt : ∀ a ∈ ps, a < p :=
      fun a ha => hpair.2.2 a ha p (List.mem_singleton_self p)
    have hlen' : ps.length < r := by
      have := hlen
      simp only [List.length_append, List.length_singleton] at this
      omega
    -- the mapped prefix is a sublist of `genPrefix p`
    have hsub : (ps.map (genSeq r k c)).Sublist (genPrefix r k c p) := by
      rw [genPrefix_eq_map]
      exact (sorted_lt_sublist_range hpair.1 hps_lt).map (genSeq r k c)
    -- goodness of `genSeq p` peels the last point off the tower
    have hstep := (genSeq_mem_goodSet r k c p).2 (ps.map (genSeq r k c))
      (List.mem_sublists.mpr hsub)
      (by rwa [List.length_map])
    rw [List.map_append, List.map_singleton, hstep]
    exact ih hpair.1 (le_of_lt hlen')

/-! ## Part 5: infinite Ramsey on `ℕ` for every uniformity and colour count -/

/-- `k`-colour homogeneity (the parent's `IsHomogeneous` is hard-wired to two
colours; this is the same predicate for an arbitrary colour count). -/
def IsHomogeneousK {S : Type*} [DecidableEq S] {n k : ℕ} (H : Set S)
    (c : Coloring S n k) (i : Fin k) : Prop :=
  ∀ (t : Finset S) (ht : t.card = n), (↑t : Set S) ⊆ H → c ⟨t, ht⟩ = i

/-- At two colours the general predicate is the parent's. -/
theorem isHomogeneousK_two {S : Type*} [DecidableEq S] (H : Set S) (n : ℕ)
    (c : Coloring S n 2) (i : Fin 2) :
    IsHomogeneousK H c i ↔ IsHomogeneous H n c i :=
  Iff.rfl

/-- **Infinite Ramsey on `ℕ`, full generality**: every colouring of the
`r`-subsets of `ℕ` by `k + 1` colours admits an infinite homogeneous set —
the range of `genSeq`, with the base colour of the majority tower. -/
theorem ramsey_nat_general (r k : ℕ) (c : Coloring ℕ r (k + 1)) :
    ∃ (H : Set ℕ) (i : Fin (k + 1)), H.Infinite ∧ IsHomogeneousK H c i := by
  refine ⟨Set.range (genSeq r k c), listMaj r k c [], ?_, ?_⟩
  · exact Set.infinite_range_of_injective (genSeq_strictMono r k c).injective
  · intro t ht hsub
    -- indices of the elements of `t`
    have hinj : Function.Injective (genSeq r k c) :=
      (genSeq_strictMono r k c).injective
    have hsub' : (↑t : Set ℕ) ⊆ genSeq r k c '' Set.univ := by
      rwa [Set.image_univ]
    obtain ⟨q, -, himg⟩ := Finset.subset_set_image_iff.mp hsub'
    have hqcard : q.card = r := by
      have hci := Finset.card_image_of_injective q hinj
      rw [himg] at hci
      omega
    -- the sorted index list
    set ps : List ℕ := q.sort with hps
    have hps_pair : ps.Pairwise (· < ·) := (Finset.sortedLT_sort q).pairwise
    have hps_len : ps.length = r := by rw [hps, Finset.length_sort]; exact hqcard
    have hps_fin : ps.toFinset = q := by rw [hps]; simp
    -- the mapped value list recovers `t`
    have hmap_fin : (ps.map (genSeq r k c)).toFinset = t := by
      rw [← himg, ← hps_fin]
      ext x
      simp [List.mem_toFinset, List.mem_map, Finset.mem_image]
    have hmap_len : r ≤ (ps.map (genSeq r k c)).length := by
      rw [List.length_map, hps_len]
    have hmap_card : (ps.map (genSeq r k c)).toFinset.card = r := by
      rw [hmap_fin]; exact ht
    -- honest colour = top of the tower = base of the tower
    have hcast : (⟨t, ht⟩ : {u : Finset ℕ // u.card = r}) =
        ⟨(ps.map (genSeq r k c)).toFinset, hmap_card⟩ :=
      Subtype.ext hmap_fin.symm
    rw [hcast, ← listMaj_eq_color c hmap_len hmap_card]
    exact listMaj_map_eq_base r k c ps hps_pair (le_of_eq hps_len)

/-! ## Part 6: infinite Ramsey over an arbitrary infinite type -/

/-- **The infinite Ramsey theorem, full generality**: on any infinite type,
every colouring of `r`-subsets by `k + 1` colours admits an infinite
homogeneous set.  Proof: pull the colouring back along `ℕ ↪ S`, run the
ultrafilter engine on `ℕ`, push the homogeneous set forward. -/
theorem infiniteRamsey_general (S : Type*) [DecidableEq S] [Infinite S]
    (r k : ℕ) (c : Coloring S r (k + 1)) :
    ∃ (H : Set S) (i : Fin (k + 1)), H.Infinite ∧ IsHomogeneousK H c i := by
  let f : ℕ ↪ S := Infinite.natEmbedding S
  obtain ⟨A, i, hAinf, hAhom⟩ :=
    ramsey_nat_general r k
      (fun t => c ⟨t.1.map f, by rw [Finset.card_map]; exact t.2⟩)
  refine ⟨f '' A, i, hAinf.image f.injective.injOn, ?_⟩
  intro t ht hsub
  -- pull `t` back to an `r`-subset of `A`
  obtain ⟨t', ht'sub, himg⟩ := Finset.subset_set_image_iff.mp hsub
  have ht'card : t'.card = r := by
    have hci := Finset.card_image_of_injective t' f.injective
    rw [himg] at hci
    omega
  have hkey := hAhom t' ht'card ht'sub
  have hmap : t'.map f = t := by
    rw [Finset.map_eq_image]; exact himg
  have hmapcard : (t'.map f).card = r := by rw [Finset.card_map]; exact ht'card
  have hcast : (⟨t, ht⟩ : {u : Finset S // u.card = r}) = ⟨t'.map f, hmapcard⟩ :=
    Subtype.ext hmap.symm
  rw [hcast]
  exact hkey

/-! ## Part 7: sanity bridges to the parent file -/

/-- The parent file's `InfiniteRamsey3` is the special case `r = 3`,
`k + 1 = 2` of the general theorem (an independent second proof — the parent
proves it with the hand-coded three-level engine). -/
theorem infiniteRamsey3_of_general : InfiniteRamsey3 := by
  intro S _ hS c
  have hinf : Infinite S := Cardinal.infinite_iff.mpr
    (by rw [hS]; exact Cardinal.aleph0_le_continuum)
  obtain ⟨H, i, h1, h2⟩ := infiniteRamsey_general S 3 1 c
  exact ⟨H, i, h1, (isHomogeneousK_two H 3 c i).mp h2⟩

/-- Second route to the formalized conjecture, through the general engine. -/
theorem erdos_70_formalized_conjecture_holds' : erdos_70_conjecture :=
  infiniteRamsey3_imp_conjecture infiniteRamsey3_of_general

/-- Infinite pigeonhole (`r = 1`) as a degenerate instance: any `(k+1)`-colouring
of the singletons of an infinite type has an infinite monochromatic set. -/
theorem infinite_pigeonhole_of_general (S : Type*) [DecidableEq S] [Infinite S]
    (k : ℕ) (c : Coloring S 1 (k + 1)) :
    ∃ (H : Set S) (i : Fin (k + 1)), H.Infinite ∧ IsHomogeneousK H c i :=
  infiniteRamsey_general S 1 k c

/-- Infinite Ramsey for graphs (`r = 2`) with any finite number of colours. -/
theorem infiniteRamsey_pairs_of_general (S : Type*) [DecidableEq S] [Infinite S]
    (k : ℕ) (c : Coloring S 2 (k + 1)) :
    ∃ (H : Set S) (i : Fin (k + 1)), H.Infinite ∧ IsHomogeneousK H c i :=
  infiniteRamsey_general S 2 k c

end RamseyGeneral

end Erdos70
