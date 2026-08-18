import Proofs.Erdos85OrderFortyNineTableVerification

/-!
# Interface for prefix-normalizing the order-49 triple systems

The finite enumeration is deliberately separated from the graph-labeling
argument.  This file characterizes membership in the three raw enumerations
by the small collection of mathematical conditions that a relabeling must
establish: the fixed first block, one of the two possible second blocks,
strict lexicographic order, and pairwise linearity.
-/

namespace Erdos85
namespace OrderFortyNineWitnessTable

def firstTriple : List Nat := [0, 1, 2]

/-! ## Relabeling primitives

The graph-facing normalization only has to choose an ordered injection of the
points already used by its first two blocks.  These lemmas extend that partial
labeling to a permutation of all nine high points.  Keeping the extension step
separate avoids making any arbitrary enumeration of the unused high points
part of the eventual theorem statement.
-/

/-- Any ordered list of at most nine distinct high points can be sent to the
same initial segment of `Fin 9` by a permutation. -/
theorem exists_perm_send_to_initialSegment {n : Nat} (hn : n ≤ 9)
    (f : Fin n → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE hn i := by
  exact Equiv.Perm.exists_extending_pair f (Fin.castLE hn) hf
    (Fin.castLE_injective hn)

/-- Relabel six selected distinct points as `0,1,2,3,4,5`.  This is the
extension step for two disjoint triple blocks. -/
theorem exists_perm_normalizing_disjoint_prefix
    (f : Fin 6 → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE (by omega) i :=
  exists_perm_send_to_initialSegment (by omega) f hf

/-- Relabel five selected distinct points as `0,1,2,3,4`.  Ordering the common
point first gives the prefix `012,034` for two triples meeting once. -/
theorem exists_perm_normalizing_intersecting_prefix
    (f : Fin 5 → Fin 9) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (f i) = Fin.castLE (by omega) i :=
  exists_perm_send_to_initialSegment (by omega) f hf

/-- Point-level form of the disjoint-block normalization. -/
theorem exists_perm_normalizing_disjoint_triples
    (a b c d e f : Fin 9)
    (hinj : Function.Injective ![a, b, c, d, e, f]) :
    ∃ σ : Equiv.Perm (Fin 9),
      ({σ a, σ b, σ c} : Finset (Fin 9)) = {0, 1, 2} ∧
      ({σ d, σ e, σ f} : Finset (Fin 9)) = {3, 4, 5} := by
  obtain ⟨σ, hσ⟩ := exists_perm_normalizing_disjoint_prefix
    ![a, b, c, d, e, f] hinj
  have h0 := hσ (0 : Fin 6)
  have h1 := hσ (1 : Fin 6)
  have h2 := hσ (2 : Fin 6)
  have h3 := hσ (3 : Fin 6)
  have h4 := hσ (4 : Fin 6)
  have h5 := hσ (5 : Fin 6)
  refine ⟨σ, ?_, ?_⟩ <;> ext x <;> fin_cases x <;>
    simp_all

/-- Point-level form of the one-point-intersection normalization. -/
theorem exists_perm_normalizing_intersecting_triples
    (x a b d e : Fin 9)
    (hinj : Function.Injective ![x, a, b, d, e]) :
    ∃ σ : Equiv.Perm (Fin 9),
      ({σ x, σ a, σ b} : Finset (Fin 9)) = {0, 1, 2} ∧
      ({σ x, σ d, σ e} : Finset (Fin 9)) = {0, 3, 4} := by
  obtain ⟨σ, hσ⟩ := exists_perm_normalizing_intersecting_prefix
    ![x, a, b, d, e] hinj
  have h0 := hσ (0 : Fin 5)
  have h1 := hσ (1 : Fin 5)
  have h2 := hσ (2 : Fin 5)
  have h3 := hσ (3 : Fin 5)
  have h4 := hσ (4 : Fin 5)
  refine ⟨σ, ?_, ?_⟩ <;> ext y <;> fin_cases y <;>
    simp_all

set_option maxHeartbeats 1000000 in
/-- Two abstract three-subsets meeting in at most one point admit exactly one
of the two prefixes used by the exhaustive table.  This is the WLOG step that
the graph's pairwise-linear high supports need. -/
theorem exists_perm_normalizing_two_threeFinsets
    (A B : Finset (Fin 9)) (hA : A.card = 3) (hB : B.card = 3)
    (hlin : (A ∩ B).card ≤ 1) :
    ∃ σ : Equiv.Perm (Fin 9),
      A.map σ.toEmbedding = {0, 1, 2} ∧
      (B.map σ.toEmbedding = {3, 4, 5} ∨
       B.map σ.toEmbedding = {0, 3, 4}) := by
  have hcases : (A ∩ B).card = 0 ∨ (A ∩ B).card = 1 := by omega
  rcases hcases with hzero | hone
  · have hinter : A ∩ B = ∅ := Finset.card_eq_zero.mp hzero
    have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hinter
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA
    obtain ⟨d, e, f, hde, hdf, hef, rfl⟩ := Finset.card_eq_three.mp hB
    simp only [Finset.disjoint_insert_left, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hdisj
    have hinj : Function.Injective ![a, b, c, d, e, f] := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> aesop
    obtain ⟨σ, hfirst, hsecond⟩ :=
      exists_perm_normalizing_disjoint_triples a b c d e f hinj
    refine ⟨σ, ?_, Or.inl ?_⟩
    · simpa using hfirst
    · simpa using hsecond
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    have hxA : x ∈ A := by
      have : x ∈ A ∩ B := by simp [hx]
      exact (Finset.mem_inter.mp this).1
    have hxB : x ∈ B := by
      have : x ∈ A ∩ B := by simp [hx]
      exact (Finset.mem_inter.mp this).2
    have hAsub : ({x} : Finset (Fin 9)) ⊆ A := by simpa
    have hBsub : ({x} : Finset (Fin 9)) ⊆ B := by simpa
    have hAdiff : (A \ {x}).card = 2 := by
      rw [Finset.card_sdiff_of_subset hAsub, hA]
      simp
    have hBdiff : (B \ {x}).card = 2 := by
      rw [Finset.card_sdiff_of_subset hBsub, hB]
      simp
    obtain ⟨a, b, hab, hArest⟩ := Finset.card_eq_two.mp hAdiff
    obtain ⟨d, e, hde, hBrest⟩ := Finset.card_eq_two.mp hBdiff
    have hAform : A = {x, a, b} := by
      rw [← Finset.sdiff_union_of_subset hAsub, hArest]
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hBform : B = {x, d, e} := by
      rw [← Finset.sdiff_union_of_subset hBsub, hBrest]
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have haRest : a ∈ A \ {x} := by rw [hArest]; simp
    have hbRest : b ∈ A \ {x} := by rw [hArest]; simp
    have hdRest : d ∈ B \ {x} := by rw [hBrest]; simp
    have heRest : e ∈ B \ {x} := by rw [hBrest]; simp
    have hcross {y z : Fin 9} (hy : y ∈ A \ {x}) (hz : z ∈ B \ {x}) :
        y ≠ z := by
      intro hyz
      have hyI : y ∈ A ∩ B := Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hy).1, hyz ▸ (Finset.mem_sdiff.mp hz).1⟩
      have hyx : y = x := by simpa [hx] using hyI
      exact (Finset.mem_sdiff.mp hy).2 (by simpa [hyx])
    have had := hcross haRest hdRest
    have hae := hcross haRest heRest
    have hbd := hcross hbRest hdRest
    have hbe := hcross hbRest heRest
    have hinj : Function.Injective ![x, a, b, d, e] := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> aesop
    obtain ⟨σ, hfirst, hsecond⟩ :=
      exists_perm_normalizing_intersecting_triples x a b d e hinj
    refine ⟨σ, ?_, Or.inr ?_⟩
    · rw [hAform]
      simpa using hfirst
    · rw [hBform]
      simpa using hsecond

/-- Coordinate-free form: on any nine-point type, two linear triple blocks
can be made the prescribed prefix by choosing the labeling itself. -/
theorem exists_labeling_normalizing_two_threeFinsets
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 9)
    (A B : Finset α) (hA : A.card = 3) (hB : B.card = 3)
    (hlin : (A ∩ B).card ≤ 1) :
    ∃ e : α ≃ Fin 9,
      A.map e.toEmbedding = {0, 1, 2} ∧
      (B.map e.toEmbedding = {3, 4, 5} ∨
       B.map e.toEmbedding = {0, 3, 4}) := by
  let e₀ : α ≃ Fin 9 := Fintype.equivFinOfCardEq hcard
  have hAmap : (A.map e₀.toEmbedding).card = 3 := by simpa [hA]
  have hBmap : (B.map e₀.toEmbedding).card = 3 := by simpa [hB]
  have hinter :
      (A.map e₀.toEmbedding ∩ B.map e₀.toEmbedding).card ≤ 1 := by
    rw [← Finset.map_inter]
    simpa using hlin
  obtain ⟨σ, hfirst, hsecond⟩ :=
    exists_perm_normalizing_two_threeFinsets
      (A.map e₀.toEmbedding) (B.map e₀.toEmbedding) hAmap hBmap hinter
  refine ⟨e₀.trans σ, ?_, ?_⟩
  · simpa [Finset.map_map] using hfirst
  · rcases hsecond with hsecond | hsecond
    · exact Or.inl (by simpa [Finset.map_map] using hsecond)
    · exact Or.inr (by simpa [Finset.map_map] using hsecond)

/-- If the two blocks meet once, the coordinate-free normalization lands in
the intersecting prefix, not the disjoint one. -/
theorem exists_labeling_normalizing_intersecting_threeFinsets
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 9)
    (A B : Finset α) (hA : A.card = 3) (hB : B.card = 3)
    (hinter : (A ∩ B).card = 1) :
    ∃ e : α ≃ Fin 9,
      A.map e.toEmbedding = {0, 1, 2} ∧
      B.map e.toEmbedding = {0, 3, 4} := by
  obtain ⟨e, hAe, hBe⟩ := exists_labeling_normalizing_two_threeFinsets
    hcard A B hA hB (by omega)
  refine ⟨e, hAe, ?_⟩
  rcases hBe with hdisjoint | hintersecting
  · exfalso
    have hmapInter :
        (A.map e.toEmbedding ∩ B.map e.toEmbedding).card = 1 := by
      rw [← Finset.map_inter]
      simpa using hinter
    rw [hAe, hdisjoint] at hmapInter
    have hz : (({0, 1, 2} : Finset (Fin 9)) ∩ {3, 4, 5}).card = 0 := by
      native_decide
    omega
  · exact hintersecting

/-- If the two blocks are disjoint, the coordinate-free normalization lands
in the disjoint prefix. -/
theorem exists_labeling_normalizing_disjoint_threeFinsets
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 9)
    (A B : Finset α) (hA : A.card = 3) (hB : B.card = 3)
    (hinter : (A ∩ B).card = 0) :
    ∃ e : α ≃ Fin 9,
      A.map e.toEmbedding = {0, 1, 2} ∧
      B.map e.toEmbedding = {3, 4, 5} := by
  obtain ⟨e, hAe, hBe⟩ := exists_labeling_normalizing_two_threeFinsets
    hcard A B hA hB (by omega)
  refine ⟨e, hAe, ?_⟩
  rcases hBe with hdisjoint | hintersecting
  · exact hdisjoint
  · exfalso
    have hmapInter :
        (A.map e.toEmbedding ∩ B.map e.toEmbedding).card = 0 := by
      rw [← Finset.map_inter]
      simpa using hinter
    rw [hAe, hintersecting] at hmapInter
    have ho : (({0, 1, 2} : Finset (Fin 9)) ∩ {0, 3, 4}).card = 1 := by
      native_decide
    omega

/-- Mathematical membership criterion for the executable list of triples. -/
theorem mem_allTriples_iff {a b c : Nat} :
    [a, b, c] ∈ allTriples ↔ a < b ∧ b < c ∧ c < 9 := by
  simp [allTriples]
  omega

@[simp] theorem encTriple_three (a b c : Nat) :
    encTriple [a, b, c] = 100 * a + 10 * b + c := by
  simp [encTriple]
  omega

/-- Decimal encoding is injective on the triples used by the enumeration. -/
theorem encTriple_injective_of_lt_nine
    {a b c d e f : Nat} (hb : b < 9) (hc : c < 9)
    (he : e < 9) (hf : f < 9)
    (henc : encTriple [a, b, c] = encTriple [d, e, f]) :
    a = d ∧ b = e ∧ c = f := by
  simp only [encTriple_three] at henc
  omega

/-- For a list without repetition, the Boolean enumeration test counts the
intersection of the underlying finsets. -/
theorem linB_eq_true_iff_toFinset_inter_le_one
    {S T : List Nat} (hS : S.Nodup) :
    linB S T = true ↔ (S.toFinset ∩ T.toFinset).card ≤ 1 := by
  simp only [linB, Nat.ble_eq]
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hS.filter _)]
  rw [List.toFinset_filter]
  have heq :
      S.toFinset.filter (fun x => T.contains x) = S.toFinset ∩ T.toFinset := by
    ext x
    simp
  rw [heq]

/-- Triple-specialized form used by the raw-enumeration interface. -/
theorem linB_eq_true_iff_card_inter_le_one
    {a b c d e f : Nat} (hS : List.Nodup [a, b, c]) :
    linB [a, b, c] [d, e, f] = true ↔
      (({a, b, c} : Finset Nat) ∩ {d, e, f}).card ≤ 1 := by
  simpa using linB_eq_true_iff_toFinset_inter_le_one (T := [d, e, f]) hS

/-- The canonical ascending digit list of a labeled high-support block. -/
def tripleDigits (S : Finset (Fin 9)) : List Nat :=
  (S.sort (· ≤ ·)).map Fin.val

@[simp] theorem length_tripleDigits (S : Finset (Fin 9)) :
    (tripleDigits S).length = S.card := by
  simp [tripleDigits]

theorem nodup_tripleDigits (S : Finset (Fin 9)) :
    (tripleDigits S).Nodup := by
  exact (Finset.sort_nodup S (· ≤ ·)).map Fin.val_injective

theorem toFinset_tripleDigits (S : Finset (Fin 9)) :
    (tripleDigits S).toFinset = S.image Fin.val := by
  ext x
  simp [tripleDigits]

/-- Every three-subset of `Fin 9`, written in increasing order, belongs to
the executable enumeration's `allTriples`. -/
theorem tripleDigits_mem_allTriples {S : Finset (Fin 9)} (hS : S.card = 3) :
    tripleDigits S ∈ allTriples := by
  have hlen : (S.sort (· ≤ ·)).length = 3 := by simpa using hS
  obtain ⟨a, b, c, hlist⟩ := List.length_eq_three.mp hlen
  have hsorted := Finset.sortedLT_sort S
  rw [hlist] at hsorted
  have hpairs : (a < b ∧ a < c) ∧ b < c := by
    simpa using hsorted.pairwise
  have habc : a < b ∧ b < c := ⟨hpairs.1.1, hpairs.2⟩
  rw [tripleDigits, hlist]
  exact mem_allTriples_iff.mpr ⟨habc.1, habc.2, c.isLt⟩

/-- The Boolean linearity test on canonical digit lists is exactly finset
linearity before forgetting the `Fin 9` bounds. -/
theorem linB_tripleDigits_eq_true_iff {S T : Finset (Fin 9)} :
    linB (tripleDigits S) (tripleDigits T) = true ↔
      (S ∩ T).card ≤ 1 := by
  rw [linB_eq_true_iff_toFinset_inter_le_one (nodup_tripleDigits S)]
  rw [toFinset_tripleDigits, toFinset_tripleDigits]
  rw [← Finset.image_inter S T Fin.val_injective]
  rw [Finset.card_image_of_injective _ Fin.val_injective]

/-- Distinct labeled triple blocks have distinct decimal encodings. -/
theorem eq_of_encTriple_tripleDigits_eq
    {S T : Finset (Fin 9)} (hS : S.card = 3) (hT : T.card = 3)
    (henc : encTriple (tripleDigits S) = encTriple (tripleDigits T)) :
    S = T := by
  have hSlen : (tripleDigits S).length = 3 := (length_tripleDigits S).trans hS
  have hTlen : (tripleDigits T).length = 3 := (length_tripleDigits T).trans hT
  obtain ⟨a, b, c, hSd⟩ := List.length_eq_three.mp hSlen
  obtain ⟨d, e, f, hTd⟩ := List.length_eq_three.mp hTlen
  have hSmem := tripleDigits_mem_allTriples hS
  have hTmem := tripleDigits_mem_allTriples hT
  rw [hSd] at hSmem henc
  rw [hTd] at hTmem henc
  have hSb := mem_allTriples_iff.mp hSmem
  have hTb := mem_allTriples_iff.mp hTmem
  have hb9 : b < 9 := lt_trans hSb.2.1 hSb.2.2
  have he9 : e < 9 := lt_trans hTb.2.1 hTb.2.2
  obtain ⟨rfl, rfl, rfl⟩ := encTriple_injective_of_lt_nine
    hb9 hSb.2.2 he9 hTb.2.2 henc
  have hdigits : tripleDigits S = tripleDigits T := hSd.trans hTd.symm
  apply Finset.image_injective Fin.val_injective
  rw [← toFinset_tripleDigits, ← toFinset_tripleDigits, hdigits]

/-! The two prefix choices also force the remaining blocks to occur later in
the executable order.  These are tiny closed nine-point facts; expressing
them here keeps the graph-facing selection argument conceptual. -/

theorem encTriple_intersectingPrefix_lt_remaining :
    ∀ S : Finset (Fin 9), S.card = 3 →
      (({0, 1, 2} : Finset (Fin 9)) ∩ S).card ≤ 1 →
      (({0, 3, 4} : Finset (Fin 9)) ∩ S).card ≤ 1 →
      S ≠ {0, 1, 2} → S ≠ {0, 3, 4} →
      encTriple [0, 3, 4] < encTriple (tripleDigits S) := by
  native_decide

theorem encTriple_disjointPrefix_lt_remaining :
    ∀ S : Finset (Fin 9), S.card = 3 →
      (({0, 1, 2} : Finset (Fin 9)) ∩ S).card = 0 →
      (({3, 4, 5} : Finset (Fin 9)) ∩ S).card = 0 →
      encTriple [3, 4, 5] < encTriple (tripleDigits S) := by
  native_decide

@[simp] theorem tripleDigits_012 :
    tripleDigits ({0, 1, 2} : Finset (Fin 9)) = [0, 1, 2] := by native_decide

@[simp] theorem tripleDigits_034 :
    tripleDigits ({0, 3, 4} : Finset (Fin 9)) = [0, 3, 4] := by native_decide

@[simp] theorem tripleDigits_345 :
    tripleDigits ({3, 4, 5} : Finset (Fin 9)) = [3, 4, 5] := by native_decide

theorem mem_rawT2_iff {T2 : List Nat} :
    [firstTriple, T2] ∈ rawT2 ↔ T2 ∈ secondTriples := by
  simp [rawT2, firstTriple]

theorem mem_rawT3_iff {T2 T3 : List Nat} :
    [firstTriple, T2, T3] ∈ rawT3 ↔
      T2 ∈ secondTriples ∧
      T3 ∈ allTriples ∧
      encTriple T2 < encTriple T3 ∧
      linB T3 firstTriple = true ∧ linB T3 T2 = true := by
  simp [rawT3, firstTriple, Bool.and_eq_true, Nat.ble_eq]

theorem mem_rawT4_iff {T2 T3 T4 : List Nat} :
    [firstTriple, T2, T3, T4] ∈ rawT4 ↔
      T2 ∈ secondTriples ∧
      T3 ∈ allTriples ∧ T4 ∈ allTriples ∧
      encTriple T2 < encTriple T3 ∧
      encTriple T3 < encTriple T4 ∧
      linB T3 firstTriple = true ∧ linB T3 T2 = true ∧
      linB T4 firstTriple = true ∧ linB T4 T2 = true ∧
      linB T4 T3 = true := by
  simp [rawT4, firstTriple, Bool.and_eq_true, Nat.ble_eq] <;> tauto

/-- An additional block after an intersecting normalized prefix gives a raw
three-block row. -/
theorem mem_rawT3_of_intersectingPrefix
    {S : Finset (Fin 9)} (hS : S.card = 3)
    (hS1 : (({0, 1, 2} : Finset (Fin 9)) ∩ S).card ≤ 1)
    (hS2 : (({0, 3, 4} : Finset (Fin 9)) ∩ S).card ≤ 1)
    (hne1 : S ≠ {0, 1, 2}) (hne2 : S ≠ {0, 3, 4}) :
    [firstTriple, [0, 3, 4], tripleDigits S] ∈ rawT3 := by
  rw [mem_rawT3_iff]
  refine ⟨by simp [secondTriples], tripleDigits_mem_allTriples hS,
    encTriple_intersectingPrefix_lt_remaining S hS hS1 hS2 hne1 hne2, ?_, ?_⟩
  · change linB (tripleDigits S) [0, 1, 2] = true
    rw [← tripleDigits_012, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hS1
  · rw [← tripleDigits_034, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hS2

/-- An additional block after a disjoint normalized prefix gives a raw
three-block row. -/
theorem mem_rawT3_of_disjointPrefix
    {S : Finset (Fin 9)} (hS : S.card = 3)
    (hS1 : (({0, 1, 2} : Finset (Fin 9)) ∩ S).card = 0)
    (hS2 : (({3, 4, 5} : Finset (Fin 9)) ∩ S).card = 0) :
    [firstTriple, [3, 4, 5], tripleDigits S] ∈ rawT3 := by
  rw [mem_rawT3_iff]
  refine ⟨by simp [secondTriples], tripleDigits_mem_allTriples hS,
    encTriple_disjointPrefix_lt_remaining S hS hS1 hS2, ?_, ?_⟩
  · change linB (tripleDigits S) [0, 1, 2] = true
    rw [← tripleDigits_012, linB_tripleDigits_eq_true_iff]
    rw [Finset.inter_comm]
    omega
  · rw [← tripleDigits_345, linB_tripleDigits_eq_true_iff]
    rw [Finset.inter_comm]
    omega

/-- Two additional blocks after an intersecting prefix can be ordered by
their injective decimal encodings to give a raw four-block row. -/
theorem mem_rawT4_of_intersectingPrefix
    {S T : Finset (Fin 9)} (hS : S.card = 3) (hT : T.card = 3)
    (hS1 : (({0, 1, 2} : Finset (Fin 9)) ∩ S).card ≤ 1)
    (hS2 : (({0, 3, 4} : Finset (Fin 9)) ∩ S).card ≤ 1)
    (hT1 : (({0, 1, 2} : Finset (Fin 9)) ∩ T).card ≤ 1)
    (hT2 : (({0, 3, 4} : Finset (Fin 9)) ∩ T).card ≤ 1)
    (hSTlin : (S ∩ T).card ≤ 1)
    (hSne1 : S ≠ {0, 1, 2}) (hSne2 : S ≠ {0, 3, 4})
    (hTne1 : T ≠ {0, 1, 2}) (hTne2 : T ≠ {0, 3, 4})
    (hST : S ≠ T) :
    [firstTriple, [0, 3, 4], tripleDigits S, tripleDigits T] ∈ rawT4 ∨
    [firstTriple, [0, 3, 4], tripleDigits T, tripleDigits S] ∈ rawT4 := by
  have hencne : encTriple (tripleDigits S) ≠ encTriple (tripleDigits T) := by
    intro heq
    exact hST (eq_of_encTriple_tripleDigits_eq hS hT heq)
  have hSfirst : linB (tripleDigits S) firstTriple = true := by
    change linB (tripleDigits S) [0, 1, 2] = true
    rw [← tripleDigits_012, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hS1
  have hSsecond : linB (tripleDigits S) [0, 3, 4] = true := by
    rw [← tripleDigits_034, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hS2
  have hTfirst : linB (tripleDigits T) firstTriple = true := by
    change linB (tripleDigits T) [0, 1, 2] = true
    rw [← tripleDigits_012, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hT1
  have hTsecond : linB (tripleDigits T) [0, 3, 4] = true := by
    rw [← tripleDigits_034, linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hT2
  have hSTb : linB (tripleDigits T) (tripleDigits S) = true := by
    rw [linB_tripleDigits_eq_true_iff]
    simpa [Finset.inter_comm] using hSTlin
  have hTSb : linB (tripleDigits S) (tripleDigits T) = true := by
    rw [linB_tripleDigits_eq_true_iff]
    exact hSTlin
  rcases lt_or_gt_of_ne hencne with hlt | hgt
  · apply Or.inl
    rw [mem_rawT4_iff]
    exact ⟨by simp [secondTriples], tripleDigits_mem_allTriples hS,
      tripleDigits_mem_allTriples hT,
      encTriple_intersectingPrefix_lt_remaining S hS hS1 hS2 hSne1 hSne2,
      hlt, hSfirst, hSsecond, hTfirst, hTsecond, hSTb⟩
  · apply Or.inr
    rw [mem_rawT4_iff]
    exact ⟨by simp [secondTriples], tripleDigits_mem_allTriples hT,
      tripleDigits_mem_allTriples hS,
      encTriple_intersectingPrefix_lt_remaining T hT hT1 hT2 hTne1 hTne2,
      hgt, hTfirst, hTsecond, hSfirst, hSsecond, hTSb⟩

theorem exists_tableT2_row_of_mem_rawT2
    {S : List (List Nat)} (hS : S ∈ rawT2) :
    ∃ row ∈ tableT2, row.1 = S := by
  have hmap : S ∈ tableT2.map (·.1) := by
    rw [← rawT2_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

theorem exists_tableT3_row_of_mem_rawT3
    {S : List (List Nat)} (hS : S ∈ rawT3) :
    ∃ row ∈ tableT3, row.1 = S := by
  have hmap : S ∈ tableT3.map (·.1) := by
    rw [← rawT3_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

theorem exists_tableT4_row_of_mem_rawT4
    {S : List (List Nat)} (hS : S ∈ rawT4) :
    ∃ row ∈ tableT4, row.1 = S := by
  have hmap : S ∈ tableT4.map (·.1) := by
    rw [← rawT4_eq_table]
    exact hS
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmap
  exact ⟨row, hrow, heq⟩

end OrderFortyNineWitnessTable
end Erdos85
