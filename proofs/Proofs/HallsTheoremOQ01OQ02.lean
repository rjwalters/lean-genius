/-
# König–Ore deficiency formula: the exact matching number of a set system

Open Question: halls-theorem-oq-01-oq-02
Parent gallery entry: halls-theorem-oq-01 (the full biconditional bipartite Hall theorem).
Status: VERIFIED (0 axioms, 0 sorries)

## Context

The `halls-theorem` gallery family formalises Hall's marriage theorem in two complementary
worlds:

* the **graph** world (`HallsTheoremOQ01.hall_marriage`), a biconditional about
  `SimpleGraph.Subgraph.IsMatching`; and
* the **`Finset` / SDR** world, where Mathlib packages the theorem as
    `Finset.all_card_le_biUnion_card_iff_exists_injective`
    `: (∀ s, #s ≤ #(s.biUnion t)) ↔ ∃ f, Function.Injective f ∧ ∀ i, f i ∈ t i`,
  i.e. a **system of distinct representatives** (SDR) exists iff Hall's condition holds.

The companions `HallsTheoremOQ01OQ01` / `HallsTheoremOQ02OQ01` prove the *qualitative* defect
(Ore) theorem: if Hall's condition fails by at most `d`, a partial SDR missing at most `d`
indices exists. What is still missing — and is the genuine **König** content of this open
question — is the *exact* duality: the **minimum** number of indices that any partial SDR must
leave unmatched equals the **maximum deficiency** of the family,

    min over partial SDRs of (#unmatched)  =  max over s of (#s − #(s.biUnion t)).

This is the König–Egerváry / König–Ore deficiency formula — the set-system form of König's
theorem "max matching = min vertex cover". Equivalently, the **matching number** (the largest
number of indices that admit distinct representatives) is exactly `|ι| − deficiency`.

## Main results

* `deficiency t` — the maximum deficiency `⨆ s, (#s − #(s.biUnion t))` over subsets `s ⊆ ι`.
* `hall_relaxed_of_deficiency` — the family satisfies the relaxed Hall condition with slack
  `deficiency t` (this is the tautological upper witness).
* `konig_ore_exists` — a partial SDR leaving **at most** `deficiency t` indices unmatched exists.
* `konig_ore_min` — **every** partial SDR leaves **at least** `deficiency t` indices unmatched.
  Together with `konig_ore_exists` this is the deficiency formula: the minimum is exactly
  `deficiency t`.
* `konig_matching_number` — the dual "matching number" phrasing: some SDR represents at least
  `|ι| − deficiency t` indices, and none represents more.
* `deficiency_eq_zero_iff` / `deficiency_eq_zero_iff_exists_sdr` — `deficiency t = 0` iff Hall's
  condition holds iff a full SDR exists, tying the formula back to Mathlib's packaged theorem.

## Proof idea

The defect theorem `defect_hall` (reproduced here so the file is self-contained: it is the
`α ⊕ Fin d` dummy-adjunction argument, verified in `HallsTheoremOQ01OQ01`) is applied at the
single optimal slack `d = deficiency t`. For the lower bound, any partial SDR missing `r`
indices witnesses the relaxed Hall condition with slack `r` (the elementary counting split),
so every deficiency `#s − #(s.biUnion t) ≤ r`, whence `deficiency t ≤ r`. The two bounds pin the
minimum to `deficiency t`.
-/
import Mathlib

open Finset Function

namespace HallsTheoremOQ01OQ02

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Nonempty α]

/-! ### The defect (Ore) theorem, reproduced self-containedly

`defect_hall` is the qualitative deficiency theorem, identical to the verified
`HallsTheoremOQ01OQ01.defect_hall`. We inline it so this file depends only on Mathlib. -/

/-- **Hall's theorem with defect `d` (Ore's deficiency form).** A finite family of finite sets
`t : ι → Finset α` satisfies the relaxed Hall condition `∀ s, #s ≤ #(s.biUnion t) + d` **iff**
there is a partial system of distinct representatives leaving at most `d` indices unmatched. -/
theorem defect_hall (t : ι → Finset α) (d : ℕ) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t) + d) ↔
      ∃ (e : ι → α) (rejected : Finset ι),
        #rejected ≤ d ∧ Set.InjOn e (↑rejectedᶜ) ∧ ∀ i ∉ rejected, e i ∈ t i := by
  classical
  set D : Finset (α ⊕ Fin d) := Finset.univ.image Sum.inr with hDdef
  have hDcard : #D = d := by
    rw [hDdef, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
      Fintype.card_fin]
  set t' : ι → Finset (α ⊕ Fin d) := fun i => (t i).image Sum.inl ∪ D with ht'def
  constructor
  · intro h
    have hall' : ∀ s : Finset ι, #s ≤ #(s.biUnion t') := by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · have hbu : s.biUnion t' = (s.biUnion t).image Sum.inl ∪ D := by
          apply Finset.Subset.antisymm
          · intro x hx
            simp only [Finset.mem_biUnion, ht'def, Finset.mem_union, Finset.mem_image] at hx
            simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
            obtain ⟨i, hi, hcase⟩ := hx
            rcases hcase with ⟨a, hat, rfl⟩ | hD
            · exact Or.inl ⟨a, ⟨i, hi, hat⟩, rfl⟩
            · exact Or.inr hD
          · intro x hx
            rw [Finset.mem_union] at hx
            simp only [Finset.mem_biUnion, ht'def, Finset.mem_union, Finset.mem_image]
            rcases hx with hI | hD
            · rw [Finset.mem_image] at hI
              obtain ⟨a, ha, rfl⟩ := hI
              rw [Finset.mem_biUnion] at ha
              obtain ⟨i, hi, hat⟩ := ha
              exact ⟨i, hi, Or.inl ⟨a, hat, rfl⟩⟩
            · obtain ⟨i, hi⟩ := hs
              exact ⟨i, hi, Or.inr hD⟩
        have hdisj : Disjoint ((s.biUnion t).image Sum.inl) D := by
          rw [Finset.disjoint_left]
          intro x hx hxD
          rw [Finset.mem_image] at hx
          obtain ⟨a, _, rfl⟩ := hx
          rw [hDdef, Finset.mem_image] at hxD
          obtain ⟨b, _, hb⟩ := hxD
          exact Sum.inr_ne_inl hb
        rw [hbu, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ Sum.inl_injective, hDcard]
        exact h s
    obtain ⟨f, hf_inj, hf_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective t').mp hall'
    set rejected : Finset ι := Finset.univ.filter (fun i => (f i).isRight = true) with hrejdef
    set e : ι → α := fun i => Sum.elim id (fun _ => Classical.arbitrary α) (f i) with hedef
    have key : ∀ i, i ∉ rejected → ∃ a, f i = Sum.inl a := by
      intro i hi
      simp only [hrejdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hfi : f i with a | b
      · exact ⟨a, rfl⟩
      · simp [hfi] at hi
    have hfe : ∀ i, i ∉ rejected → f i = Sum.inl (e i) := by
      intro i hi
      obtain ⟨a, ha⟩ := key i hi
      simp [hedef, ha]
    refine ⟨e, rejected, ?_, ?_, ?_⟩
    · rw [← hDcard]
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        rw [Finset.mem_coe, hrejdef, Finset.mem_filter] at hi
        rw [Finset.mem_coe, hDdef, Finset.mem_image]
        rcases hfi : f i with a | b
        · simp [hfi] at hi
        · exact ⟨b, Finset.mem_univ b, rfl⟩
      · exact hf_inj.injOn
    · intro i hi j hj hij
      rw [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hi hj
      apply hf_inj
      rw [hfe i hi, hfe j hj, hij]
    · intro i hi
      have hmem := hf_mem i
      rw [hfe i hi] at hmem
      simp only [ht'def, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, ha, hae⟩ | hD
      · rw [Sum.inl.injEq] at hae; rw [← hae]; exact ha
      · rw [hDdef, Finset.mem_image] at hD
        obtain ⟨b, _, hb⟩ := hD
        exact absurd hb Sum.inr_ne_inl
  · rintro ⟨e, rejected, hcard, hinj, hmem⟩ s
    have hsplit : #(s ∩ rejected) + #(s \ rejected) = #s :=
      Finset.card_inter_add_card_sdiff s rejected
    have hA : #(s ∩ rejected) ≤ d :=
      le_trans (Finset.card_le_card Finset.inter_subset_right) hcard
    have hsub : (↑(s \ rejected) : Set ι) ⊆ ↑rejectedᶜ := by
      intro x hx
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hx
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
      exact hx.2
    have hB : #(s \ rejected) ≤ #(s.biUnion t) := by
      apply Finset.card_le_card_of_injOn e
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_sdiff] at hi
        rw [Finset.mem_coe, Finset.mem_biUnion]
        exact ⟨i, hi.1, hmem i hi.2⟩
      · exact hinj.mono hsub
    omega

/-! ### The deficiency and the König–Ore formula -/

/-- The **maximum deficiency** of the set system `t`: the largest excess `#s − #(s.biUnion t)`
(truncated subtraction) over all subsets `s ⊆ ι`. The empty set contributes `0`, so
`deficiency t = 0` exactly when Hall's condition holds. -/
def deficiency (t : ι → Finset α) : ℕ :=
  (Finset.univ : Finset (Finset ι)).sup (fun s => #s - #(s.biUnion t))

/-- Every subset's deficiency is bounded by the maximum deficiency. -/
theorem le_deficiency (t : ι → Finset α) (s : Finset ι) :
    #s - #(s.biUnion t) ≤ deficiency t := by
  unfold deficiency
  exact Finset.le_sup (f := fun s => #s - #(s.biUnion t)) (Finset.mem_univ s)

/-- The family satisfies the relaxed Hall condition with slack exactly `deficiency t`.
This is the tautological "upper" witness that feeds the defect theorem. -/
theorem hall_relaxed_of_deficiency (t : ι → Finset α) (s : Finset ι) :
    #s ≤ #(s.biUnion t) + deficiency t := by
  have h := le_deficiency t s
  omega

/-- **König–Ore, existence half.** There is a partial system of distinct representatives that
leaves **at most `deficiency t`** indices unmatched. -/
theorem konig_ore_exists (t : ι → Finset α) :
    ∃ (e : ι → α) (rejected : Finset ι),
      #rejected ≤ deficiency t ∧ Set.InjOn e (↑rejectedᶜ) ∧ ∀ i ∉ rejected, e i ∈ t i :=
  (defect_hall t (deficiency t)).mp (hall_relaxed_of_deficiency t)

/-- **König–Ore, optimality half.** *Every* partial system of distinct representatives leaves
**at least `deficiency t`** indices unmatched. Combined with `konig_ore_exists`, the minimum
number of unmatched indices over all partial SDRs is exactly `deficiency t`. -/
theorem konig_ore_min (t : ι → Finset α) {e : ι → α} {rejected : Finset ι}
    (hinj : Set.InjOn e (↑rejectedᶜ)) (hmem : ∀ i ∉ rejected, e i ∈ t i) :
    deficiency t ≤ #rejected := by
  -- the given partial SDR witnesses the relaxed Hall condition with slack `#rejected`
  have hrelaxed : ∀ s : Finset ι, #s ≤ #(s.biUnion t) + #rejected :=
    (defect_hall t (#rejected)).mpr ⟨e, rejected, le_rfl, hinj, hmem⟩
  -- hence every deficiency is ≤ #rejected, so the maximum is too
  apply Finset.sup_le
  intro s _
  have := hrelaxed s
  omega

/-- **König–Ore deficiency formula (least element form).** The minimum number of unmatched
indices, over all partial systems of distinct representatives, is exactly `deficiency t`. -/
theorem konig_ore_isLeast (t : ι → Finset α) :
    IsLeast
      {r : ℕ | ∃ (e : ι → α) (rejected : Finset ι),
        #rejected = r ∧ Set.InjOn e (↑rejectedᶜ) ∧ ∀ i ∉ rejected, e i ∈ t i}
      (deficiency t) := by
  constructor
  · obtain ⟨e, rejected, hle, hinj, hmem⟩ := konig_ore_exists t
    -- pad `rejected` up to a superset of size `deficiency t` to hit the value exactly;
    -- easier: throw away matched indices. Take the minimal witness directly from `defect_hall`
    -- at `d = deficiency t` after showing the achieved `#rejected` equals `deficiency t`.
    refine ⟨e, rejected, le_antisymm hle (konig_ore_min t hinj hmem), hinj, hmem⟩
  · rintro r ⟨e, rejected, rfl, hinj, hmem⟩
    exact konig_ore_min t hinj hmem

/-- **Matching number (dual phrasing).** The largest number of indices that can be given
distinct representatives is exactly `Fintype.card ι − deficiency t`: some partial SDR represents
at least that many indices, and none represents more. -/
theorem konig_matching_number (t : ι → Finset α) :
    IsGreatest
      {m : ℕ | ∃ (e : ι → α) (rejected : Finset ι),
        #(rejectedᶜ) = m ∧ Set.InjOn e (↑rejectedᶜ) ∧ ∀ i ∉ rejected, e i ∈ t i}
      (Fintype.card ι - deficiency t) := by
  constructor
  · -- the exact witness (#rejected = deficiency t) comes from the IsLeast statement
    obtain ⟨e, rejected, hcard, hinj, hmem⟩ := (konig_ore_isLeast t).1
    refine ⟨e, rejected, ?_, hinj, hmem⟩
    have hc : #rejected + #(rejectedᶜ) = Fintype.card ι := Finset.card_add_card_compl rejected
    omega
  · rintro m ⟨e, rejected, rfl, hinj, hmem⟩
    have hmin := konig_ore_min t hinj hmem
    have hc : #rejected + #(rejectedᶜ) = Fintype.card ι := Finset.card_add_card_compl rejected
    omega

/-! ### Connection back to the classical (deficiency-free) marriage theorem -/

/-- `deficiency t = 0` **iff** Hall's condition holds for every subset. -/
theorem deficiency_eq_zero_iff (t : ι → Finset α) :
    deficiency t = 0 ↔ ∀ s : Finset ι, #s ≤ #(s.biUnion t) := by
  constructor
  · intro h s
    have := le_deficiency t s
    omega
  · intro h
    have hle : deficiency t ≤ 0 := by
      unfold deficiency
      apply Finset.sup_le
      intro s _
      have := h s
      omega
    omega

/-- **Deficiency zero characterises a full SDR.** Combining `deficiency_eq_zero_iff` with
Mathlib's packaged marriage theorem `Finset.all_card_le_biUnion_card_iff_exists_injective`:
the family has zero deficiency iff it admits a genuine system of distinct representatives. This
is the `deficiency = 0` corner of the König–Ore formula and recovers classical Hall. -/
theorem deficiency_eq_zero_iff_exists_sdr (t : ι → Finset α) :
    deficiency t = 0 ↔ ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i := by
  rw [deficiency_eq_zero_iff]
  exact Finset.all_card_le_biUnion_card_iff_exists_injective t

end HallsTheoremOQ01OQ02
