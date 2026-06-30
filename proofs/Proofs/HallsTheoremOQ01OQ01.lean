/-
Hall's theorem with a defect: the deficiency (Ore) form of the marriage theorem

Source: Open question from the halls-theorem gallery family (follow-up to
`HallsTheoremOQ01`, whose `exists_violating_of_no_matching` is the qualitative
"a deficient family must violate Hall somewhere" statement; here we quantify it).
Status: VERIFIED (0 axioms, 0 sorries)

The ordinary marriage theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`
in Mathlib) says a finite family of finite sets `t : ι → Finset α` admits a *system
of distinct representatives* — an injective `e : ι → α` with `e i ∈ t i` for every
`i` — **iff** Hall's condition holds:

    ∀ s : Finset ι,  #s ≤ #(s.biUnion t).

The **defect** (or **deficiency**) version, due to Ore, measures *how far* a family
is from having a full SDR. For a fixed slack `d : ℕ`:

  * the *relaxed* Hall condition is  `∀ s, #s ≤ #(s.biUnion t) + d`;
  * the matching conclusion is a *partial* SDR that leaves at most `d` indices
    unrepresented: a set `rejected` of indices with `#rejected ≤ d`, together with
    an assignment `e` that is injective on the remaining indices and represents
    each of them (`e i ∈ t i` for `i ∉ rejected`).

`defect_hall` proves these are equivalent. Taking `d = 0` recovers the classical
marriage theorem (`defect_hall_zero`).

Novel content (absent from Mathlib, which has only the `d = 0` case):

  * `defect_hall` : the relaxed Hall condition `∀ s, #s ≤ #(s.biUnion t) + d`
        holds **iff** there is a partial SDR missing at most `d` indices.
  * `defect_hall_zero` : the `d = 0` specialisation, recovering the SDR theorem.

Proof idea (the standard reduction). Adjoin `d` brand-new "universal" candidates by
working over `α ⊕ Fin d`, where every set gains all `d` right-hand dummies:
`t' i = (t i).image inl ∪ (univ.image inr)`. For a nonempty `s` the enlarged
neighbourhood is exactly the old one plus the `d` dummies, so the relaxed condition
for `t` becomes the *ordinary* Hall condition for `t'`. Mathlib's marriage theorem
gives a genuine SDR `f : ι → α ⊕ Fin d`; since `f` is injective and there are only
`d` dummies, at most `d` indices land on a dummy (these are the `rejected` ones),
and the rest are sent injectively into `α`, giving the partial SDR. The converse is
an elementary counting split `s = (s ∩ rejected) ∪ (s \ rejected)`.

(The ground type `α` is assumed nonempty — representatives are drawn from it — which
is the standard hypothesis; for empty `α` the family is the empty family of sets and
the statement degenerates.)
-/
import Mathlib

open Finset Function

namespace HallsTheoremOQ01OQ01

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Nonempty α]

/-- **Hall's theorem with defect `d` (Ore's deficiency form).** A finite family of
finite sets `t : ι → Finset α` satisfies the relaxed Hall condition
`∀ s, #s ≤ #(s.biUnion t) + d` **iff** there is a partial system of distinct
representatives leaving at most `d` indices unmatched: a set `rejected` with
`#rejected ≤ d` and an assignment `e` injective off `rejected` with `e i ∈ t i`
for every `i ∉ rejected`. -/
theorem defect_hall (t : ι → Finset α) (d : ℕ) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t) + d) ↔
      ∃ (e : ι → α) (rejected : Finset ι),
        #rejected ≤ d ∧ Set.InjOn e (↑rejectedᶜ) ∧ ∀ i ∉ rejected, e i ∈ t i := by
  classical
  -- the `d` universal dummies, living on the right of `α ⊕ Fin d`
  set D : Finset (α ⊕ Fin d) := Finset.univ.image Sum.inr with hDdef
  have hDcard : #D = d := by
    rw [hDdef, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
      Fintype.card_fin]
  -- the enlarged family: each set gains all `d` dummies
  set t' : ι → Finset (α ⊕ Fin d) := fun i => (t i).image Sum.inl ∪ D with ht'def
  constructor
  · -- (⟹) relaxed Hall for `t`  ⟹  ordinary Hall for `t'`  ⟹  partial SDR
    intro h
    -- ordinary Hall's condition holds for the enlarged family `t'`
    have hall' : ∀ s : Finset ι, #s ≤ #(s.biUnion t') := by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · -- for nonempty `s`, the enlarged neighbourhood is `inl`-image ⊎ all dummies
        have hbu : s.biUnion t' = (s.biUnion t).image Sum.inl ∪ D := by
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
    -- Mathlib's marriage theorem: a genuine SDR for `t'`
    obtain ⟨f, hf_inj, hf_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective t').mp hall'
    -- indices sent to a dummy are "rejected"
    set rejected : Finset ι := Finset.univ.filter (fun i => (f i).isRight = true) with hrejdef
    -- the actual representative: extract the `α`-component, defaulting off the dummies
    set e : ι → α := fun i => Sum.elim id (fun _ => Classical.arbitrary α) (f i) with hedef
    -- off `rejected`, `f i` is genuinely `inl (e i)`
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
    · -- at most `d` rejected indices: `f` injects them into the `d` dummies
      rw [← hDcard]
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        rw [Finset.mem_coe, hrejdef, Finset.mem_filter] at hi
        rw [Finset.mem_coe, hDdef, Finset.mem_image]
        rcases hfi : f i with a | b
        · simp [hfi] at hi
        · exact ⟨b, Finset.mem_univ b, rfl⟩
      · exact hf_inj.injOn
    · -- injective off `rejected`
      intro i hi j hj hij
      rw [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hi hj
      apply hf_inj
      rw [hfe i hi, hfe j hj, hij]
    · -- each non-rejected index is represented
      intro i hi
      have hmem := hf_mem i
      rw [hfe i hi] at hmem
      simp only [ht'def, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, ha, hae⟩ | hD
      · rw [Sum.inl.injEq] at hae; rw [← hae]; exact ha
      · rw [hDdef, Finset.mem_image] at hD
        obtain ⟨b, _, hb⟩ := hD
        exact absurd hb Sum.inr_ne_inl
  · -- (⟸) a partial SDR forces the relaxed Hall condition, by a counting split
    rintro ⟨e, rejected, hcard, hinj, hmem⟩ s
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

/-- **Marriage theorem (no defect).** Taking `d = 0` in `defect_hall` recovers the
classical statement: Hall's condition is equivalent to a full system of distinct
representatives. -/
theorem defect_hall_zero (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ e : ι → α, Function.Injective e ∧ ∀ i, e i ∈ t i := by
  have h0 : (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      (∀ s : Finset ι, #s ≤ #(s.biUnion t) + 0) := by simp
  rw [h0, defect_hall t 0]
  constructor
  · rintro ⟨e, rejected, hrej, hinj, hmem⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hrej
    subst hrej
    rw [Finset.compl_empty, Finset.coe_univ, Set.injOn_univ] at hinj
    exact ⟨e, hinj, fun i => hmem i (Finset.notMem_empty i)⟩
  · rintro ⟨e, hinj, hmem⟩
    refine ⟨e, ∅, by simp, ?_, fun i _ => hmem i⟩
    rw [Finset.compl_empty, Finset.coe_univ, Set.injOn_univ]
    exact hinj

end HallsTheoremOQ01OQ01
