import Mathlib

/-!
# The Defect (Deficiency) Form of Hall's Marriage Theorem

Hall's marriage theorem says a family of finite sets `t : ι → Finset α` admits a
*system of distinct representatives* (an injective transversal `f` with
`f x ∈ t x`) **iff** the Hall condition `#s ≤ #(s.biUnion t)` holds for every
`s : Finset ι`.

This entry proves the **defect version** (also called the *deficiency* or
*König–Ore* form): if the Hall condition fails by at most `d`, i.e.

    ∀ s : Finset ι,  #s ≤ #(s.biUnion t) + d,          (`hcond`)

then one can still match **all but at most `d`** of the index set — there is a
subset `s ⊆ ι` with `Fintype.card ι ≤ #s + d` together with an injective choice
function `f : ι → α` such that `f x ∈ t x` for every `x ∈ s`.

## Proof idea

Adjoin `d` universal dummy targets: pass to the coproduct `α ⊕ Fin d` and set

    t' i = (t i).image Sum.inl ∪ D,     D := Finset.univ.image Sum.inr

the set `D` of all `d` dummies being available to every index. The `+ d` slack
turns the *defect* Hall condition for `t` into the *exact* Hall condition for
`t'`, so Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`
delivers an injective `g : ι → α ⊕ Fin d`. Indices whose value lands in the left
summand give a genuine matching into `α`; since `g` is injective, at most `d`
indices can land on the `d` dummies, so at most `d` indices go unmatched.

## Main results

* `HallDefect.hall_defect` — the defect matching theorem.
* `HallDefect.hall_of_hall_defect` — specialising to `d = 0` recovers the
  classical system of distinct representatives, confirming the defect theorem is
  a genuine generalisation of Hall's marriage theorem.
-/

open Finset

namespace HallDefect

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι] [Nonempty α]

/-- **Defect / deficiency form of Hall's marriage theorem.**

If the Hall condition for `t : ι → Finset α` fails by at most `d`
(`∀ s, #s ≤ #(s.biUnion t) + d`), then some `s : Finset ι` of size at least
`Fintype.card ι - d` (equivalently `Fintype.card ι ≤ #s + d`) carries an
injective choice function `f` with `f x ∈ t x` for all `x ∈ s`: at most `d`
indices are left unmatched. -/
theorem hall_defect (t : ι → Finset α) (d : ℕ)
    (hcond : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card + d) :
    ∃ (s : Finset ι) (f : ι → α),
      Fintype.card ι ≤ s.card + d ∧
      (∀ x ∈ s, f x ∈ t x) ∧
      Set.InjOn f (s : Set ι) := by
  classical
  -- The `d` dummy targets living in the right summand of `α ⊕ Fin d`.
  set D : Finset (α ⊕ Fin d) := Finset.univ.image (Sum.inr : Fin d → α ⊕ Fin d)
    with hDdef
  have hcardD : D.card = d := by
    rw [hDdef, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
      Fintype.card_fin]
  -- The augmented family satisfies the *exact* Hall condition.
  have hHall : ∀ (s : Finset ι),
      s.card ≤ (s.biUnion (fun i => (t i).image Sum.inl ∪ D)).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · -- `(s.biUnion t).image inl ∪ D` sits inside the augmented biUnion, and its
      -- two halves are disjoint, giving the `+ d` we need.
      have hsub : (s.biUnion t).image Sum.inl ∪ D
          ⊆ s.biUnion (fun i => (t i).image Sum.inl ∪ D) := by
        intro y hy
        rw [Finset.mem_union] at hy
        rcases hy with hy | hy
        · rw [Finset.mem_image] at hy
          obtain ⟨a, ha, rfl⟩ := hy
          rw [Finset.mem_biUnion] at ha
          obtain ⟨i, hi, hai⟩ := ha
          rw [Finset.mem_biUnion]
          exact ⟨i, hi, by
            rw [Finset.mem_union]
            exact Or.inl (by rw [Finset.mem_image]; exact ⟨a, hai, rfl⟩)⟩
        · obtain ⟨i, hi⟩ := hne
          rw [Finset.mem_biUnion]
          exact ⟨i, hi, by rw [Finset.mem_union]; exact Or.inr hy⟩
      have hdisj : Disjoint ((s.biUnion t).image Sum.inl) D := by
        rw [Finset.disjoint_left]
        intro y hyl hyr
        rw [Finset.mem_image] at hyl
        obtain ⟨a, _, rfl⟩ := hyl
        rw [hDdef, Finset.mem_image] at hyr
        obtain ⟨j, _, hj⟩ := hyr
        exact absurd hj (by simp)
      calc s.card ≤ (s.biUnion t).card + d := hcond s
        _ = ((s.biUnion t).image Sum.inl).card + D.card := by
              rw [Finset.card_image_of_injective _ Sum.inl_injective, hcardD]
        _ = ((s.biUnion t).image Sum.inl ∪ D).card :=
              (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (s.biUnion (fun i => (t i).image Sum.inl ∪ D)).card :=
              Finset.card_le_card hsub
  -- Hall for the augmented family produces an injective `g`.
  obtain ⟨g, hg_inj, hg_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hHall
  -- The matched indices: those whose value is *not* a dummy.
  set s : Finset ι := Finset.univ.filter (fun x => g x ∉ D) with hsdef
  set f : ι → α := fun x => Sum.elim id (fun _ => Classical.arbitrary α) (g x) with hfdef
  -- On matched indices, `g` factors through `inl` at value `f`.
  have hform : ∀ z ∈ s, g z = Sum.inl (f z) := by
    intro z hz
    rw [hsdef, Finset.mem_filter] at hz
    have hmem := hg_mem z
    rw [Finset.mem_union] at hmem
    rcases hmem with hL | hR
    · rw [Finset.mem_image] at hL
      obtain ⟨a, _, hga⟩ := hL
      have hgz : g z = Sum.inl a := hga.symm
      have hfz : f z = a := by rw [hfdef]; simp [hgz]
      rw [hgz, hfz]
    · exact absurd hR hz.2
  refine ⟨s, f, ?_, ?_, ?_⟩
  · -- Size bound: complement of `s` injects into the `d` dummies.
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (p := fun x => g x ∉ D)
    rw [Finset.card_univ] at hsplit
    have hcompl : (Finset.univ.filter (fun x => ¬ (g x ∉ D))).card ≤ d := by
      have himg : (Finset.univ.filter (fun x => ¬ (g x ∉ D))).image g ⊆ D := by
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
        exact hx
      calc (Finset.univ.filter (fun x => ¬ (g x ∉ D))).card
          = ((Finset.univ.filter (fun x => ¬ (g x ∉ D))).image g).card :=
            (Finset.card_image_of_injOn hg_inj.injOn).symm
        _ ≤ D.card := Finset.card_le_card himg
        _ = d := hcardD
    rw [hsdef]
    omega
  · intro x hx
    obtain ⟨a, ha, hga⟩ : ∃ a ∈ t x, Sum.inl a = g x := by
      have hmem := hg_mem x
      rw [Finset.mem_union] at hmem
      rcases hmem with hL | hR
      · rwa [Finset.mem_image] at hL
      · rw [hsdef, Finset.mem_filter] at hx
        exact absurd hR hx.2
    have hgx : g x = Sum.inl a := hga.symm
    have hfx : f x = a := by rw [hfdef]; simp [hgx]
    rw [hfx]; exact ha
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    have hx' := hform x hx
    have hy' := hform y hy
    apply hg_inj
    rw [hx', hy', hxy]

/-- Specialising the defect theorem to `d = 0` recovers the classical Hall
system of distinct representatives: a full injective transversal. This confirms
`hall_defect` genuinely generalises Hall's marriage theorem. -/
theorem hall_of_hall_defect (t : ι → Finset α)
    (hcond : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  obtain ⟨s, f, hcard, hmem, hinj⟩ := hall_defect t 0 (fun s => by simpa using hcond s)
  have hs : s = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hle : s.card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ s)
    omega
  rw [hs] at hmem hinj
  refine ⟨f, ?_, fun x => hmem x (Finset.mem_univ x)⟩
  intro a b hab
  exact hinj (by simp) (by simp) hab

end HallDefect
