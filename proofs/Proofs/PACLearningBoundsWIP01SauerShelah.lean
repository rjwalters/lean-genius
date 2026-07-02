import Proofs.PACLearningBoundsWIP01

/-
# PAC Learning, wip-01 · Sauer–Shelah — |H| ≤ Σ_{k ≤ d} C(n,k) and the growth bound

The parent entry `pac-learning-bounds-wip-01` builds proper, `0`-axiom foundations for
Vapnik–Chervonenkis theory: the **trace** `Π_H(S) = {h ∩ S : h ∈ H}`, the **shattering**
relation, and the **VC dimension** `VCDim H` as the largest cardinality of a shattered
set. It proves the *elementary* half of the Sauer–Shelah circle of ideas
(`shatters_card_le_log`: a shattered set has size at most `log₂|H|`).

This file supplies the **hard half** — the actual **Sauer–Shelah lemma** — by connecting
the parent's hand-rolled definitions to Mathlib's `Finset.Shatters` / `Finset.vcDim`
machinery (`Mathlib.Combinatorics.SetFamily.Shatter`) and transporting Mathlib's proof of
the lemma across the bridge.

## What is proved

* `shatters_iff_finsetShatters` — the parent's `Shatters H S` (defined via `h ∩ S`)
  coincides with Mathlib's `Finset.Shatters H S` (defined via `S ∩ h`). The two differ
  only by commutativity of `∩`.
* `vcDim_eq` — the parent's `VCDim H` equals Mathlib's `Finset.vcDim H`. Hence the two VC
  dimensions are literally the same natural number.
* `card_le_sum_choose_vcDim` — the **Sauer–Shelah lemma**: over a finite ground type `α`
  with `n = |α|`, a hypothesis class of VC dimension `d = VCDim H` has at most
  `Σ_{k ≤ d} C(n,k)` members. This is the celebrated *polynomial* bound on the size of a
  class of bounded VC dimension — the quantitative statement the parent's `log₂` bound only
  gestured at.
* `vcDim_le_card` — over a finite ground type, `VCDim H ≤ |α|`.

The `|H|` bound above fixes the ground type. The **operationally central** quantity in PAC
learning is the *growth function* `Π_H(m)` — the number of distinct patterns a class cuts
out on an arbitrary set `S` of size `m`, with NO finiteness assumption on the ambient type
`α`. The second half of this file proves the Sauer–Shelah bound for exactly that quantity,
by transporting the trace onto the finite subtype `↥S` (of cardinality `|S|`) and checking
the transport preserves both the pattern count and the VC dimension:

* `card_restrFam` — restricting each pattern of `trace H S` to `↥S` is injective, so the
  transported family has the same cardinality: no patterns are lost or merged.
* `vcDim_restrFam_le` — a set shattered by the transported family lifts to a subset of `S`
  of equal size shattered by `H`, so the transported VC dimension is `≤ VCDim H`.
* `trace_card_le_sum_choose` — **the growth-function bound**:
  `|Π_H(S)| ≤ Σ_{i ≤ VCDim H} C(|S|, i)`, for an arbitrary set `S` over an arbitrary type.
* `trace_card_le_sum_choose_of_le`, `trace_card_le_sum_range_choose` — the same for any
  explicit `d ≥ VCDim H`, the latter in the familiar `Σ_{i=0}^{d} C(m,i)` form.

Fully machine-checked; `0` axioms beyond Mathlib's foundations; no `native_decide`.

Tags: pac-learning, vc-dimension, sauer-shelah, shattering, growth-function, combinatorics,
learning-theory
-/

namespace PACLearningBoundsWIP01

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Bridge to Mathlib.** The parent entry's `Shatters H S` — defined as
`H.image (· ∩ S) = S.powerset`, i.e. via restrictions `h ∩ S` — coincides with Mathlib's
`Finset.Shatters H S`, whose `shatters_iff` characterisation uses `S ∩ h`. The two families
of restrictions agree because `h ∩ S = S ∩ h`. -/
theorem shatters_iff_finsetShatters (H : Finset (Finset α)) (S : Finset α) :
    Shatters H S ↔ Finset.Shatters H S := by
  rw [Finset.shatters_iff]
  have himg : H.image (fun t => t ∩ S) = H.image (fun t => S ∩ t) :=
    Finset.image_congr (fun t _ => Finset.inter_comm t S)
  unfold Shatters trace
  rw [himg]

/-- Mathlib's VC dimension is at most the parent's: every set in the Mathlib `shatterer`
is shattered (in the parent's sense), hence has size at most `VCDim H`. -/
theorem finsetVcDim_le_vcDim (H : Finset (Finset α)) : Finset.vcDim H ≤ VCDim H := by
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  exact card_le_vcDim H s ((shatters_iff_finsetShatters H s).2 (Finset.mem_shatterer.1 hs))

/-- The parent's VC dimension is at most Mathlib's: any set shattered (in the parent's
sense) is shattered in Mathlib's sense, so its cardinality is `≤ Finset.vcDim H`, and the
supremum inherits the bound. -/
theorem vcDim_le_finsetVcDim (H : Finset (Finset α)) : VCDim H ≤ Finset.vcDim H := by
  rcases Set.eq_empty_or_nonempty {n | ∃ S : Finset α, S.card = n ∧ Shatters H S} with he | hne
  · rw [VCDim, he, csSup_empty]; exact bot_le
  · refine csSup_le hne fun n hn => ?_
    obtain ⟨S, rfl, hS⟩ := hn
    exact ((shatters_iff_finsetShatters H S).1 hS).card_le_vcDim

/-- **The two VC dimensions coincide.** The parent entry's `VCDim H` is the same natural
number as Mathlib's `Finset.vcDim H`. This lets Mathlib's Sauer–Shelah proof be quoted
for the parent's notion of VC dimension. -/
theorem vcDim_eq (H : Finset (Finset α)) : Finset.vcDim H = VCDim H :=
  le_antisymm (finsetVcDim_le_vcDim H) (vcDim_le_finsetVcDim H)

/-- **The Sauer–Shelah lemma.** Over a finite ground type `α` with `n = |α|`, a hypothesis
class `H` of VC dimension `d = VCDim H` contains at most `Σ_{k ≤ d} C(n,k)` hypotheses.

This is the quantitative heart of VC theory: a class of bounded VC dimension `d` is
*polynomially* small (`O(n^d)`), not merely `≤ 2^n`. It sharpens the parent entry's
`shatters_card_le_log` bound from a statement about a single shattered set to a statement
about the entire class. The proof composes Pajor's inequality `|H| ≤ |shatterer H|` with
Mathlib's `card_shatterer_le_sum_vcDim`, transported along `vcDim_eq`. -/
theorem card_le_sum_choose_vcDim [Fintype α] (H : Finset (Finset α)) :
    H.card ≤ ∑ k ∈ Finset.Iic (VCDim H), (Fintype.card α).choose k := by
  rw [← vcDim_eq]
  calc H.card ≤ H.shatterer.card := Finset.card_le_card_shatterer H
    _ ≤ ∑ k ∈ Finset.Iic (Finset.vcDim H), (Fintype.card α).choose k :=
        Finset.card_shatterer_le_sum_vcDim

/-- **VC dimension is bounded by the ground size.** Over a finite ground type, no set larger
than `α` itself can be shattered, so `VCDim H ≤ |α|`. -/
theorem vcDim_le_card [Fintype α] (H : Finset (Finset α)) :
    VCDim H ≤ Fintype.card α := by
  rw [← vcDim_eq]
  unfold Finset.vcDim
  refine Finset.sup_le fun s _ => ?_
  exact (Finset.card_le_univ s).trans_eq Finset.card_univ

-- ============================================================================
-- The growth function Π_H(m) on an arbitrary subset (no `Fintype α`)
-- ============================================================================

/-- Restrict a pattern `T ⊆ S` to the finite subtype `↥S = {x // x ∈ S}`. -/
def restr (S : Finset α) (T : Finset α) : Finset {x // x ∈ S} := T.subtype (· ∈ S)

/-- The trace family transported onto the finite ground set `↥S`. Since every member of
`trace H S` is a subset of `S`, this is a faithful copy of the trace living over a
`Fintype` (namely `↥S`, of cardinality `|S|`) — which is what lets Mathlib's Sauer–Shelah
bound apply with `n = |S|` even when the ambient type `α` is infinite. -/
def restrFam (H : Finset (Finset α)) (S : Finset α) : Finset (Finset {x // x ∈ S}) :=
  (trace H S).image (restr S)

/-- Restricting to `↥S` is injective on the trace: each pattern `T` there satisfies `T ⊆ S`,
hence is recovered from `restr S T` by mapping back along the subtype embedding. -/
theorem restr_injOn (H : Finset (Finset α)) (S : Finset α) :
    Set.InjOn (restr S) (trace H S) := by
  intro T1 h1 T2 h2 hEq
  have s1 : T1 ⊆ S := mem_powerset.mp (trace_subset_powerset H S h1)
  have s2 : T2 ⊆ S := mem_powerset.mp (trace_subset_powerset H S h2)
  have e1 : (restr S T1).map (Function.Embedding.subtype (· ∈ S)) = T1 :=
    Finset.subtype_map_of_mem (fun x hx => s1 hx)
  have e2 : (restr S T2).map (Function.Embedding.subtype (· ∈ S)) = T2 :=
    Finset.subtype_map_of_mem (fun x hx => s2 hx)
  rw [← e1, ← e2, hEq]

/-- The transport preserves the pattern count: `|restrFam H S| = |trace H S|`. -/
theorem card_restrFam (H : Finset (Finset α)) (S : Finset α) :
    (restrFam H S).card = (trace H S).card :=
  Finset.card_image_of_injOn (restr_injOn H S)

/-- Any subset `s ⊆ ↥S` shattered by the transported family lifts, along the subtype
embedding, to a subset `s.map emb ⊆ S` of the same cardinality shattered by `H` (parent's
`Shatters`). Hence the transported VC dimension is bounded by `VCDim H`. -/
theorem vcDim_restrFam_le (H : Finset (Finset α)) (S : Finset α) :
    (restrFam H S).vcDim ≤ VCDim H := by
  refine Finset.sup_le ?_
  intro s hs
  have hShat : (restrFam H S).Shatters s := Finset.mem_shatterer.mp hs
  set emb : {x // x ∈ S} ↪ α := Function.Embedding.subtype (· ∈ S) with hemb
  set S0 : Finset α := s.map emb with hS0
  have hS0S : S0 ⊆ S := by
    intro a ha
    rw [hS0] at ha
    exact Finset.property_of_mem_map_subtype s ha
  -- H shatters S0 (parent sense): every T0 ⊆ S0 is realised as some h ∩ S0.
  have key : Shatters H S0 := by
    refine Finset.Subset.antisymm (trace_subset_powerset H S0) ?_
    intro T0 hT0
    have hT0S0 : T0 ⊆ S0 := mem_powerset.mp hT0
    set t : Finset {x // x ∈ S} := T0.subtype (· ∈ S) with ht
    have htmap : t.map emb = T0 := by
      rw [ht, hemb]
      exact Finset.subtype_map_of_mem (fun x hx => hS0S (hT0S0 hx))
    have hts : t ⊆ s := by
      intro x hx
      rw [ht, Finset.mem_subtype] at hx
      have hxS0 : (↑x : α) ∈ S0 := hT0S0 hx
      rw [hS0, Finset.mem_map] at hxS0
      obtain ⟨y, hy, hyx⟩ := hxS0
      have hyx' : (y : α) = (x : α) := by simpa [hemb, Function.Embedding.coe_subtype] using hyx
      have hyeq : y = x := Subtype.ext hyx'
      rw [hyeq] at hy
      exact hy
    obtain ⟨u, hu, hsu⟩ := hShat hts
    rw [restrFam, Finset.mem_image] at hu
    obtain ⟨P, hP, hPu⟩ := hu
    rw [trace, Finset.mem_image] at hP
    obtain ⟨h, hh, hhP⟩ := hP
    rw [trace, Finset.mem_image]
    refine ⟨h, hh, ?_⟩
    -- from `s ∩ u = t`, map along emb and simplify to `h ∩ S0 = T0`.
    have hmap : (s ∩ u).map emb = t.map emb := by rw [hsu]
    rw [Finset.map_inter] at hmap
    have hu_map : u.map emb = h ∩ S := by
      rw [← hPu]
      simp only [restr, hemb]
      rw [Finset.subtype_map, ← hhP]
      exact Finset.filter_true_of_mem (fun x hx => (Finset.mem_inter.mp hx).2)
    rw [← hS0, hu_map, htmap] at hmap
    -- hmap : S0 ∩ (h ∩ S) = T0
    have hrw : h ∩ S0 = S0 ∩ (h ∩ S) := by
      ext a
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨ha_h, ha_S0⟩; exact ⟨ha_S0, ha_h, hS0S ha_S0⟩
      · rintro ⟨ha_S0, ha_h, _⟩; exact ⟨ha_h, ha_S0⟩
    rw [hrw]; exact hmap
  have hcard : (s.map emb).card = s.card := Finset.card_map _
  have hle := card_le_vcDim H S0 key
  rw [hS0, hcard] at hle
  exact hle

/-- **The Sauer–Shelah growth bound.** The trace (growth function) of a hypothesis class
`H` on a finite set `S` realises at most `Σ_{i ≤ VCDim H} C(|S|, i)` patterns. When
`VCDim H = d` this is a polynomial in `|S|` of degree `d`, decisively sharper than the
parent's exponential `|trace H S| ≤ 2^|S|`. Unlike `card_le_sum_choose_vcDim`, this makes
no finiteness assumption on the ambient type `α`: it bounds `Π_H(m)` at `m = |S|`, the form
uniform-convergence arguments actually consume. -/
theorem trace_card_le_sum_choose (H : Finset (Finset α)) (S : Finset α) :
    (trace H S).card ≤ ∑ i ∈ Finset.Iic (VCDim H), S.card.choose i := by
  have h1 : (restrFam H S).card ≤ (restrFam H S).shatterer.card :=
    Finset.card_le_card_shatterer _
  have h2 : (restrFam H S).shatterer.card
      ≤ ∑ k ∈ Finset.Iic (restrFam H S).vcDim, (Fintype.card {x // x ∈ S}).choose k :=
    Finset.card_shatterer_le_sum_vcDim
  rw [Fintype.card_coe] at h2
  have h3 : (restrFam H S).vcDim ≤ VCDim H := vcDim_restrFam_le H S
  have h4 : ∑ k ∈ Finset.Iic (restrFam H S).vcDim, S.card.choose k
      ≤ ∑ i ∈ Finset.Iic (VCDim H), S.card.choose i :=
    Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr h3)
  calc (trace H S).card
        = (restrFam H S).card := (card_restrFam H S).symm
    _ ≤ (restrFam H S).shatterer.card := h1
    _ ≤ ∑ k ∈ Finset.Iic (restrFam H S).vcDim, S.card.choose k := h2
    _ ≤ ∑ i ∈ Finset.Iic (VCDim H), S.card.choose i := h4

/-- The growth bound for any explicit VC-dimension upper bound `d ≥ VCDim H`. -/
theorem trace_card_le_sum_choose_of_le {d : ℕ} (H : Finset (Finset α)) (S : Finset α)
    (hd : VCDim H ≤ d) :
    (trace H S).card ≤ ∑ i ∈ Finset.Iic d, S.card.choose i :=
  le_trans (trace_card_le_sum_choose H S)
    (Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hd))

/-- The Sauer–Shelah growth bound in the familiar `Σ_{i=0}^{d} C(m,i)` form over
`range (d+1)`. -/
theorem trace_card_le_sum_range_choose {d : ℕ} (H : Finset (Finset α)) (S : Finset α)
    (hd : VCDim H ≤ d) :
    (trace H S).card ≤ ∑ i ∈ Finset.range (d + 1), S.card.choose i := by
  have hIic : Finset.Iic d = Finset.range (d + 1) := by
    ext i; simp [Nat.lt_succ_iff]
  rw [← hIic]
  exact trace_card_le_sum_choose_of_le H S hd

#check @card_le_sum_choose_vcDim
#check @trace_card_le_sum_choose
#check @trace_card_le_sum_range_choose

#print axioms card_le_sum_choose_vcDim
#print axioms trace_card_le_sum_choose
#print axioms trace_card_le_sum_range_choose

end PACLearningBoundsWIP01
