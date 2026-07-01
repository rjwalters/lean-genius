/-
  Erdős Problem #862 — Open Question OQ-03:
  "Extend the counting theory to maximal B_h sets for h ≥ 3:
   how does the number of maximal B_h subsets of {1,…,N} grow?"

  Source: https://erdosproblems.com/862  (parent: Maximal Sidon Subsets)

  The parent problem #862 concerns A₁(N), the number of *maximal Sidon*
  (= B₂) subsets of {1,…,N}, resolved by Saxton–Thomason (2015) via the
  hypergraph container method:  A₁(N) ≥ 2^{(0.16+o(1))√N}.

  This open question asks for the analogue for B_h sequences with h ≥ 3.
  A B_h set is a set in which every h-element subset has a distinct sum.
  The counting problem for maximal B_h sets (h ≥ 3) is GENUINELY OPEN:
  the container method applies, but the controlling hypergraph becomes
  (2h)-uniform and the size asymptotics of B_h sets in [N] are less precise
  than the f(N) ~ √N estimate available for Sidon sets.

  This file does NOT resolve the open question.  It instead builds the
  *counting framework* for maximal B_h subsets and proves the fully
  machine-checked (0 sorry, 0 axiom) structural facts that any such theory
  rests on:

    • B_h is hereditary (closed under taking subsets);
    • every set of ≤ h elements is automatically B_h (so ∅, singletons are);
    • the parent's Sidon condition implies the B₂ condition
      (`IsSidonSet S → IsBhSet 2 S`), tying this generalization to #862;
    • for every N and every h ≥ 2 a maximal B_h subset of [N] EXISTS, so the
      counting function `Aₕ N h` is well-defined and `≥ 1`
      (a maximum-cardinality B_h subset is maximal — the finite analogue of
      the Zorn argument used implicitly in the parent).

  The open growth law itself is recorded as a `def`
  (`MaximalBhCountingQuestion`) — a statement, not a theorem — so the file
  makes no unproven claim.

  Reference: Cameron–Erdős (1992); Saxton–Thomason, *Hypergraph containers*,
  Invent. Math. 201 (2015), 925–992.
-/

import Mathlib

open Real Finset

namespace Erdos862OQ03

/-! ## Part I — Definitions (self-contained; B₂ agrees with the parent #862) -/

/-- A Sidon set (B₂ sequence): all pairwise sums are distinct.
    Reproduced verbatim from the parent `Erdos862` entry. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/-- The interval `{1, …, N}`. -/
def Interval (N : ℕ) : Finset ℕ := Finset.range (N + 1) \ {0}

/-- A set `S` is a **B_h set** if every `h`-element subset has a distinct sum:
    any two `h`-element subsets of `S` with the same element-sum coincide.

    This is the natural element-sum reading of the B_h condition; `h = 2`
    recovers the (subset form of the) Sidon property. -/
def IsBhSet (h : ℕ) (S : Finset ℕ) : Prop :=
  2 ≤ h ∧ ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ S → T₂ ⊆ S →
    T₁.card = h → T₂.card = h → (∑ x ∈ T₁, x) = (∑ x ∈ T₂, x) → T₁ = T₂

/-- A B_h subset of `{1,…,N}`. -/
def IsBhSubset (N h : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Interval N ∧ IsBhSet h S

/-- A B_h subset is **maximal** if no element of `{1,…,N}` can be added while
    preserving the B_h property. -/
def IsMaximalBhSet (N h : ℕ) (S : Finset ℕ) : Prop :=
  IsBhSubset N h S ∧
  ∀ x ∈ Interval N, x ∉ S → ¬ IsBhSet h (insert x S)

open Classical in
/-- `Aₕ(N, h)` = number of maximal B_h subsets of `{1,…,N}`.
    For `h = 2` this is the parent's `A₁(N)`. -/
noncomputable def Aₕ (N h : ℕ) : ℕ :=
  ((Interval N).powerset.filter (fun S => IsMaximalBhSet N h S)).card

/-! ## Part II — Structural lemmas (verified, axiom-free) -/

/-- **Hereditary.** A subset of a B_h set is a B_h set: shrinking can only
    remove `h`-subsets, never create a sum collision. -/
theorem bhSet_subset {h : ℕ} {S T : Finset ℕ}
    (hS : IsBhSet h S) (hTS : T ⊆ S) : IsBhSet h T := by
  obtain ⟨hh, hsum⟩ := hS
  refine ⟨hh, fun T₁ T₂ h₁ h₂ hc₁ hc₂ he => ?_⟩
  exact hsum T₁ T₂ (h₁.trans hTS) (h₂.trans hTS) hc₁ hc₂ he

/-- Any set with at most `h` elements is automatically a B_h set: there is at
    most one `h`-element subset (the whole set, if `|S| = h`), so no two
    distinct `h`-subsets exist to collide. -/
theorem bhSet_of_card_le {h : ℕ} {S : Finset ℕ}
    (hh : 2 ≤ h) (hcard : S.card ≤ h) : IsBhSet h S := by
  refine ⟨hh, fun T₁ T₂ h₁ h₂ hc₁ hc₂ _ => ?_⟩
  have e₁ : T₁ = S := Finset.eq_of_subset_of_card_le h₁ (by omega)
  have e₂ : T₂ = S := Finset.eq_of_subset_of_card_le h₂ (by omega)
  rw [e₁, e₂]

/-- The empty set is a B_h set for every `h ≥ 2`. -/
theorem bhSet_empty {h : ℕ} (hh : 2 ≤ h) : IsBhSet h (∅ : Finset ℕ) :=
  bhSet_of_card_le hh (by simp)

/-- Every singleton is a B_h set for every `h ≥ 2`. -/
theorem bhSet_singleton {h : ℕ} (hh : 2 ≤ h) (a : ℕ) :
    IsBhSet h ({a} : Finset ℕ) :=
  bhSet_of_card_le hh (by rw [Finset.card_singleton]; omega)

/-- **Bridge to the parent #862.** The Sidon (B₂) condition of the parent
    entry implies the `IsBhSet 2` condition used here, so this B_h framework
    genuinely generalizes maximal-Sidon counting. -/
theorem sidon_imp_b2 {S : Finset ℕ} (hS : IsSidonSet S) : IsBhSet 2 S := by
  refine ⟨le_refl 2, fun T₁ T₂ h₁ h₂ hc₁ hc₂ he => ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc₁
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hc₂
  have ha : a ∈ S := h₁ (by simp)
  have hb : b ∈ S := h₁ (by simp)
  have hc : c ∈ S := h₂ (by simp)
  have hd : d ∈ S := h₂ (by simp)
  rw [Finset.sum_pair hab, Finset.sum_pair hcd] at he
  exact hS a b c d ha hb hc hd he

/-- `0` is never a member of the ambient interval `{1,…,N}`. -/
theorem zero_notMem_interval (N : ℕ) : (0 : ℕ) ∉ Interval N := by
  simp [Interval]

/-- **Ambient size.** The interval `{1,…,N}` has exactly `N` elements.  This
    pins down the size of the ground set over which maximal B_h subsets are
    counted, so `Aₕ(N,h)` is a count of subsets of an `N`-element set. -/
theorem interval_card (N : ℕ) : (Interval N).card = N := by
  have hIcc : Interval N = Finset.Icc 1 N := by
    ext x
    simp only [Interval, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  rw [hIcc, Nat.card_Icc]
  omega

/-! ## Part III — Existence of maximal B_h sets and well-definedness of `Aₕ` -/

/-- **Existence.** For every `N` and every `h ≥ 2`, a maximal B_h subset of
    `{1,…,N}` exists.  Proof: among all B_h subsets of `[N]` (a nonempty finite
    family, since `∅` qualifies) take one of maximum cardinality; it cannot be
    extended, because any extension would be a larger B_h subset.  This is the
    finite, fully constructive analogue of the Zorn's-lemma step used in the
    parent #862 counting argument. -/
theorem exists_maximal_bhSet (N h : ℕ) (hh : 2 ≤ h) :
    ∃ S, IsMaximalBhSet N h S := by
  classical
  set 𝒮 := (Interval N).powerset.filter (fun S => IsBhSet h S) with h𝒮
  have hne : 𝒮.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, bhSet_empty hh⟩
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image 𝒮 Finset.card hne
  rw [h𝒮, Finset.mem_filter, Finset.mem_powerset] at hSmem
  obtain ⟨hSsub, hSbh⟩ := hSmem
  refine ⟨S, ⟨hSsub, hSbh⟩, fun x hxI hxS hcontra => ?_⟩
  have hins_mem : insert x S ∈ 𝒮 := by
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hxI hSsub, hcontra⟩
  have hle := hSmax (insert x S) hins_mem
  rw [Finset.card_insert_of_notMem hxS] at hle
  omega

/-- **`Aₕ` is well-defined and positive.** Since a maximal B_h subset always
    exists, the count `Aₕ(N, h)` is at least `1` for every `h ≥ 2`. -/
theorem Aₕ_pos (N h : ℕ) (hh : 2 ≤ h) : 1 ≤ Aₕ N h := by
  classical
  obtain ⟨S, hS⟩ := exists_maximal_bhSet N h hh
  rw [Aₕ]
  refine Finset.Nonempty.card_pos ⟨S, ?_⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS.1.1, hS⟩

/-! ## Part IV — The open question (stated, not proved) -/

/-- The OPEN growth question for maximal B_h sets, `h ≥ 3`: does the number of
    maximal B_h subsets of `{1,…,N}` grow exponentially in some power of `N`?

    This is a *statement*, deliberately left unproven — it is open in the
    literature.  The parent `h = 2` case is the Saxton–Thomason theorem
    (`Aₕ(N,2) ≥ 2^{(0.16+o(1))√N}`); for `h ≥ 3` no analogous bound is known. -/
def MaximalBhCountingQuestion (h : ℕ) : Prop :=
  ∃ α > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (Aₕ N h : ℝ) ≥ 2 ^ (α * (N : ℝ) ^ (1 / (h + 1 : ℝ)))

/-- Companion framing: the well-definedness results above show the counting
    function is a genuine object — for every `h ≥ 2` and every `N`, `Aₕ N h`
    is a positive integer — so `MaximalBhCountingQuestion h` asks a meaningful
    question about an honestly-defined quantity. -/
theorem maximal_bh_counting_well_posed (h : ℕ) (hh : 2 ≤ h) :
    ∀ N : ℕ, 1 ≤ Aₕ N h := fun N => Aₕ_pos N h hh

end Erdos862OQ03
