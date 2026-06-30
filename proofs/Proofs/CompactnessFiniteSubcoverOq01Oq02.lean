import Mathlib

/-
# The Finite-Intersection Dual and Cantor's Intersection Theorem

## What This Proves

This file answers the **second** open question recorded on the parent entry
*"Compactness via Finite Subcovers: the Heine–Borel Characterization"*:

> Prove the finite-intersection-property dual and Cantor's intersection theorem
> for nested compacts.

The parent's headline is the open-cover characterization of compactness
(`every open cover admits a finite subcover`).  Taking complements turns covers
into families of closed sets, and the statement dualises to the **finite
intersection property (FIP)**:

> a set is compact **iff** every family of closed sets, every finite subfamily
> of which meets the set, has its *whole* intersection meeting the set.

The headline result here is that FIP characterisation, and its main payoff is
**Cantor's intersection theorem**: a decreasing sequence of nonempty closed
subsets of a compact set has nonempty intersection.

* `compact_iff_finite_subfamily_closed` — the FIP characterisation, recorded as
  the closed-set dual of the parent's `compact_iff_finite_subcover`
  (a `Mathlib` re-export of `isCompact_iff_finite_subfamily_closed`).
* `compact_inter_iInter_nonempty` — the everyday nonempty form: to meet the
  intersection of a closed family it suffices to meet every *finite* subfamily
  (`Mathlib`'s `IsCompact.inter_iInter_nonempty`, recorded as the FIP dual).
* `cantor_inter_of_isCompact` — **Cantor's intersection theorem** for a compact
  ambient set, proved **by hand** from the FIP dual: every finite subfamily of a
  decreasing sequence is pinned below by its largest-index term, which is a
  nonempty subset of the compact set, so the finite intersection property holds
  and the full intersection is nonempty.
* `cantor_inter` — the `[CompactSpace X]` corollary.
* a concrete `ℝ` instance: the nested intervals `[0, 1/(n+1)]`.

## Why This Is a Non-Wrapper

`Mathlib` already carries `nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`,
its ready-made Cantor theorem.  That lemma is **never invoked**.  Instead Cantor
is rebuilt from the finite-intersection dual exactly as the parent rebuilds
compactness consequences from the finite-subcover characterization: the genuine
content is the antitone bookkeeping that shows every finite subfamily intersection
contains the largest-index term, which is nonempty.  That hand derivation, the
`CompactSpace` corollary, and the concrete nested-interval instance are the
mathematical substance; the two FIP statements are recorded as the explicit
closed-set dual of the parent's open-cover headline.
-/

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ## The finite-intersection-property dual of compactness -/

/-- **The finite-intersection characterisation of compactness.**  A set `s` is
compact iff, for every family of closed sets whose total intersection avoids `s`,
already some *finite* subfamily intersection avoids `s`.  This is the closed-set
dual of the parent entry's `compact_iff_finite_subcover`, obtained by
complementing covers into closed families (`Mathlib`'s
`isCompact_iff_finite_subfamily_closed`). -/
theorem compact_iff_finite_subfamily_closed {s : Set X} :
    IsCompact s ↔ ∀ {ι : Type u} (t : ι → Set X),
      (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
        ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  isCompact_iff_finite_subfamily_closed

/-- **The finite-intersection property (nonempty form).**  To meet the
intersection of a family of closed sets, a compact set need only meet every
*finite* subfamily.  This is the form Cantor's theorem is built from; it is
`Mathlib`'s `IsCompact.inter_iInter_nonempty`, recorded as the FIP dual. -/
theorem compact_inter_iInter_nonempty {ι : Type*} {s : Set X} (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i))
    (hfip : ∀ v : Finset ι, (s ∩ ⋂ i ∈ v, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty :=
  hs.inter_iInter_nonempty t htc hfip

/-! ## Cantor's intersection theorem, re-derived from the FIP dual -/

/-- **Cantor's intersection theorem (compact-set form).**  A decreasing sequence
of nonempty closed subsets of a compact set `s` has nonempty intersection.

Proved by hand from the finite-intersection dual `compact_inter_iInter_nonempty`,
not from `Mathlib`'s ready-made `nonempty_iInter_of_sequence_…`.  The content is
the antitone bookkeeping: for a finite set `v` of indices, every term `t i`
(`i ∈ v`) contains the largest-index term `t (v.max')`, so
`⋂_{i ∈ v} t i ⊇ t (v.max')`, which is a nonempty subset of `s`.  Hence every
finite subfamily meets `s`, and the FIP dual returns a point in `s ∩ ⋂ t`; since
`⋂ t ⊆ t 0 ⊆ s`, that point lies in `⋂ t`. -/
theorem cantor_inter_of_isCompact {s : Set X} (hs : IsCompact s) (t : ℕ → Set X)
    (hsub : ∀ n, t n ⊆ s) (hanti : Antitone t) (hcl : ∀ n, IsClosed (t n))
    (hne : ∀ n, (t n).Nonempty) : (⋂ n, t n).Nonempty := by
  -- Every finite subfamily already meets `s`.
  have key : ∀ v : Finset ℕ, (s ∩ ⋂ i ∈ v, t i).Nonempty := by
    intro v
    rcases v.eq_empty_or_nonempty with rfl | hv
    · simpa using (hne 0).mono (hsub 0)
    · refine (hne (v.max' hv)).mono ?_
      refine subset_inter (hsub _) (subset_iInter₂ fun i hi => ?_)
      exact hanti (v.le_max' i hi)
  -- The FIP dual yields a point of `s ∩ ⋂ t`; as `⋂ t ⊆ s`, it lies in `⋂ t`.
  have hmeet := compact_inter_iInter_nonempty hs t hcl key
  rwa [inter_eq_right.mpr ((iInter_subset t 0).trans (hsub 0))] at hmeet

/-- **Cantor's intersection theorem (compact-space form).**  In a compact space, a
decreasing sequence of nonempty closed sets has nonempty intersection. -/
theorem cantor_inter [CompactSpace X] (t : ℕ → Set X) (hanti : Antitone t)
    (hcl : ∀ n, IsClosed (t n)) (hne : ∀ n, (t n).Nonempty) :
    (⋂ n, t n).Nonempty :=
  cantor_inter_of_isCompact isCompact_univ t (fun _ => subset_univ _) hanti hcl hne

/-! ## A concrete instance over `ℝ` -/

/-- **Concrete Cantor instance over `ℝ`.**  The nested closed intervals
`[0, 1/(n+1)]` form a decreasing sequence of nonempty compacts, so their
intersection is nonempty (it is in fact `{0}`). -/
example : (⋂ n : ℕ, Set.Icc (0 : ℝ) (1 / (n + 1))).Nonempty := by
  have hanti : Antitone (fun n : ℕ => Set.Icc (0 : ℝ) (1 / (n + 1))) := by
    intro n m hnm
    refine Set.Icc_subset_Icc_right ?_
    gcongr
  refine cantor_inter_of_isCompact (s := Set.Icc (0 : ℝ) 1) isCompact_Icc
    (fun n => Set.Icc (0 : ℝ) (1 / (n + 1))) (fun n => ?_) hanti
    (fun _ => isClosed_Icc) (fun n => ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, by positivity⟩⟩)
  refine Set.Icc_subset_Icc_right ?_
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
