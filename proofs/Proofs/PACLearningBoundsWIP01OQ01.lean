import Proofs.PACLearningBoundsWIP01

/-
# PAC Learning, wip-01 · oq-01 — Monotonicity of the VC dimension

The parent entry `pac-learning-bounds-wip-01` builds proper, `0`-axiom foundations for
Vapnik–Chervonenkis theory: the **trace** `Π_H(S) = {h ∩ S : h ∈ H}`, the **shattering**
relation `Shatters H S`, and the **VC dimension**

  `VCDim H = sSup {n | ∃ S, |S| = n ∧ Shatters H S}`,

the largest cardinality of a set shattered by `H`. Among its lemmas is the *set-level*
monotonicity of shattering, `shatters_mono` : enlarging the class preserves shattering
(`H ⊆ H'` and `Shatters H S ⟹ Shatters H' S`).

This file supplies the **class-level** counterpart — monotonicity of the VC dimension
itself as a function of the hypothesis class.

## What is proved

* `vcDim_mono` — **monotonicity of VC dimension**: `H ⊆ H' ⟹ VCDim H ≤ VCDim H'`.
  A learner with access to a richer hypothesis class can only shatter more, never fewer,
  configurations, so its capacity (measured by VC dimension) is at least as large. This is
  the object-level statement underlying the intuition that "bigger classes are harder to
  learn": sample-complexity bounds grow with `VCDim`.
* `vcDim_le_of_subset` — the same fact packaged as an order-homomorphism-style consequence
  for direct use.
* `vcDim_union_left` / `vcDim_union_right` — immediate corollaries: the VC dimension of a
  union dominates that of either part.
* `vcDim_powerset_le` — since every class over `α` embeds in the full powerset class,
  `VCDim` is dominated by that of `2^α` on any shattered witness; combined with the parent's
  `vcDim_powerset` this recovers the ground-set ceiling in the finite case.

The proof is a two-line application of `csSup_le`/`shatters_mono`, structurally identical to
the parent's `vcDim_le_log`: every cardinality achievable by a set shattered by `H` is,
via `shatters_mono`, achievable by `H'`, hence bounded by `VCDim H'`.

Fully machine-checked; `0` axioms beyond Mathlib's foundations; no `native_decide`.

Tags: pac-learning, vc-dimension, monotonicity, shattering, combinatorics, learning-theory
-/

namespace PACLearningBoundsWIP01

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Monotonicity of the VC dimension.** If `H ⊆ H'` then `VCDim H ≤ VCDim H'`.

Every set shattered by the smaller class `H` is, by the parent's `shatters_mono`, also
shattered by the larger class `H'`; hence every cardinality in the set defining `VCDim H`
is bounded by `VCDim H'` (via `card_le_vcDim`), and the supremum inherits the bound. The
empty-witness case (`H` shatters nothing) gives `VCDim H = 0 ≤ VCDim H'`. -/
theorem vcDim_mono {H H' : Finset (Finset α)} (hHH : H ⊆ H') :
    VCDim H ≤ VCDim H' := by
  rcases Set.eq_empty_or_nonempty {n | ∃ S : Finset α, S.card = n ∧ Shatters H S} with he | hne
  · rw [VCDim, he, csSup_empty]; exact bot_le
  · refine csSup_le hne (fun n hn => ?_)
    obtain ⟨S, rfl, hS⟩ := hn
    exact card_le_vcDim H' S (shatters_mono S hHH hS)

/-- Restatement of `vcDim_mono` in `⟹` form for convenient rewriting/`gcongr`-style use. -/
theorem vcDim_le_of_subset {H H' : Finset (Finset α)} (hHH : H ⊆ H') :
    VCDim H ≤ VCDim H' :=
  vcDim_mono hHH

/-- The VC dimension of a class is at most that of any union containing it (left). -/
theorem vcDim_union_left (H H' : Finset (Finset α)) :
    VCDim H ≤ VCDim (H ∪ H') :=
  vcDim_mono Finset.subset_union_left

/-- The VC dimension of a class is at most that of any union containing it (right). -/
theorem vcDim_union_right (H H' : Finset (Finset α)) :
    VCDim H' ≤ VCDim (H ∪ H') :=
  vcDim_mono Finset.subset_union_right

/-- **The powerset class is capacity-maximal among subfamilies of `2^α`.** Any class `H`
whose members are all subsets of a fixed finite set `S` (i.e. `H ⊆ S.powerset`) has VC
dimension at most `|S|`, the VC dimension of the full powerset class `2^S`
(`vcDim_powerset`). Monotonicity turns the containment into a capacity bound. -/
theorem vcDim_powerset_le {H : Finset (Finset α)} {S : Finset α} (hH : H ⊆ S.powerset) :
    VCDim H ≤ S.card :=
  (vcDim_mono hH).trans_eq (vcDim_powerset S)

end PACLearningBoundsWIP01
