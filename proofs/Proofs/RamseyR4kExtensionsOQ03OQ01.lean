/-
  Lovász Local Lemma and Ramsey Lower Bounds — the bad-event probability
  (ramsey-r4k-extensions-oq-03-oq-01)

  The symmetric Lovász Local Lemma (LLL) feasibility test for Spencer's improved
  diagonal Ramsey lower bound is `e · p · (d + 1) ≤ 1`, where

    * `p` is the probability that a fixed k-clique is monochromatic under a
      uniformly random 2-colouring of the edges of Kₙ, and
    * `d` is the LLL dependency degree of the monochromatic-clique events.

  The companion file `RamseyR4kExtensionsOQ03.lean` (Key Lemma 3) supplies the
  dependency-degree bound `d + 1 ≤ C(k,2)·C(n-2,k-2)`, entirely by finite
  counting.  **This file supplies the other input — Key Lemma 2, the bad-event
  probability** — again with no probability theory at all, purely by counting
  colourings.

  A k-clique has exactly `C(k,2)` edges.  Colouring each edge with one of two
  colours gives `2^{C(k,2)}` equally likely colourings, of which exactly **two**
  are monochromatic (all-red and all-blue).  Hence

        p  =  #{monochromatic colourings} / #{all colourings}
           =  2 / 2^{C(k,2)}
           =  2^{1 - C(k,2)}.

  The combinatorial heart is a clean finite fact, stated abstractly over the
  edge set: among all `Bool`-colourings of a nonempty finite type, exactly two
  are constant.  Everything here is machine-checked with no `sorry`, no `axiom`,
  and no `native_decide`.

  References:
  - P. Erdős, L. Lovász (1975), "Problems and results on 3-chromatic
    hypergraphs and some related questions."
  - J. Spencer (1975), "Ramsey's theorem — a new lower bound," JCTA.
  - N. Alon, J. Spencer, *The Probabilistic Method*, Ch. 5.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace RamseyLLL

open Finset

/-! ### The abstract counting core: exactly two constant `Bool`-colourings -/

/-- **Constant-colouring count.**  Among all `Bool`-valued colourings of a
    nonempty finite type `α`, exactly two are *constant* (monochromatic): the
    all-`true` colouring and the all-`false` colouring.  A colouring `c` is
    constant iff `c = fun _ => c x₀` for any fixed `x₀`, so the constant
    colourings are the image of `Bool` under `b ↦ (fun _ => b)`, an injection
    (because `α` is nonempty). -/
theorem card_constant_colorings (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] :
    ((univ : Finset (α → Bool)).filter (fun c => ∀ x y, c x = c y)).card = 2 := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hset :
      ((univ : Finset (α → Bool)).filter (fun c => ∀ x y, c x = c y))
        = (univ : Finset Bool).image (fun b => (fun _ : α => b)) := by
    ext c
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · intro hc
      exact ⟨c x₀, funext fun x => (hc x x₀).symm⟩
    · rintro ⟨b, rfl⟩
      intro x y; rfl
  have hinj : Function.Injective (fun b : Bool => (fun _ : α => b)) := by
    intro b1 b2 hb
    simpa using congrFun hb x₀
  rw [hset, Finset.card_image_of_injective (univ : Finset Bool) hinj]
  simp

/-! ### Instantiation for the edges of a k-clique -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge set of the k-clique on vertex set `S`: the 2-element subsets of `S`.
    A k-clique has `C(k,2)` edges (`cliqueEdges_card`). -/
def cliqueEdges (S : Finset V) : Finset (Finset V) := S.powersetCard 2

/-- A k-clique has exactly `C(k,2)` edges. -/
theorem cliqueEdges_card (k : ℕ) (S : Finset V) (hS : S.card = k) :
    (cliqueEdges S).card = k.choose 2 := by
  rw [cliqueEdges, Finset.card_powersetCard, hS]

/-- The type of 2-colourings of the edges of the k-clique `S`: a `Bool` for each
    edge.  There are `2^{C(k,2)}` of them (`card_edgeColorings`). -/
abbrev EdgeColoring (S : Finset V) : Type _ := {e : Finset V // e ∈ cliqueEdges S} → Bool

/-- **Total colourings.**  The number of 2-colourings of a k-clique's edges is
    `2^{C(k,2)}` — two colour choices independently on each of the `C(k,2)`
    edges. -/
theorem card_edgeColorings (k : ℕ) (S : Finset V) (hS : S.card = k) :
    Fintype.card (EdgeColoring S) = 2 ^ k.choose 2 := by
  simp only [EdgeColoring, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rw [cliqueEdges_card k S hS]

/-- **Monochromatic-colouring count (main result).**  Exactly two of the
    `2^{C(k,2)}` edge-colourings of a k-clique are monochromatic: the all-red and
    the all-blue colourings.  This is Key Lemma 2 — the numerator of the bad-event
    probability `p = 2 / 2^{C(k,2)}` that feeds the symmetric LLL feasibility test.
    Requires `k ≥ 2` so that the clique actually has an edge. -/
theorem card_monochromatic_edgeColorings (k : ℕ) (hk : 2 ≤ k) (S : Finset V)
    (hS : S.card = k) :
    ((univ : Finset (EdgeColoring S)).filter (fun c => ∀ x y, c x = c y)).card = 2 := by
  have hne : (cliqueEdges S).Nonempty := by
    rw [cliqueEdges, Finset.powersetCard_nonempty, hS]; exact hk
  have : Nonempty {e : Finset V // e ∈ cliqueEdges S} := by
    obtain ⟨e, he⟩ := hne; exact ⟨⟨e, he⟩⟩
  exact card_constant_colorings {e : Finset V // e ∈ cliqueEdges S}

/-! ### The bad-event probability -/

/-- **Bad-event probability (p).**  The probability that a fixed k-clique is
    monochromatic under the uniform random 2-colouring equals `2^{1 - C(k,2)}`.
    Computed as `#monochromatic / #total = 2 / 2^{C(k,2)}`, using the two counts
    above.  This is the value of `p` plugged into the symmetric LLL condition
    `e · p · (d + 1) ≤ 1`; together with the dependency-degree bound
    `d + 1 ≤ C(k,2)·C(n-2,k-2)` from Key Lemma 3 it gives the full feasibility
    input for Spencer's improved Ramsey lower bound. -/
theorem clique_monochromatic_probability (k : ℕ) (hk : 2 ≤ k) (S : Finset V)
    (hS : S.card = k) :
    (((univ : Finset (EdgeColoring S)).filter (fun c => ∀ x y, c x = c y)).card : ℝ)
        / (Fintype.card (EdgeColoring S) : ℝ)
      = (2 : ℝ) ^ (1 - (k.choose 2 : ℤ)) := by
  rw [card_monochromatic_edgeColorings k hk S hS, card_edgeColorings k S hS]
  rw [zpow_sub₀ (two_ne_zero), zpow_one, zpow_natCast]
  norm_num

/-- **Sanity check (k = 3).**  A triangle has `C(3,2) = 3` edges, hence
    `2^3 = 8` colourings, of which exactly `2` are monochromatic — the classical
    per-triangle monochromaticity probability `2/8 = 1/4 = 2^{1-3}`. -/
theorem triangle_monochromatic_count (S : Finset V) (hS : S.card = 3) :
    ((univ : Finset (EdgeColoring S)).filter (fun c => ∀ x y, c x = c y)).card = 2
      ∧ Fintype.card (EdgeColoring S) = 8 := by
  refine ⟨card_monochromatic_edgeColorings 3 (by norm_num) S hS, ?_⟩
  rw [card_edgeColorings 3 S hS]; decide

end RamseyLLL
