import Mathlib
import Proofs.UrysohnsLemmaOQ01OQ01OQ01

/-!
# The Norm-Preserving Tietze Extension from the Explicit Urysohn Series

The grandparent entry (`urysohns-lemma-oq-01-oq-01`) isolates the *engine* of the
classical Tietze proof, and the parent entry (`urysohns-lemma-oq-01-oq-01-oq-01`)
assembles the extension **by hand** as a genuinely convergent series

    G  =  ∑' n, gₙ          in the Banach space  BoundedContinuousFunction X ℝ

proving `G = f` on the closed set `s` and the sup-bound `‖G‖ ≤ M` for any bound
`M` on the data.  That bound is not yet sharp: it controls `G` by whatever ambient
`M` was supplied, not by `f` itself.

This entry tracks the sup-norm through the series to recover the **sharp,
norm-preserving** Tietze form

    ‖G‖ = ‖f‖

directly from the explicit construction.  The mechanism is the partial-sum bound
`partialSum_norm_le`: every partial sum `∑_{i<n} gᵢ` of the correction series has
sup-norm `≤ M`, because the geometric majorant `∑ (2/3)ⁱ·(M/3)` sums to exactly `M`.
Specialising `M` to the actual sup-norm `‖f‖` of the data turns the parent's
`‖G‖ ≤ M` into `‖G‖ ≤ ‖f‖`; the reverse inequality `‖f‖ ≤ ‖G‖` is automatic because
`G` extends `f` (any extension is at least as large in sup-norm as the function it
extends).  Antisymmetry gives the equality.

## Main results

* `TietzeTsum.partialSum_norm_le` — every partial sum of the correction series stays
  within the data bound: `‖∑_{i<n} gᵢ‖ ≤ M`.
* `tietze_extension_norm_preserving` — for a bounded continuous `f` on a closed set
  `s` in a normal space, there is a bounded continuous `G` on `X`, equal to the
  explicit Urysohn series, with `G = f` on `s` and `‖G‖ = ‖f‖`.

Everything is machine-checked with no `sorry`, building only on the parent's explicit
series and never on Mathlib's `TietzeExtension` machinery.
-/

open Set Function Filter Topology

namespace TietzeTsum

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] {s : Set X}
  (hs : IsClosed s) (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, |f x| ≤ M)

/-- **Tracking the sup-norm of the partial sums.** Every finite partial sum of the
correction series stays inside the data bound `[-M, M]`: `‖∑_{i<n} gᵢ‖ ≤ M`. This is the
norm-level shadow of the residual recursion — the partial sums never overshoot the bound
that the residual is decaying inside. The proof bounds the partial sum by the head of the
geometric majorant `∑_{i<n} (2/3)ⁱ·(M/3)`, which is dominated by the full sum `M`. -/
lemma partialSum_norm_le (n : ℕ) :
    ‖∑ i ∈ Finset.range n, gbcf hs f hM hf i‖ ≤ M := by
  calc
    ‖∑ i ∈ Finset.range n, gbcf hs f hM hf i‖
        ≤ ∑ i ∈ Finset.range n, ‖gbcf hs f hM hf i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, (2 / 3 : ℝ) ^ i * (M / 3) :=
          Finset.sum_le_sum (fun i _ => gbcf_norm_le hs f hM hf i)
    _ ≤ ∑' i, (2 / 3 : ℝ) ^ i * (M / 3) :=
          Summable.sum_le_tsum _ (fun i _ => by positivity) (summable_geo (M := M))
    _ = M := by
          have hr : (1 - 2 / 3 : ℝ)⁻¹ = 3 := by norm_num
          rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3)
            (by norm_num : (2 / 3 : ℝ) < 1), hr]
          ring

end TietzeTsum

/-- **Norm-preserving Tietze extension theorem, from the explicit Urysohn series.**

For a closed set `s` in a normal space `X` and a *bounded* continuous `f : s →ᵇ ℝ`, the
explicit correction series `G = ∑' n, gₙ` of the parent entry — built entirely from
Urysohn's lemma, with no appeal to Mathlib's `TietzeExtension` machinery — is a bounded
continuous extension of `f` to all of `X` whose sup-norm exactly matches that of the data:

    ‖G‖ = ‖f‖.

This is the sharp form of the bounded Tietze extension: the extension is no larger than the
function it extends. The `≤` direction is the parent's bound `‖G‖ ≤ M` specialised to the
sharp bound `M = ‖f‖`; the `≥` direction holds because `G` agrees with `f` on `s`, so every
value of `f` is a value of `G`. -/
theorem tietze_extension_norm_preserving {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) (f : BoundedContinuousFunction s ℝ) :
    ∃ G : BoundedContinuousFunction X ℝ,
      (∀ x : s, G (x : X) = f x) ∧ ‖G‖ = ‖f‖ := by
  -- Specialise the parent's explicit series to the sharp bound `M = ‖f‖`.
  have hM : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hf : ∀ x : s, |f.toContinuousMap x| ≤ ‖f‖ := by
    intro x
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  obtain ⟨G, hGeq, _, hGle⟩ :=
    tietze_extension_via_tsum hs f.toContinuousMap hM hf
  refine ⟨G, hGeq, le_antisymm ?_ ?_⟩
  · -- `‖G‖ ≤ ‖f‖`: the parent's sharp bound, since `|G y| ≤ ‖f‖` everywhere.
    refine (BoundedContinuousFunction.norm_le hM).2 (fun y => ?_)
    simpa [Real.norm_eq_abs] using hGle y
  · -- `‖f‖ ≤ ‖G‖`: `G` extends `f`, so each `|f x| = |G x| ≤ ‖G‖`.
    refine (BoundedContinuousFunction.norm_le (norm_nonneg G)).2 (fun x => ?_)
    have hx : f x = G (x : X) := (hGeq x).symm
    rw [hx]
    exact G.norm_coe_le_norm (x : X)
