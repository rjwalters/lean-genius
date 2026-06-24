import Mathlib
import Proofs.UrysohnsLemmaOQ01OQ01OQ01

/-
# The Norm-Preserving (Sharp) Tietze Extension  (urysohns-lemma-oq-01-oq-01-oq-01-oq-01)

The parent entry **urysohns-lemma-oq-01-oq-01-oq-01** builds the Tietze extension of a
bounded continuous `f` on a closed set `s ⊆ X` (`X` normal) as an explicit, absolutely
convergent series of Urysohn corrections `G = ∑' n, gₙ`, and proves the *sup-bound*
`|G| ≤ M` for any bound `M` with `|f| ≤ M` (`tietze_extension_via_tsum`).

Its declared open question asks to **sharpen the bound to an equality**:

  `‖G‖ = ‖f‖`,

recovering the standard *norm-preserving* form of the Tietze theorem directly from the
construction.  This entry settles it.

## Method

Two halves, each elementary once the parent's construction is in hand.

* **Upper bound `‖G‖ ≤ ‖f‖`.** Instantiate the parent's free bound `M` at the *exact*
  sup-norm `M = ‖f‖` (legitimate because `|f x| = ‖f x‖ ≤ ‖f‖` for a bounded continuous
  `f`).  The parent then delivers `|G y| ≤ ‖f‖` for every `y`, i.e. `‖G‖ ≤ ‖f‖`.

* **Lower bound `‖f‖ ≤ ‖G‖`.** This half needs *nothing* about the construction: it holds
  for **every** extension `E` of `f` (`norm_ge_of_extends`).  Indeed for `x ∈ s` we have
  `‖f x‖ = ‖E x‖ ≤ ‖E‖`, and taking the supremum over `s` gives `‖f‖ ≤ ‖E‖`.  So `‖f‖`
  is a *universal lower bound* on the norm of any extension, and our `G` attains it — `G`
  is a **norm-minimal** extension.

Combining the two halves gives the sharp equality `‖G‖ = ‖f‖`.  Because the lower bound is
universal, the result also says the parent's series construction is optimal: no continuous
extension can have smaller sup-norm than `f` itself.
-/

open scoped BoundedContinuousFunction

namespace UrysohnsLemmaOQ01OQ01OQ01OQ01

variable {X : Type*} [TopologicalSpace X]

/-- **Universal lower bound on extensions.** Any bounded continuous `E : X →ᵇ ℝ` that
restricts to `f` on `s` has norm at least `‖f‖`. No normality or construction is needed —
this is just "the sup over `X` dominates the sup over `s`". -/
theorem norm_ge_of_extends {s : Set X} (f : BoundedContinuousFunction s ℝ)
    (E : BoundedContinuousFunction X ℝ) (hE : ∀ x : s, E (x : X) = f x) :
    ‖f‖ ≤ ‖E‖ := by
  refine (BoundedContinuousFunction.norm_le (norm_nonneg E)).2 (fun x => ?_)
  calc ‖f x‖ = ‖E (x : X)‖ := by rw [hE x]
    _ ≤ ‖E‖ := E.norm_coe_le_norm (x : X)

variable [NormalSpace X]

/-- **The norm-preserving (sharp) Tietze extension.**

For a closed set `s` in a normal space `X` and a bounded continuous `f : s →ᵇ ℝ`, the
explicit-series extension `G` of the parent entry can be taken with the *same norm*:
`‖G‖ = ‖f‖`. The upper bound comes from instantiating the parent's construction at the
exact sup-norm `M = ‖f‖`; the lower bound is the universal `norm_ge_of_extends`. -/
theorem tietze_norm_preserving {s : Set X} (hs : IsClosed s)
    (f : BoundedContinuousFunction s ℝ) :
    ∃ G : BoundedContinuousFunction X ℝ,
      (∀ x : s, G (x : X) = f x) ∧ ‖G‖ = ‖f‖ := by
  -- Run the parent's series construction with the *sharp* bound `M = ‖f‖`.
  obtain ⟨G, hext, _hGeq, hbound⟩ :=
    tietze_extension_via_tsum hs f.toContinuousMap (norm_nonneg f)
      (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
  have hext' : ∀ x : s, G (x : X) = f x := fun x => by simpa using hext x
  refine ⟨G, hext', le_antisymm ?_ (norm_ge_of_extends f G hext')⟩
  -- `‖G‖ ≤ ‖f‖`: every value of `G` is bounded by `‖f‖` (the parent's `hbound`).
  refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (fun y => ?_)
  simpa [Real.norm_eq_abs] using hbound y

/-- **Restatement: the construction is norm-minimal.** The norm of the parent's extension
equals the smallest norm achievable by *any* continuous extension of `f`, namely `‖f‖`. -/
theorem exists_minimal_norm_extension {s : Set X} (hs : IsClosed s)
    (f : BoundedContinuousFunction s ℝ) :
    ∃ G : BoundedContinuousFunction X ℝ,
      (∀ x : s, G (x : X) = f x) ∧
      ∀ E : BoundedContinuousFunction X ℝ, (∀ x : s, E (x : X) = f x) → ‖G‖ ≤ ‖E‖ := by
  obtain ⟨G, hext, hnorm⟩ := tietze_norm_preserving hs f
  exact ⟨G, hext, fun E hE => hnorm.le.trans (norm_ge_of_extends f E hE)⟩

end UrysohnsLemmaOQ01OQ01OQ01OQ01
