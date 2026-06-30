import Mathlib

/-
# The descent-complementing involution and bijective Eulerian palindromy

The grandparent **geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02-oq-01** introduced the
permutation descent statistic

  `descentCount σ = |{i : Fin n | σ (i.succ) < σ (i.castSucc)}|`     (σ : Equiv.Perm (Fin (n+1)))

and proved the **left border** `k = 0` of the still-open bijection
`|{σ : descentCount σ = k}| = ⟨n+1,k⟩` (`descentCount σ = 0 ↔ σ = 1`). The sibling
**…-oq-02-oq-01-oq-01** proved the **right border** `k = n` (`descentCount σ = n ↔ σ = Fin.revPerm`):
the increasing and decreasing permutations are the unique extremes. Both borders give cardinality
`1 = ⟨n+1,0⟩ = ⟨n+1,n⟩`.

This entry proves the **symmetry that unifies the two borders and every interior column**: the
*descent-complementing involution*

  `Φ(σ) = Fin.revPerm * σ`,    i.e. `(Φ σ) i = (σ i).rev`   (reverse every **value**),

satisfies

  `descentCount_complement` :  `descentCount (Fin.revPerm * σ) = n − descentCount σ`,

and is its own inverse (`Fin.revPerm` is an involution). Hence `Φ` is an explicit bijection between
the descent classes `{σ : descentCount σ = k}` and `{σ : descentCount σ = n−k}`, giving the
**permutation-level palindromy**

  `card_descentClass_palindrome` :  `|{σ : descentCount σ = k}| = |{σ : descentCount σ = n−k}|`   (k ≤ n).

The sibling **…-oq-02-oq-02** already proves the *algebraic* palindromy `⟨n+1,k⟩ = ⟨n+1,n−k⟩` of the
Eulerian numbers from the closed alternating-sum form. This entry instead provides the
**bijective** explanation — an honest involution on permutations whose action on descent counts is
the reflection `k ↦ n−k`. Specialized to the borders it collapses to a single statement
unifying the two sibling entries:

  `card_descentFree_eq_card_descentMax` :  `|{descentCount = 0}| = |{descentCount = n}|`.

## Method

Reversing every value (`σ i ↦ (σ i).rev`) turns each adjacent comparison into its opposite, because
`Fin.rev` is strictly antitone (`Fin.rev_lt_rev`): position `i` is a descent of `Φ σ` exactly when
it is an *ascent* of `σ`. Since `σ` is injective the two strict inequalities are exhaustive on each
of the `n` adjacent positions, so the descent set of `Φ σ` is the set-complement (inside
`univ : Finset (Fin n)`) of the descent set of `σ`; taking cardinalities gives `n − descentCount σ`
(`Finset.filter_not`, `Finset.card_sdiff`). The map `Φ` is left-multiplication by `Fin.revPerm`,
hence injective (`mul_left_cancel`); its square is the identity (`Fin.rev_rev`), so the image of
`{descentCount = k}` under `Φ` is exactly `{descentCount = n−k}` and the two finsets have equal
cardinality (`Finset.card_image_of_injective`).

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free. The
descent statistic is re-declared locally; only the parent Eulerian-number development is imported.
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01OQ01OQ01

open Equiv Finset

/-! ## The descent statistic (re-declared) -/

/-- The **descent count** of a permutation `σ` of `Fin (n+1)`: the number of positions
`i : Fin n` at which `σ` falls, `σ (i.succ) < σ (i.castSucc)`. -/
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : ℕ :=
  (univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc)).card

/-! ## The descent-complementing involution `Φ σ = Fin.revPerm * σ` -/

/-- **Value-reversal complements descents.** Reversing every value of `σ` (left-multiplying by
`Fin.revPerm`) sends a permutation with `d` descents to one with `n − d` descents: each adjacent
position that was an ascent becomes a descent and vice versa, and there are `n` positions in all. -/
theorem descentCount_complement {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    descentCount (Fin.revPerm * σ) = n - descentCount σ := by
  -- The descent set of `Fin.revPerm * σ` is the complement of the descent set of `σ`.
  have hfilter : descentCount (Fin.revPerm * σ)
      = (univ.filter (fun i : Fin n => ¬ (σ i.succ < σ i.castSucc))).card := by
    unfold descentCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    -- `(Fin.revPerm * σ) j = (σ j).rev`, and `Fin.rev` is strictly antitone.
    show ((σ i.succ).rev < (σ i.castSucc).rev) ↔ ¬ (σ i.succ < σ i.castSucc)
    rw [Fin.rev_lt_rev]
    constructor
    · intro h
      exact not_lt.mpr h.le
    · intro h
      rcases lt_trichotomy (σ i.castSucc) (σ i.succ) with hlt | heq | hgt
      · exact hlt
      · exact absurd (σ.injective heq) (Fin.castSucc_lt_succ (i := i)).ne
      · exact absurd hgt h
  rw [hfilter]
  unfold descentCount
  rw [Finset.filter_not, Finset.card_univ_diff, Fintype.card_fin]

/-- `Fin.revPerm` is an involution: reversing values twice is the identity. -/
theorem revPerm_mul_self {n : ℕ} :
    (Fin.revPerm : Equiv.Perm (Fin (n + 1))) * Fin.revPerm = 1 := by
  refine Equiv.ext (fun i => ?_)
  show (i.rev).rev = i
  exact Fin.rev_rev i

/-! ## Bijective Eulerian palindromy at the permutation level -/

/-- **Permutation-level palindromy of the descent statistic.** For every `k ≤ n` the descent class
with `k` descents and the class with `n − k` descents have the same cardinality, exhibited by the
explicit descent-complementing involution `σ ↦ Fin.revPerm * σ`. This is the bijective counterpart
of the algebraic Eulerian palindromy `⟨n+1,k⟩ = ⟨n+1,n−k⟩` proved by the sibling …-oq-02-oq-02. -/
theorem card_descentClass_palindrome {n k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = k)).card
      = (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = n - k)).card := by
  -- `Φ = (Fin.revPerm * ·)` is injective and carries `{= n−k}` onto `{= k}`.
  have hinj : Function.Injective
      (fun σ : Equiv.Perm (Fin (n + 1)) => Fin.revPerm * σ) :=
    fun a b hab => mul_left_cancel hab
  have himg : (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = n - k))
      = (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = k)).image
          (fun σ => Fin.revPerm * σ) := by
    ext τ
    simp only [Finset.mem_image, mem_filter, mem_univ, true_and]
    constructor
    · intro hτ
      refine ⟨Fin.revPerm * τ, ?_, ?_⟩
      · rw [descentCount_complement, hτ]
        omega
      · rw [← mul_assoc, revPerm_mul_self, one_mul]
    · rintro ⟨σ, hσ, rfl⟩
      rw [descentCount_complement, hσ]
  rw [himg, Finset.card_image_of_injective _ hinj]

/-- **The two extreme borders coincide, via one involution.** Specializing the palindromy to `k = 0`
recovers `|{descentCount = 0}| = |{descentCount = n}|`: the increasing and decreasing permutations
are exchanged by value-reversal, unifying the left border (`…-oq-02-oq-01`) and the right border
(`…-oq-02-oq-01-oq-01`) of the Eulerian row. -/
theorem card_descentFree_eq_card_descentMax {n : ℕ} :
    (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = 0)).card
      = (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = n)).card := by
  have h := card_descentClass_palindrome (n := n) (k := 0) (Nat.zero_le n)
  simpa using h

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01OQ01OQ01
