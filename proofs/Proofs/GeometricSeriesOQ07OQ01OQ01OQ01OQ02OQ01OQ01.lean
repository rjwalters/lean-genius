import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

/-
# The maximal-descent rung of the Eulerian bijection

The sibling entry **geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02-oq-01** introduced the
permutation descent statistic

  `descentCount σ = |{i : Fin n | σ (i.succ) < σ (i.castSucc)}|`     (σ : Equiv.Perm (Fin (n+1)))

and proved the **left border** `k = 0` of the still-open bijection
`|{σ : descentCount σ = k}| = ⟨n+1,k⟩`:

  `descentCount σ = 0 ↔ σ = 1`,   `|{σ : descentCount σ = 0}| = ⟨n+1,0⟩ = 1`.

The increasing permutation is the unique descent-free one. This entry proves the **opposite
border**, the open question `…-oq-02-oq-01-oq-01` — the maximal rung `k = n`:

  `descentCount_eq_n_iff` :  `descentCount σ = n ↔ σ = Fin.revPerm`,
  `card_descentMax`       :  `|{σ : descentCount σ = n}| = ⟨n+1, n⟩  (= 1)`.

Combinatorially: a permutation of `Fin (n+1)` realizes the **maximum** possible `n` descents iff
it is *strictly decreasing*, and the decreasing arrangement `Fin.revPerm : i ↦ rev i` is unique —
so the maximally-descending permutations are counted by `⟨n+1,n⟩ = 1`, the **right** border of the
Eulerian triangle, dual to the `⟨n+1,0⟩ = 1` left border. Together the two entries pin down both
ends of the Eulerian row by honest cardinalities of descent classes.

## Method

There are exactly `n` adjacent positions, so `descentCount σ = n` forces *every* adjacent pair to
be a descent: `σ (i.succ) < σ (i.castSucc)` for all `i`. Equivalently `rev ∘ σ` is strictly
*increasing* at every adjacent pair (`Fin.rev` is antitone, `Fin.rev_lt_rev`), hence strictly
monotone (`Fin.strictMono_iff_lt_succ`). A strictly monotone self-equivalence of `Fin (n+1)` is
the identity (`perm_eq_one_of_strictMono`, the subsingleton `Fin m ≃o Fin m` argument reused from
the sibling), so `σ.trans Fin.revPerm = 1`, i.e. `(σ i).rev = i`, i.e. `σ = Fin.revPerm`. The
converse is immediate from `Fin.castSucc_lt_succ` and antitonicity of `rev`.

The cardinality then follows from `Finset.card_eq_one`, the unique maximal-descent permutation
being `Fin.revPerm`, and `eulerian_succ_pred : ⟨n+1,n⟩ = 1` (a short induction off the Eulerian
recurrence and `eulerian_succ_self`).

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
The descent statistic is re-declared locally (the sibling's compiled artifact is not imported) so
this entry stands alone on top of the parent Eulerian-number development.
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01OQ01

open Equiv Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## A strictly monotone permutation of `Fin n` is the identity -/

/-- A strictly monotone self-equivalence of `Fin n` is the identity. The monotone equivalence is
an `OrderIso`, and `Fin n ≃o Fin n` is a subsingleton (its only element is the identity). -/
private theorem perm_eq_one_of_strictMono {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : StrictMono σ) : σ = 1 := by
  have hmono : Monotone (σ : Fin n → Fin n) := hσ.monotone
  have hmono' : Monotone (σ.symm : Fin n → Fin n) := by
    intro a b hab
    by_contra h
    push_neg at h
    have h2 := hσ h
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd hab (not_le.2 h2)
  let e : Fin n ≃o Fin n := σ.toOrderIso hmono hmono'
  have he : e = OrderIso.refl _ := Subsingleton.elim _ _
  have key : ∀ i, σ i = i := by
    intro i
    have hei : e i = i := by rw [he]; rfl
    simpa [e, Equiv.toOrderIso] using hei
  exact Equiv.ext key

/-! ## The descent statistic (re-declared) -/

/-- The **descent count** of a permutation `σ` of `Fin (n+1)`: the number of positions
`i : Fin n` at which `σ` falls, `σ (i.succ) < σ (i.castSucc)`. -/
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : ℕ :=
  (univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc)).card

/-! ## The right border `⟨n+1,n⟩ = 1` of the Eulerian triangle -/

/-- The next-to-last Eulerian number on each row is `1`: `⟨n+1,n⟩ = 1`. A short induction using
the Eulerian recurrence and the vanishing diagonal `eulerian_succ_self`. -/
theorem eulerian_succ_pred (n : ℕ) : eulerian (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [eulerian_succ_succ, eulerian_succ_self, mul_zero, zero_add,
      show (k + 1) - k = 1 from by omega, one_mul, ih]

/-! ## The maximal-descent rung `k = n` -/

/-- **Maximal descents ⟺ reverse permutation.** A permutation of `Fin (n+1)` attains the maximum
possible `n` descents exactly when it is the strictly decreasing arrangement `Fin.revPerm`. -/
theorem descentCount_eq_n_iff {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    descentCount σ = n ↔ σ = Fin.revPerm := by
  constructor
  · intro hn
    -- `n` descents over `n` adjacent positions ⟹ every adjacent pair is a descent.
    have hfull : (univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc)) = univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      exact hn
    have hall : ∀ i : Fin n, σ i.succ < σ i.castSucc := by
      intro i
      have hi : i ∈ univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc) := by
        rw [hfull]; exact mem_univ i
      exact (Finset.mem_filter.mp hi).2
    -- `rev ∘ σ` is strictly monotone, hence the identity.
    have hg : StrictMono (σ.trans Fin.revPerm) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      show (σ i.castSucc).rev < (σ i.succ).rev
      rw [Fin.rev_lt_rev]
      exact hall i
    have h1 : σ.trans Fin.revPerm = 1 := perm_eq_one_of_strictMono _ hg
    have hrev : ∀ a : Fin (n + 1), (Fin.revPerm : Equiv.Perm (Fin (n + 1))) a = a.rev :=
      fun _ => rfl
    apply Equiv.ext
    intro i
    have h2 := Equiv.ext_iff.mp h1 i
    rw [Equiv.Perm.one_apply, Equiv.trans_apply, hrev] at h2
    -- h2 : (σ i).rev = i
    rw [hrev, ← Fin.rev_rev (σ i), h2]
  · intro hrev
    subst hrev
    -- Every adjacent pair of `Fin.revPerm` is a descent.
    have hfull : (univ.filter (fun i : Fin n =>
        (Fin.revPerm : Equiv.Perm (Fin (n + 1))) i.succ
          < (Fin.revPerm : Equiv.Perm (Fin (n + 1))) i.castSucc)) = univ := by
      rw [Finset.filter_eq_self]
      intro i _
      show (i.succ).rev < (i.castSucc).rev
      rw [Fin.rev_lt_rev]
      exact Fin.castSucc_lt_succ (i := i)
    show (univ.filter (fun i : Fin n =>
        (Fin.revPerm : Equiv.Perm (Fin (n + 1))) i.succ
          < (Fin.revPerm : Equiv.Perm (Fin (n + 1))) i.castSucc)).card = n
    rw [hfull, Finset.card_univ, Fintype.card_fin]

/-- **The maximal-descent rung of the Eulerian bijection.** The permutations of `Fin (n+1)` with
the maximum number of descents number exactly the Eulerian number `⟨n+1,n⟩ = 1`: the decreasing
permutation is the unique one. This is the `k = n` case of the open claim
`|{σ : descentCount σ = k}| = ⟨n+1,k⟩`, dual to the `k = 0` border. -/
theorem card_descentMax {n : ℕ} :
    (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = n)).card
      = eulerian (n + 1) n := by
  rw [eulerian_succ_pred, Finset.card_eq_one]
  refine ⟨Fin.revPerm, ?_⟩
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_singleton, descentCount_eq_n_iff]

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01OQ01
