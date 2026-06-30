import Mathlib
import Proofs.CatalanAndreReflection

/-
# The generalized ballot / cycle-lemma count via André's reflection

The parent file (`Proofs.CatalanAndreReflection`) realizes the Catalan
reflection form `catalan n = C(2n, n) − C(2n, n+1)` as an explicit reflection
bijection: monotone `n`-up lattice paths that dip to height `-1` (the *bad*
paths) are matched with all `(n-1)`-up paths.

Here we generalize the barrier from `-1` to an arbitrary depth `-k`.  A path
(encoded, as in the parent, by its set `S : Finset (Fin (2n))` of up-step
positions) **reaches depth `-k`** when some prefix has `k` more downs than ups,
i.e. `j = 2 · preUps S j + k`.  The same André reflection — flip every step
from the first descent to `-k` — is a bijection

    { n-up paths reaching `-k` }  ≃  { (n-k)-up paths },

because reflecting a path that first touches `-k` turns its `n` up-steps into
`n - k` up-steps, and *every* `(n-k)`-up path reaches `-k` (it ends at height
`-2k`).  Counting both sides gives the **generalized ballot number**

    #{ n-up paths staying strictly above `-k` }
        = C(2n, n) − C(2n, n+k),

the number of paths that never dip to depth `k` below the axis.  At `k = 1`
this is `catalan n`, recovering the parent's reflection form as a special case.

The construction reuses the parent's barrier-independent infrastructure verbatim
(`preUps`, `reflect`, `card_reflect_add`, `preUps_reflect_eq`, …); only the
depth-`k` predicates and the first-descent cut point are re-derived.

Verified: 0 sorries, 0 axioms.
-/

namespace CatalanGeneralizedBallot

open Finset
open CatalanAndreReflection

variable {n : ℕ}

/-! ### Depth-`k` descent predicates -/

/-- The path `S` **reaches depth `-k`** at prefix length `j`: among the first
`j` steps there are exactly `k` more downs than ups, i.e. `j = 2·preUps + k`.
The parent's `hitsAt` is the case `k = 1`. -/
def hitsAtK (S : Finset (Fin (2 * n))) (k j : ℕ) : Prop :=
  j = 2 * preUps S j + k

instance (S : Finset (Fin (2 * n))) (k j : ℕ) : Decidable (hitsAtK S k j) := by
  unfold hitsAtK; infer_instance

/-- The path reaches depth `-k` somewhere among its `2n` prefixes. -/
def ReachesK (S : Finset (Fin (2 * n))) (k : ℕ) : Prop :=
  ∃ j ∈ Finset.range (2 * n + 1), hitsAtK S k j

instance (S : Finset (Fin (2 * n))) (k : ℕ) : Decidable (ReachesK S k) := by
  unfold ReachesK; infer_instance

/-! ### Discrete intermediate value at depth `k` -/

/-- **Discrete IVT at depth `k`.** A path with at most `n − k` up-steps ends at
height `≤ -2k`, so it must dip to depth exactly `-k` at some first prefix. -/
lemma reachesK_of_card_add_le (S : Finset (Fin (2 * n))) (k : ℕ) (hk : 1 ≤ k)
    (hcard : S.card + k ≤ n) : ReachesK S k := by
  -- `P j` : the height `2·preUps − j` has reached `≤ -k` at prefix length `j`.
  have hP : ∃ j, 2 * preUps S j + k ≤ j := by
    refine ⟨2 * n, ?_⟩
    rw [preUps_eq_card S (le_refl _)]; omega
  classical
  set j₀ := Nat.find hP with hj₀
  have hspec : 2 * preUps S j₀ + k ≤ j₀ := Nat.find_spec hP
  have hpos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, preUps_zero] at hspec; omega
    · exact h
  -- `j₀ - 1` has not yet reached depth `-k`.
  have hprev : ¬ (2 * preUps S (j₀ - 1) + k ≤ j₀ - 1) :=
    Nat.find_min hP (m := j₀ - 1) (by omega)
  have hstep : preUps S j₀ = preUps S (j₀ - 1) + (S.filter (fun i => i.val = j₀ - 1)).card := by
    conv_lhs => rw [show j₀ = (j₀ - 1) + 1 by omega]
    rw [preUps_succ]
  have hδ : (S.filter (fun i => i.val = j₀ - 1)).card ≤ 1 := card_filter_val_eq_le_one S _
  -- The first descent to `≤ -k` lands exactly on `-k`: `hitsAtK S k j₀`.
  refine ⟨j₀, Finset.mem_range.mpr ?_, ?_⟩
  · have hle : j₀ ≤ 2 * n := Nat.find_le (by rw [preUps_eq_card S (le_refl _)]; omega)
    omega
  · show j₀ = 2 * preUps S j₀ + k
    omega

/-! ### The reflection is depth-`k`-aware: cut point and cardinality -/

/-- `hitsAtK` agrees between `S` and `reflect S t` at every prefix up to `t`,
since reflection does not change the prefix up-count below the cut. -/
lemma hitsAtK_reflect_iff (S : Finset (Fin (2 * n))) (k t : ℕ) {j : ℕ} (hj : j ≤ t) :
    hitsAtK (reflect S t) k j ↔ hitsAtK S k j := by
  unfold hitsAtK
  rw [preUps_reflect_eq S t hj]

open scoped Classical in
/-- The depth-`k` cut point: the first prefix length at which the path reaches
depth `-k`. -/
noncomputable def cutK (S : Finset (Fin (2 * n))) (k : ℕ) : ℕ := sInf {j | hitsAtK S k j}

lemma cutK_hits {S : Finset (Fin (2 * n))} {k : ℕ} (h : ReachesK S k) :
    hitsAtK S k (cutK S k) := by
  obtain ⟨m, _, hm⟩ := h
  have : sInf {j | hitsAtK S k j} ∈ {j | hitsAtK S k j} := Nat.sInf_mem ⟨m, hm⟩
  exact this

lemma cutK_min {S : Finset (Fin (2 * n))} {k j : ℕ} (hj : hitsAtK S k j) : cutK S k ≤ j :=
  Nat.sInf_le hj

lemma cutK_le {S : Finset (Fin (2 * n))} {k : ℕ} (h : ReachesK S k) : cutK S k ≤ 2 * n := by
  obtain ⟨j, hjr, hj⟩ := h
  exact le_trans (cutK_min hj) (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hjr))

/-- Reflecting a depth-`k` path at its own cut point keeps it a depth-`k` path. -/
lemma reachesK_reflect {S : Finset (Fin (2 * n))} {k : ℕ} (h : ReachesK S k) :
    ReachesK (reflect S (cutK S k)) k := by
  refine ⟨cutK S k, Finset.mem_range.mpr (Nat.lt_succ_of_le (cutK_le h)), ?_⟩
  exact (hitsAtK_reflect_iff S k (cutK S k) (le_refl _)).mpr (cutK_hits h)

/-- The cut point is preserved by reflecting there: both words share the prefix
up to the first descent, so they reach depth `-k` for the first time together. -/
lemma cutK_reflect {S : Finset (Fin (2 * n))} {k : ℕ} (h : ReachesK S k) :
    cutK (reflect S (cutK S k)) k = cutK S k := by
  apply le_antisymm
  · exact cutK_min ((hitsAtK_reflect_iff S k (cutK S k) (le_refl _)).mpr (cutK_hits h))
  · by_contra hlt
    push_neg at hlt
    have hc : hitsAtK (reflect S (cutK S k)) k (cutK (reflect S (cutK S k)) k) :=
      cutK_hits (reachesK_reflect h)
    have hle : cutK (reflect S (cutK S k)) k ≤ cutK S k := le_of_lt hlt
    have : hitsAtK S k (cutK (reflect S (cutK S k)) k) :=
      (hitsAtK_reflect_iff S k (cutK S k) hle).mp hc
    exact absurd (cutK_min this) (by omega)

/-- Cardinality after reflecting at the depth-`k` cut point: subtraction-free
form `#(reflect S) + #S + k = 2n`.  This is the single quantitative input of the
generalized reflection bijection. -/
lemma card_reflect_cutK {S : Finset (Fin (2 * n))} {k : ℕ} (h : ReachesK S k) :
    (reflect S (cutK S k)).card + S.card + k = 2 * n := by
  have hadd := card_reflect_add S (cutK S k) (cutK_le h)
  have hhit : cutK S k = 2 * preUps S (cutK S k) + k := cutK_hits h
  omega

/-! ### The generalized reflection bijection and the ballot count -/

variable (n) in
/-- Monotone `n`-up paths that dip to depth `-k` (the depth-`k` *bad* paths). -/
def BadPathsK (k : ℕ) : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n ∧ ReachesK S k)

variable (n) in
/-- All `(n-k)`-up paths (each automatically dips to depth `-k`). -/
def LowPathsK (k : ℕ) : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n - k)

variable (n) in
/-- Monotone `n`-up paths that **never** dip to depth `-k`: the generalized Dyck
/ ballot paths staying strictly above the line at height `-k`. -/
def GoodPathsK (k : ℕ) : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n ∧ ¬ ReachesK S k)

/-- **Generalized André reflection bijection.** For `1 ≤ k ≤ n`, reflecting at
the first descent to depth `-k` is a bijection between depth-`k` bad `n`-up paths
and all `(n-k)`-up paths. -/
theorem card_badPathsK (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (BadPathsK n k).card = (LowPathsK n k).card := by
  apply Finset.card_bij'
    (fun S _ => reflect S (cutK S k)) (fun T _ => reflect T (cutK T k))
  · -- bad ↦ low
    intro S hS
    simp only [BadPathsK, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [LowPathsK, Finset.mem_filter, Finset.mem_univ, true_and]
    have := card_reflect_cutK hS.2
    omega
  · -- low ↦ bad
    intro T hT
    simp only [LowPathsK, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [BadPathsK, Finset.mem_filter, Finset.mem_univ, true_and]
    have hreach : ReachesK T k := reachesK_of_card_add_le T k hk (by omega)
    refine ⟨?_, reachesK_reflect hreach⟩
    have := card_reflect_cutK hreach
    omega
  · -- left inverse
    intro S hS
    simp only [BadPathsK, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [cutK_reflect hS.2, reflect_involutive]
  · -- right inverse
    intro T hT
    simp only [LowPathsK, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have hreach : ReachesK T k := reachesK_of_card_add_le T k hk (by omega)
    rw [cutK_reflect hreach, reflect_involutive]

/-- The depth-`k` bad-path count: `#BadPathsK = C(2n, n+k)`, for `1 ≤ k ≤ n`. -/
theorem card_badPathsK_eq (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (BadPathsK n k).card = (2 * n).choose (n + k) := by
  rw [card_badPathsK k hk hkn, LowPathsK, card_filter_card_eq]
  rw [← Nat.choose_symm (by omega : n + k ≤ 2 * n)]
  congr 1; omega

/-- **Generalized ballot / cycle-lemma count.** For `1 ≤ k ≤ n`, the number of
monotone `n`-up paths that stay strictly above depth `-k` is

  `#GoodPathsK = C(2n, n) − C(2n, n+k)`

(stated in subtraction-free additive form). -/
theorem card_goodPathsK_add (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (GoodPathsK n k).card + (2 * n).choose (n + k) = (2 * n).choose n := by
  have hsplit : (BadPathsK n k).card + (GoodPathsK n k).card
      = (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => S.card = n)).card := by
    rw [GoodPathsK, BadPathsK, ← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  rw [card_filter_card_eq n, card_badPathsK_eq k hk hkn] at hsplit
  omega

/-- Subtraction form of the generalized ballot count over `ℤ`. -/
theorem card_goodPathsK_sub (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((GoodPathsK n k).card : ℤ) = (2 * n).choose n - (2 * n).choose (n + k) := by
  have h := card_goodPathsK_add k hk hkn
  have : ((GoodPathsK n k).card : ℤ) + ((2 * n).choose (n + k) : ℤ)
      = ((2 * n).choose n : ℤ) := by exact_mod_cast h
  linarith

/-! ### Recovering the Catalan reflection form as the `k = 1` case -/

/-- At depth `k = 1`, the depth-`k` descent predicate is the parent's `Reaches`. -/
lemma reachesK_one_iff (S : Finset (Fin (2 * n))) :
    ReachesK S 1 ↔ CatalanAndreReflection.Reaches S := Iff.rfl

/-- The generalized good paths at `k = 1` are exactly the parent's Dyck paths. -/
lemma goodPathsK_one (n : ℕ) :
    GoodPathsK n 1 = CatalanAndreReflection.GoodPaths n := by
  unfold GoodPathsK CatalanAndreReflection.GoodPaths
  ext S
  simp only [Finset.mem_filter, reachesK_one_iff]

/-- **Recovery of the parent's reflection form.** The generalized ballot count at
`k = 1` is the Catalan number: `#GoodPathsK n 1 = catalan n`. -/
theorem card_goodPathsK_one (n : ℕ) : (GoodPathsK n 1).card = catalan n := by
  rw [goodPathsK_one]
  exact CatalanAndreReflection.card_goodPaths_eq_catalan n

/-! ### Concrete instance -/

/-- For `n = 3`, `k = 2`: the number of `3`-up paths staying strictly above depth
`-2` is `C(6,3) − C(6,5) = 20 − 6 = 14`. -/
example : (GoodPathsK 3 2).card + 6 = 20 := by
  have h := card_goodPathsK_add (n := 3) 2 (by norm_num) (by norm_num)
  have e1 : (2 * 3).choose (3 + 2) = 6 := by decide
  have e2 : (2 * 3).choose 3 = 20 := by decide
  rw [e1, e2] at h
  exact h

end CatalanGeneralizedBallot
