import Mathlib

/-
# André's reflection as an explicit bijection for the Catalan count

We give the classical **reflection (André) bijection** behind the Catalan
reflection form `catalan n = C(2n, n) − C(2n, n+1)`.

A monotone lattice path with `2n` steps is encoded as a finite set
`S : Finset (Fin (2*n))` of *up-step positions* (the complement holds the
down-steps). Writing `preUps S j` for the number of up-steps among the first
`j` steps, the height of the path after `j` steps is `2 * preUps S j - j`
(ups minus downs). A path is **bad** when it dips to height `-1`, i.e. some
prefix has one more down than up.

André's reflection flips every step from the first moment the height reaches
`-1`. On the encoding this is the involution `reflect`, which fixes the prefix
up to (and including) the first descent to `-1` and complements membership
afterwards. Its single quantitative input is the cardinality identity

  `#(reflect S) = 2n − 1 − #S`   (for every `S` that reaches `-1`),

which together with the fact that every set of size `n-1` automatically reaches
`-1` upgrades the arithmetic reflection identity to a genuine bijection between
bad `n`-up paths and *all* `(n-1)`-up paths.
-/

namespace CatalanAndreReflection

open Finset

variable {n : ℕ}

/-- Number of up-steps among the first `j` positions of the path `S`. -/
def preUps (S : Finset (Fin (2 * n))) (j : ℕ) : ℕ :=
  (S.filter (fun i => i.val < j)).card

/-- The path `S` **reaches height `-1`** at prefix length `j`: among the first
`j` steps there is exactly one more down than up, i.e. `j = 2 · preUps + 1`.
We keep `j` bounded by `2 * n` so the predicate ranges over genuine prefixes. -/
def hitsAt (S : Finset (Fin (2 * n))) (j : ℕ) : Prop :=
  j = 2 * preUps S j + 1

instance (S : Finset (Fin (2 * n))) (j : ℕ) : Decidable (hitsAt S j) := by
  unfold hitsAt; infer_instance

/-- The path reaches height `-1` somewhere among its `2n` prefixes. -/
def Reaches (S : Finset (Fin (2 * n))) : Prop :=
  ∃ j ∈ Finset.range (2 * n + 1), hitsAt S j

instance (S : Finset (Fin (2 * n))) : Decidable (Reaches S) := by
  unfold Reaches; infer_instance

/-- **André's reflection** with cut point `t`: keep every step before position
`t`, complement membership from `t` onwards. -/
def reflect (S : Finset (Fin (2 * n))) (t : ℕ) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun i => if i.val < t then i ∈ S else i ∉ S)

/-- Number of step-positions strictly before `t` (for `t ≤ 2n`). -/
lemma card_lt (t : ℕ) (ht : t ≤ 2 * n) :
    (Finset.univ.filter (fun i : Fin (2 * n) => i.val < t)).card = t := by
  rw [← Finset.card_range t]
  refine Finset.card_bij' (fun i _ => i.val) (fun k hk => ⟨k, by simp at hk; omega⟩) ?_ ?_ ?_ ?_
  · intro a ha; simp at ha ⊢; omega
  · intro a ha; simp at ha ⊢; omega
  · intro a ha; simp
  · intro a ha; simp

/-- **Key cardinality identity for reflection.** Reflecting at any cut point
`t ≤ 2n` and the original path together account for `2·preUps + (2n − t)`
up-steps; equivalently, in subtraction-free form,
`#(reflect S t) + #S + t = 2·preUps S t + 2n`. -/
lemma card_reflect_add (S : Finset (Fin (2 * n))) (t : ℕ) (ht : t ≤ 2 * n) :
    (reflect S t).card + S.card + t = 2 * preUps S t + 2 * n := by
  classical
  have e1 : (reflect S t).card
      = ∑ i : Fin (2 * n), if (if i.val < t then i ∈ S else i ∉ S) then 1 else 0 := by
    rw [reflect, Finset.card_filter]
  have e2 : S.card = ∑ i : Fin (2 * n), if i ∈ S then 1 else 0 := by
    conv_lhs => rw [← Finset.filter_univ_mem S]
    rw [Finset.card_filter]
  have e3 : preUps S t = ∑ i : Fin (2 * n), if (i ∈ S ∧ i.val < t) then 1 else 0 := by
    rw [preUps, show S.filter (fun i => i.val < t)
          = Finset.univ.filter (fun i => i ∈ S ∧ i.val < t) by
        ext i; simp [Finset.mem_filter], Finset.card_filter]
  have e4 : t = ∑ i : Fin (2 * n), if i.val < t then 1 else 0 := by
    conv_lhs => rw [← card_lt t ht]
    rw [Finset.card_filter]
  have e5 : 2 * n = ∑ _i : Fin (2 * n), (1 : ℕ) := by simp
  have key : ∀ i : Fin (2 * n),
      (if (if i.val < t then i ∈ S else i ∉ S) then (1 : ℕ) else 0)
        + (if i ∈ S then 1 else 0) + (if i.val < t then 1 else 0)
        = 2 * (if (i ∈ S ∧ i.val < t) then 1 else 0) + 1 := by
    intro i; by_cases h : i.val < t <;> by_cases hS : i ∈ S <;> simp [h, hS]
  have hsum : ∑ i : Fin (2 * n),
        ((if (if i.val < t then i ∈ S else i ∉ S) then (1 : ℕ) else 0)
          + (if i ∈ S then 1 else 0) + (if i.val < t then 1 else 0))
      = ∑ i : Fin (2 * n), (2 * (if (i ∈ S ∧ i.val < t) then (1 : ℕ) else 0) + 1) :=
    Finset.sum_congr rfl (fun i _ => key i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  rw [← e1, ← e2, ← e4, ← e3, ← e5] at hsum
  omega

/-! ### Prefix-count recurrence and basic bounds -/

/-- At most one position carries index `j`. -/
lemma card_filter_val_eq_le_one (S : Finset (Fin (2 * n))) (j : ℕ) :
    (S.filter (fun i => i.val = j)).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact Fin.ext (ha.2.trans hb.2.symm)

/-- Stepping the prefix length by one adds the (0-or-1) number of up-steps at
position `j`. -/
lemma preUps_succ (S : Finset (Fin (2 * n))) (j : ℕ) :
    preUps S (j + 1) = preUps S j + (S.filter (fun i => i.val = j)).card := by
  unfold preUps
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    by_cases hS : i ∈ S
    · simp only [hS, true_and]; omega
    · simp [hS]
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter] at hi hi'
    omega

lemma preUps_zero (S : Finset (Fin (2 * n))) : preUps S 0 = 0 := by
  simp [preUps]

lemma preUps_le_card (S : Finset (Fin (2 * n))) (j : ℕ) : preUps S j ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Beyond the last position the prefix count is the full up-count. -/
lemma preUps_eq_card (S : Finset (Fin (2 * n))) {j : ℕ} (hj : 2 * n ≤ j) :
    preUps S j = S.card := by
  unfold preUps
  congr 1
  apply Finset.filter_true_of_mem
  intro i _
  exact lt_of_lt_of_le i.isLt hj

/-! ### Discrete intermediate value: a deficient path reaches `-1` -/

/-- **Discrete IVT.** If a path has fewer than `n` up-steps (so it ends below
the axis) it must dip to height `-1` at some prefix. -/
lemma reaches_of_card_lt (S : Finset (Fin (2 * n))) (hcard : S.card < n) :
    Reaches S := by
  -- `P j` : the height `2·preUps − j` is negative at prefix length `j`.
  have hP : ∃ j, 2 * preUps S j < j := by
    refine ⟨2 * n, ?_⟩
    rw [preUps_eq_card S (le_refl _)]; omega
  classical
  set j₀ := Nat.find hP with hj₀
  have hspec : 2 * preUps S j₀ < j₀ := Nat.find_spec hP
  have hpos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, preUps_zero] at hspec; omega
    · exact h
  -- `j₀ - 1` does not yet satisfy `P`.
  have hprev : ¬ (2 * preUps S (j₀ - 1) < j₀ - 1) :=
    Nat.find_min hP (m := j₀ - 1) (by omega)
  have hstep : preUps S j₀ = preUps S (j₀ - 1) + (S.filter (fun i => i.val = j₀ - 1)).card := by
    conv_lhs => rw [show j₀ = (j₀ - 1) + 1 by omega]
    rw [preUps_succ]
  have hδ : (S.filter (fun i => i.val = j₀ - 1)).card ≤ 1 := card_filter_val_eq_le_one S _
  -- The first descent below the axis lands exactly on `-1`: `hitsAt S j₀`.
  refine ⟨j₀, Finset.mem_range.mpr ?_, ?_⟩
  · have hle : j₀ ≤ 2 * n := Nat.find_le (by rw [preUps_eq_card S (le_refl _)]; omega)
    omega
  · show j₀ = 2 * preUps S j₀ + 1
    omega

/-! ### The reflection is an involution that fixes the first descent -/

@[simp] lemma mem_reflect {S : Finset (Fin (2 * n))} {t : ℕ} {i : Fin (2 * n)} :
    i ∈ reflect S t ↔ (if i.val < t then i ∈ S else i ∉ S) := by
  simp [reflect]

/-- Reflecting twice at the same cut point is the identity. -/
lemma reflect_involutive (S : Finset (Fin (2 * n))) (t : ℕ) :
    reflect (reflect S t) t = S := by
  ext i
  simp only [mem_reflect]
  by_cases h : i.val < t <;> simp [h]

/-- The prefix up-count is unchanged below the cut point. -/
lemma preUps_reflect_eq (S : Finset (Fin (2 * n))) (t : ℕ) {j : ℕ} (hj : j ≤ t) :
    preUps (reflect S t) j = preUps S j := by
  unfold preUps
  congr 1
  ext i
  simp only [Finset.mem_filter, mem_reflect]
  constructor
  · rintro ⟨hi, hlt⟩
    rw [if_pos (lt_of_lt_of_le hlt hj)] at hi
    exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩
    exact ⟨by rw [if_pos (lt_of_lt_of_le hlt hj)]; exact hi, hlt⟩

/-- `hitsAt` agrees between `S` and `reflect S t` at every prefix up to `t`. -/
lemma hitsAt_reflect_iff (S : Finset (Fin (2 * n))) (t : ℕ) {j : ℕ} (hj : j ≤ t) :
    hitsAt (reflect S t) j ↔ hitsAt S j := by
  unfold hitsAt
  rw [preUps_reflect_eq S t hj]

/-! ### The first-descent cut point -/

open scoped Classical in
/-- The cut point: the first prefix length at which the path reaches height `-1`. -/
noncomputable def cut (S : Finset (Fin (2 * n))) : ℕ := sInf {j | hitsAt S j}

lemma cut_hits {S : Finset (Fin (2 * n))} (h : Reaches S) : hitsAt S (cut S) := by
  obtain ⟨m, _, hm⟩ := h
  have : sInf {j | hitsAt S j} ∈ {j | hitsAt S j} := Nat.sInf_mem ⟨m, hm⟩
  exact this

lemma cut_min {S : Finset (Fin (2 * n))} {j : ℕ} (hj : hitsAt S j) : cut S ≤ j :=
  Nat.sInf_le hj

lemma cut_le {S : Finset (Fin (2 * n))} (h : Reaches S) : cut S ≤ 2 * n := by
  obtain ⟨j, hjr, hj⟩ := h
  exact le_trans (cut_min hj) (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hjr))

/-- Reflecting at its own cut point keeps a bad path bad. -/
lemma reaches_reflect {S : Finset (Fin (2 * n))} (h : Reaches S) :
    Reaches (reflect S (cut S)) := by
  refine ⟨cut S, Finset.mem_range.mpr (Nat.lt_succ_of_le (cut_le h)), ?_⟩
  exact (hitsAt_reflect_iff S (cut S) (le_refl _)).mpr (cut_hits h)

/-- The cut point is preserved by reflecting there: both words share the prefix
up to the first descent, so they descend for the first time at the same place. -/
lemma cut_reflect {S : Finset (Fin (2 * n))} (h : Reaches S) :
    cut (reflect S (cut S)) = cut S := by
  apply le_antisymm
  · exact cut_min ((hitsAt_reflect_iff S (cut S) (le_refl _)).mpr (cut_hits h))
  · by_contra hlt
    push_neg at hlt
    have hc : hitsAt (reflect S (cut S)) (cut (reflect S (cut S))) :=
      cut_hits (reaches_reflect h)
    have hle : cut (reflect S (cut S)) ≤ cut S := le_of_lt hlt
    have : hitsAt S (cut (reflect S (cut S))) :=
      (hitsAt_reflect_iff S (cut S) hle).mp hc
    exact absurd (cut_min this) (by omega)

/-- Cardinality after reflecting at the cut point: subtraction-free form. -/
lemma card_reflect_cut {S : Finset (Fin (2 * n))} (h : Reaches S) :
    (reflect S (cut S)).card + S.card + 1 = 2 * n := by
  have hadd := card_reflect_add S (cut S) (cut_le h)
  have hhit : cut S = 2 * preUps S (cut S) + 1 := cut_hits h
  omega

/-! ### The reflection bijection and the Catalan count -/

variable (n) in
/-- Monotone `n`-up paths that dip below the axis (the *bad* paths). -/
def BadPaths : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n ∧ Reaches S)

variable (n) in
/-- All `(n-1)`-up paths (each automatically dips below the axis). -/
def LowPaths : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n - 1)

variable (n) in
/-- Monotone `n`-up paths that never dip below the axis (Dyck paths / *good*). -/
def GoodPaths : Finset (Finset (Fin (2 * n))) :=
  Finset.univ.filter (fun S => S.card = n ∧ ¬ Reaches S)

/-- Number of `k`-subsets of the `2n` positions is `C(2n, k)`. -/
lemma card_filter_card_eq (k : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => S.card = k)).card
      = (2 * n).choose k := by
  have h : Finset.univ.filter (fun S : Finset (Fin (2 * n)) => S.card = k)
      = Finset.powersetCard k Finset.univ := by
    ext S; simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard]; simp

/-- **André's reflection bijection.** For `n ≥ 1`, reflecting at the first
descent is a bijection between bad `n`-up paths and all `(n-1)`-up paths. -/
theorem card_badPaths (hn : 1 ≤ n) : (BadPaths n).card = (LowPaths n).card := by
  apply Finset.card_bij'
    (fun S _ => reflect S (cut S)) (fun T _ => reflect T (cut T))
  · -- bad ↦ low
    intro S hS
    simp only [BadPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [LowPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    have := card_reflect_cut hS.2
    omega
  · -- low ↦ bad
    intro T hT
    simp only [LowPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [BadPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    have hreach : Reaches T := reaches_of_card_lt T (by omega)
    refine ⟨?_, reaches_reflect hreach⟩
    have := card_reflect_cut hreach
    omega
  · -- left inverse
    intro S hS
    simp only [BadPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [cut_reflect hS.2, reflect_involutive]
  · -- right inverse
    intro T hT
    simp only [LowPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have hreach : Reaches T := reaches_of_card_lt T (by omega)
    rw [cut_reflect hreach, reflect_involutive]

/-- The bad-path count for every `n` (the `n = 0` path never dips). -/
theorem card_badPaths_eq (n : ℕ) : (BadPaths n).card = (2 * n).choose (n + 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hempty : BadPaths 0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro S hS
      rw [BadPaths, Finset.mem_filter] at hS
      obtain ⟨_, _, j, hj, hhit⟩ := hS
      rw [Finset.mem_range] at hj
      unfold hitsAt at hhit
      omega
    rw [hempty]; simp
  · rw [card_badPaths hn, LowPaths, card_filter_card_eq]
    rw [← Nat.choose_symm (by omega : n + 1 ≤ 2 * n)]
    congr 1; omega

/-- The additive partition `C(2n, n) = catalan n + C(2n, n+1)` (reproved inline,
no truncated subtraction). -/
lemma centralBinom_eq_catalan_add_choose (m : ℕ) :
    (2 * m).choose m = catalan m + (2 * m).choose (m + 1) := by
  have hcat : (m + 1) * catalan m = (2 * m).choose m := succ_mul_catalan_eq_centralBinom m
  have hchoose : (m + 1) * ((2 * m).choose (m + 1)) = m * ((2 * m).choose m) := by
    have h := Nat.choose_succ_right_eq (2 * m) m
    have e : 2 * m - m = m := by omega
    rw [e] at h
    calc (m + 1) * ((2 * m).choose (m + 1))
          = (2 * m).choose (m + 1) * (m + 1) := by ring
      _ = (2 * m).choose m * m := h
      _ = m * ((2 * m).choose m) := by ring
  refine Nat.eq_of_mul_eq_mul_left (show 0 < m + 1 by omega) ?_
  rw [Nat.mul_add, hcat, hchoose]; ring

/-- **Main theorem (André reflection ⟹ Catalan count).** The number of monotone
`n`-up lattice paths that stay weakly above the axis equals the `n`-th Catalan
number, realized through the explicit reflection bijection:

  `#GoodPaths = C(2n, n) − C(2n, n+1) = catalan n`. -/
theorem card_goodPaths_eq_catalan (n : ℕ) : (GoodPaths n).card = catalan n := by
  -- All `n`-up paths split into bad (dip) and good (never dip).
  have hsplit : (BadPaths n).card + (GoodPaths n).card
      = (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => S.card = n)).card := by
    rw [GoodPaths, BadPaths, ← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  rw [card_filter_card_eq n, card_badPaths_eq n] at hsplit
  have hcb := centralBinom_eq_catalan_add_choose n
  omega

end CatalanAndreReflection
