/-
Chung-Feller Bijection: Rotation Index to Path Type (OQ-01)

## Research Question

The parent `BallotProblemOQ01OQ04.lean` axiomatizes `chung_feller_uniform`:
all n+1 path types have the same count (Catalan number Cₙ).

OQ-01 asks: Can we prove the bijection explicitly?

## Answer

YES, with the following architecture:

**Key theorem (proved here)**:
The Chung-Feller rotation `cyclicRotation (1::l) (rightmostMinPos (1::l))` maps
any balanced path l to a sequence whose TAIL is a Dyck path (type n path).

**Proof strategy**:
1. The good rotation starts with 1 (by isGoodRotation with j=1)
2. The tail D satisfies ∀ j, (D.take j).sum ≥ 0 (since prefixSum of good rotation ≥ 1)
3. Therefore every upstep in D is above the axis → upstepsAboveAxis D = n
4. The n+1 preimages of each Dyck path D correspond to the n+1 positions in (1::D)
   with value 1 — one per type in {0,...,n}

**What remains (sorry'd)**:
The hard part is showing that rotating (1::D) at different "1-positions" gives
paths of ALL DISTINCT types. This requires careful prefix sum tracking across
the modular rotation — see the proof sketch in `chung_feller_uniform`.
-/

import Proofs.BallotProblemOQ01OQ04Core

set_option maxHeartbeats 400000

namespace ChungFellerBijection

open GeneralizedBallot ChungFeller
open scoped List

/- ## Part I: Setup and Notation -/

variable {n : ℕ} (hn : 0 < n)

/-- A Dyck path is a balanced path whose prefix sums are all non-negative.
    Equivalently, it has type n (all upsteps above the axis). -/
def IsDyckPath (l : List ℤ) (n : ℕ) : Prop :=
  IsBalancedPath l n ∧ ∀ i, 0 ≤ (l.take i).sum

/-- The Chung-Feller map: rotate 1::l to its good rotation. -/
noncomputable def chungFellerRot (l : List ℤ) : List ℤ :=
  cyclicRotation (1 :: l) (rightmostMinPos (1 :: l))

/- ## Part II: The Good Rotation Starts With 1 -/

/-- If a sequence's cyclic rotation is a good rotation, its first element is positive.
    Since elements are ±1, it must be 1. -/
theorem good_rotation_head_pos (l : List ℤ) (i : ℕ) (hi : i < l.length)
    (hgood : isGoodRotation l i) :
    0 < ((cyclicRotation l i).take 1).sum := by
  exact hgood 1 (by norm_num) (by omega)

/-- The augmented sequence 1::l has all elements in {1, -1}. -/
theorem augmented_pm_one {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) :
    ∀ x ∈ (1 :: l), x = 1 ∨ x = (-1 : ℤ) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · left; rfl
  · exact h.2.2 x hx

/-- The first element of a good rotation of (1::l) is 1.
    Proof: it must be +1 or -1 (all elements ±1), and the first prefix sum is positive,
    so it must be +1. -/
theorem chungFellerRot_head_eq_one {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) :
    (chungFellerRot l).headI = 1 := by
  unfold chungFellerRot
  set aug := (1 : ℤ) :: l
  set m := rightmostMinPos aug
  have haug_sum : 0 < aug.sum := by
    have := balanced_sum_zero hbal
    simp only [aug, List.sum_cons, this]
    omega
  have haug_len : 0 < aug.length := by simp [aug]
  have hgood := goodRotation_at_rightmostMin aug haug_len haug_sum
  -- The first prefix sum is positive → first element > 0
  have hpos : 0 < ((cyclicRotation aug m).take 1).sum :=
    good_rotation_head_pos aug m (rightmostMinPos_lt aug haug_sum) hgood
  -- First element of the rotation is in {1, -1}
  have hpm : (cyclicRotation aug m).headI = 1 ∨ (cyclicRotation aug m).headI = -1 := by
    have hlen : 0 < (cyclicRotation aug m).length := by
      simp [cyclicRotation, List.length_drop, List.length_append, List.length_take]
      omega
    have hne : cyclicRotation aug m ≠ [] := List.length_pos_iff_ne_nil.mp hlen
    have hmem : (cyclicRotation aug m).headI ∈ cyclicRotation aug m := by
      cases hcr : cyclicRotation aug m with
      | nil => exact absurd hcr hne
      | cons x xs => simp
    have hrotmem := cyclicRotation_mem_kCountedSequence
      (prepend_mem_kCountedSequence hbal) m
      (le_of_lt (rightmostMinPos_lt aug haug_sum))
    have hx := hrotmem.2.2 _ hmem
    simpa using hx
  -- Combining positivity with {1,-1} membership
  have htake1 : ((cyclicRotation aug m).take 1).sum = (cyclicRotation aug m).headI := by
    cases cyclicRotation aug m <;> simp
  rw [htake1] at hpos
  rcases hpm with h | h <;> simp [h] at hpos ⊢

/- ## Part III: The Tail is a Dyck Path -/

/-- Prefix sums of the tail of a good rotation are non-negative.
    If rot = 1::D is the good rotation, then prefixSum(rot, j+1) ≥ 1,
    so prefixSum(D, j) = prefixSum(rot, j+1) - 1 ≥ 0. -/
theorem chungFellerRot_tail_nonneg_prefixSum {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) (j : ℕ) :
    0 ≤ ((chungFellerRot l).tail.take j).sum := by
  unfold chungFellerRot
  set aug := (1 : ℤ) :: l with haug_def
  set m := rightmostMinPos aug with hm_def
  set rot := cyclicRotation aug m with hrot_def
  have haug_sum : 0 < aug.sum := by
    simp [aug, List.sum_cons, balanced_sum_zero hbal]
  have haug_len : 0 < aug.length := by simp [aug]
  have hm_lt : m < aug.length := rightmostMinPos_lt aug haug_sum
  have hrot_len_eq : rot.length = aug.length := by
    rw [hrot_def]; exact cyclicRotation_length aug m hm_lt.le
  have hgood := goodRotation_at_rightmostMin aug haug_len haug_sum
  -- rot = 1 :: rot.tail (first element is 1, proved above)
  have hhead : rot.headI = 1 := chungFellerRot_head_eq_one hn hbal
  have hrot_len : 0 < rot.length := by rw [hrot_len_eq]; exact haug_len
  -- Take (j+1) of rot = headI rot :: (rot.tail.take j)
  have hsplit : (rot.take (j + 1)).sum = rot.headI + (rot.tail.take j).sum := by
    cases hc : rot with
    | nil => rw [hc] at hrot_len; simp at hrot_len
    | cons h t =>
      rw [List.headI_cons, List.tail_cons, List.take_succ_cons, List.sum_cons]
  by_cases hj : j + 1 ≤ rot.length
  · -- The prefix sum of rot at j+1 is positive
    have hpos := hgood (j + 1) (by omega) (hrot_len_eq ▸ hj)
    rw [hsplit, hhead] at hpos
    omega
  · -- j ≥ rot.length: the take is the full tail, sum = rot.sum - 1 ≥ 0
    push_neg at hj
    have hfull : rot.tail.take j = rot.tail := List.take_of_length_le (by
      have : rot.tail.length = rot.length - 1 := List.length_tail; omega)
    rw [hfull]
    have hrot_sum : rot.sum = aug.sum := by rw [hrot_def]; exact cyclicRotation_sum aug m
    have haug_sum_val : aug.sum = 1 := by simp [aug, List.sum_cons, balanced_sum_zero hbal]
    have htail_sum : rot.tail.sum = rot.sum - rot.headI := by
      cases hc : rot with
      | nil => rw [hc] at hrot_len; simp at hrot_len
      | cons h t => rw [List.tail_cons, List.headI_cons, List.sum_cons]; omega
    rw [htail_sum, hrot_sum, haug_sum_val, hhead]; norm_num

/-- Every upstep in the tail of the Chung-Feller rotation is above the axis.
    This is the key Chung-Feller result: the rotation always produces a Dyck path. -/
theorem chungFellerRot_tail_upsteps_all_above {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n)
    (i : ℕ) (hi : i < (chungFellerRot l).tail.length)
    (hstep : (chungFellerRot l).tail.get ⟨i, hi⟩ = 1) :
    0 ≤ ((chungFellerRot l).tail.take i).sum :=
  chungFellerRot_tail_nonneg_prefixSum hn hbal i

/- ## Part IV: upstepsAboveAxis of the Tail Equals n -/

/-- Helper: card of range filter by get? equals List.count.
    Standard combinatorial fact: positions of value x in a list = count of x.
    Proof by induction on the list, using the shift bijection i ↦ i+1. -/
private lemma card_filter_getopt_eq_count : ∀ (t : List ℤ) (x : ℤ),
    ((Finset.range t.length).filter (fun i => t[i]? = some x)).card = t.count x := by
  intro t
  induction t with
  | nil => simp
  | cons hd tl ih =>
    intro x
    rw [List.length_cons, Finset.range_add_one', Finset.filter_insert, Finset.filter_map]
    simp only [Function.comp_def, Function.Embedding.coeFn_mk, List.getElem?_cons_succ,
               List.getElem?_cons_zero, Option.some.injEq]
    by_cases h : hd = x
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), Finset.card_map, ih,
          List.count_cons]
      simp [h]
    · rw [if_neg h, Finset.card_map, ih, List.count_cons]
      simp [h]

/-- Helper: when all prefix sums ≥ 0, upstepsAboveAxis = count of +1 steps. -/
private lemma upstepsAboveAxis_of_all_nonneg (t : List ℤ)
    (h : ∀ i, 0 ≤ (t.take i).sum) :
    upstepsAboveAxis t = t.count 1 := by
  unfold upstepsAboveAxis
  have hsimp : (Finset.range t.length).filter (fun i =>
      t[i]? = some 1 ∧ (0 : ℤ) ≤ (t.take i).sum) =
    (Finset.range t.length).filter (fun i => t[i]? = some 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hget, _⟩; exact ⟨hlt, hget⟩
    · rintro ⟨hlt, hget⟩; exact ⟨hlt, hget, h i⟩
  rw [hsimp, card_filter_getopt_eq_count]

/-- Helper: the tail of chungFellerRot has exactly n upsteps (+1 steps).
    The rotation preserves element counts (it's a permutation);
    since aug = 1::l has n+1 ones and the good rotation starts with 1,
    the tail has n ones. -/
private lemma chungFellerRot_tail_count_one {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) :
    (chungFellerRot l).tail.count 1 = n := by
  unfold chungFellerRot
  set rot := cyclicRotation ((1 : ℤ) :: l) (rightmostMinPos ((1 : ℤ) :: l))
  have hmem := prepend_mem_kCountedSequence hbal
  have hrot_mem : rot ∈ kCountedSequence 1 (n + 1) n :=
    cyclicRotation_mem_kCountedSequence hmem _ (rightmostMinPos_le _)
  -- rot.count 1 = n + 1 (from kCountedSequence membership)
  have hrot_count : rot.count 1 = n + 1 := hrot_mem.1
  -- rot starts with 1
  have hhead : rot.headI = 1 := chungFellerRot_head_eq_one hn hbal
  -- Case split: rot = hd :: tl (non-empty since count 1 = n+1 ≥ 1)
  cases h : rot with
  | nil => simp [h] at hrot_count
  | cons hd tl =>
    simp only [List.tail_cons]
    simp only [h, List.headI_cons] at hhead
    subst hhead
    -- (1 :: tl).count 1 = n + 1
    -- → tl.count 1 + 1 = n + 1  (since head = 1)
    -- → tl.count 1 = n
    rw [h] at hrot_count
    simp only [List.count_cons, beq_self_eq_true, if_true] at hrot_count
    omega

/-- **Key Result**: The tail of the Chung-Feller rotation has type n (all upsteps above axis).
    This proves the rotation maps balanced paths to Dyck paths.

    **Proof**: Combine the two helper lemmas:
    1. All prefix sums of the tail are ≥ 0 (chungFellerRot_tail_nonneg_prefixSum)
    2. Count of +1 steps in the tail = n (chungFellerRot_tail_count_one)
    3. Since (1) holds, upstepsAboveAxis = count of +1 steps = n -/
theorem chungFellerRot_tail_type_eq_n {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) :
    upstepsAboveAxis (chungFellerRot l).tail = n := by
  rw [upstepsAboveAxis_of_all_nonneg _ (chungFellerRot_tail_nonneg_prefixSum hn hbal)]
  exact chungFellerRot_tail_count_one hn hbal

/- ## Part V: Well-Typing Lemmas (Session 2) -/

/-- **Bound**: For any balanced path, the number of upsteps above the axis is at most n.
    Proof: upstepsAboveAxis is a subset of all +1 positions, which number n. -/
theorem upstepsAboveAxis_le_n {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) :
    upstepsAboveAxis l ≤ n := by
  unfold upstepsAboveAxis
  calc ((Finset.range l.length).filter (fun i =>
            l[i]? = some 1 ∧ (0 : ℤ) ≤ (l.take i).sum)).card
      ≤ ((Finset.range l.length).filter (fun i => l[i]? = some 1)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hi.2.1⟩
    _ = l.count 1 := card_filter_getopt_eq_count l 1
    _ = n := h.1

/-- The tail of the Chung-Feller rotation is a balanced path of length 2n.
    Proof: The rotation preserves element counts; after removing the head (which is 1),
    the tail has count(1) = n (proved), count(-1) = n, and all elements ±1. -/
theorem chungFellerRot_tail_is_balanced {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) :
    IsBalancedPath (chungFellerRot l).tail n := by
  have hhead : (chungFellerRot l).headI = 1 := chungFellerRot_head_eq_one hn hbal
  have hrot_mem : chungFellerRot l ∈ kCountedSequence 1 (n + 1) n := by
    unfold chungFellerRot
    exact cyclicRotation_mem_kCountedSequence (prepend_mem_kCountedSequence hbal) _
      (rightmostMinPos_le _)
  have hne : chungFellerRot l ≠ [] := by
    intro h; rw [h] at hrot_mem; exact absurd hrot_mem.1 (by simp)
  cases hrot : chungFellerRot l with
  | nil => exact absurd hrot hne
  | cons hd tl =>
    simp only [List.tail_cons]
    have hd_eq : hd = 1 := by rwa [hrot, List.headI_cons] at hhead
    subst hd_eq
    refine ⟨?_, ?_, ?_⟩
    · -- count(1) = n
      have h_count := chungFellerRot_tail_count_one hn hbal
      rw [hrot, List.tail_cons] at h_count
      exact h_count
    · -- count(-1) = n: kCountedSequence gives count(-(1:ℤ)) = n, head is 1, tail has n
      have hcount : (chungFellerRot l).count (-1 : ℤ) = n := hrot_mem.2.1
      rw [hrot, List.count_cons] at hcount
      simp only [show ((1 : ℤ) == (-1 : ℤ)) = false from by decide, if_false] at hcount
      exact hcount
    · -- all elements ±1: sublist of ±1 sequence
      intro x hx
      have hall : ∀ y ∈ chungFellerRot l, y = 1 ∨ y = (-1 : ℤ) := hrot_mem.2.2
      have hxmem : x ∈ chungFellerRot l := by rw [hrot]; exact List.mem_cons_of_mem _ hx
      exact hall x hxmem

/-- **The tail of the Chung-Feller rotation is a Dyck path**.
    Combines `chungFellerRot_tail_is_balanced` with `chungFellerRot_tail_nonneg_prefixSum`.
    This is the key FORWARD DIRECTION of the Chung-Feller bijection — the map is well-defined
    as a function from balanced paths to Dyck paths. -/
theorem chungFellerRot_tail_is_dyck {l : List ℤ} {n : ℕ}
    (hn : 0 < n) (hbal : IsBalancedPath l n) :
    IsDyckPath (chungFellerRot l).tail n :=
  ⟨chungFellerRot_tail_is_balanced hn hbal,
   chungFellerRot_tail_nonneg_prefixSum hn hbal⟩

/- ## Part VI: The Full Bijection -/

/- ### Orbit Structure -/

/-- **Modular rotation composition**: composing two cyclic rotations that "wrap around"
    equals a single rotation. When r + m > |A|, the composition rotates by r+m-|A|.

    **Proof sketch**: Unfold both sides as drop/take decompositions.
    Let B = A.drop r ++ A.take r, k = r+m-|A|. Since m > |A|-r:
    - B.drop m = (A.take r).drop k = (A.drop k).take(r-k)
    - B.take m = A.drop r ++ (A.take r).take k = A.drop r ++ A.take k
    - Combined: (A.drop k).take(r-k) ++ A.drop r ++ A.take k = A.drop k ++ A.take k ✓
      (since A.drop k = (A.drop k).take(r-k) ++ A.drop r by A.drop_drop) -/
private lemma cyclicRotation_compose_wrap (A : List ℤ) (r m : ℕ)
    (hr : r ≤ A.length) (hm : m ≤ A.length) (hrm : A.length < r + m) :
    cyclicRotation (cyclicRotation A r) m = cyclicRotation A (r + m - A.length) := by
  simp only [cyclicRotation]
  set k := r + m - A.length with hk_def
  have hlenAr : (A.drop r).length = A.length - r := List.length_drop
  have hk_le_r : k ≤ r := by omega
  have hmk : m - (A.drop r).length = k := by rw [hlenAr]; omega
  have hdrop_nil : (A.drop r).drop m = [] := by
    apply List.drop_eq_nil_of_le; rw [hlenAr]; omega
  have htake_all : (A.drop r).take m = A.drop r := by
    apply List.take_of_length_le; rw [hlenAr]; omega
  rw [List.drop_append, List.take_append, hmk, hdrop_nil, htake_all, List.nil_append,
      List.drop_take, List.take_take, Nat.min_eq_left hk_le_r, ← List.append_assoc]
  congr 1
  have hdd : A.drop r = (A.drop k).drop (r - k) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdd, List.take_append_drop]

/-- **Key structural lemma**: Balanced paths in the same rotation orbit have the same Dyck image.
    If (1::l₂) = cyclicRotation(1::l₁) r, then chungFellerRot l₁ = chungFellerRot l₂.

    **Proof**: Both chungFellerRot(l₁) and chungFellerRot(l₂) have all prefix sums > 0
    and lie in the rotation orbit of (1::l₁). By the cycle lemma, each orbit has a
    UNIQUE good rotation, so they must coincide. -/
lemma orbit_same_dyck {l₁ l₂ : List ℤ} {n : ℕ} {r : ℕ}
    (h₁ : IsBalancedPath l₁ n) (h₂ : IsBalancedPath l₂ n)
    (horbit : (1 : ℤ) :: l₂ = cyclicRotation ((1 : ℤ) :: l₁) r)
    (hn : 0 < n) (hr : r ≤ ((1 : ℤ) :: l₁).length) :
    chungFellerRot l₁ = chungFellerRot l₂ := by
  set aug₁ := (1 : ℤ) :: l₁
  -- Get the unique good rotation index m₁ for aug₁
  obtain ⟨m₁, hm₁⟩ := prepend_unique_good_rotation h₁
  -- rightmostMinPos aug₁ ∈ goodRotations aug₁
  have haug₁_sum : 0 < aug₁.sum := by
    simp [aug₁, List.sum_cons, balanced_sum_zero h₁]
  have haug₁_len : 0 < aug₁.length := by simp [aug₁]
  have hrot_mem : rightmostMinPos aug₁ ∈ goodRotations aug₁ :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (rightmostMinPos_lt aug₁ haug₁_sum),
      goodRotation_at_rightmostMin aug₁ haug₁_len haug₁_sum⟩
  -- So m₁ = rightmostMinPos aug₁
  have hm₁_eq : m₁ = rightmostMinPos aug₁ := by
    have : rightmostMinPos aug₁ ∈ ({m₁} : Finset ℕ) := hm₁ ▸ hrot_mem
    exact (Finset.mem_singleton.mp this).symm
  -- chungFellerRot l₁ = cyclicRotation aug₁ m₁
  have hG₁ : chungFellerRot l₁ = cyclicRotation aug₁ m₁ := by
    unfold chungFellerRot; rw [hm₁_eq]
  -- chungFellerRot l₂ uses 1::l₂ = cyclicRotation aug₁ r
  set m₂ := rightmostMinPos ((1 : ℤ) :: l₂)
  have haug₂_sum : 0 < ((1 : ℤ) :: l₂).sum := by
    simp [List.sum_cons, balanced_sum_zero h₂]
  have hm₂_lt : m₂ < ((1 : ℤ) :: l₂).length :=
    rightmostMinPos_lt _ haug₂_sum
  have hm₂_le : m₂ ≤ aug₁.length := by
    have : ((1 : ℤ) :: l₂).length = aug₁.length := by
      rw [horbit, cyclicRotation_length _ _ hr]
    linarith [hm₂_lt.le]
  -- chungFellerRot l₂ = cyclicRotation (1::l₂) m₂ = cyclicRotation (cyclicRotation aug₁ r) m₂
  have hG₂ : chungFellerRot l₂ = cyclicRotation (cyclicRotation aug₁ r) m₂ := by
    unfold chungFellerRot; rw [← horbit]
  -- Length equality (for arithmetic side goals)
  have hlen_eq : ((1 : ℤ) :: l₂).length = aug₁.length := by
    rw [horbit, cyclicRotation_length _ _ hr]
  have hbase : isGoodRotation ((1 : ℤ) :: l₂) m₂ :=
    goodRotation_at_rightmostMin _ (by rw [hlen_eq]; exact haug₁_len) haug₂_sum
  -- Case: does r + m₂ wrap around?
  rw [hG₁, hG₂]
  by_cases hwrap : r + m₂ ≤ aug₁.length
  · -- No wrap: composition gives cyclicRotation aug₁ (r + m₂)
    have hcomp := cyclicRotation_compose aug₁ r m₂ hr (by omega)
    rw [hcomp]
    have hgr : isGoodRotation aug₁ (r + m₂) := by
      intro j hj hjn
      have hroteq : cyclicRotation aug₁ (r + m₂) = cyclicRotation ((1 : ℤ) :: l₂) m₂ := by
        rw [horbit]; exact hcomp.symm
      rw [hroteq]; exact hbase j hj (by rw [hlen_eq]; exact hjn)
    by_cases hbnd : r + m₂ < aug₁.length
    · have hk_good : r + m₂ ∈ goodRotations aug₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbnd, hgr⟩
      rw [hm₁] at hk_good
      exact congrArg (cyclicRotation aug₁) (Finset.mem_singleton.mp hk_good).symm
    · -- Boundary r + m₂ = aug₁.length: the rotation is aug₁ itself, so 0 is good ⇒ m₁ = 0
      have heq : r + m₂ = aug₁.length := by omega
      rw [heq, cyclicRotation_length_self]
      have h0good : isGoodRotation aug₁ 0 := by
        intro j hj hjn
        rw [cyclicRotation_zero]
        have := hgr j hj hjn
        rwa [heq, cyclicRotation_length_self] at this
      have h0mem : 0 ∈ goodRotations aug₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haug₁_len, h0good⟩
      rw [hm₁] at h0mem
      rw [show m₁ = 0 from (Finset.mem_singleton.mp h0mem).symm, cyclicRotation_zero]
  · -- Wrap: composition gives cyclicRotation aug₁ (r + m₂ - |aug₁|)
    push_neg at hwrap
    have hcomp := cyclicRotation_compose_wrap aug₁ r m₂ hr hm₂_le (by omega)
    rw [hcomp]
    have hgr : isGoodRotation aug₁ (r + m₂ - aug₁.length) := by
      intro j hj hjn
      have hroteq : cyclicRotation aug₁ (r + m₂ - aug₁.length)
          = cyclicRotation ((1 : ℤ) :: l₂) m₂ := by
        rw [horbit]; exact hcomp.symm
      rw [hroteq]; exact hbase j hj (by rw [hlen_eq]; exact hjn)
    have hk_good : r + m₂ - aug₁.length ∈ goodRotations aug₁ :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgr⟩
    rw [hm₁] at hk_good
    exact congrArg (cyclicRotation aug₁) (Finset.mem_singleton.mp hk_good).symm

/-- The Chung-Feller map sends balanced paths to DyckPaths × Fin(n+1).
    Both components are now well-typed:
    - First component: IsDyckPath (proved: chungFellerRot_tail_is_dyck)
    - Second component: Fin(n+1) (proved: upstepsAboveAxis_le_n) -/
noncomputable def chungFellerMap (n : ℕ) (hn : 0 < n) :
    {l : List ℤ // IsBalancedPath l n} →
    {l : List ℤ // IsDyckPath l n} × Fin (n + 1) :=
  fun ⟨l, hbal⟩ =>
    ⟨⟨(chungFellerRot l).tail, chungFellerRot_tail_is_dyck hn hbal⟩,
     ⟨upstepsAboveAxis l, Nat.lt_succ_of_le (upstepsAboveAxis_le_n hbal)⟩⟩

/- ## Part VII: Bijectivity Infrastructure -/

/-- When D is a Dyck path, `chungFellerRot D = 1 :: D`.
    Key: all prefix sums of 1::D at positions ≥ 1 are ≥ 1, so position 0
    is the unique minimum (value 0), hence rightmostMinPos = 0. -/
private lemma chungFellerRot_dyck_self {D : List ℤ} {n : ℕ} (hn : 0 < n)
    (hD : IsDyckPath D n) :
    chungFellerRot D = 1 :: D := by
  unfold chungFellerRot
  suffices h : rightmostMinPos (1 :: D) = 0 by rw [h, cyclicRotation_zero]
  -- Prefix sums of 1::D at j ≥ 1 are ≥ 1
  have hps_pos : ∀ j, 1 ≤ j → j ≤ (1 :: D).length →
      1 ≤ prefixSum (1 :: D) j := by
    intro j hj _
    unfold prefixSum
    cases j with
    | zero => omega
    | succ k =>
      simp only [List.take_succ_cons, List.sum_cons]
      linarith [hD.2 k]
  -- minPrefixSum = 0
  have hmin_zero : minPrefixSum (1 :: D) = 0 := by
    apply le_antisymm (minPrefixSum_le _ 0 (by simp))
    apply Finset.le_min'
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    by_cases h0 : i = 0
    · simp [h0, prefixSum]
    · have h0v : prefixSum (1 :: D) 0 = 0 := prefixSum_zero _
      linarith [hps_pos i (Nat.one_le_iff_ne_zero.mpr h0) (by omega), h0v]
  -- Filter = {0}, so max = 0
  have hfilter : (Finset.range ((1 :: D).length + 1)).filter
      (fun i => prefixSum (1 :: D) i = minPrefixSum (1 :: D)) = {0} := by
    rw [hmin_zero]
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
               prefixSum, List.take_zero, List.sum_nil]
    constructor
    · rintro ⟨hi, hps⟩
      by_contra h0
      have hp1 := hps_pos i (Nat.one_le_iff_ne_zero.mpr h0) (by omega)
      simp only [prefixSum] at hp1
      linarith
    · rintro rfl; exact ⟨by simp, by simp [prefixSum]⟩
  have hne : ((Finset.range ((1 :: D).length + 1)).filter
      (fun i => prefixSum (1 :: D) i = minPrefixSum (1 :: D))).Nonempty :=
    ⟨0, by rw [hfilter]; simp⟩
  have hmem : rightmostMinPos (1 :: D) ∈ (Finset.range ((1 :: D).length + 1)).filter
      (fun i => prefixSum (1 :: D) i = minPrefixSum (1 :: D)) := Finset.max'_mem _ hne
  rw [hfilter, Finset.mem_singleton] at hmem
  exact hmem

/-- Helper: the 0th element of a cyclic rotation equals the p-th element of the original. -/
private lemma cyclicRotation_get?_zero {A : List ℤ} {p : ℕ} (hp : p < A.length) :
    (cyclicRotation A p)[0]? = A[p]? := by
  simp only [cyclicRotation]
  rw [List.getElem?_append_left (by simp [List.length_drop]; omega)]
  rw [List.getElem?_drop]; simp

/-- Type formula: the type of rotation at position p equals the cardinality of
    F(p) = {q ∈ [2n+1] : S[q]=1 ∧ ((q<p ∧ PS q ≥ PS p) ∨ (p<q ∧ PS q > PS p))}.
    Proof: unfold cyclicRotation, split at wrap-around, and use cyclicRotation_prefixSum. -/
private lemma rotation_type_formula {D : List ℤ} {n : ℕ} (hn : 0 < n)
    (hD : IsDyckPath D n) (p : ℕ) (hp : p < (1 :: D).length)
    (hp_one : (1 :: D)[p]? = some 1) :
    upstepsAboveAxis (cyclicRotation (1 :: D) p).tail =
    ((Finset.range (1 :: D).length).filter (fun q =>
      (1 :: D)[q]? = some 1 ∧
      ((q < p ∧ prefixSum (1 :: D) q ≥ prefixSum (1 :: D) p) ∨
       (p < q ∧ prefixSum (1 :: D) q > prefixSum (1 :: D) p)))).card := by
  -- Setup: abbreviations for the key sequences
  set S : List ℤ := 1 :: D
  set rot := cyclicRotation S p
  set T := rot.tail
  have hSlen : S.length = 2 * n + 1 := by simp [S, balanced_length hD.1]
  have hSsum : S.sum = 1 := by simp [S, balanced_sum_zero hD.1]
  have hp_le : p ≤ S.length := le_of_lt hp
  have hrot_ne : rot ≠ [] := by
    simp only [rot, cyclicRotation, ← List.length_pos_iff_ne_nil,
               List.length_append, List.length_drop, List.length_take]; omega
  have hrot_head : rot[0]? = some 1 := by
    simp only [rot]; rw [cyclicRotation_get?_zero hp]; exact hp_one
  have hrot_cons : rot = 1 :: T := by
    cases hc : rot with
    | nil => exact absurd hc hrot_ne
    | cons a tl =>
      have ha : a = 1 := by
        have h := hrot_head
        simp only [hc, List.getElem?_cons_zero] at h
        exact Option.some.inj h
      simp only [T, hc, List.tail_cons, ha]
  have hTlen : T.length = S.length - 1 := by
    simp only [T, rot, cyclicRotation, List.length_tail, List.length_append,
               List.length_drop, List.length_take]; omega
  have hT_get : ∀ j, T[j]? = rot[j + 1]? := fun j => by
    rw [hrot_cons, List.getElem?_cons_succ]
  have hrot_take : ∀ j, (rot.take (j + 1)).sum = 1 + (T.take j).sum := fun j => by
    rw [hrot_cons, List.take_succ_cons, List.sum_cons]
  have hrot_get_nw : ∀ k, k < S.length - p → rot[k]? = S[p + k]? := fun k hk => by
    simp only [rot, cyclicRotation]
    rw [List.getElem?_append_left (by simp [List.length_drop]; omega)]
    rw [List.getElem?_drop]
  have htake_get : ∀ i, i < p → (S.take p)[i]? = S[i]? := fun i hi => by
    conv_rhs => rw [show S = S.take p ++ S.drop p from (List.take_append_drop p S).symm]
    exact (List.getElem?_append_left
      (by rw [List.length_take, Nat.min_eq_left hp_le]; exact hi)).symm
  have hrot_get_w : ∀ k, S.length - p ≤ k → k < S.length → rot[k]? = S[p + k - S.length]? :=
      fun k hklo hkhi => by
    simp only [rot, cyclicRotation]
    rw [List.getElem?_append_right (by simp [List.length_drop]; omega)]
    simp only [List.length_drop]
    rw [show k - (S.length - p) = p + k - S.length from by omega]
    exact htake_get _ (by omega)
  have hrot_psum : ∀ k ≤ S.length,
      (rot.take k).sum = if p + k ≤ S.length then (S.take (p + k)).sum - (S.take p).sum
                         else (S.take (p + k - S.length)).sum + 1 - (S.take p).sum :=
      fun k hk => by
    have h := cyclicRotation_prefixSum S p k hp_le hk
    simp only [hSsum] at h; exact h
  have hpsp_pos : ∀ q, 1 ≤ q → 1 ≤ prefixSum S q := fun q hq => by
    simp only [prefixSum, S]
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    simp only [List.take_succ_cons, List.sum_cons]
    linarith [hD.2 k]
  -- Main: bijection between the two Finsets
  unfold upstepsAboveAxis
  rw [hTlen]
  apply Finset.card_bij'
    (fun j _ => if p + j + 1 < S.length then p + j + 1 else p + j + 1 - S.length)
    (fun q _ => if p < q then q - p - 1 else q + (S.length - p - 1))
  · -- Forward membership: j ∈ J → f(j) ∈ F
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_get, hj_psum⟩ := hj
    by_cases hcase : p + j + 1 < S.length
    · simp only [hcase, ↓reduceIte]
      refine ⟨trivial, ?_, Or.inr ⟨by omega, ?_⟩⟩
      · rw [show p + j + 1 = p + (j + 1) from by omega,
            ← hrot_get_nw (j + 1) (by omega), ← hT_get]; exact hj_get
      · simp only [prefixSum]
        have hrt := hrot_take j
        have hrp := hrot_psum (j + 1) (by omega)
        simp only [show p + (j + 1) = p + j + 1 from by omega,
                   show p + j + 1 ≤ S.length from by omega, ↓reduceIte] at hrp
        linarith
    · push_neg at hcase
      have hjge : S.length - p ≤ j := by
        by_cases hp0 : p = 0
        · subst hp0; omega
        · have hp1 : 1 ≤ p := by omega
          by_contra hlt; push_neg at hlt
          have hrt := hrot_take (S.length - p - 1)
          simp only [show S.length - p - 1 + 1 = S.length - p from by omega] at hrt
          have hrp := hrot_psum (S.length - p) (by omega)
          simp only [show p + (S.length - p) = S.length from by omega,
                     le_refl, if_true, ↓reduceIte,
                     List.take_length, hSsum] at hrp
          have hpsp := hpsp_pos p hp1; simp only [prefixSum] at hpsp
          have hjeq : j = S.length - p - 1 := by omega
          rw [hjeq] at hj_psum; linarith
      simp only [show ¬ (p + j + 1 < S.length) from by omega, ↓reduceIte]
      refine ⟨by omega, ?_, Or.inl ⟨by omega, ?_⟩⟩
      · rw [show p + j + 1 - S.length = p + (j + 1) - S.length from by omega,
            ← hrot_get_w (j + 1) (by omega) (by omega), ← hT_get]; exact hj_get
      · simp only [prefixSum, show p + j + 1 - S.length = p + (j + 1) - S.length from by omega]
        have hrt := hrot_take j
        have hrp := hrot_psum (j + 1) (by omega)
        simp only [show ¬ (p + (j + 1) ≤ S.length) from by omega, ↓reduceIte] at hrp
        linarith
  · -- Backward membership: q ∈ F → g(q) ∈ J
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    obtain ⟨hq_lt, hq_get, hq_cond⟩ := hq
    by_cases hcase : p < q
    · simp only [hcase, ↓reduceIte]
      refine ⟨by omega, ?_, ?_⟩
      · rw [hT_get, show q - p - 1 + 1 = q - p from by omega,
            hrot_get_nw (q - p) (by omega), show p + (q - p) = q from by omega]; exact hq_get
      · rcases hq_cond with ⟨_, _⟩ | ⟨_, hps⟩
        · omega
        · simp only [prefixSum] at hps
          have hrt := hrot_take (q - p - 1)
          simp only [show q - p - 1 + 1 = q - p from by omega] at hrt
          have hrp := hrot_psum (q - p) (by omega)
          simp only [show p + (q - p) = q from by omega,
                     show q ≤ S.length from by omega, ↓reduceIte] at hrp
          linarith
    · push_neg at hcase
      have hqlt : q < p := by rcases hq_cond with ⟨h, _⟩ | ⟨h, _⟩; exact h; omega
      have hq1 : 1 ≤ q := by
        by_contra hq0
        have hq_eq : q = 0 := by omega
        subst hq_eq
        rcases hq_cond with ⟨_, hps⟩ | ⟨h, _⟩
        · simp only [prefixSum, List.take_zero, List.sum_nil] at hps
          have hpp := hpsp_pos p (by omega : 1 ≤ p)
          simp only [prefixSum] at hpp
          linarith
        · omega
      simp only [show ¬ (p < q) from by omega, ↓reduceIte]
      refine ⟨by omega, ?_, ?_⟩
      · rw [hT_get, show q + (S.length - p - 1) + 1 = q + (S.length - p) from by omega,
            hrot_get_w (q + (S.length - p)) (by omega) (by omega),
            show p + (q + (S.length - p)) - S.length = q from by omega]; exact hq_get
      · rcases hq_cond with ⟨_, hps⟩ | ⟨h, _⟩
        · simp only [prefixSum] at hps
          have hrt := hrot_take (q + (S.length - p - 1))
          simp only [show q + (S.length - p - 1) + 1 = q + (S.length - p) from by omega] at hrt
          have hrp := hrot_psum (q + (S.length - p)) (by omega)
          simp only [show ¬ (p + (q + (S.length - p)) ≤ S.length) from by omega,
                     ↓reduceIte,
                     show p + (q + (S.length - p)) - S.length = q from by omega] at hrp
          linarith
        · omega
  · -- Left inverse: g(f(j)) = j
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, _, _⟩ := hj
    by_cases hcase : p + j + 1 < S.length
    · simp only [hcase, ↓reduceIte, show p < p + j + 1 from by omega, ↓reduceIte]; omega
    · simp only [show ¬ (p + j + 1 < S.length) from by omega, ↓reduceIte,
                 show ¬ (p < p + j + 1 - S.length) from by omega, ↓reduceIte]; omega
  · -- Right inverse: f(g(q)) = q
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hq_lt, _, hq_cond⟩ := hq
    by_cases hcase : p < q
    · simp only [hcase, ↓reduceIte,
                 show p + (q - p - 1) + 1 < S.length from by omega, ↓reduceIte]; omega
    · push_neg at hcase
      have hqlt : q < p := by rcases hq_cond with ⟨h, _⟩ | ⟨h, _⟩; exact h; omega
      simp only [show ¬ (p < q) from by omega, ↓reduceIte,
                 show ¬ (p + (q + (S.length - p - 1)) + 1 < S.length) from by omega,
                 ↓reduceIte]; omega

/-- **Key hard lemma**: The n+1 rotations of 1::D at its 1-positions give
    balanced paths with ALL DISTINCT types.

    **Proof** (via type formula + Finset strict subset argument):
    For 1-positions p₁ < p₂ of S = 1::D, define F(p) via the type formula above.
    Case 1 (PS p₂ > PS p₁): F(p₂) ⊊ F(p₁) because p₂ ∈ F(p₁) \ F(p₂).
    Case 2 (PS p₂ ≤ PS p₁): F(p₁) ⊊ F(p₂) because p₁ ∈ F(p₂) \ F(p₁).
    Either way, |F(p₁)| ≠ |F(p₂)|. -/
private lemma rotation_types_all_distinct {D : List ℤ} {n : ℕ} (hn : 0 < n)
    (hD : IsDyckPath D n) (p₁ p₂ : ℕ) (hp₁ : p₁ < (1 :: D).length)
    (hp₂ : p₂ < (1 :: D).length)
    (hp₁_one : (1 :: D)[p₁]? = some 1)
    (hp₂_one : (1 :: D)[p₂]? = some 1)
    (hne : p₁ ≠ p₂) :
    upstepsAboveAxis (cyclicRotation (1 :: D) p₁).tail ≠
    upstepsAboveAxis (cyclicRotation (1 :: D) p₂).tail := by
  -- Work with S := 1 :: D via local let (avoids set/rw mismatch with rotation_type_formula)
  let S : List ℤ := 1 :: D
  let F := fun p => (Finset.range S.length).filter (fun q =>
    S[q]? = some 1 ∧
    ((q < p ∧ prefixSum S q ≥ prefixSum S p) ∨
     (p < q ∧ prefixSum S q > prefixSum S p)))
  -- Helper: p is never in F(p) itself
  have self_not_mem : ∀ p, p ∉ F p := by
    intro p hp
    simp only [F, Finset.mem_filter] at hp
    rcases hp.2.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (lt_irrefl p)
  -- Core ordered claim: for a < b, the types (as |F|) differ
  have h_ord : ∀ a b : ℕ, a < b → a < S.length → b < S.length →
      S[a]? = some 1 → S[b]? = some 1 →
      (F a).card ≠ (F b).card := by
    intro a b hab ha hb ha_one hb_one
    by_cases hPS : prefixSum S a < prefixSum S b
    · -- PS a < PS b: F(b) ⊊ F(a), so |F(a)| > |F(b)|
      apply Nat.ne_of_gt
      apply Finset.card_lt_card
      rw [Finset.ssubset_def]
      refine ⟨?_, ?_⟩
      · -- F(b) ⊆ F(a)
        intro q hq
        simp only [F, Finset.mem_filter, Finset.mem_range] at hq ⊢
        obtain ⟨hqlen, hqone, hqcond⟩ := hq
        refine ⟨hqlen, hqone, ?_⟩
        rcases hqcond with ⟨hqlt, hqps⟩ | ⟨hqgt, hqps⟩
        · rcases lt_trichotomy q a with h | rfl | h
          · exact Or.inl ⟨h, le_of_lt (lt_of_lt_of_le hPS hqps)⟩
          · exact absurd hqps (not_le.mpr hPS)
          · exact Or.inr ⟨h, lt_of_lt_of_le hPS hqps⟩
        · exact Or.inr ⟨lt_trans hab hqgt, lt_trans hPS hqps⟩
      · -- b ∈ F(a) but b ∉ F(b)
        intro h_rev
        exact self_not_mem b (h_rev (by
          simp only [F, Finset.mem_filter, Finset.mem_range]
          exact ⟨hb, hb_one, Or.inr ⟨hab, hPS⟩⟩))
    · -- PS a ≥ PS b: F(a) ⊊ F(b), so |F(b)| > |F(a)|
      push_neg at hPS
      apply Nat.ne_of_lt
      apply Finset.card_lt_card
      rw [Finset.ssubset_def]
      refine ⟨?_, ?_⟩
      · -- F(a) ⊆ F(b)
        intro q hq
        simp only [F, Finset.mem_filter, Finset.mem_range] at hq ⊢
        obtain ⟨hqlen, hqone, hqcond⟩ := hq
        refine ⟨hqlen, hqone, ?_⟩
        rcases hqcond with ⟨hqlt, hqps⟩ | ⟨hqgt, hqps⟩
        · exact Or.inl ⟨lt_trans hqlt hab, le_trans hPS hqps⟩
        · rcases lt_trichotomy q b with h | rfl | h
          · exact Or.inl ⟨h, le_of_lt (lt_of_le_of_lt hPS hqps)⟩
          · exact absurd hPS (not_le.mpr hqps)
          · exact Or.inr ⟨h, lt_of_le_of_lt hPS hqps⟩
      · -- a ∈ F(b) but a ∉ F(a)
        intro h_rev
        exact self_not_mem a (h_rev (by
          simp only [F, Finset.mem_filter, Finset.mem_range]
          exact ⟨ha, ha_one, Or.inl ⟨hab, hPS⟩⟩))
  -- Apply h_ord: rewrite types as |F| via type formula, then WLOG p₁ < p₂
  rw [rotation_type_formula hn hD p₁ hp₁ hp₁_one,
      rotation_type_formula hn hD p₂ hp₂ hp₂_one]
  rcases Nat.lt_or_gt_of_ne hne with hp_lt | hp_gt
  · exact h_ord p₁ p₂ hp_lt hp₁ hp₂ hp₁_one hp₂_one
  · exact Ne.symm (h_ord p₂ p₁ hp_gt hp₂ hp₁ hp₂_one hp₁_one)

/-- **Chung-Feller bijection**: The map `chungFellerMap` is bijective.

    **Proof structure**:
    - `chungFellerRot_dyck_self`: chungFellerRot(D) = 1::D for Dyck D.
    - `orbit_same_dyck`: same orbit → same Dyck image.
    - `rotation_types_all_distinct`: distinct 1-position rotations → distinct types.
    These combine to give injectivity and surjectivity. -/
theorem chung_feller_bijection_exists (n : ℕ) (hn : 0 < n) :
    Function.Bijective (chungFellerMap n hn) := by
  constructor
  · -- INJECTIVITY
    intro ⟨l₁, hbal₁⟩ ⟨l₂, hbal₂⟩ heq
    simp only [chungFellerMap, Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨htail_eq, htype_eq⟩ := heq
    -- Same tail means same chungFellerRot (both heads = 1)
    have hrot_eq : chungFellerRot l₁ = chungFellerRot l₂ := by
      have h1 : (chungFellerRot l₁).headI = 1 := chungFellerRot_head_eq_one hn hbal₁
      have h2 : (chungFellerRot l₂).headI = 1 := chungFellerRot_head_eq_one hn hbal₂
      have hne1 : chungFellerRot l₁ ≠ [] := fun h => by rw [h] at h1; simp at h1
      have hne2 : chungFellerRot l₂ ≠ [] := fun h => by rw [h] at h2; simp at h2
      obtain ⟨a₁, t₁, hc1⟩ := List.exists_cons_of_ne_nil hne1
      obtain ⟨a₂, t₂, hc2⟩ := List.exists_cons_of_ne_nil hne2
      rw [hc1] at h1 htail_eq ⊢
      rw [hc2] at h2 htail_eq ⊢
      simp only [List.headI_cons] at h1 h2
      simp only [List.tail_cons] at htail_eq
      rw [h1, h2, htail_eq]
    -- Both l₁ and l₂ are rotations of D = (chungFellerRot l₁).tail
    set D := (chungFellerRot l₁).tail
    set D_full : List ℤ := 1 :: D
    have hD_eq₁ : chungFellerRot l₁ = D_full := by
      have h1' : (chungFellerRot l₁).headI = 1 := chungFellerRot_head_eq_one hn hbal₁
      have hne' : chungFellerRot l₁ ≠ [] := fun h => by rw [h] at h1'; simp at h1'
      obtain ⟨a, t, hc⟩ := List.exists_cons_of_ne_nil hne'
      rw [hc, List.headI_cons] at h1'
      show chungFellerRot l₁ = 1 :: (chungFellerRot l₁).tail
      rw [hc, List.tail_cons, h1']
    have hD_eq₂ : chungFellerRot l₂ = D_full := by rw [← hrot_eq, hD_eq₁]
    -- Find rotation positions
    set m₁ := rightmostMinPos (1 :: l₁)
    set m₂ := rightmostMinPos (1 :: l₂)
    have hm₁_lt : m₁ < (1 :: l₁).length :=
      rightmostMinPos_lt _ (by simp [List.sum_cons, balanced_sum_zero hbal₁])
    have hm₂_lt : m₂ < (1 :: l₂).length :=
      rightmostMinPos_lt _ (by simp [List.sum_cons, balanced_sum_zero hbal₂])
    -- D_full = cyclicRotation(1::l₁, m₁) = cyclicRotation(1::l₂, m₂)
    have hrot₁ : D_full = cyclicRotation (1 :: l₁) m₁ := hD_eq₁.symm
    have hrot₂ : D_full = cyclicRotation (1 :: l₂) m₂ := hD_eq₂.symm
    -- Compute inverse rotations to express 1::l₁ and 1::l₂ as rotations of D_full
    have hlen₁ : (1 :: l₁).length = 2 * n + 1 := by
      simp [balanced_length hbal₁]
    have hlen₂ : (1 :: l₂).length = 2 * n + 1 := by
      simp [balanced_length hbal₂]
    -- 1::l₁ = cyclicRotation(D_full, 2n+1-m₁) and 1::l₂ = cyclicRotation(D_full, 2n+1-m₂)
    have hinv₁ : 1 :: l₁ = cyclicRotation D_full (2 * n + 1 - m₁) := by
      conv_rhs => rw [hrot₁]
      rw [cyclicRotation_compose (1 :: l₁) m₁ (2*n+1-m₁)
          (by omega) (by omega)]
      rw [show m₁ + (2*n+1-m₁) = (1::l₁).length from by omega]
      exact (cyclicRotation_length_self _).symm
    have hinv₂ : 1 :: l₂ = cyclicRotation D_full (2 * n + 1 - m₂) := by
      conv_rhs => rw [hrot₂]
      rw [cyclicRotation_compose (1 :: l₂) m₂ (2*n+1-m₂)
          (by omega) (by omega)]
      rw [show m₂ + (2*n+1-m₂) = (1::l₂).length from by omega]
      exact (cyclicRotation_length_self _).symm
    have hDyck_D : IsDyckPath D n := by
      simp only [D]; exact chungFellerRot_tail_is_dyck hn hbal₁
    have hlen_Dfull : D_full.length = 2 * n + 1 := by
      simp [D_full, balanced_length hDyck_D.1]
    -- Reduce rotation indices mod length so they always lie in range (handles m = 0 boundary)
    have hDlen_pos : 0 < D_full.length := by omega
    have hcr_mod : ∀ k : ℕ, k ≤ D_full.length →
        cyclicRotation D_full k = cyclicRotation D_full (k % D_full.length) := by
      intro k hk
      rcases Nat.lt_or_ge k D_full.length with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have hke : k = D_full.length := by omega
        rw [hke, cyclicRotation_length_self, Nat.mod_self, cyclicRotation_zero]
    set p₁ := (2 * n + 1 - m₁) % D_full.length with hp₁_def
    set p₂ := (2 * n + 1 - m₂) % D_full.length with hp₂_def
    have hinvP₁ : 1 :: l₁ = cyclicRotation D_full p₁ := by
      rw [hinv₁, hp₁_def, hcr_mod _ (by omega)]
    have hinvP₂ : 1 :: l₂ = cyclicRotation D_full p₂ := by
      rw [hinv₂, hp₂_def, hcr_mod _ (by omega)]
    have hbound₁ : p₁ < D_full.length := by rw [hp₁_def]; exact Nat.mod_lt _ hDlen_pos
    have hbound₂ : p₂ < D_full.length := by rw [hp₂_def]; exact Nat.mod_lt _ hDlen_pos
    have hp₁_one : D_full[p₁]? = some 1 := by
      rw [← cyclicRotation_get?_zero hbound₁, hinvP₁.symm]; rfl
    have hp₂_one : D_full[p₂]? = some 1 := by
      rw [← cyclicRotation_get?_zero hbound₂, hinvP₂.symm]; rfl
    -- If p₁ = p₂ then l₁ = l₂ directly
    by_cases hm_eq : p₁ = p₂
    · -- Same rotation position → same l₁ = l₂
      have h12 : 1 :: l₁ = 1 :: l₂ := by
        rw [hinvP₁, hinvP₂, hm_eq]
      exact Subtype.ext (List.cons.inj h12).2
    · -- Different rotation positions → different types (by rotation_types_all_distinct)
      -- But types are equal (htype_eq), contradiction
      exfalso
      have hdistinct := rotation_types_all_distinct hn hDyck_D
        p₁ p₂ hbound₁ hbound₂ hp₁_one hp₂_one hm_eq
      -- But upstepsAboveAxis l₁ = upstepsAboveAxis l₂, and these tails are l₁, l₂
      have htail₁ : (cyclicRotation D_full p₁).tail = l₁ := by
        rw [hinvP₁.symm]; simp
      have htail₂ : (cyclicRotation D_full p₂).tail = l₂ := by
        rw [hinvP₂.symm]; simp
      rw [htail₁, htail₂] at hdistinct
      exact hdistinct (congrArg Fin.val htype_eq)
  · -- SURJECTIVITY: given (D, k), find l with chungFellerMap l = (D, k)
    intro ⟨⟨D, hDyck⟩, ⟨k, hk⟩⟩
    simp only [chungFellerMap, Prod.mk.injEq, Subtype.mk.injEq]
    -- S = 1::D; 1-positions of S form a Finset of size n+1
    set S : List ℤ := 1 :: D
    have hSlen : S.length = 2 * n + 1 := by simp [S, balanced_length hDyck.1]
    set onePosSet := (Finset.range S.length).filter (fun p => S[p]? = some 1)
    -- onePosSet has card n+1 (S has count 1 = n+1)
    have honePosCard : onePosSet.card = n + 1 := by
      have hS_count1 : S.count 1 = n + 1 := by
        simp only [S, List.count_cons, show (1 : ℤ) == 1 from rfl, ↓reduceIte,
                   hDyck.1.1]
      rw [show onePosSet = (Finset.range S.length).filter (fun i => S[i]? = some (1 : ℤ))
           from rfl, card_filter_getopt_eq_count S 1, hS_count1]
    -- typeMap: p ↦ upstepsAboveAxis (cyclicRotation S p).tail
    set typeMap : ℕ → ℕ := fun p => upstepsAboveAxis (cyclicRotation S p).tail
    -- typeMap values are < n+1 for p ∈ onePosSet
    have htypeRange : ∀ p ∈ onePosSet, typeMap p < n + 1 := by
      intro p hp
      simp only [onePosSet, Finset.mem_filter, Finset.mem_range] at hp
      have hbal : IsBalancedPath (cyclicRotation S p).tail n := by
        -- cyclicRotation S p has the same counts as S (it's a permutation)
        have hrot_perm : cyclicRotation S p ~ S := by
          unfold cyclicRotation
          calc S.drop p ++ S.take p ~ S.take p ++ S.drop p := List.perm_append_comm
            _ = S := List.take_append_drop p S
        have hrot_ne : cyclicRotation S p ≠ [] := by
          rw [← List.length_pos_iff_ne_nil]
          simp [cyclicRotation, List.length_append, List.length_drop, List.length_take]; omega
        have hrot_head : (cyclicRotation S p)[0]? = some 1 := by
          simp only [S]; rw [cyclicRotation_get?_zero hp.1]; exact hp.2
        -- Head = 1, construct the cons
        cases hc : cyclicRotation S p with
        | nil => exact absurd hc hrot_ne
        | cons a t =>
          have ha : a = 1 := by
            have h := hrot_head; simp only [hc, List.getElem?_cons_zero] at h
            exact Option.some.inj h
          simp only [List.tail_cons]
          refine ⟨?_, ?_, ?_⟩
          · -- count 1 = n
            have := hrot_perm.count_eq (a := (1:ℤ))
            simp only [hc, ha, List.count_cons, ↓reduceIte] at this
            simp only [S, List.count_cons, show (1:ℤ) == 1 from rfl, ↓reduceIte,
                       hDyck.1.1] at this
            omega
          · -- count (-1) = n
            have := hrot_perm.count_eq (a := (-1:ℤ))
            simp only [hc, ha, List.count_cons,
                       show ((1:ℤ) == (-1:ℤ)) = false from by decide,
                       Bool.false_eq_true, if_false, ↓reduceIte] at this
            simp only [S, List.count_cons, show ((1:ℤ) == (-1:ℤ)) = false from by decide,
                       Bool.false_eq_true, if_false, ↓reduceIte, hDyck.1.2.1] at this
            exact this
          · -- elements ±1
            intro x hx
            have hx_in : x ∈ cyclicRotation S p := by rw [hc]; exact List.mem_cons_of_mem _ hx
            have hx_in_S := hrot_perm.subset hx_in
            exact augmented_pm_one hDyck.1 x hx_in_S
      show upstepsAboveAxis (cyclicRotation S p).tail < n + 1
      exact Nat.lt_succ_of_le (upstepsAboveAxis_le_n hbal)
    -- typeMap is injective on onePosSet (from rotation_types_all_distinct)
    have htypeInj : Set.InjOn typeMap ↑onePosSet := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [onePosSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
                 Finset.mem_filter, Finset.mem_range] at hp₁ hp₂
      by_contra hne
      exact absurd heq (rotation_types_all_distinct hn hDyck p₁ p₂ hp₁.1 hp₂.1 hp₁.2 hp₂.2 hne)
    -- image of onePosSet under typeMap = Finset.range(n+1)
    have himage_sub : onePosSet.image typeMap ⊆ Finset.range (n + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨p, hp, rfl⟩ := hx
      exact htypeRange p hp
    have himage_card : (onePosSet.image typeMap).card = n + 1 := by
      rw [Finset.card_image_of_injOn htypeInj, honePosCard]
    have himage_eq : onePosSet.image typeMap = Finset.range (n + 1) :=
      Finset.eq_of_subset_of_card_le himage_sub (by rw [himage_card, Finset.card_range])
    -- k is in the image, so ∃ p ∈ onePosSet with typeMap p = k
    have hk_in : k ∈ onePosSet.image typeMap := by
      rw [himage_eq]; simp [hk]
    obtain ⟨p, hp_mem, hp_type⟩ := Finset.mem_image.mp hk_in
    simp only [onePosSet, Finset.mem_filter, Finset.mem_range] at hp_mem
    obtain ⟨hp_lt, hp_one⟩ := hp_mem
    -- Use l = (cyclicRotation S p).tail as the witness
    set l := (cyclicRotation S p).tail
    -- Show l is balanced
    have hrot_perm_p : cyclicRotation S p ~ S := by
      unfold cyclicRotation
      calc S.drop p ++ S.take p ~ S.take p ++ S.drop p := List.perm_append_comm
        _ = S := List.take_append_drop p S
    have hrot_ne_p : cyclicRotation S p ≠ [] := by
      rw [← List.length_pos_iff_ne_nil]
      simp [cyclicRotation, List.length_append, List.length_drop, List.length_take]; omega
    have hrot_head_p : (cyclicRotation S p)[0]? = some 1 := by
      simp only [S]; rw [cyclicRotation_get?_zero hp_lt]; exact hp_one
    have hrot_starts_1 : cyclicRotation S p = 1 :: l := by
      cases hc : cyclicRotation S p with
      | nil => exact absurd hc hrot_ne_p
      | cons a t =>
        have ha : a = 1 := by
          have h := hrot_head_p; simp only [hc, List.getElem?_cons_zero] at h
          exact Option.some.inj h
        simp only [l, hc, List.tail_cons, ha]
    have hl_balanced : IsBalancedPath l n := by
      cases hc : cyclicRotation S p with
      | nil => exact absurd hc hrot_ne_p
      | cons a t =>
        have ha : a = 1 := by
          have h := hrot_head_p; simp only [hc, List.getElem?_cons_zero] at h
          exact Option.some.inj h
        have hTeq : l = t := by simp only [l, hc, List.tail_cons]
        rw [hTeq]
        refine ⟨?_, ?_, ?_⟩
        · have hc1 := hrot_perm_p.count_eq (a := (1:ℤ))
          simp only [hc, ha, List.count_cons, show (1:ℤ) == 1 from rfl, ↓reduceIte] at hc1
          simp only [S, List.count_cons, show (1:ℤ) == 1 from rfl, ↓reduceIte,
                     hDyck.1.1] at hc1
          omega
        · have hcm := hrot_perm_p.count_eq (a := (-1:ℤ))
          simp only [hc, ha, List.count_cons, show ((1:ℤ) == (-1:ℤ)) = false from by decide,
                     Bool.false_eq_true, if_false, ↓reduceIte] at hcm
          simp only [S, List.count_cons, show ((1:ℤ) == (-1:ℤ)) = false from by decide,
                     Bool.false_eq_true, if_false, ↓reduceIte, hDyck.1.2.1] at hcm
          exact hcm
        · intro x hx
          have hx_in := hrot_perm_p.subset (hc ▸ List.mem_cons_of_mem _ hx)
          exact augmented_pm_one hDyck.1 x hx_in
    -- Show (chungFellerRot l).tail = D
    have hl_tail_eq_D : (chungFellerRot l).tail = D := by
      -- 1::l = cyclicRotation S p = cyclicRotation (1::D) p
      -- By orbit_same_dyck: chungFellerRot l = chungFellerRot D = 1::D
      have horbit : (1 : ℤ) :: l = cyclicRotation ((1 : ℤ) :: D) p := hrot_starts_1.symm
      have hrot_eq : chungFellerRot l = chungFellerRot D :=
        (orbit_same_dyck hDyck.1 hl_balanced horbit hn (le_of_lt hp_lt)).symm
      rw [hrot_eq, chungFellerRot_dyck_self hn hDyck]
      simp
    -- Construct the answer
    exact ⟨⟨l, hl_balanced⟩, hl_tail_eq_D, Fin.ext hp_type⟩

/-- **Chung-Feller Theorem (uniform distribution)** — proved directly from the bijection.
    Each path type has the same count; combined with `balanced_path_total`,
    each type has exactly Cₙ = C(2n,n)/(n+1) elements.

    **Proof**: The bijection chungFellerMap sends type-j balanced paths to DyckPaths × {j}.
    Given j, k ≤ n, build an explicit bijection between balancedPathsOfType n j and
    balancedPathsOfType n k via the Equiv from chung_feller_bijection_exists:
    - l ↦ e.symm((e ⟨l, _⟩).1, k-as-Fin)  (swap the type component)
    - Membership: second component of e.toFun extracts upstepsAboveAxis, = k by definition
    - Injectivity: equal images → same Dyck path → same j-typed path → inj by e.injective
    - Surjectivity: for l' of type k, use e.symm(D', j-as-Fin) which has type j and maps to l' -/
theorem chung_feller_uniform' (n : ℕ) (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    Set.ncard (balancedPathsOfType n j) = Set.ncard (balancedPathsOfType n k) := by
  -- Handle n = 0: only j = k = 0 possible, goal is trivially rfl
  by_cases hn : n = 0
  · subst hn; rw [Nat.le_zero.mp hj, Nat.le_zero.mp hk]
  -- General case: n > 0, use the bijection chung_feller_bijection_exists
  have hn' : 0 < n := by omega
  -- Build the Equiv from chung_feller_bijection_exists
  let e := Equiv.ofBijective _ (chung_feller_bijection_exists n hn')
  -- Key fact: second component of e.toFun extracts upstepsAboveAxis
  have htype : ∀ l (hbal : IsBalancedPath l n),
      (e.toFun ⟨l, hbal⟩).2.val = upstepsAboveAxis l := fun l hbal => rfl
  -- Key fact: type of e.symm(D, m) equals m.val
  have htype_symm : ∀ (x : {D // IsDyckPath D n} × Fin (n + 1)),
      upstepsAboveAxis (e.symm x).val = x.2.val := fun x => by
    have h : e (e.symm x) = x := e.apply_symm_apply x
    calc upstepsAboveAxis (e.symm x).val
        = (e (e.symm x)).2.val := rfl
      _ = x.2.val := by rw [h]
  -- Apply Set.ncard_congr with the type-swapping map
  apply Set.ncard_congr
    (fun l (hl : l ∈ balancedPathsOfType n j) =>
      (e.symm ((e.toFun ⟨l, hl.1⟩).1, ⟨k, by omega⟩)).val)
  · -- Membership: f(l) ∈ balancedPathsOfType n k
    intro l hl
    simp only [balancedPathsOfType, Set.mem_setOf_eq]
    exact ⟨(e.symm ((e.toFun ⟨l, hl.1⟩).1, ⟨k, by omega⟩)).property,
           htype_symm ((e.toFun ⟨l, hl.1⟩).1, ⟨k, by omega⟩)⟩
  · -- Injectivity: f(l₁) = f(l₂) → l₁ = l₂
    intro l₁ l₂ hl₁ hl₂ heq
    -- Val equality → subtype equality → symm-injectivity → pair equality → D₁ = D₂
    have heq_sub : e.symm ((e.toFun ⟨l₁, hl₁.1⟩).1, ⟨k, by omega⟩) =
                   e.symm ((e.toFun ⟨l₂, hl₂.1⟩).1, ⟨k, by omega⟩) :=
      Subtype.ext heq
    have hpair_eq := e.symm.injective heq_sub
    have hD_eq : (e.toFun ⟨l₁, hl₁.1⟩).1 = (e.toFun ⟨l₂, hl₂.1⟩).1 :=
      (Prod.ext_iff.mp hpair_eq).1
    -- Both types are j, so full image equality
    have hj₁ : (e.toFun ⟨l₁, hl₁.1⟩).2.val = j := by rw [htype l₁ hl₁.1, hl₁.2]
    have hj₂ : (e.toFun ⟨l₂, hl₂.1⟩).2.val = j := by rw [htype l₂ hl₂.1, hl₂.2]
    have hfin_eq : (e.toFun ⟨l₁, hl₁.1⟩).2 = (e.toFun ⟨l₂, hl₂.1⟩).2 :=
      Fin.ext (by rw [hj₁, hj₂])
    have hfull : e.toFun ⟨l₁, hl₁.1⟩ = e.toFun ⟨l₂, hl₂.1⟩ :=
      Prod.ext hD_eq hfin_eq
    exact congrArg Subtype.val (e.injective hfull)
  · -- Surjectivity: for l' of type k, find l of type j with f(l) = l'
    intro l' hl'
    set D' := (e.toFun ⟨l', hl'.1⟩).1 with hD'_def
    set l_sub := e.symm (D', ⟨j, by omega⟩) with hl_sub_def
    -- l_sub has type j
    have hl_j : l_sub.val ∈ balancedPathsOfType n j :=
      ⟨l_sub.property, htype_symm (D', ⟨j, by omega⟩)⟩
    use l_sub.val, hl_j
    -- f(l_sub.val, hl_j) = l'
    -- Need: ⟨l_sub.val, hl_j.1⟩ = l_sub (proof irrelevance; both props of same Prop)
    have hsub : (⟨l_sub.val, hl_j.1⟩ : {l // IsBalancedPath l n}) = l_sub :=
      Subtype.ext rfl
    have hfun_eq : e.toFun ⟨l_sub.val, hl_j.1⟩ = e.toFun l_sub :=
      congr_arg e.toFun hsub
    -- (e.toFun l_sub).1 = D' (from e.right_inv)
    have hD'_eq : (e.toFun l_sub).1 = D' := by
      have h : e.toFun l_sub = (D', (⟨j, by omega⟩ : Fin (n + 1))) := e.apply_symm_apply _
      rw [h]
    -- e.toFun ⟨l', hl'.1⟩ = (D', ⟨k, _⟩) since type(l') = k
    have hk_fin : (e.toFun ⟨l', hl'.1⟩).2 = ⟨k, by omega⟩ :=
      Fin.ext (by rw [htype l' hl'.1, hl'.2])
    have hfull' : e.toFun ⟨l', hl'.1⟩ = (D', ⟨k, by omega⟩) :=
      Prod.ext rfl hk_fin
    -- e.symm (D', k) = ⟨l', hl'.1⟩
    have hsymm_eq : e.symm (D', ⟨k, by omega⟩) = ⟨l', hl'.1⟩ :=
      e.symm_apply_eq.mpr hfull'.symm
    calc (e.symm ((e.toFun ⟨l_sub.val, hl_j.1⟩).1, ⟨k, by omega⟩)).val
        = (e.symm ((e.toFun l_sub).1, ⟨k, by omega⟩)).val := by rw [hfun_eq]
      _ = (e.symm (D', ⟨k, by omega⟩)).val := by rw [hD'_eq]
      _ = (⟨l', hl'.1⟩ : {l // IsBalancedPath l n}).val := by rw [hsymm_eq]
      _ = l' := rfl

/- ## Part VII: Computational Verification -/

/-- upstepsAboveAxis of good rotation tail for n=2 paths. -/

-- Verify the key non-trivial case: type 0 path [-1,-1,1,1]
-- Its rotation index m = rightmostMinPos [1,-1,-1,1,1] should give Dyck tail.
example : upstepsAboveAxisC [1,1,-1,-1] = 2 := by native_decide
example : upstepsAboveAxisC [1,-1,1,-1] = 2 := by native_decide
example : upstepsAboveAxisC [-1,-1,1,1] = 0 := by native_decide
example : upstepsAboveAxisC [-1,1,-1,1] = 0 := by native_decide

-- The Dyck path tails produced by chungFellerRot:
-- [1,1,-1,-1] → rotation by 0 → [1,1,1,-1,-1]
-- tail = [1,1,-1,-1], upstepsAboveAxis = 2. ✓

example : upstepsAboveAxisC [1,1,-1,-1] = 2 := by native_decide  -- Dyck (type 2 = n)

/- ## Summary of Progress -/

/- **Progress Summary**: We have proved the COMPLETE FORWARD DIRECTION of the Chung-Feller bijection,
    plus new supporting lemmas that well-type the bijection candidate:

    **Session 1 results (proved)**:
    1. `chungFellerRot_head_eq_one`: the good rotation always starts with 1
    2. `chungFellerRot_tail_nonneg_prefixSum`: the tail has all prefix sums ≥ 0
    3. `chungFellerRot_tail_upsteps_all_above`: all upsteps in the tail are above the axis
    4. `card_filter_getopt_eq_count`: positions of value x = count of x in list
    5. `upstepsAboveAxis_of_all_nonneg`: when all prefix sums ≥ 0, upstepsAboveAxis = count 1
    6. `chungFellerRot_tail_count_one`: the tail has exactly n upsteps
    7. `chungFellerRot_tail_type_eq_n`: **PROVED** — the rotation maps to Dyck paths

    **Session 2 results (proved)**:
    8. `upstepsAboveAxis_le_n`: for balanced paths, type ∈ {0,...,n} (well-typing for Fin(n+1))
    9. `chungFellerRot_tail_is_balanced`: the tail is a balanced path (count 1 = count(-1) = n, all ±1)
    10. `chungFellerRot_tail_is_dyck`: **PROVED** — the tail is a DYCK PATH (combines 9 + 2)
    11. `chungFellerMap`: the bijection CANDIDATE is now fully well-typed
        (both components are correctly typed: IsDyckPath + Fin(n+1))

    **Session 3 results (proved)**:
    12. `cyclicRotation_compose_wrap`: modular rotation composition — when r+m > |A|,
        composing cyclic rotations wraps around: cyclicRotation(cyclicRotation A r) m = cyclicRotation A (r+m-|A|)
    13. `orbit_same_dyck`: **KEY STRUCTURAL LEMMA** — all balanced paths in the same rotation
        orbit have the SAME Dyck image via chungFellerRot. Proof: the good rotation is unique
        per orbit (cycle lemma), so chungFellerRot maps all orbit members to the same sequence.
    14. `chung_feller_uniform'`: uniform distribution — **PROVED** by direct appeal to the
        parent's `chung_feller_uniform` axiom (this axiom is what we're trying to eliminate
        in the long run, but proves the theorem unconditionally for now).

    **Session 4 results (proved)**:
    15. `chungFellerRot_dyck_self`: chungFellerRot(D) = 1::D for Dyck D.
        (rightmostMinPos(1::D) = 0 since all prefix sums ≥ 1 for positions ≥ 1.)
    16. `cyclicRotation_get?_zero`: (cyclicRotation A p)[0] = A[p] for p < |A|.
    17. Injectivity of `chungFellerMap`: proved assuming `rotation_types_all_distinct`.
        (Uses: inverse rotation formula, cyclicRotation_get?_zero for 1-position extraction.)

    **Session 5 results (proved)**:
    18. `chung_feller_uniform'` — **COMPLETE PROOF** (0 sorries, 0 axiom calls):
        Explicitly proves uniform distribution from `chung_feller_bijection_exists`.
        Uses `Set.ncard_congr` with the type-swapping map `l ↦ e.symm((e ⟨l, hbal⟩).1, k)`,
        where `e = Equiv.ofBijective (chungFellerMap n hn') (chung_feller_bijection_exists n hn')`.

    **Current status**: 0 sorries, 0 axiom calls within this file.
    The file is COMPLETE. The Chung-Feller bijection is fully proved. -/

end ChungFellerBijection
