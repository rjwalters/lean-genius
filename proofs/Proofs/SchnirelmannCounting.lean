/-
  Schnirelmann's gap-counting inequality — the finite combinatorial core of
  Schnirelmann's inequality  σ(A ⊕ B) ≥ σA + σB − σA·σB.

  Prior sessions on `weak-goldbach-oq-01` reduced Schnirelmann's inequality (and
  hence the `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean`) to a single
  purely-combinatorial statement (Nathanson, *Additive Number Theory*, Thm 7.4):

      C(n) ≥ A(n) + σB · (n − A(n))                              (†)

  where `A(n) = #{a ∈ Ioc 0 n | a ∈ A}`, `C(n) = #{c ∈ Ioc 0 n | c ∈ C}`, and
  `C ⊇ A + B`.  The inf-extraction layer turning (†) into the density inequality
  was proved separately (`SchnirelmannInequality.schnirelmannDensity_add_le_of_countingBound`).

  This file proves (†) itself — the delicate gap-counting step — from scratch,
  via the *predecessor map* `p m = largest element of A that is ≤ m`.  The two
  facts driving the argument are:

    * for every `m`, if `m − p m ∈ B` then `m = p m + (m − p m) ∈ A + B ⊆ C`
      (so the set `M := {m ∈ (0,n] : m − p m ∈ B}` is contained in `C ∩ (0,n]`);
    * the fibres of `p` on `(0,n]` are *integer intervals*, on which the count of
      `m` with `m − p m ∈ B` is bounded below by Schnirelmann's density estimate.

  Telescoping the fibre lengths (which sum to `n`) then yields (†).
-/
import Mathlib

open Finset

namespace SchnirelmannCounting

variable {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

/-- The Schnirelmann *predecessor*: the largest element of `A` that is `≤ m`
    (or `0` when there is none — harmless here since `0 ∈ A`). -/
def pred (A : Set ℕ) [DecidablePred (· ∈ A)] (m : ℕ) : ℕ := Nat.findGreatest (· ∈ A) m

lemma pred_le (m : ℕ) : pred A m ≤ m := Nat.findGreatest_le m

lemma pred_mem (hA0 : 0 ∈ A) (m : ℕ) : pred A m ∈ A :=
  Nat.findGreatest_spec (Nat.zero_le m) hA0

lemma le_pred {m a : ℕ} (ha : a ∈ A) (hle : a ≤ m) : a ≤ pred A m :=
  Nat.le_findGreatest hle ha

lemma pred_mono {m m' : ℕ} (h : m ≤ m') : pred A m ≤ pred A m' :=
  Nat.findGreatest_mono_right _ h

/-- Contiguity of the predecessor fibres: if `p m = a`, `a ∈ A`, and `a ≤ m' ≤ m`,
    then `p m' = a` as well. -/
lemma pred_contig {m m' a : ℕ} (ha : a ∈ A) (hpm : pred A m = a)
    (h1 : a ≤ m') (h2 : m' ≤ m) : pred A m' = a := by
  have hle : pred A m' ≤ pred A m := pred_mono h2
  have hge : a ≤ pred A m' := le_pred ha h1
  omega

/-- **Fibre-as-interval.** For `a ∈ A` with `a ≤ n`, the (nonempty) fibre
    `{m ∈ (0,n] : p m = a}` equals the integer interval `Icc (max 1 a) hi`, where
    `hi` is its maximum. -/
lemma fib_eq_Icc {n a : ℕ} (ha : a ∈ A) (han : a ≤ n)
    (hne : ((Ioc 0 n).filter (fun m => pred A m = a)).Nonempty) :
    (Ioc 0 n).filter (fun m => pred A m = a)
      = Icc (max 1 a) (((Ioc 0 n).filter (fun m => pred A m = a)).max' hne) := by
  set S := (Ioc 0 n).filter (fun m => pred A m = a) with hS
  set hi := S.max' hne with hhi
  have hhi_mem : hi ∈ S := S.max'_mem hne
  have hhi_props : (0 < hi ∧ hi ≤ n) ∧ pred A hi = a := by
    have := hhi_mem; rw [hS, mem_filter, mem_Ioc] at this; exact this
  apply Finset.ext
  intro m
  simp only [hS, mem_filter, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hm0, hmn⟩, hpm⟩
    refine ⟨?_, ?_⟩
    · -- max 1 a ≤ m
      have : a ≤ m := hpm ▸ pred_le m
      omega
    · -- m ≤ hi
      exact S.le_max' m (by rw [hS, mem_filter, mem_Ioc]; exact ⟨⟨hm0, hmn⟩, hpm⟩)
  · rintro ⟨hlo, hmhi⟩
    have ham : a ≤ m := le_trans (le_max_right 1 a) hlo
    have hm1 : 1 ≤ m := le_trans (le_max_left 1 a) hlo
    have hmn : m ≤ n := le_trans hmhi hhi_props.1.2
    exact ⟨⟨hm1, hmn⟩, pred_contig ha hhi_props.2 ham hmhi⟩


/-- Local restatement of the density estimate on an initial segment including `0`:
    since `0 ∈ B`, `#(B ∩ [0,K]) ≥ σB·K + 1`. -/
lemma card_Icc_filter_ge (hB0 : 0 ∈ B) (K : ℕ) :
    schnirelmannDensity B * K + 1 ≤ (#{b ∈ Icc 0 K | b ∈ B} : ℝ) := by
  have h0not : (0 : ℕ) ∉ {b ∈ Ioc 0 K | b ∈ B} := by simp
  have hsub : insert 0 {b ∈ Ioc 0 K | b ∈ B} ⊆ {b ∈ Icc 0 K | b ∈ B} := by
    intro x hx
    simp only [mem_insert, mem_filter, mem_Ioc, mem_Icc] at hx ⊢
    rcases hx with rfl | ⟨⟨_, h2⟩, h3⟩
    · exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hB0⟩
    · exact ⟨⟨Nat.zero_le _, h2⟩, h3⟩
  have hcard : #{b ∈ Ioc 0 K | b ∈ B} + 1 ≤ #{b ∈ Icc 0 K | b ∈ B} := by
    have := card_le_card hsub
    rwa [card_insert_of_notMem h0not] at this
  have hdens : schnirelmannDensity B * K ≤ (#{b ∈ Ioc 0 K | b ∈ B} : ℝ) :=
    schnirelmannDensity_mul_le_card_filter
  have hcast : (#{b ∈ Ioc 0 K | b ∈ B} : ℝ) + 1 ≤ (#{b ∈ Icc 0 K | b ∈ B} : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Shift/reindex: on the interval `Icc a hi`, counting `m` with `m − a ∈ B`
    equals counting `d ∈ Icc 0 (hi − a)` with `d ∈ B`. -/
lemma card_shift (a hi : ℕ) (hah : a ≤ hi) :
    (#{m ∈ Icc a hi | (m - a) ∈ B} : ℕ) = #{d ∈ Icc 0 (hi - a) | d ∈ B} := by
  have hmap : Icc a hi = (Icc 0 (hi - a)).map (addRightEmbedding a) := by
    rw [map_add_right_Icc]; congr 1 <;> omega
  rw [hmap, filter_map, card_map]
  congr 1
  apply filter_congr
  intro d _hd
  simp only [Function.comp, addRightEmbedding_apply, Nat.add_sub_cancel]


/-- **Per-fibre count, positive part.** For `a ∈ A` with `1 ≤ a ≤ n`, the number
    of `m ∈ (0,n]` with `p m = a` *and* `m − a ∈ B` is at least
    `σB · (L − 1) + 1`, where `L` is the size of the fibre `{m : p m = a}`.  The
    `+1` counts `a` itself (`a − a = 0 ∈ B`); the `σB·(L−1)` is Schnirelmann's
    density estimate on the reflected gap. -/
lemma fib_count_ge_pos (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) {n a : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (han : a ≤ n) :
    schnirelmannDensity B * ((#((Ioc 0 n).filter (fun m => pred A m = a)) : ℝ) - 1) + 1
      ≤ (#((Ioc 0 n).filter (fun m => pred A m = a ∧ (m - a) ∈ B)) : ℝ) := by
  -- the fibre is nonempty: `a` itself lies in it
  have hpa : pred A a = a := le_antisymm (pred_le a) (le_pred ha (le_refl a))
  have hane : a ∈ (Ioc 0 n).filter (fun m => pred A m = a) := by
    rw [mem_filter, mem_Ioc]; exact ⟨⟨ha1, han⟩, hpa⟩
  have hne : ((Ioc 0 n).filter (fun m => pred A m = a)).Nonempty := ⟨a, hane⟩
  set hi := ((Ioc 0 n).filter (fun m => pred A m = a)).max' hne with hhi
  have hfib := fib_eq_Icc ha han hne
  rw [← hhi] at hfib
  have hmax1a : max 1 a = a := by omega
  rw [hmax1a] at hfib
  -- `a ≤ hi`
  have hhi_mem : hi ∈ (Ioc 0 n).filter (fun m => pred A m = a) := max'_mem _ hne
  have hahi : a ≤ hi := by
    have : pred A hi = a := (mem_filter.1 hhi_mem).2
    calc a = pred A hi := this.symm
      _ ≤ hi := pred_le hi
  -- rewrite the ∧-filter as a filter of the fibre
  have hfilt : (Ioc 0 n).filter (fun m => pred A m = a ∧ (m - a) ∈ B)
      = ((Ioc 0 n).filter (fun m => pred A m = a)).filter (fun m => (m - a) ∈ B) := by
    rw [filter_filter]
  rw [hfilt, hfib]
  -- count on the interval via the shift
  have hcard : (#((Icc a hi).filter (fun m => (m - a) ∈ B)) : ℕ)
      = #{d ∈ Icc 0 (hi - a) | d ∈ B} := card_shift a hi hahi
  -- length of the fibre
  have hL : (#((Icc a hi)) : ℕ) = (hi - a) + 1 := by rw [Nat.card_Icc]; omega
  rw [hfib] at *
  -- assemble as reals
  have hbound := card_Icc_filter_ge (B := B) hB0 (hi - a)
  have hcardR : (#((Icc a hi).filter (fun m => (m - a) ∈ B)) : ℝ)
      = (#{d ∈ Icc 0 (hi - a) | d ∈ B} : ℝ) := by exact_mod_cast hcard
  have hLR : (#((Icc a hi)) : ℝ) = ((hi - a : ℕ) : ℝ) + 1 := by
    rw [hL]; push_cast; ring
  rw [hcardR, hLR]
  linarith [hbound]

/-- **Per-fibre count, `a = 0` part.** The `a = 0` fibre `{m ∈ (0,n] : p m = 0}`
    (the initial gap before the first positive element of `A`) contributes at
    least `σB · L` with `L` its size — here there is *no* `+1`, since `0` is not
    counted among `m ∈ (0,n]`. -/
lemma fib_count_ge_zero (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) {n : ℕ} :
    schnirelmannDensity B * (#((Ioc 0 n).filter (fun m => pred A m = 0)) : ℝ)
      ≤ (#((Ioc 0 n).filter (fun m => pred A m = 0 ∧ (m - 0) ∈ B)) : ℝ) := by
  have hσB0 : 0 ≤ schnirelmannDensity B := schnirelmannDensity_nonneg
  rcases (((Ioc 0 n).filter (fun m => pred A m = 0)).eq_empty_or_nonempty) with hemp | hne
  · rw [hemp]
    have hz : (Ioc 0 n).filter (fun m => pred A m = 0 ∧ (m - 0) ∈ B) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro m hm
      have hmem : m ∈ (Ioc 0 n).filter (fun m => pred A m = 0) := by
        rw [mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.1⟩
      rw [hemp] at hmem; exact absurd hmem (notMem_empty m)
    rw [hz]; simp
  · set hi := ((Ioc 0 n).filter (fun m => pred A m = 0)).max' hne with hhi
    have hfib := fib_eq_Icc (A := A) hA0 (Nat.zero_le n) hne
    rw [← hhi] at hfib
    have hmax10 : max 1 0 = 1 := by norm_num
    rw [hmax10] at hfib
    -- rewrite the ∧-filter and simplify `m - 0 = m`
    have hfilt : (Ioc 0 n).filter (fun m => pred A m = 0 ∧ (m - 0) ∈ B)
        = ((Ioc 0 n).filter (fun m => pred A m = 0)).filter (fun m => m ∈ B) := by
      rw [filter_filter]; apply filter_congr; intro m _; simp
    rw [hfilt, hfib]
    -- `Icc 1 hi = Ioc 0 hi`, so the count is `#(B ∩ (0,hi])`
    have hIcc_Ioc : (Icc 1 hi).filter (fun m => m ∈ B) = {b ∈ Ioc 0 hi | b ∈ B} := by
      apply Finset.ext; intro m; simp only [mem_filter, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hB⟩; exact ⟨⟨h1, h2⟩, hB⟩
      · rintro ⟨⟨h1, h2⟩, hB⟩; exact ⟨⟨h1, h2⟩, hB⟩
    rw [hIcc_Ioc]
    -- length of the fibre `Icc 1 hi` is `hi`
    have hL : (#(Icc 1 hi) : ℕ) = hi := by rw [Nat.card_Icc]; omega
    have hLR : (#(Icc 1 hi) : ℝ) = (hi : ℝ) := by rw [hL]
    rw [hLR]
    have hdens : schnirelmannDensity B * hi ≤ (#{b ∈ Ioc 0 hi | b ∈ B} : ℝ) :=
      schnirelmannDensity_mul_le_card_filter
    linarith [hdens]

/-- **Schnirelmann's gap-counting inequality (†).**  For `0 ∈ A`, `0 ∈ B`, and any
    `C ⊇ A + B`, the count of `C`-elements in `(0,n]` satisfies

      `C(n) ≥ A(n) + σB · (n − A(n))`.

    This is the finite combinatorial core of Schnirelmann's inequality
    `σ(A ⊕ B) ≥ σA + σB − σA·σB`; combined with the inf-extraction layer
    (`SchnirelmannInequality.schnirelmannDensity_add_le_of_countingBound`) it
    yields the full density inequality (an open Mathlib TODO). -/
theorem counting_bound (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) {C : Set ℕ} [DecidablePred (· ∈ C)]
    (hC : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) (n : ℕ) (hn : 0 < n) :
    (#{a ∈ Ioc 0 n | a ∈ A} : ℝ)
      + schnirelmannDensity B * ((n : ℝ) - #{a ∈ Ioc 0 n | a ∈ A})
    ≤ (#{c ∈ Ioc 0 n | c ∈ C} : ℝ) := by
  classical
  set M := (Ioc 0 n).filter (fun m => (m - pred A m) ∈ B) with hM
  set Afin := (Ioc 0 n).filter (fun a => a ∈ A) with hAfin
  set Afin0 := (Icc 0 n).filter (fun a => a ∈ A) with hAfin0
  -- `M ⊆ C ∩ (0,n]`
  have hMC : M ⊆ {c ∈ Ioc 0 n | c ∈ C} := by
    intro m hm
    rw [hM, mem_filter] at hm
    obtain ⟨hmIoc, hmB⟩ := hm
    rw [mem_filter]
    refine ⟨hmIoc, ?_⟩
    have hpm : pred A m ∈ A := pred_mem hA0 m
    have hsum : pred A m + (m - pred A m) = m := Nat.add_sub_cancel' (pred_le m)
    have := hC (pred A m) hpm (m - pred A m) hmB
    rwa [hsum] at this
  have hMcard : (M.card : ℝ) ≤ (#{c ∈ Ioc 0 n | c ∈ C} : ℝ) := by
    have := card_le_card hMC; exact_mod_cast this
  -- fibrewise decomposition of `M` and of `(0,n]` over predecessor values in `Afin0`
  have hfibM : ∀ m ∈ M, pred A m ∈ Afin0 := by
    intro m hm
    rw [hM, mem_filter, mem_Ioc] at hm
    rw [hAfin0, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, le_trans (pred_le m) hm.1.2⟩, pred_mem hA0 m⟩
  have hfibI : ∀ m ∈ Ioc 0 n, pred A m ∈ Afin0 := by
    intro m hm
    rw [mem_Ioc] at hm
    rw [hAfin0, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, le_trans (pred_le m) hm.2⟩, pred_mem hA0 m⟩
  have hMsum : M.card = ∑ a ∈ Afin0, (M.filter (fun m => pred A m = a)).card :=
    card_eq_sum_card_fiberwise hfibM
  have hIsum : (Ioc 0 n).card = ∑ a ∈ Afin0, ((Ioc 0 n).filter (fun m => pred A m = a)).card :=
    card_eq_sum_card_fiberwise hfibI
  -- identify each `M`-fibre with the `∧`-filtered fibre used by the per-fibre lemmas
  have hgc : ∀ a, (M.filter (fun m => pred A m = a)).card
      = ((Ioc 0 n).filter (fun m => pred A m = a ∧ (m - a) ∈ B)).card := by
    intro a
    congr 1
    rw [hM, filter_filter]
    apply Finset.ext; intro m
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hIoc, hB, hp⟩; exact ⟨hIoc, hp, by rw [← hp]; exact hB⟩
    · rintro ⟨hIoc, hp, hB⟩; exact ⟨hIoc, by rw [hp]; exact hB, hp⟩
  -- abbreviations for the fibre `B`-count and fibre length
  set g : ℕ → ℕ := fun a => ((Ioc 0 n).filter (fun m => pred A m = a ∧ (m - a) ∈ B)).card with hg
  set L : ℕ → ℕ := fun a => ((Ioc 0 n).filter (fun m => pred A m = a)).card with hL
  have hMsum' : (M.card : ℝ) = ∑ a ∈ Afin0, (g a : ℝ) := by
    rw [hMsum]; push_cast; apply Finset.sum_congr rfl; intro a _; rw [hgc a]
  have hIsum' : (n : ℝ) = ∑ a ∈ Afin0, (L a : ℝ) := by
    have hIcard : (Ioc 0 n).card = n := by rw [Nat.card_Ioc]; omega
    rw [hIcard] at hIsum
    rw [hIsum]; push_cast; rfl
  -- split off the `a = 0` fibre
  have h0notAfin : (0 : ℕ) ∉ Afin := by rw [hAfin, mem_filter, mem_Ioc]; rintro ⟨⟨h, _⟩, _⟩; omega
  have hAfin0_eq : Afin0 = insert 0 Afin := by
    rw [hAfin0, hAfin]
    apply Finset.ext; intro a
    simp only [mem_insert, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, ha⟩
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hpos, h2⟩, ha⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, ha⟩)
      · exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hA0⟩
      · exact ⟨⟨Nat.zero_le _, h2⟩, ha⟩
  -- per-fibre lower bounds
  have hzero : schnirelmannDensity B * (L 0 : ℝ) ≤ (g 0 : ℝ) := by
    have := fib_count_ge_zero (A := A) (B := B) hA0 hB0 (n := n); simpa [hg, hL] using this
  have hpos : ∀ a ∈ Afin, schnirelmannDensity B * ((L a : ℝ) - 1) + 1 ≤ (g a : ℝ) := by
    intro a ha
    rw [hAfin, mem_filter, mem_Ioc] at ha
    have := fib_count_ge_pos (A := A) (B := B) hA0 hB0 ha.2 ha.1.1 ha.1.2
    simpa [hg, hL] using this
  -- assemble
  set σB := schnirelmannDensity B with hσB
  have hAn : (#{a ∈ Ioc 0 n | a ∈ A} : ℝ) = (Afin.card : ℝ) := by rw [hAfin]
  -- sum of the per-fibre lower bounds equals the target
  have hLsplit : (n : ℝ) = (L 0 : ℝ) + ∑ a ∈ Afin, (L a : ℝ) := by
    rw [hIsum', hAfin0_eq, Finset.sum_insert h0notAfin]
  have hexp : (∑ a ∈ Afin, (σB * ((L a : ℝ) - 1) + 1))
      = σB * (∑ a ∈ Afin, (L a : ℝ)) - σB * (Afin.card : ℝ) + (Afin.card : ℝ) := by
    have e2 : (∑ a ∈ Afin, σB * ((L a : ℝ) - 1)) = σB * (∑ a ∈ Afin, ((L a : ℝ) - 1)) :=
      (Finset.mul_sum _ _ _).symm
    have e3 : (∑ a ∈ Afin, ((L a : ℝ) - 1)) = (∑ a ∈ Afin, (L a : ℝ)) - (Afin.card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have e4 : (∑ a ∈ Afin, (1 : ℝ)) = (Afin.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib, e2, e3, e4]; ring
  have hEq : σB * (L 0 : ℝ) + ∑ a ∈ Afin, (σB * ((L a : ℝ) - 1) + 1)
      = (Afin.card : ℝ) + σB * ((n : ℝ) - (Afin.card : ℝ)) := by
    rw [hexp, hLsplit]; ring
  have hgsum_ge : (Afin.card : ℝ) + σB * ((n : ℝ) - (Afin.card : ℝ))
      ≤ ∑ a ∈ Afin0, (g a : ℝ) := by
    rw [← hEq, hAfin0_eq, Finset.sum_insert h0notAfin]
    have hsle : ∑ a ∈ Afin, (σB * ((L a : ℝ) - 1) + 1) ≤ ∑ a ∈ Afin, (g a : ℝ) :=
      Finset.sum_le_sum hpos
    linarith [hzero, hsle]
  rw [hAn]
  calc (Afin.card : ℝ) + σB * ((n : ℝ) - (Afin.card : ℝ))
      ≤ ∑ a ∈ Afin0, (g a : ℝ) := hgsum_ge
    _ = (M.card : ℝ) := hMsum'.symm
    _ ≤ (#{c ∈ Ioc 0 n | c ∈ C} : ℝ) := hMcard

/-- **Schnirelmann's inequality.**  For `0 ∈ A`, `0 ∈ B`, and any `C ⊇ A + B`,

      `σ(A) + σ(B) − σ(A)·σ(B) ≤ σ(C)`.

    This is the subadditivity-of-deficiency estimate `1 − σC ≤ (1 − σA)(1 − σB)`,
    an open TODO in `Mathlib/Combinatorics/Schnirelmann.lean` ("Prove Schnirelmann's
    theorem and Mann's theorem on the subadditivity of this density"), and the sole
    remaining gap for the `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean`.

    The combinatorial core is `counting_bound` above; the infimum-extraction step
    here divides the counting bound by `n`, replaces `A(n)/n` by its lower bound
    `σA` (valid as `1 − σB ≥ 0`), and takes the infimum over `n`. -/
theorem schnirelmann_inequality (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) {C : Set ℕ}
    [DecidablePred (· ∈ C)] (hC : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) :
    schnirelmannDensity A + schnirelmannDensity B
        - schnirelmannDensity A * schnirelmannDensity B ≤ schnirelmannDensity C := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  set a : ℝ := (#{a ∈ Ioc 0 n | a ∈ A} : ℝ) with ha
  set c : ℝ := (#{c ∈ Ioc 0 n | c ∈ C} : ℝ) with hc
  have hn0 : n ≠ 0 := hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hσB0 : 0 ≤ schnirelmannDensity B := schnirelmannDensity_nonneg
  have hσB1 : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  have hσA_div : schnirelmannDensity A ≤ a / n := by rw [ha]; exact schnirelmannDensity_le_div hn0
  have hσA_mul : schnirelmannDensity A * n ≤ a := by
    calc schnirelmannDensity A * n ≤ (a / n) * n :=
            mul_le_mul_of_nonneg_right hσA_div (le_of_lt hnpos)
      _ = a := by field_simp
  have hcn := counting_bound hA0 hB0 hC n hn
  rw [← ha, ← hc] at hcn
  have hfac : (1 : ℝ) - schnirelmannDensity B ≥ 0 := by linarith
  have hstep : schnirelmannDensity A * n * (1 - schnirelmannDensity B)
      ≤ a * (1 - schnirelmannDensity B) := mul_le_mul_of_nonneg_right hσA_mul hfac
  have hkey : (schnirelmannDensity A + schnirelmannDensity B
      - schnirelmannDensity A * schnirelmannDensity B) * n ≤ c := by
    nlinarith [hcn, hstep, hnpos]
  rw [le_div_iff₀ hnpos]; linarith [hkey]

end SchnirelmannCounting
