/-
  Erdős Probabilistic Lower Bound for Diagonal Ramsey Numbers (Erdős 1947)

  The first application of the probabilistic method to Ramsey theory.

  Main result (`erdos_ramsey_criterion`): if
      `2 * (n.choose k) < 2 ^ (k.choose 2)`
  then there is a symmetric, irreflexive 2-colouring of the edges of the
  complete graph `K_n` with **no** monochromatic `k`-clique (neither all-red
  nor all-blue).  Equivalently the diagonal Ramsey number satisfies
  `R(k, k) > n`.

  The proof is the *counting* form of the first moment method.  Among the
  `2 ^ (#edges)` colourings, the number that are monochromatic on a fixed
  `k`-clique is `2 * 2 ^ (#edges − C(k,2))`.  A union bound over the `C(n,k)`
  cliques leaves a colouring avoiding all of them whenever the displayed
  inequality holds.  **No measure theory is required** — the whole argument
  lives in a finite probability (= counting) space, so it is fully
  machine-checked with no axioms.

  This de-axiomatizes `erdos_probabilistic_lower_bound` from
  `Proofs/RamseyR4kExtensions.lean`, where it had been stated as an `axiom`.

  Tags: combinatorics, ramsey-theory, probabilistic-method, first-moment-method
-/

import Mathlib

namespace ErdosRamsey

open Finset

/-!
## Part I.  The abstract counting (first-moment) lemma

Work over an arbitrary finite type `E` of "edges".  A colouring is a function
`c : E → Bool`.  Given a family `bad` of edge-sets, if the total count of
colourings that are *constant* on some member of `bad` is strictly below the
number of colourings, a colouring avoiding all of them exists.
-/

/-- The number of colourings `c : E → Bool` that are identically `b` on a
finite set `W` of edges is `2 ^ (|E| − |W|)`: the `|W|` coordinates of `W` are
pinned, the remaining `|E| − |W|` are free. -/
lemma card_const_on {E : Type*} [Fintype E] [DecidableEq E]
    (W : Finset E) (b : Bool) :
    (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = b)).card
      = 2 ^ (Fintype.card E - W.card) := by
  classical
  have hset : (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = b))
      = Fintype.piFinset (fun e => if e ∈ W then {b} else (univ : Finset Bool)) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hc e
      by_cases he : e ∈ W
      · simp [he, hc e he]
      · simp [he]
    · intro hc e he
      have := hc e
      simp only [he, if_true, mem_singleton] at this
      exact this
  rw [hset, Fintype.card_piFinset]
  have hprod : (∏ e : E, (if e ∈ W then ({b} : Finset Bool) else univ).card)
      = ∏ e : E, 2 ^ (if e ∈ W then 0 else 1) := by
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ W <;> simp [he]
  rw [hprod, Finset.prod_pow_eq_pow_sum]
  congr 1
  -- ∑ e, (if e ∈ W then 0 else 1) = |E| − |W|
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
      mul_one, Finset.filter_not, Finset.card_univ_diff, Finset.filter_mem_eq_inter,
      Finset.univ_inter]

/-- **First moment / counting lemma.**  If the number of colourings that are
constant on some `W ∈ bad`, bounded by `∑_{W ∈ bad} 2·2^(|E|−|W|)`, is below
`2^|E|`, then some colouring is non-constant on every `W ∈ bad`. -/
theorem exists_avoiding_coloring {E : Type*} [Fintype E] [DecidableEq E]
    (bad : Finset (Finset E))
    (hbound : (∑ W ∈ bad, 2 * 2 ^ (Fintype.card E - W.card)) < 2 ^ Fintype.card E) :
    ∃ c : E → Bool, ∀ W ∈ bad, ¬ ∃ b, ∀ e ∈ W, c e = b := by
  classical
  set badC : Finset (E → Bool) :=
    bad.biUnion (fun W => univ.filter (fun c => ∃ b, ∀ e ∈ W, c e = b)) with hbadC
  have hcard_badC : badC.card < 2 ^ Fintype.card E := by
    calc badC.card
        ≤ ∑ W ∈ bad, (univ.filter (fun c : E → Bool => ∃ b, ∀ e ∈ W, c e = b)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ W ∈ bad, 2 * 2 ^ (Fintype.card E - W.card) := by
          apply Finset.sum_le_sum
          intro W _
          have hsub : (univ.filter (fun c : E → Bool => ∃ b, ∀ e ∈ W, c e = b))
              ⊆ (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = true))
                ∪ (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = false)) := by
            intro c hc
            simp only [mem_filter, mem_univ, true_and, mem_union] at hc ⊢
            obtain ⟨b, hb⟩ := hc
            cases b
            · right; exact hb
            · left; exact hb
          calc (univ.filter (fun c : E → Bool => ∃ b, ∀ e ∈ W, c e = b)).card
              ≤ ((univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = true))
                  ∪ (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = false))).card :=
                Finset.card_le_card hsub
            _ ≤ (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = true)).card
                + (univ.filter (fun c : E → Bool => ∀ e ∈ W, c e = false)).card :=
                Finset.card_union_le _ _
            _ = 2 * 2 ^ (Fintype.card E - W.card) := by
                rw [card_const_on, card_const_on]; ring
      _ < 2 ^ Fintype.card E := hbound
  have hne : badC ≠ univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at hcard_badC
    exact lt_irrefl _ hcard_badC
  have hss : badC ⊂ univ := Finset.ssubset_univ_iff.mpr hne
  obtain ⟨c, _, hc⟩ := Finset.exists_of_ssubset hss
  refine ⟨c, ?_⟩
  intro W hW hcon
  apply hc
  rw [hbadC, Finset.mem_biUnion]
  exact ⟨W, hW, by simp only [mem_filter, mem_univ, true_and]; exact hcon⟩

/-!
## Part II.  The Ramsey specialisation

Specialise `E := Sym2 (Fin n)` (unordered pairs of vertices; the diagonal
"loops" are harmless and cancel).  The edge set of a `k`-subset `S` is
`S.offDiag.image Sym2.mk`, which has exactly `C(k,2)` elements by
`Finset.card_image_offDiag`.
-/

/-- The Erdős counting criterion in `Sym2` form: if `2·C(n,k) < 2^C(k,2)` then
some 2-colouring of the pairs of `Fin n` is monochromatic on no `k`-clique. -/
theorem exists_good_coloring_sym2 (n k : ℕ)
    (h : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Sym2 (Fin n) → Bool, ∀ S : Finset (Fin n), S.card = k →
      ¬ ∃ b, ∀ e ∈ S.offDiag.image Sym2.mk, c e = b := by
  classical
  set E := Sym2 (Fin n)
  set edgesOf : Finset (Fin n) → Finset E := fun S => S.offDiag.image Sym2.mk with hedges
  set bad : Finset (Finset E) := (univ.powersetCard k).image edgesOf with hbad
  -- Every W ∈ bad is the edge set of some k-clique, so has card C(k,2).
  have hWcard : ∀ W ∈ bad, W.card = k.choose 2 := by
    intro W hW
    rw [hbad, Finset.mem_image] at hW
    obtain ⟨S, hS, rfl⟩ := hW
    rw [Finset.mem_powersetCard] at hS
    show #(S.offDiag.image Sym2.mk) = k.choose 2
    rw [Sym2.card_image_offDiag, hS.2]
  -- The union bound.
  have hbound : (∑ W ∈ bad, 2 * 2 ^ (Fintype.card E - W.card)) < 2 ^ Fintype.card E := by
    rcases bad.eq_empty_or_nonempty with he | hbne
    · rw [he, Finset.sum_empty]; positivity
    · obtain ⟨W₀, hW₀⟩ := hbne
      -- C(k,2) ≤ |E| since W₀ ⊆ univ has card C(k,2)
      have hCM : k.choose 2 ≤ Fintype.card E := by
        have h1 : W₀.card ≤ Fintype.card E := Finset.card_le_univ W₀
        rw [hWcard W₀ hW₀] at h1; exact h1
      -- rewrite the sum with constant summand
      rw [Finset.sum_congr rfl (fun W hW => by rw [hWcard W hW])]
      rw [Finset.sum_const, smul_eq_mul]
      -- bad.card ≤ n.choose k
      have hbc : bad.card ≤ n.choose k := by
        rw [hbad]
        calc (Finset.image edgesOf (univ.powersetCard k)).card
            ≤ (univ.powersetCard k).card := Finset.card_image_le
          _ = n.choose k := by rw [Finset.card_powersetCard, Finset.card_univ,
                Fintype.card_fin]
      calc bad.card * (2 * 2 ^ (Fintype.card E - k.choose 2))
          ≤ n.choose k * (2 * 2 ^ (Fintype.card E - k.choose 2)) := by gcongr
        _ = (2 * n.choose k) * 2 ^ (Fintype.card E - k.choose 2) := by ring
        _ < 2 ^ (k.choose 2) * 2 ^ (Fintype.card E - k.choose 2) :=
            mul_lt_mul_of_pos_right h (pow_pos (by norm_num) _)
        _ = 2 ^ Fintype.card E := by
            rw [← pow_add, Nat.add_sub_cancel' hCM]
  -- apply the abstract lemma
  obtain ⟨c, hc⟩ := exists_avoiding_coloring bad hbound
  refine ⟨c, ?_⟩
  intro S hS
  apply hc
  rw [hbad, Finset.mem_image]
  exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩, rfl⟩

/-!
## Part III.  The classical statement

Repackage in terms of a symmetric, irreflexive colouring
`color : Fin n → Fin n → Bool`, matching exactly the (previously axiomatized)
`erdos_probabilistic_lower_bound`.
-/

/-- **Erdős (1947), counting form.**  If `2·C(n,k) < 2^C(k,2)` then there is a
symmetric, irreflexive 2-colouring of `K_n` with no monochromatic `k`-clique of
either colour.  Hence the diagonal Ramsey number satisfies `R(k,k) > n`. -/
theorem erdos_ramsey_criterion (n k : ℕ)
    (h : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ color : Fin n → Fin n → Bool,
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false)) := by
  classical
  obtain ⟨c, hc⟩ := exists_good_coloring_sym2 n k h
  refine ⟨fun x y => if x = y then false else c (Sym2.mk (x, y)), ?_, ?_, ?_, ?_⟩
  · -- symmetric
    intro x y
    show (if x = y then false else c (Sym2.mk (x, y)))
        = (if y = x then false else c (Sym2.mk (y, x)))
    by_cases hxy : x = y
    · rw [hxy]
    · rw [if_neg hxy, if_neg (Ne.symm hxy), Sym2.eq_swap]
  · -- irreflexive
    intro x
    show (if x = x then false else c (Sym2.mk (x, x))) = false
    rw [if_pos rfl]
  · -- no all-true k-clique
    intro s hs hmono
    apply hc s hs
    refine ⟨true, ?_⟩
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := he
    rw [Finset.mem_offDiag] at hxy
    obtain ⟨hx, hy, hne⟩ := hxy
    have hm := hmono x y hx hy hne
    simp only [if_neg hne] at hm
    exact hm
  · -- no all-false k-clique
    intro s hs hmono
    apply hc s hs
    refine ⟨false, ?_⟩
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := he
    rw [Finset.mem_offDiag] at hxy
    obtain ⟨hx, hy, hne⟩ := hxy
    have hm := hmono x y hx hy hne
    simp only [if_neg hne] at hm
    exact hm

/-!
## Part IV.  The classical `R(k,k) > 2^(k/2)` bound

The Erdős criterion `2·C(n,k) < 2^C(k,2)` is implied by `n ≤ 2^(⌊k/2⌋)` once
`k ≥ 3`.  The elementary estimate combines `k! · C(n,k) = n^{falling k} ≤ n^k`
with the exponent comparison `⌊k/2⌋·k ≤ C(k,2) + ⌊k/2⌋` and the factorial
growth `2^{⌊k/2⌋+1} < k!`.
-/

/-- Elementary numeric estimate: for `k ≥ 3` and `n ≤ 2^⌊k/2⌋`, the Erdős
counting criterion `2·C(n,k) < 2^C(k,2)` holds. -/
theorem erdos_diagonal_numeric (n k : ℕ) (hk : 3 ≤ k) (hn : n ≤ 2 ^ (k / 2)) :
    2 * n.choose k < 2 ^ (k.choose 2) := by
  -- k! · C(n,k) ≤ n^k
  have hfac : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  -- n^k ≤ 2^(⌊k/2⌋·k)
  have hpow : n ^ k ≤ 2 ^ ((k / 2) * k) := by
    calc n ^ k ≤ (2 ^ (k / 2)) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ ((k / 2) * k) := by rw [← pow_mul]
  -- 2^(⌊k/2⌋+1) < k!
  have hC2 : 2 ^ (k / 2 + 1) < k.factorial := by
    have step : ∀ j, 3 ≤ j → 2 ^ (j - 1) < j.factorial := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => decide
      | succ m hm ih =>
          have e : 2 ^ m = 2 * 2 ^ (m - 1) := by
            conv_lhs => rw [show m = (m - 1) + 1 from by omega]
            rw [pow_succ']
          rw [Nat.add_sub_cancel, Nat.factorial_succ]
          calc 2 ^ m = 2 * 2 ^ (m - 1) := e
            _ < 2 * m.factorial := by omega
            _ ≤ (m + 1) * m.factorial := Nat.mul_le_mul (by omega) (le_refl _)
    calc 2 ^ (k / 2 + 1) ≤ 2 ^ (k - 1) := by
          apply Nat.pow_le_pow_right (by norm_num); omega
      _ < k.factorial := step k hk
  -- ⌊k/2⌋·k ≤ C(k,2) + ⌊k/2⌋
  have hchoose : k * (k - 1) / 2 = k.choose 2 := (Nat.choose_two_right k).symm
  have hC1' : (k - 1) * (k / 2) ≤ k * (k - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (k - 1) * (k / 2) * 2 = (k - 1) * (2 * (k / 2)) := by ring
      _ ≤ (k - 1) * k := by gcongr; omega
      _ = k * (k - 1) := by ring
  have expand : (k / 2) * k = (k - 1) * (k / 2) + k / 2 := by
    have h1 : (k - 1) + 1 = k := by omega
    calc (k / 2) * k = (k / 2) * ((k - 1) + 1) := by rw [h1]
      _ = (k / 2) * (k - 1) + k / 2 := by ring
      _ = (k - 1) * (k / 2) + k / 2 := by rw [Nat.mul_comm (k / 2) (k - 1)]
  have hC1 : (k / 2) * k ≤ k.choose 2 + k / 2 := by
    rw [expand, ← hchoose]
    exact Nat.add_le_add_right hC1' (k / 2)
  -- Step C : 2·2^(⌊k/2⌋·k) < k!·2^C(k,2)
  have hStepC : 2 * 2 ^ ((k / 2) * k) < k.factorial * 2 ^ (k.choose 2) := by
    calc 2 * 2 ^ ((k / 2) * k) = 2 ^ ((k / 2) * k + 1) := by rw [pow_succ']
      _ ≤ 2 ^ (k.choose 2 + k / 2 + 1) := by
          apply Nat.pow_le_pow_right (by norm_num); omega
      _ = 2 ^ (k.choose 2) * 2 ^ (k / 2 + 1) := by ring
      _ < 2 ^ (k.choose 2) * k.factorial := mul_lt_mul_of_pos_left hC2 (pow_pos (by norm_num) _)
      _ = k.factorial * 2 ^ (k.choose 2) := by ring
  -- assemble: k! · (2·C(n,k)) < k! · 2^C(k,2)
  have chain : k.factorial * (2 * n.choose k) < k.factorial * 2 ^ (k.choose 2) := by
    calc k.factorial * (2 * n.choose k) = 2 * (k.factorial * n.choose k) := by ring
      _ ≤ 2 * n ^ k := by gcongr
      _ ≤ 2 * 2 ^ ((k / 2) * k) := by gcongr
      _ < k.factorial * 2 ^ (k.choose 2) := hStepC
  exact lt_of_mul_lt_mul_left chain (Nat.zero_le _)

/-- **Erdős (1947).**  `R(k, k) > 2^⌊k/2⌋`:  for `k ≥ 3` and any `n ≤ 2^⌊k/2⌋`
there is a symmetric, irreflexive 2-colouring of `K_n` with no monochromatic
`k`-clique of either colour.  This is the exact statement that was previously
the `axiom erdos_probabilistic_lower_bound` in `Proofs/RamseyR4kExtensions.lean`,
now proved with no axioms. -/
theorem erdos_probabilistic_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∀ n : ℕ, n ≤ 2 ^ (k / 2) →
    ∃ color : Fin n → Fin n → Bool,
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ s : Finset (Fin n), s.card = k →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false)) :=
  fun n hn => erdos_ramsey_criterion n k (erdos_diagonal_numeric n k hk hn)

end ErdosRamsey
