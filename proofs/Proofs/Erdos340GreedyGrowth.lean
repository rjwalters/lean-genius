/-
# Erdős Problem #340 (oq-01): The cubic growth bound for the greedy Sidon sequence

The parent file `Erdos340GreedySidon.lean` **constructs** the greedy (Mian–Chowla)
Sidon sequence `aₙ` as an explicit `Nat.find` recursion and discharges the three former
existence axioms.  What remained only as a *comment-level proof sketch* there was the
**N^(1/3) lower bound** — the quantitative heart of Erdős #340's known direction.

This file formalizes the crux of that sketch: the **global covering argument** giving the
cubic upper bound on the sequence values,

  `aₙ ≤ (n+1) + (n+1)³`            (`greedySidonSeq_le_cubic`)

which is exactly the bound whose cube-root inversion yields `|A ∩ [1,N]| = Ω(N^(1/3))`.

## The argument

For a Sidon set `A` and a value `m` strictly above every element of `A`, inserting `m`
breaks the Sidon property **iff** `m = c + d - a` for some `a, c, d ∈ A` (the only
surviving collision once `m` exceeds `max A`).  Collect these *forbidden* values into
`forbidden A`; there are at most `|A|³` of them.

The greedy step picks the **least** valid `m`, so every integer `p` skipped between two
consecutive greedy terms is forbidden against the prefix placed so far — and `forbidden`
is monotone, so `p` is forbidden against the full set `Aₙ`.  Hence every `p ∈ [1, aₙ]` is
either an element of `Aₙ` or forbidden against `Aₙ`:

  `aₙ = |[1, aₙ]| ≤ |Aₙ| + |forbidden Aₙ| ≤ (n+1) + (n+1)³`.

The crux necessary lemma (`not_sidon_insert_forbidden`) is the contrapositive of the
parent's `sidon_insert_of_large`, which already carries the hard 6-way collision case
analysis — so here it is a one-line `by_contra`.

NOTE on the `1/3`-vs-`1/2` gap: the cubic bound is the *known* result.  Improving the
exponent past `1/3` for the greedy sequence is the OPEN part of Erdős #340 and is **not**
attempted here.
-/
import Proofs.Erdos340GreedySidon

namespace Erdos340

open Finset

/- ## Forbidden values -/

/-- The **forbidden set** of `A`: all values `c + d - a` with `a, c, d ∈ A`.  When `m`
exceeds every element of `A`, `insert m A` stays Sidon unless `m` lands in `forbidden A`
(see `not_sidon_insert_forbidden`). -/
def forbidden (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A ×ˢ A).image (fun p => p.2.1 + p.2.2 - p.1)

/-- There are at most `|A|³` forbidden values: each is the image of a triple `(a, c, d)`. -/
theorem forbidden_card_le (A : Finset ℕ) : (forbidden A).card ≤ A.card ^ 3 := by
  calc (forbidden A).card ≤ (A ×ˢ A ×ˢ A).card := Finset.card_image_le
    _ = A.card ^ 3 := by rw [Finset.card_product, Finset.card_product]; ring

/-- `forbidden` is monotone: a larger ground set forbids at least as much. -/
theorem forbidden_mono {A B : Finset ℕ} (h : A ⊆ B) : forbidden A ⊆ forbidden B := by
  apply Finset.image_subset_image
  exact Finset.product_subset_product h (Finset.product_subset_product h h)

/-- **Necessary direction** (crux).  If `m` is above every element of the Sidon set `A`
and `insert m A` is *not* Sidon, then `m` is a forbidden value `c + d - a`.

This is the contrapositive of `sidon_insert_of_large`, which already contains the hard
case analysis. -/
theorem not_sidon_insert_forbidden {A : Finset ℕ} (hA : IsSidon A) {m : ℕ}
    (hm : ∀ a ∈ A, a < m) (hbad : ¬ IsSidon (insert m A)) :
    m ∈ forbidden A := by
  by_contra hmem
  apply hbad
  apply sidon_insert_of_large hA hm
  intro a ha c hc d hd heq
  -- heq : m + a = c + d ;  goal : False  (m + a ≠ c + d)
  apply hmem
  rw [forbidden, Finset.mem_image]
  refine ⟨(a, c, d), ?_, ?_⟩
  · simp only [Finset.mem_product]
    exact ⟨ha, hc, hd⟩
  · show c + d - a = m
    omega

/- ## Greedy-sequence bookkeeping -/

/-- Every greedy term lies in its own prefix set. -/
theorem greedySidonSeq_mem (n : ℕ) : greedySidonSeq n ∈ greedySeqSet n := by
  rw [greedySeqSet_eq_image]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- `aₙ` is the largest element of the prefix `Aₙ` (the sequence is strictly increasing). -/
theorem greedySeqSet_le {n x : ℕ} (hx : x ∈ greedySeqSet n) : x ≤ greedySidonSeq n := by
  rw [greedySeqSet_eq_image, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  exact greedySidonSeq_strictMono.monotone (by omega)

/-- The prefix set has exactly `n + 1` elements (strict monotonicity ⇒ injectivity). -/
theorem greedySeqSet_card (n : ℕ) : (greedySeqSet n).card = n + 1 := by
  rw [greedySeqSet_eq_image,
      Finset.card_image_of_injective _ greedySidonSeq_strictMono.injective,
      Finset.card_range]

/-- Prefixes grow by insertion. -/
theorem greedySeqSet_subset_succ (n : ℕ) : greedySeqSet n ⊆ greedySeqSet (n + 1) := by
  have h : greedySeqSet (n + 1)
      = insert (greedySidonSeq (n + 1)) (greedySeqSet n) := rfl
  rw [h]
  exact Finset.subset_insert _ _

/-- **Greedy minimality.**  Any value strictly between consecutive greedy terms was
*skipped*: inserting it into the prefix would have broken the Sidon property. -/
theorem greedy_skip_not_sidon {n p : ℕ}
    (h1 : greedySidonSeq n < p) (h2 : p < greedySidonSeq (n + 1)) :
    ¬ IsSidon (insert p (greedySeqSet n)) := by
  classical
  have hSidon : IsSidon (greedySeqSet n) := greedySeqSet_isSidon n
  have hex : ∃ m, greedySidonSeq n < m ∧ IsSidon (insert m (greedySeqSet n)) := by
    obtain ⟨m, hbm, _, hm⟩ := sidon_exists_extension (greedySeqSet n) hSidon (greedySidonSeq n)
    exact ⟨m, hbm, hm⟩
  have hnext : greedySidonSeq (n + 1) = nextSidon (greedySeqSet n) (greedySidonSeq n) := rfl
  have hval : nextSidon (greedySeqSet n) (greedySidonSeq n) = Nat.find hex := by
    unfold nextSidon; exact dif_pos hex
  rw [hnext, hval] at h2
  have hmin := Nat.find_min hex h2
  push_neg at hmin
  exact hmin h1

/- ## The covering bound -/

/-- **Global covering.**  Every integer `p ∈ [1, aₙ]` is either a greedy element or a
forbidden value against the *full* prefix `Aₙ`. -/
theorem greedy_covering (n : ℕ) :
    ∀ p, 1 ≤ p → p ≤ greedySidonSeq n →
      p ∈ greedySeqSet n ∨ p ∈ forbidden (greedySeqSet n) := by
  induction n with
  | zero =>
    intro p hp1 hp2
    have h0 : greedySidonSeq 0 = 1 := rfl
    rw [h0] at hp2
    have hp : p = 1 := by omega
    left
    have hset : greedySeqSet 0 = {1} := rfl
    rw [hp, hset]
    exact Finset.mem_singleton_self 1
  | succ n ih =>
    intro p hp1 hp2
    by_cases hle : p ≤ greedySidonSeq n
    · rcases ih p hp1 hle with hin | hforb
      · exact Or.inl (greedySeqSet_subset_succ n hin)
      · exact Or.inr (forbidden_mono (greedySeqSet_subset_succ n) hforb)
    · push_neg at hle
      by_cases hpeq : p = greedySidonSeq (n + 1)
      · left
        rw [hpeq]
        exact greedySidonSeq_mem (n + 1)
      · have hlt : p < greedySidonSeq (n + 1) := lt_of_le_of_ne hp2 hpeq
        have hnotsidon := greedy_skip_not_sidon hle hlt
        right
        have hmem : p ∈ forbidden (greedySeqSet n) := by
          apply not_sidon_insert_forbidden (greedySeqSet_isSidon n) ?_ hnotsidon
          intro a ha
          exact lt_of_le_of_lt (greedySeqSet_le ha) hle
        exact forbidden_mono (greedySeqSet_subset_succ n) hmem

/-- **Cubic growth bound.**  The `n`-th greedy Sidon term satisfies `aₙ ≤ (n+1) + (n+1)³`.

This is the quantitative crux of the known `N^(1/3)` lower bound for Erdős #340: the
greedy sequence cannot grow faster than cubically, because every value it skips is one of
at most `|Aₙ|³ = (n+1)³` forbidden differences against the placed prefix. -/
theorem greedySidonSeq_le_cubic (n : ℕ) :
    greedySidonSeq n ≤ (n + 1) + (n + 1) ^ 3 := by
  have hcover : Finset.Icc 1 (greedySidonSeq n)
      ⊆ greedySeqSet n ∪ forbidden (greedySeqSet n) := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    rw [Finset.mem_union]
    exact greedy_covering n p hp.1 hp.2
  have hcard := Finset.card_le_card hcover
  rw [Nat.card_Icc] at hcard
  have hunion : (greedySeqSet n ∪ forbidden (greedySeqSet n)).card
      ≤ (greedySeqSet n).card + (forbidden (greedySeqSet n)).card :=
    Finset.card_union_le _ _
  have hsetcard : (greedySeqSet n).card = n + 1 := greedySeqSet_card n
  have hforbcard : (forbidden (greedySeqSet n)).card ≤ (n + 1) ^ 3 := by
    calc (forbidden (greedySeqSet n)).card ≤ (greedySeqSet n).card ^ 3 := forbidden_card_le _
      _ = (n + 1) ^ 3 := by rw [hsetcard]
  omega

/- ## Cube-root inversion: the discrete `Ω(N^(1/3))` count -/

/-- Every greedy term is positive (`a₀ = 1` is the minimum). -/
theorem one_le_greedySidonSeq (k : ℕ) : 1 ≤ greedySidonSeq k := by
  have hmono : greedySidonSeq 0 ≤ greedySidonSeq k :=
    greedySidonSeq_strictMono.monotone (Nat.zero_le k)
  have h0 : greedySidonSeq 0 = 1 := rfl
  omega

/-- Cleaner cubic bound: `aₙ ≤ 2(n+1)³`, absorbing the linear term. -/
theorem greedySidonSeq_le_two_mul_cubic (n : ℕ) :
    greedySidonSeq n ≤ 2 * (n + 1) ^ 3 := by
  have h := greedySidonSeq_le_cubic n
  have hle : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) (n + 1)
  omega

/-- The first `n+1` greedy terms all lie inside the window `[1, 2(n+1)³]`. -/
theorem greedySeqSet_subset_Icc (n : ℕ) :
    greedySeqSet n ⊆ Finset.Icc 1 (2 * (n + 1) ^ 3) := by
  intro x hx
  rw [Finset.mem_Icc]
  refine ⟨?_, le_trans (greedySeqSet_le hx) (greedySidonSeq_le_two_mul_cubic n)⟩
  rw [greedySeqSet_eq_image, Finset.mem_image] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact one_le_greedySidonSeq k

/-- **Discrete `Ω(N^(1/3))` lower bound for the greedy Sidon counting function.**

Whenever `N ≥ 2(n+1)³`, at least `n+1` of the integers in `[1, N]` are greedy Sidon
terms.  Reading it the other way: the count `A(N)` of greedy terms `≤ N` satisfies
`A(N) ≥ k` as soon as `N ≥ 2k³`, i.e. `A(N) ≥ ⌊(N/2)^{1/3}⌋ = Ω(N^{1/3})`.

This is the known lower-bound direction of Erdős #340, now an elementary, fully verified
counting statement (no `rpow`, no axiom).  The `1/3`→`1/2` exponent improvement remains
the OPEN conjecture and is not addressed here. -/
theorem greedy_count_ge {n N : ℕ} (hN : 2 * (n + 1) ^ 3 ≤ N) :
    n + 1 ≤ ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet n)).card := by
  have hsub : greedySeqSet n
      ⊆ (Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet n) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨?_, hx⟩
    have hwin := greedySeqSet_subset_Icc n hx
    rw [Finset.mem_Icc] at hwin ⊢
    omega
  calc n + 1 = (greedySeqSet n).card := (greedySeqSet_card n).symm
    _ ≤ _ := Finset.card_le_card hsub

/- ## Analytic phrasing: the `Ω(N^{1/3})` density lower bound

`greedy_count_ge` is already the rigorous lower-bound direction of Erdős #340, but stated
as a *discrete* window inequality (`N ≥ 2k³ ⇒ A(N) ≥ k`).  Here we invert it into the
asymptotic-density form mathematicians recognize: there is a constant `C > 0` with
`C · N^{1/3} ≤ A(N)` for all `N ≥ 1`, i.e. `A(N) = Ω(N^{1/3})`. -/

/-- **The greedy Sidon counting function** `A(N)` — the number of greedy terms in `[1, N]`.
We count over the prefix `greedySeqSet N = {a₀, …, a_N}`; since `greedySidonSeq` is strictly
increasing from `a₀ = 1` we have `k ≤ a_k`, so every greedy term `≤ N` already has index
`≤ N` and this set is exactly `{k : a_k ≤ N}`. -/
noncomputable def greedyCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet N)).card

/-- `greedySeqSet` is monotone in its index: a longer prefix contains a shorter one. -/
theorem greedySeqSet_mono {a b : ℕ} (h : a ≤ b) : greedySeqSet a ⊆ greedySeqSet b := by
  intro x hx
  rw [greedySeqSet_eq_image, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  rw [greedySeqSet_eq_image, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

/-- Cube then cube-root collapses: `(x^{1/3})³ = x` for `x ≥ 0`. -/
private theorem cube_cubrt {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1:ℝ)/3)) ^ (3:ℕ) = x := by
  rw [← Real.rpow_natCast (x ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hx]
  norm_num

/-- Cube-root then cube collapses: `(y³)^{1/3} = y` for `y ≥ 0`. -/
private theorem cubrt_cube {y : ℝ} (hy : 0 ≤ y) : (y ^ (3:ℕ)) ^ ((1:ℝ)/3) = y := by
  rw [← Real.rpow_natCast y 3, ← Real.rpow_mul hy]
  norm_num

/-- **Analytic `Ω(N^{1/3})` lower bound for the greedy Sidon counting function.**
There is a constant `C > 0` with `C · N^{1/3} ≤ A(N)` for every `N ≥ 1`, where `A(N)` is the
number of greedy terms in `[1, N]` (`greedyCount`).

This is the asymptotic-density phrasing of the discrete bound `greedy_count_ge`
(`N ≥ 2k³ ⇒ A(N) ≥ k`).  Inverting the cubic window with `k = ⌊(N/2)^{1/3}⌋` gives
`2k³ ≤ N` (so `A(N) ≥ k`) and, by maximality, `N < 16k³` (so `k > 16^{-1/3}·N^{1/3}`); hence
`C = 16^{-1/3}` works.  Crucially the constant is uniform — the `1/3`→`1/2` exponent
improvement remains the OPEN part of Erdős #340 and is *not* addressed here. -/
theorem greedy_count_omega_cubrt :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → C * (N : ℝ) ^ ((1:ℝ)/3) ≤ (greedyCount N : ℝ) := by
  refine ⟨(1/16 : ℝ) ^ ((1:ℝ)/3), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro N hN
  set m : ℕ := ⌊((N:ℝ)/2) ^ ((1:ℝ)/3)⌋₊ with hm
  have hbase : (0:ℝ) ≤ (N:ℝ)/2 := by positivity
  have hfloor_le : (m:ℝ) ≤ ((N:ℝ)/2) ^ ((1:ℝ)/3) := Nat.floor_le (by positivity)
  have hlt_floor : ((N:ℝ)/2) ^ ((1:ℝ)/3) < m + 1 := Nat.lt_floor_add_one _
  -- `1 = a₀` is always counted, so `A(N) ≥ 1`.
  have h10 : (1:ℕ) ∈ greedySeqSet 0 := greedySidonSeq_mem 0
  have h1mem : (1:ℕ) ∈ (Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet N) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, hN⟩, greedySeqSet_mono (Nat.zero_le N) h10⟩
  have hge1 : 1 ≤ greedyCount N := by
    rw [greedyCount]; exact Finset.card_pos.mpr ⟨1, h1mem⟩
  by_cases hm0 : m = 0
  · -- small-`N` region: `m = 0 ⇔ N = 1`, handled by `A(1) ≥ 1 ≥ C`.
    have hNlt2 : N < 2 := by
      by_contra hcon
      push_neg at hcon
      have h1le : (1:ℝ) ≤ (N:ℝ)/2 := by
        have : (2:ℝ) ≤ N := by exact_mod_cast hcon
        linarith
      have hge : (1:ℝ) ≤ ((N:ℝ)/2) ^ ((1:ℝ)/3) := by
        calc (1:ℝ) = (1:ℝ) ^ ((1:ℝ)/3) := (Real.one_rpow _).symm
          _ ≤ ((N:ℝ)/2) ^ ((1:ℝ)/3) := by gcongr
      have : 1 ≤ m := by rw [hm]; exact Nat.le_floor (by exact_mod_cast hge)
      omega
    interval_cases N
    · have e1 : ((1:ℕ):ℝ) ^ ((1:ℝ)/3) = 1 := by rw [Nat.cast_one, Real.one_rpow]
      rw [e1, mul_one]
      have hC1 : (1/16:ℝ) ^ ((1:ℝ)/3) ≤ 1 :=
        Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
      have hgc : (1:ℝ) ≤ (greedyCount 1 : ℝ) := by exact_mod_cast hge1
      linarith
  · -- main region `m ≥ 1`.
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    -- `2m³ ≤ N` from `m ≤ (N/2)^{1/3}`.
    have hcube_le : (m:ℝ)^3 ≤ (N:ℝ)/2 := by
      have hstep : (m:ℝ)^3 ≤ (((N:ℝ)/2) ^ ((1:ℝ)/3))^(3:ℕ) := by gcongr
      rwa [cube_cubrt hbase] at hstep
    have h2m3 : 2 * m^3 ≤ N := by
      have hr : (2:ℝ) * (m:ℝ)^3 ≤ (N:ℝ) := by linarith
      exact_mod_cast hr
    -- `A(N) ≥ m`, via `greedy_count_ge` at `n = m-1` lifted along the prefix chain.
    have hmN : m - 1 ≤ N := by
      have h1 : m ≤ m^3 := Nat.le_self_pow (by norm_num) m
      omega
    have hmcount : m ≤ greedyCount N := by
      have hkey := greedy_count_ge (n := m - 1) (N := N) (by
        rw [show (m-1)+1 = m from by omega]; exact h2m3)
      rw [show (m-1)+1 = m from by omega] at hkey
      have hsub : greedySeqSet (m-1) ⊆ greedySeqSet N := greedySeqSet_mono hmN
      have hfsub : ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet (m-1)))
          ⊆ ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet N)) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hsub hx.2⟩
      calc m ≤ ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet (m-1))).card := hkey
        _ ≤ ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet N)).card :=
            Finset.card_le_card hfsub
        _ = greedyCount N := rfl
    -- `N < 16m³` from maximality of the floor `(N/2)^{1/3} < m+1 ≤ 2m`.
    have hlt : ((N:ℝ)/2) ^ ((1:ℝ)/3) < 2 * (m:ℝ) := by
      have h2m : (m:ℝ) + 1 ≤ 2 * m := by
        have : (1:ℝ) ≤ m := by exact_mod_cast hm1
        linarith
      linarith [hlt_floor]
    have hcube : (N:ℝ)/2 < (2*(m:ℝ))^(3:ℕ) := by
      have hstep : (((N:ℝ)/2) ^ ((1:ℝ)/3))^(3:ℕ) < (2*(m:ℝ))^(3:ℕ) := by gcongr
      rwa [cube_cubrt hbase] at hstep
    have hN16 : (N:ℝ) ≤ 16 * (m:ℝ)^3 := by
      have hexp : (2*(m:ℝ))^(3:ℕ) = 8 * (m:ℝ)^3 := by ring
      rw [hexp] at hcube; linarith
    -- combine: `C·N^{1/3} = (N/16)^{1/3} ≤ (m³)^{1/3} = m ≤ A(N)`.
    have hmul : (1/16:ℝ) ^ ((1:ℝ)/3) * (N:ℝ) ^ ((1:ℝ)/3) = ((N:ℝ)/16) ^ ((1:ℝ)/3) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      congr 1; ring
    have hle : (N:ℝ)/16 ≤ (m:ℝ)^3 := by linarith
    have hfin : (1/16:ℝ) ^ ((1:ℝ)/3) * (N:ℝ) ^ ((1:ℝ)/3) ≤ (m:ℝ) := by
      rw [hmul]
      calc ((N:ℝ)/16) ^ ((1:ℝ)/3) ≤ ((m:ℝ)^3) ^ ((1:ℝ)/3) := by gcongr
        _ = m := cubrt_cube (by positivity)
    have hmR : (m:ℝ) ≤ (greedyCount N : ℝ) := by exact_mod_cast hmcount
    linarith

end Erdos340
