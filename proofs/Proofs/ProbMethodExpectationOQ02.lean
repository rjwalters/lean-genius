/-
  First Moment Method — OQ-02: the genuine Erdős (1947) Ramsey lower bound.

  The parent entry `ProbMethodExpectation` states `erdos_ramsey_lower_bound` as
  `∃ n, n ≥ 2^(k/2) ∧ n > 0` — which is *vacuously true* and proves nothing about
  Ramsey numbers.  This file supplies the real content of the first-moment method:
  the union-bound counting argument that actually produces a good 2-colouring.

  We model a 2-colouring of the edges of the complete graph `K_n` as a function
  `c : Edge n → Bool`, where `Edge n` is the (finite) type of 2-element subsets of
  `Fin n`.  A `k`-subset `S` is a **monochromatic clique** under `c` when every edge
  inside `S` receives the same colour.

  Headline result (`ramsey_lower_bound`): if

        C(n,k) · 2 ^ (C(n,2) − C(k,2) + 1)  <  2 ^ C(n,2)

  then there is a 2-colouring of `K_n` with **no** monochromatic `K_k` — equivalently
  `R(k,k) > n`.  This is the exact statement obtained from the first moment method:
  the expected number of monochromatic `k`-cliques is `C(n,k)·2^(1−C(k,2))`, and when
  this is `< 1` a good colouring must exist.

  Supporting infrastructure:
  * `card_const_le` — the core counting bound: the number of colourings constant on a
    nonempty set `I` of coordinates is `≤ 2 ^ (|ι| − |I| + 1)`.  (A clean, reusable
    "fix |I|−1 degrees of freedom" lemma proved by an injection.)
  * `ramsey_lower_bound_rat` — the textbook form with the hypothesis stated over `ℚ`
    as `C(n,k)·2^(1−C(k,2)) < 1`.
  * `ramsey_K6_no_mono_K4` — a concrete non-vacuous instance: a 2-colouring of `K_6`
    with no monochromatic `K_4` (so `R(4,4) > 6`).

  All results are fully machine-checked: 0 sorries, 0 axioms.

  Reference: Alon–Spencer, *The Probabilistic Method*, Ch. 1 (Ramsey numbers).
-/

import Mathlib

namespace ProbMethod.ExpectationOQ02

open Finset BigOperators

-- ═══════════════════════════════════════════════════════════════════
-- Part I: Core counting bound (reusable, type-generic)
-- ═══════════════════════════════════════════════════════════════════

/-- **Counting colourings constant on a set of coordinates.**
    For a finite index type `ι` and a nonempty coordinate set `I` (with a chosen
    base point `i₀ ∈ I`), the number of Boolean colourings that are constant on `I`
    is at most `2 ^ (|ι| − |I| + 1)`: such a colouring is determined by its common
    value on `I` (1 degree of freedom) together with its values off `I`
    (`|ι| − |I|` degrees of freedom).

    This is the engine behind every "expected number of bad events" computation in
    the probabilistic method. -/
theorem card_const_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ I) :
    (univ.filter (fun c : ι → Bool => ∀ i ∈ I, c i = c i₀)).card
      ≤ 2 ^ (Fintype.card ι - I.card + 1) := by
  -- Inject a constant-on-`I` colouring into `(common value, values off I)`.
  classical
  set φ : (ι → Bool) → Bool × ({x : ι // x ∉ I} → Bool) :=
    fun c => (c i₀, fun x => c x.val) with hφ
  have hsub : (univ.filter (fun c : ι → Bool => ∀ i ∈ I, c i = c i₀)).card
      ≤ (univ : Finset (Bool × ({x : ι // x ∉ I} → Bool))).card := by
    apply Finset.card_le_card_of_injOn φ
    · intro c _; exact mem_univ _
    · intro c hc c' hc' hcc'
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hc hc'
      -- equate the two colourings pointwise
      funext y
      by_cases hy : y ∈ I
      · -- on `I`: both equal their (common, equal) base value
        have h1 : c y = c i₀ := hc y hy
        have h2 : c' y = c' i₀ := hc' y hy
        have hbase : c i₀ = c' i₀ := congrArg Prod.fst hcc'
        rw [h1, hbase, ← h2]
      · -- off `I`: read off the second component
        have hsnd : (fun x : {x : ι // x ∉ I} => c x.val)
            = (fun x : {x : ι // x ∉ I} => c' x.val) := congrArg Prod.snd hcc'
        have := congrFun hsnd ⟨y, hy⟩
        simpa using this
  -- evaluate the cardinality of the codomain
  have hcompl : Fintype.card {x : ι // x ∉ I} = Fintype.card ι - I.card := by
    have : Fintype.card {x : ι // x ∈ I} = I.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext x; simp
    rw [Fintype.card_subtype_compl, this]
  have hcard : (univ : Finset (Bool × ({x : ι // x ∉ I} → Bool))).card
      = 2 ^ (Fintype.card ι - I.card + 1) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
        Fintype.card_bool, hcompl, pow_succ]
    ring
  rw [← hcard]
  exact hsub

-- ═══════════════════════════════════════════════════════════════════
-- Part II: Edge / clique model for the complete graph K_n
-- ═══════════════════════════════════════════════════════════════════

section Graph

variable (n : ℕ)

/-- An **edge** of `K_n`: a 2-element subset of the vertex set `Fin n`. -/
abbrev Edge := {e : Finset (Fin n) // e.card = 2}

variable {n}

/-- The edges lying inside a vertex set `S` (the internal edges of the clique on `S`). -/
def internal (S : Finset (Fin n)) : Finset (Edge n) :=
  univ.filter (fun e => (e : Finset (Fin n)) ⊆ S)

/-- The internal edges of `S` are in bijection with the 2-subsets of `S`, hence there
    are `C(|S|, 2)` of them. -/
theorem card_internal (S : Finset (Fin n)) :
    (internal S).card = S.card.choose 2 := by
  classical
  have himg : (internal S).image (Subtype.val) = S.powersetCard 2 := by
    ext e'
    simp only [internal, mem_image, mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨he, e.2⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨e', hcard⟩, hsub, rfl⟩
  calc (internal S).card
      = ((internal S).image (Subtype.val)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (S.powersetCard 2).card := by rw [himg]
    _ = S.card.choose 2 := Finset.card_powersetCard _ _

/-- There are `C(n,2)` edges in `K_n`. -/
theorem card_edge : Fintype.card (Edge n) = n.choose 2 := by
  classical
  have : (internal (univ : Finset (Fin n))) = (univ : Finset (Edge n)) := by
    ext e; simp [internal]
  have h := card_internal (univ : Finset (Fin n))
  rw [this] at h
  rwa [Finset.card_univ, Finset.card_univ, Fintype.card_fin] at h

/-- A vertex set `S` is a **monochromatic clique** under colouring `c` when every pair
    of internal edges shares a colour. -/
def Mono (c : Edge n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ e₁ ∈ internal S, ∀ e₂ ∈ internal S, c e₁ = c e₂

instance (c : Edge n → Bool) (S : Finset (Fin n)) : Decidable (Mono c S) := by
  unfold Mono; infer_instance

end Graph

-- ═══════════════════════════════════════════════════════════════════
-- Part III: The first-moment Ramsey lower bound
-- ═══════════════════════════════════════════════════════════════════

/-- **Erdős 1947 — first-moment Ramsey lower bound (colouring-existence form).**

    If `C(n,k) · 2 ^ (C(n,2) − C(k,2) + 1) < 2 ^ C(n,2)`, then there is a 2-colouring
    of the edges of `K_n` with **no** monochromatic `K_k`: every `k`-subset of
    vertices contains two internal edges of different colours.  Equivalently,
    `R(k,k) > n`.

    Proof: the bad colourings (those admitting *some* monochromatic `k`-clique) are a
    union, over the `C(n,k)` choices of `k`-set `S`, of the colourings constant on the
    `C(k,2)` internal edges of `S`.  By `card_const_le` each such set has at most
    `2 ^ (C(n,2) − C(k,2) + 1)` colourings, so the bad set has fewer than `2^C(n,2)`
    colourings — leaving a good one. -/
theorem ramsey_lower_bound (n k : ℕ) (hk : 2 ≤ k)
    (hbound : n.choose k * 2 ^ (n.choose 2 - k.choose 2 + 1) < 2 ^ n.choose 2) :
    ∃ c : Edge n → Bool, ∀ S : Finset (Fin n), S.card = k →
      ∃ e₁ ∈ internal S, ∃ e₂ ∈ internal S, c e₁ ≠ c e₂ := by
  classical
  -- the family of k-subsets of vertices
  set K : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard k with hK
  have hKcard : K.card = n.choose k := by
    rw [hK, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- the set of "bad" colourings (admitting some monochromatic k-clique)
  set bad : Finset (Edge n → Bool) :=
    univ.filter (fun c => ∃ S ∈ K, Mono c S) with hbad
  -- bound the number of bad colourings
  have hbad_le : bad.card ≤ n.choose k * 2 ^ (n.choose 2 - k.choose 2 + 1) := by
    have hsub : bad ⊆ K.biUnion (fun S => univ.filter (fun c => Mono c S)) := by
      intro c hc
      rw [hbad, mem_filter] at hc
      obtain ⟨_, S, hS, hmono⟩ := hc
      exact mem_biUnion.mpr ⟨S, hS, mem_filter.mpr ⟨mem_univ _, hmono⟩⟩
    -- per-clique bound on the number of monochromatic colourings
    have hper : ∀ S ∈ K, (univ.filter (fun c : Edge n → Bool => Mono c S)).card
        ≤ 2 ^ (n.choose 2 - k.choose 2 + 1) := by
      intro S hS
      rw [hK, mem_powersetCard] at hS
      obtain ⟨_, hScard⟩ := hS
      -- the internal edges of S are nonempty (k ≥ 2 ⟹ C(k,2) ≥ 1)
      have hpos : 0 < (internal S).card := by
        rw [card_internal, hScard]; exact Nat.choose_pos hk
      obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp hpos
      -- a fully-monochromatic colouring is constant relative to e₀
      have hsub2 : (univ.filter (fun c : Edge n → Bool => Mono c S))
          ⊆ univ.filter (fun c : Edge n → Bool => ∀ e ∈ internal S, c e = c e₀) := by
        intro c hc
        rw [mem_filter] at hc ⊢
        exact ⟨hc.1, fun e he => hc.2 e he e₀ he₀⟩
      calc (univ.filter (fun c : Edge n → Bool => Mono c S)).card
          ≤ (univ.filter (fun c : Edge n → Bool => ∀ e ∈ internal S, c e = c e₀)).card :=
            Finset.card_le_card hsub2
        _ ≤ 2 ^ (Fintype.card (Edge n) - (internal S).card + 1) :=
            card_const_le _ e₀ he₀
        _ = 2 ^ (n.choose 2 - k.choose 2 + 1) := by
            rw [card_edge, card_internal, hScard]
    calc bad.card
        ≤ (K.biUnion (fun S => univ.filter (fun c => Mono c S))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ S ∈ K, (univ.filter (fun c : Edge n → Bool => Mono c S)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ K, 2 ^ (n.choose 2 - k.choose 2 + 1) := Finset.sum_le_sum hper
      _ = K.card * 2 ^ (n.choose 2 - k.choose 2 + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = n.choose k * 2 ^ (n.choose 2 - k.choose 2 + 1) := by rw [hKcard]
  -- hence the bad set is strictly smaller than the whole colouring space
  have htot : Fintype.card (Edge n → Bool) = 2 ^ n.choose 2 := by
    rw [Fintype.card_fun, Fintype.card_bool, card_edge]
  have hlt : bad.card < (univ : Finset (Edge n → Bool)).card := by
    rw [Finset.card_univ, htot]
    exact lt_of_le_of_lt hbad_le hbound
  -- so some good colouring exists
  have hne : (univ.filter (fun c : Edge n → Bool => ¬ (∃ S ∈ K, Mono c S))).Nonempty := by
    rw [← Finset.card_pos]
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Edge n → Bool))) (p := fun c => ∃ S ∈ K, Mono c S)
    rw [← hbad] at hsplit
    have huniv : (univ : Finset (Edge n → Bool)).card = 2 ^ n.choose 2 := by
      rw [Finset.card_univ, htot]
    omega
  obtain ⟨c, hc⟩ := hne
  rw [mem_filter] at hc
  refine ⟨c, ?_⟩
  intro S hScard
  -- S is one of the k-subsets
  have hSK : S ∈ K := by
    rw [hK, mem_powersetCard]; exact ⟨Finset.subset_univ _, hScard⟩
  -- c is not monochromatic on S
  have hnotmono : ¬ Mono c S := fun h => hc.2 ⟨S, hSK, h⟩
  unfold Mono at hnotmono
  push_neg at hnotmono
  obtain ⟨e₁, he₁, e₂, he₂, hne'⟩ := hnotmono
  exact ⟨e₁, he₁, e₂, he₂, hne'⟩

-- ═══════════════════════════════════════════════════════════════════
-- Part IV: Textbook rational form  C(n,k)·2^(1−C(k,2)) < 1
-- ═══════════════════════════════════════════════════════════════════

/-- **First-moment Ramsey bound, textbook form.**

    If the expected number of monochromatic `k`-cliques is `< 1`, i.e.

          C(n,k) · 2 ^ (1 − C(k,2))  <  1     (over ℚ),

    then `K_n` has a 2-colouring with no monochromatic `K_k`.  This is the statement
    as it appears in Alon–Spencer; it is equivalent to the integer hypothesis of
    `ramsey_lower_bound` (using `C(k,2) ≤ C(n,2)`, valid since `k ≤ n`). -/
theorem ramsey_lower_bound_rat (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hexp : (n.choose k : ℚ) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ)) < 1) :
    ∃ c : Edge n → Bool, ∀ S : Finset (Fin n), S.card = k →
      ∃ e₁ ∈ internal S, ∃ e₂ ∈ internal S, c e₁ ≠ c e₂ := by
  apply ramsey_lower_bound n k hk
  have hle : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
  have hk1 : 1 ≤ k.choose 2 := Nat.choose_pos hk
  -- Step 1: collapse the ℚ hypothesis (with its negative ℤ exponent) into the clean
  -- ℕ bound  C(n,k) < 2 ^ (C(k,2) − 1).
  have hexp' : (n.choose k : ℚ) < 2 ^ (k.choose 2 - 1) := by
    have heq : (1 : ℤ) - (k.choose 2 : ℤ) = -((k.choose 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hk1]; push_cast; ring
    rw [heq, zpow_neg, zpow_natCast] at hexp
    have hb : (0 : ℚ) < 2 ^ (k.choose 2 - 1) := by positivity
    have h2 := mul_lt_mul_of_pos_right hexp hb
    rwa [inv_mul_cancel_right₀ (ne_of_gt hb), one_mul] at h2
  have hnat : n.choose k < 2 ^ (k.choose 2 - 1) := by exact_mod_cast hexp'
  -- Step 2: multiply by 2 ^ (C(n,2) − C(k,2) + 1) and recombine the exponents.
  calc n.choose k * 2 ^ (n.choose 2 - k.choose 2 + 1)
      < 2 ^ (k.choose 2 - 1) * 2 ^ (n.choose 2 - k.choose 2 + 1) :=
        mul_lt_mul_of_pos_right hnat (by positivity)
    _ = 2 ^ n.choose 2 := by rw [← pow_add]; congr 1; omega

-- ═══════════════════════════════════════════════════════════════════
-- Part V: A concrete non-vacuous instance
-- ═══════════════════════════════════════════════════════════════════

/-- **Concrete instance: `R(4,4) > 6`.**
    There is a 2-colouring of the edges of `K_6` with no monochromatic `K_4`.
    Here `C(6,4)·2^(C(6,2)−C(4,2)+1) = 15·2^10 = 15360 < 32768 = 2^15`. -/
theorem ramsey_K6_no_mono_K4 :
    ∃ c : Edge 6 → Bool, ∀ S : Finset (Fin 6), S.card = 4 →
      ∃ e₁ ∈ internal S, ∃ e₂ ∈ internal S, c e₁ ≠ c e₂ := by
  apply ramsey_lower_bound 6 4 (by norm_num)
  decide

end ProbMethod.ExpectationOQ02
