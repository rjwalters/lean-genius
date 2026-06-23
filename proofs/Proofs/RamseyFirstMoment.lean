/-
  The First-Moment (Union-Bound) Ramsey Lower Bound

  Open question (prob-method-expectation-oq-02):
    "What is the tightest Ramsey bound achievable via the first moment method alone?"

  Answer formalized here: the classical Erdős (1947) union-bound criterion, over genuine
  edge 2-colorings of the complete graph K_n.  If

        2 · C(n,k) < 2^(C(k,2))          (equivalently  C(n,k)·2^(1-C(k,2)) < 1)

  then there exists a 2-coloring of the edges of K_n with NO monochromatic K_k, i.e.

        R(k,k) > n.

  This is the *tightest* bound the first moment / union bound alone can give: the expected
  number of monochromatic k-cliques under a uniform random 2-coloring is C(n,k)·2^(1-C(k,2)),
  and when that is < 1 a coloring beating the average exists.

  Engine: a direct counting / union bound, entirely over ℕ (no probability measure needed).
    * The number of colorings monochromatic on a fixed k-clique is at most 2·2^(C(n,2)-C(k,2))
      (proved via an explicit injection: such a coloring is determined by the common color of
      the clique's edges together with its values on every other edge).
    * Summing over the C(n,k) cliques (union bound) the number of "bad" colorings is below the
      total 2^(C(n,2)) exactly when 2·C(n,k) < 2^(C(k,2)).
    * A coloring outside the bad set is a good coloring.

  Replaces the trivial placeholder `erdos_ramsey_lower_bound` (∃ n ≥ 2^(k/2), vacuously true)
  in the parent entry with the real, content-bearing first-moment bound.

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib

namespace ProbMethod.RamseyFirstMoment

open Finset

variable {n k : ℕ}

/-- Edges of the complete graph on `Fin n`: the 2-element subsets of the vertex set. -/
def Edges (n : ℕ) : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard 2

/-- A 2-coloring assigns a Boolean color to every edge. -/
abbrev Coloring (n : ℕ) := ↥(Edges n) → Bool

/-- The number of edges of `K_n` is `C(n,2)`. -/
theorem card_Edges (n : ℕ) : (Edges n).card = n.choose 2 := by
  rw [Edges, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The edges contained inside a vertex set `K` (its induced clique edges). -/
def EdgesIn (n : ℕ) (K : Finset (Fin n)) : Finset (↥(Edges n)) :=
  univ.filter (fun e => (e : Finset (Fin n)) ⊆ K)

/-- The induced edges of `K` biject with the 2-subsets of `K`, so there are `C(|K|,2)` of them. -/
theorem card_EdgesIn (n : ℕ) (K : Finset (Fin n)) :
    (EdgesIn n K).card = K.card.choose 2 := by
  have hinj : Function.Injective (fun e : ↥(Edges n) => (e : Finset (Fin n))) :=
    Subtype.coe_injective
  have himg : (EdgesIn n K).image (fun e : ↥(Edges n) => (e : Finset (Fin n)))
      = K.powersetCard 2 := by
    ext s
    simp only [EdgesIn, mem_image, mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨e, hsub, rfl⟩
      have he : (e : Finset (Fin n)) ∈ Edges n := e.2
      simp only [Edges, Finset.mem_powersetCard] at he
      exact ⟨hsub, he.2⟩
    · rintro ⟨hsub, hcard⟩
      have he : s ∈ Edges n := by
        simp only [Edges, Finset.mem_powersetCard]; exact ⟨subset_univ s, hcard⟩
      exact ⟨⟨s, he⟩, hsub, rfl⟩
  calc (EdgesIn n K).card
      = ((EdgesIn n K).image (fun e : ↥(Edges n) => (e : Finset (Fin n)))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ = (K.powersetCard 2).card := by rw [himg]
    _ = K.card.choose 2 := Finset.card_powersetCard _ _

/-- `K` is **monochromatic** under coloring `c` when all of its induced edges share one color. -/
def Mono (c : Coloring n) (K : Finset (Fin n)) : Prop :=
  ∀ e ∈ EdgesIn n K, ∀ f ∈ EdgesIn n K, c e = c f

instance (c : Coloring n) (K : Finset (Fin n)) : Decidable (Mono c K) := by
  unfold Mono; infer_instance

/-- **Crux count.** The number of colorings monochromatic on a fixed clique `K`
    with at least one edge is at most `2 · 2^(C(n,2) - |EdgesIn K|)`.

    Proof: such a coloring `c` is recovered from the pair
    `(common color of the clique's edges, values of c on every non-clique edge)`,
    giving an injection into `Bool × (non-clique edges → Bool)`. -/
theorem card_mono_le (K : Finset (Fin n)) (hK : (EdgesIn n K).Nonempty) :
    (univ.filter (fun c : Coloring n => Mono c K)).card
      ≤ 2 * 2 ^ ((Edges n).card - (EdgesIn n K).card) := by
  set T := EdgesIn n K with hT
  obtain ⟨e₀, he₀⟩ := hK
  -- injection from monochromatic colorings into Bool × (off-clique edges → Bool)
  let ψ : {c : Coloring n // Mono c K} → Bool × ({j : ↥(Edges n) // j ∉ T} → Bool) :=
    fun c => (c.1 e₀, fun j => c.1 j.1)
  have hψ : Function.Injective ψ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ hcc
    simp only [ψ, Prod.mk.injEq] at hcc
    obtain ⟨h0, hoff⟩ := hcc
    apply Subtype.ext
    funext i
    show c i = c' i
    by_cases hi : i ∈ T
    · -- on clique edges everything equals the common color at e₀
      have h1 : c i = c e₀ := hc i hi e₀ he₀
      have h2 : c' i = c' e₀ := hc' i hi e₀ he₀
      rw [h1, h2, h0]
    · -- off clique edges the values agree directly
      exact congrFun hoff ⟨i, hi⟩
  have hcard_le : Fintype.card {c : Coloring n // Mono c K}
      ≤ Fintype.card (Bool × ({j : ↥(Edges n) // j ∉ T} → Bool)) :=
    Fintype.card_le_of_injective ψ hψ
  -- evaluate the cardinalities
  have hcompl : Fintype.card {j : ↥(Edges n) // j ∉ T}
      = Fintype.card (↥(Edges n)) - T.card := by
    rw [Fintype.card_subtype_compl]
    congr 1
    exact Fintype.card_coe T
  have hrhs : Fintype.card (Bool × ({j : ↥(Edges n) // j ∉ T} → Bool))
      = 2 * 2 ^ (Fintype.card (↥(Edges n)) - T.card) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hcompl]
  rw [Fintype.card_subtype (fun c : Coloring n => Mono c K)] at hcard_le
  rw [hrhs, Fintype.card_coe] at hcard_le
  exact hcard_le

/-- **First-Moment (Union-Bound) Ramsey lower bound.**
    If `2·C(n,k) < 2^(C(k,2))` then there is a 2-coloring of the edges of `K_n`
    with no monochromatic `K_k`.  Equivalently, the diagonal Ramsey number satisfies
    `R(k,k) > n`.  This is the tightest bound obtainable from the first moment method. -/
theorem first_moment_ramsey (hk : 2 ≤ k) (hkn : k ≤ n)
    (hbound : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Coloring n, ∀ K : Finset (Fin n), K.card = k → ¬ Mono c K := by
  classical
  set Cliques : Finset (Finset (Fin n)) := univ.powersetCard k with hCl
  -- the set of "bad" colorings: those monochromatic on some k-clique
  set Bad : Finset (Coloring n) :=
    Cliques.biUnion (fun K => univ.filter (fun c : Coloring n => Mono c K)) with hBad
  -- each clique has C(k,2) edges, at least one
  have hedge_card : ∀ K ∈ Cliques, (EdgesIn n K).card = k.choose 2 := by
    intro K hKc
    rw [hCl, Finset.mem_powersetCard] at hKc
    rw [card_EdgesIn, hKc.2]
  have hb_le_a : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
  -- union bound: |Bad| ≤ C(n,k) · 2 · 2^(C(n,2) - C(k,2))
  have hBad_le : Bad.card ≤ n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
    calc Bad.card
        ≤ ∑ K ∈ Cliques, (univ.filter (fun c : Coloring n => Mono c K)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _K ∈ Cliques, 2 * 2 ^ (n.choose 2 - k.choose 2) := by
          apply Finset.sum_le_sum
          intro K hKc
          have hne : (EdgesIn n K).Nonempty := by
            rw [← Finset.card_pos, hedge_card K hKc]
            exact Nat.choose_pos hk
          have := card_mono_le K hne
          rwa [card_Edges, hedge_card K hKc] at this
      _ = Cliques.card * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [hCl, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- the bound is strictly below the total number of colorings 2^(C(n,2))
  have htotal : Fintype.card (Coloring n) = 2 ^ n.choose 2 := by
    show Fintype.card (↥(Edges n) → Bool) = 2 ^ n.choose 2
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_Edges]
  have hstrict : Bad.card < Fintype.card (Coloring n) := by
    rw [htotal]
    refine lt_of_le_of_lt hBad_le ?_
    -- C(n,k)·2·2^(a-b) = (2·C(n,k))·2^(a-b) < 2^b·2^(a-b) = 2^a
    have hsplit : (2 : ℕ) ^ n.choose 2
        = 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by
      rw [← pow_add, Nat.add_sub_cancel' hb_le_a]
    rw [hsplit]
    have hpos : 0 < 2 ^ (n.choose 2 - k.choose 2) := pow_pos (by norm_num) _
    calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
        = (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by ring
      _ < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
          (Nat.mul_lt_mul_right hpos).mpr hbound
  -- so some coloring is not bad
  obtain ⟨c, hcnot⟩ : ∃ c : Coloring n, c ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (univ : Finset (Coloring n)).card ≤ Bad.card :=
      Finset.card_le_card (fun c _ => hcon c)
    rw [Finset.card_univ] at hle
    omega
  refine ⟨c, ?_⟩
  intro K hKcard hmono
  apply hcnot
  rw [hBad, Finset.mem_biUnion]
  refine ⟨K, ?_, ?_⟩
  · rw [hCl, Finset.mem_powersetCard]; exact ⟨subset_univ K, hKcard⟩
  · rw [mem_filter]; exact ⟨mem_univ c, hmono⟩

/-- **Diagonal Ramsey number lower bound, witness form.**
    The "Ramsey-good" colorings of `K_n` (no monochromatic `K_k`) are nonempty under the
    first-moment criterion — i.e. `n` is below the Ramsey number `R(k,k)`. -/
theorem ramsey_number_gt (hk : 2 ≤ k) (hkn : k ≤ n)
    (hbound : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Coloring n, ∀ K : Finset (Fin n), K.card = k → ∃ e ∈ EdgesIn n K,
      ∃ f ∈ EdgesIn n K, c e ≠ c f := by
  obtain ⟨c, hc⟩ := first_moment_ramsey hk hkn hbound
  refine ⟨c, fun K hKcard => ?_⟩
  have := hc K hKcard
  unfold Mono at this
  push_neg at this
  obtain ⟨e, he, f, hf, hne⟩ := this
  exact ⟨e, he, f, hf, hne⟩

/-- The first-moment hypothesis is satisfiable: e.g. for `k = 4, n = 6` we get
    `2·C(6,4) = 30 < 64 = 2^(C(4,2))`, so `R(4,4) > 6` — a concrete good 2-coloring
    of `K_6` with no monochromatic `K_4` exists. -/
theorem ramsey_four_gt_six :
    ∃ c : Coloring 6, ∀ K : Finset (Fin 6), K.card = 4 → ¬ Mono c K :=
  first_moment_ramsey (by norm_num) (by norm_num) (by decide)

end ProbMethod.RamseyFirstMoment
