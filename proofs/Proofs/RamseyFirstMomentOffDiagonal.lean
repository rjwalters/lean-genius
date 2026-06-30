/-
  The Off-Diagonal First-Moment (Union-Bound) Ramsey Lower Bound

  Open question (prob-method-expectation-oq-02, follow-up OQ-02):
    "Formalize the off-diagonal version: thresholds giving lower bounds on R(s,t)
     for s ≠ t via the same union bound."

  Answer formalized here.  Colour the edges of the complete graph K_n with two
  colours (`true` = "red", `false` = "blue").  If

        C(n,s) · 2^(C(t,2))  +  C(n,t) · 2^(C(s,2))  <  2^(C(s,2) + C(t,2))

  (equivalently the first-moment criterion  C(n,s)·2^(-C(s,2)) + C(n,t)·2^(-C(t,2)) < 1)
  then there is a 2-colouring of the edges of K_n with NO red K_s and NO blue K_t,
  i.e.

        R(s,t) > n.

  This generalises the diagonal bound `prob-method-expectation-oq-02`
  (`first_moment_ramsey`, the s = t case): the union bound now runs over two families
  — the red s-cliques and the blue t-cliques — each counted separately, since the
  expected number of red K_s plus the expected number of blue K_t under a uniform
  random 2-colouring is exactly C(n,s)·2^(-C(s,2)) + C(n,t)·2^(-C(t,2)).

  Engine: a direct counting / union bound, entirely over ℕ (no probability measure).
    * The number of colourings that are constant of a *fixed* colour on a fixed
      k-clique is at most 2^(C(n,2) - C(k,2)) — an injection: such a colouring is
      determined by its values on every non-clique edge (the clique edges are forced).
    * Summing C(n,s) red s-cliques and C(n,t) blue t-cliques (union bound) the number
      of "bad" colourings is below the total 2^(C(n,2)) exactly when the threshold holds.
    * A colouring outside the bad set has no red K_s and no blue K_t.

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib

namespace ProbMethod.RamseyOffDiagonal

open Finset

variable {n s t : ℕ}

/-- Edges of the complete graph on `Fin n`: the 2-element subsets of the vertex set. -/
def Edges (n : ℕ) : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard 2

/-- A 2-colouring assigns a Boolean colour to every edge (`true` = red, `false` = blue). -/
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
    ext sset
    simp only [EdgesIn, mem_image, mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨e, hsub, rfl⟩
      have he : (e : Finset (Fin n)) ∈ Edges n := e.2
      simp only [Edges, Finset.mem_powersetCard] at he
      exact ⟨hsub, he.2⟩
    · rintro ⟨hsub, hcard⟩
      have he : sset ∈ Edges n := by
        simp only [Edges, Finset.mem_powersetCard]; exact ⟨subset_univ sset, hcard⟩
      exact ⟨⟨sset, he⟩, hsub, rfl⟩
  calc (EdgesIn n K).card
      = ((EdgesIn n K).image (fun e : ↥(Edges n) => (e : Finset (Fin n)))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ = (K.powersetCard 2).card := by rw [himg]
    _ = K.card.choose 2 := Finset.card_powersetCard _ _

/-- `K` is **monochromatic of colour `col`** under colouring `c` when every induced edge
    of `K` has colour `col`.  `MonoColor c K true` says `K` is a red clique;
    `MonoColor c K false` says `K` is a blue clique. -/
def MonoColor (c : Coloring n) (K : Finset (Fin n)) (col : Bool) : Prop :=
  ∀ e ∈ EdgesIn n K, c e = col

instance (c : Coloring n) (K : Finset (Fin n)) (col : Bool) :
    Decidable (MonoColor c K col) := by
  unfold MonoColor; infer_instance

/-- **Crux count.** The number of colourings that are constant of a fixed colour `col`
    on a fixed clique `K` is at most `2^(C(n,2) - |EdgesIn K|)`.

    Proof: such a colouring `c` is recovered from its values on every non-clique edge,
    since on `K`'s edges it is forced to be `col`; this is an injection into
    `(non-clique edges → Bool)`.  Unlike the diagonal count there is no factor of `2`,
    because the colour is fixed in advance. -/
theorem card_monoColor_le (K : Finset (Fin n)) (col : Bool) :
    (univ.filter (fun c : Coloring n => MonoColor c K col)).card
      ≤ 2 ^ ((Edges n).card - (EdgesIn n K).card) := by
  set T := EdgesIn n K with hT
  -- injection from colour-`col`-monochromatic colourings into (off-clique edges → Bool)
  let ψ : {c : Coloring n // MonoColor c K col} → ({j : ↥(Edges n) // j ∉ T} → Bool) :=
    fun c => fun j => c.1 j.1
  have hψ : Function.Injective ψ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ hcc
    simp only [ψ] at hcc
    apply Subtype.ext
    funext i
    show c i = c' i
    by_cases hi : i ∈ T
    · -- on clique edges both colourings equal the fixed colour `col`
      rw [hc i hi, hc' i hi]
    · -- off clique edges the values agree directly
      exact congrFun hcc ⟨i, hi⟩
  have hcard_le : Fintype.card {c : Coloring n // MonoColor c K col}
      ≤ Fintype.card ({j : ↥(Edges n) // j ∉ T} → Bool) :=
    Fintype.card_le_of_injective ψ hψ
  have hcompl : Fintype.card {j : ↥(Edges n) // j ∉ T}
      = Fintype.card (↥(Edges n)) - T.card := by
    rw [Fintype.card_subtype_compl]
    congr 1
    exact Fintype.card_coe T
  have hrhs : Fintype.card ({j : ↥(Edges n) // j ∉ T} → Bool)
      = 2 ^ (Fintype.card (↥(Edges n)) - T.card) := by
    rw [Fintype.card_fun, Fintype.card_bool, hcompl]
  rw [Fintype.card_subtype (fun c : Coloring n => MonoColor c K col)] at hcard_le
  rw [hrhs, Fintype.card_coe] at hcard_le
  rw [card_Edges] at hcard_le ⊢
  -- T.card and (EdgesIn n K).card are definitionally the same set
  simpa [hT] using hcard_le

/-- **Off-Diagonal First-Moment (Union-Bound) Ramsey lower bound.**
    For `s, t ≥ 2` with `s, t ≤ n`, if

      `C(n,s) · 2^(C(t,2)) + C(n,t) · 2^(C(s,2)) < 2^(C(s,2) + C(t,2))`

    then there is a 2-colouring of the edges of `K_n` with no red `K_s` and no
    blue `K_t`.  Equivalently the off-diagonal Ramsey number satisfies `R(s,t) > n`.
    (No `s, t ≥ 2` hypothesis is needed: the union bound is self-correcting, since for
    `s ≤ 1` the threshold forces `n.choose s < 1`, which is impossible for `s ≤ n`.) -/
theorem first_moment_offdiagonal
    (hsn : s ≤ n) (htn : t ≤ n)
    (hbound : n.choose s * 2 ^ (t.choose 2) + n.choose t * 2 ^ (s.choose 2)
                < 2 ^ (s.choose 2 + t.choose 2)) :
    ∃ c : Coloring n,
      (∀ K : Finset (Fin n), K.card = s → ¬ MonoColor c K true) ∧
      (∀ K : Finset (Fin n), K.card = t → ¬ MonoColor c K false) := by
  classical
  set a := s.choose 2 with ha
  set b := t.choose 2 with hb
  set E := n.choose 2 with hE
  have haE : a ≤ E := by rw [ha, hE]; exact Nat.choose_le_choose 2 hsn
  have hbE : b ≤ E := by rw [hb, hE]; exact Nat.choose_le_choose 2 htn
  -- the two bad families: red s-cliques and blue t-cliques
  set SCliques : Finset (Finset (Fin n)) := univ.powersetCard s with hSC
  set TCliques : Finset (Finset (Fin n)) := univ.powersetCard t with hTC
  set BadRed : Finset (Coloring n) :=
    SCliques.biUnion (fun K => univ.filter (fun c : Coloring n => MonoColor c K true)) with hBR
  set BadBlue : Finset (Coloring n) :=
    TCliques.biUnion (fun K => univ.filter (fun c : Coloring n => MonoColor c K false)) with hBB
  set Bad : Finset (Coloring n) := BadRed ∪ BadBlue with hBad
  -- each s-clique has exactly C(s,2) induced edges, each t-clique exactly C(t,2)
  have hSedge : ∀ K ∈ SCliques, (EdgesIn n K).card = a := by
    intro K hKc
    rw [hSC, Finset.mem_powersetCard] at hKc
    rw [card_EdgesIn, hKc.2, ha]
  have hTedge : ∀ K ∈ TCliques, (EdgesIn n K).card = b := by
    intro K hKc
    rw [hTC, Finset.mem_powersetCard] at hKc
    rw [card_EdgesIn, hKc.2, hb]
  -- union bound on each family
  have hBR_le : BadRed.card ≤ n.choose s * 2 ^ (E - a) := by
    calc BadRed.card
        ≤ ∑ K ∈ SCliques, (univ.filter (fun c : Coloring n => MonoColor c K true)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _K ∈ SCliques, 2 ^ (E - a) := by
          apply Finset.sum_le_sum
          intro K hKc
          have := card_monoColor_le K true
          rwa [card_Edges, hSedge K hKc] at this
      _ = SCliques.card * 2 ^ (E - a) := by rw [Finset.sum_const, smul_eq_mul]
      _ = n.choose s * 2 ^ (E - a) := by
          rw [hSC, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hBB_le : BadBlue.card ≤ n.choose t * 2 ^ (E - b) := by
    calc BadBlue.card
        ≤ ∑ K ∈ TCliques, (univ.filter (fun c : Coloring n => MonoColor c K false)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _K ∈ TCliques, 2 ^ (E - b) := by
          apply Finset.sum_le_sum
          intro K hKc
          have := card_monoColor_le K false
          rwa [card_Edges, hTedge K hKc] at this
      _ = TCliques.card * 2 ^ (E - b) := by rw [Finset.sum_const, smul_eq_mul]
      _ = n.choose t * 2 ^ (E - b) := by
          rw [hTC, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hBad_le : Bad.card ≤ n.choose s * 2 ^ (E - a) + n.choose t * 2 ^ (E - b) :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add hBR_le hBB_le)
  -- the total number of colourings
  have htotal : Fintype.card (Coloring n) = 2 ^ E := by
    show Fintype.card (↥(Edges n) → Bool) = 2 ^ E
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_Edges, hE]
  -- the bad bound is strictly below the total 2^E.
  -- Multiply through by 2^(a+b) and use the threshold hypothesis.
  have hstrict : Bad.card < Fintype.card (Coloring n) := by
    rw [htotal]
    refine lt_of_le_of_lt hBad_le ?_
    -- it suffices to compare after multiplying by 2^(a+b) > 0
    have key1 : 2 ^ (E - a) * 2 ^ (a + b) = 2 ^ (E + b) := by
      rw [← pow_add]; congr 1; omega
    have key2 : 2 ^ (E - b) * 2 ^ (a + b) = 2 ^ (E + a) := by
      rw [← pow_add]; congr 1; omega
    have hmul : (n.choose s * 2 ^ (E - a) + n.choose t * 2 ^ (E - b)) * 2 ^ (a + b)
        < 2 ^ E * 2 ^ (a + b) := by
      calc (n.choose s * 2 ^ (E - a) + n.choose t * 2 ^ (E - b)) * 2 ^ (a + b)
          = n.choose s * (2 ^ (E - a) * 2 ^ (a + b))
              + n.choose t * (2 ^ (E - b) * 2 ^ (a + b)) := by ring
        _ = n.choose s * 2 ^ (E + b) + n.choose t * 2 ^ (E + a) := by rw [key1, key2]
        _ = 2 ^ E * (n.choose s * 2 ^ b + n.choose t * 2 ^ a) := by
            rw [pow_add, pow_add]; ring
        _ < 2 ^ E * 2 ^ (a + b) := by gcongr
    exact (Nat.mul_lt_mul_right (show (0 : ℕ) < 2 ^ (a + b) by positivity)).mp hmul
  -- hence some colouring is not bad
  obtain ⟨c, hcnot⟩ : ∃ c : Coloring n, c ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (univ : Finset (Coloring n)).card ≤ Bad.card :=
      Finset.card_le_card (fun c _ => hcon c)
    rw [Finset.card_univ] at hle
    omega
  refine ⟨c, ?_, ?_⟩
  · intro K hKcard hmono
    apply hcnot
    rw [hBad, Finset.mem_union]
    left
    rw [hBR, Finset.mem_biUnion]
    exact ⟨K, by rw [hSC, Finset.mem_powersetCard]; exact ⟨subset_univ K, hKcard⟩,
      by rw [mem_filter]; exact ⟨mem_univ c, hmono⟩⟩
  · intro K hKcard hmono
    apply hcnot
    rw [hBad, Finset.mem_union]
    right
    rw [hBB, Finset.mem_biUnion]
    exact ⟨K, by rw [hTC, Finset.mem_powersetCard]; exact ⟨subset_univ K, hKcard⟩,
      by rw [mem_filter]; exact ⟨mem_univ c, hmono⟩⟩

/-- **Off-diagonal Ramsey number lower bound, witness form.**
    Under the first-moment criterion there is a 2-colouring of `K_n` in which every
    `s`-subset has a blue edge and every `t`-subset has a red edge — i.e. no red `K_s`
    and no blue `K_t`, so `n < R(s,t)`. -/
theorem ramsey_offdiagonal_gt
    (hsn : s ≤ n) (htn : t ≤ n)
    (hbound : n.choose s * 2 ^ (t.choose 2) + n.choose t * 2 ^ (s.choose 2)
                < 2 ^ (s.choose 2 + t.choose 2)) :
    ∃ c : Coloring n,
      (∀ K : Finset (Fin n), K.card = s → ∃ e ∈ EdgesIn n K, c e = false) ∧
      (∀ K : Finset (Fin n), K.card = t → ∃ e ∈ EdgesIn n K, c e = true) := by
  obtain ⟨c, hred, hblue⟩ := first_moment_offdiagonal hsn htn hbound
  refine ⟨c, fun K hK => ?_, fun K hK => ?_⟩
  · have := hred K hK
    unfold MonoColor at this
    push_neg at this
    obtain ⟨e, he, hne⟩ := this
    exact ⟨e, he, by simpa using hne⟩
  · have := hblue K hK
    unfold MonoColor at this
    push_neg at this
    obtain ⟨e, he, hne⟩ := this
    exact ⟨e, he, by simpa using hne⟩

/-- The off-diagonal criterion recovers the diagonal witness `R(4,4) > 6`:
    `s = t = 4`, `n = 6` gives `C(6,4)·2^6 + C(6,4)·2^6 = 1920 < 4096 = 2^(6+6)`. -/
theorem ramsey_four_four_gt_six :
    ∃ c : Coloring 6,
      (∀ K : Finset (Fin 6), K.card = 4 → ¬ MonoColor c K true) ∧
      (∀ K : Finset (Fin 6), K.card = 4 → ¬ MonoColor c K false) :=
  first_moment_offdiagonal (by norm_num) (by norm_num) (by decide)

/-- A genuinely off-diagonal instance: `R(3,4) > 4`.
    `s = 3, t = 4, n = 4` gives `C(4,3)·2^6 + C(4,4)·2^3 = 256 + 8 = 264 < 512 = 2^(3+6)`. -/
theorem ramsey_three_four_gt_four :
    ∃ c : Coloring 4,
      (∀ K : Finset (Fin 4), K.card = 3 → ¬ MonoColor c K true) ∧
      (∀ K : Finset (Fin 4), K.card = 4 → ¬ MonoColor c K false) :=
  first_moment_offdiagonal (by norm_num) (by norm_num) (by decide)

end ProbMethod.RamseyOffDiagonal
