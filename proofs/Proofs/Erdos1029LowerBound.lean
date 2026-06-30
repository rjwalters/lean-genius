import Mathlib

open Finset

namespace Erdos1029LB

variable {n : ℕ}

/-- A 2-coloring of the edges of the complete graph `K_n`, as a function on
unordered pairs of vertices. -/
abbrev Coloring (n : ℕ) := Sym2 (Fin n) → Bool

/-- A finset `S` of vertices is monochromatic in color `b` if every edge between
two distinct vertices of `S` has color `b`. -/
def IsMono (c : Coloring n) (S : Finset (Fin n)) (b : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = b

/-- `c` contains a monochromatic `k`-clique. -/
def HasMonoClique (c : Coloring n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ (IsMono c S true ∨ IsMono c S false)

/-- The set of edges spanned by a vertex set `S`: unordered pairs of distinct
vertices both lying in `S`. -/
def edgesWithin (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.offDiag.image Sym2.mk

/-- The number of edges spanned by an `S` with `S.card = k` is `C(k, 2)`. -/
lemma card_edgesWithin (S : Finset (Fin n)) :
    (edgesWithin S).card = (S.card).choose 2 :=
  Sym2.card_image_offDiag S

/-- **Counting lemma.** Among all `2^N` colorings, at most `2^(N - |T|)` are
constant equal to `b` on a fixed edge set `T` — fixing the colors on `T` leaves
only the edges outside `T` free. -/
lemma constOn_card_le (T : Finset (Sym2 (Fin n))) (b : Bool) :
    (univ.filter (fun c : Coloring n => ∀ e ∈ T, c e = b)).card
      ≤ 2 ^ (Fintype.card (Sym2 (Fin n)) - T.card) := by
  classical
  -- Restrict a coloring to the complement of `T`.
  let ρ : Coloring n → (↥(Tᶜ : Finset (Sym2 (Fin n))) → Bool) := fun c x => c x.1
  have hcard :
      (univ.filter (fun c : Coloring n => ∀ e ∈ T, c e = b)).card
        ≤ (univ : Finset (↥(Tᶜ : Finset (Sym2 (Fin n))) → Bool)).card := by
    apply Finset.card_le_card_of_injOn ρ
    · intro c _; exact mem_univ _
    · intro c1 hc1 c2 hc2 hρ
      have h1 : ∀ e ∈ T, c1 e = b := (mem_filter.mp hc1).2
      have h2 : ∀ e ∈ T, c2 e = b := (mem_filter.mp hc2).2
      funext e
      by_cases he : e ∈ T
      · rw [h1 e he, h2 e he]
      · have hec : e ∈ (Tᶜ : Finset (Sym2 (Fin n))) := mem_compl.mpr he
        have := congrFun hρ ⟨e, hec⟩
        simpa [ρ] using this
  calc
    (univ.filter (fun c : Coloring n => ∀ e ∈ T, c e = b)).card
        ≤ (univ : Finset (↥(Tᶜ : Finset (Sym2 (Fin n))) → Bool)).card := hcard
    _ = Fintype.card (↥(Tᶜ : Finset (Sym2 (Fin n))) → Bool) := Finset.card_univ
    _ = 2 ^ (Fintype.card (Sym2 (Fin n)) - T.card) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl]

/-- **Erdős (1947) first-moment lower bound.** If `2·C(n,k) < 2^{C(k,2)}` then the
union bound beats the total count, so some 2-coloring of `K_n` has *no*
monochromatic `k`-clique. This is the probabilistic-method lower bound for the
Ramsey number, here proved by an exact counting (no probability, no choice beyond
classical logic of finite sets). -/
theorem exists_good_coloring (n k : ℕ)
    (h : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ c : Coloring n, ¬ HasMonoClique c k := by
  classical
  set N := Fintype.card (Sym2 (Fin n)) with hN
  by_contra hcon
  push_neg at hcon
  -- From `hcon` every coloring has a monochromatic `k`-clique; in particular `k ≤ n`.
  have hkn : k ≤ n := by
    obtain ⟨S, hScard, _⟩ := hcon (fun _ => true)
    have : S.card ≤ n := by
      have := Finset.card_le_univ S
      simpa [Fintype.card_fin] using this
    omega
  -- `C(k,2) ≤ N`.
  have hkN : k.choose 2 ≤ N := by
    have h1 : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    have h2 : n.choose 2 ≤ (n + 1).choose 2 := Nat.choose_le_choose 2 (Nat.le_succ n)
    have h3 : (n + 1).choose 2 = N := by
      rw [hN, Sym2.card, Fintype.card_fin]
    omega
  -- The "monochromatic on `S` in color `b`" colorings.
  let M : Finset (Fin n) → Bool → Finset (Coloring n) :=
    fun S b => univ.filter (fun c : Coloring n => IsMono c S b)
  -- Every coloring is covered by some `M S true ∪ M S false` with `S` of card `k`.
  have cover :
      (univ : Finset (Coloring n)) ⊆
        (powersetCard k univ).biUnion (fun S => M S true ∪ M S false) := by
    intro c _
    obtain ⟨S, hScard, hmono⟩ := hcon c
    rw [mem_biUnion]
    refine ⟨S, ?_, ?_⟩
    · rw [mem_powersetCard]; exact ⟨subset_univ S, hScard⟩
    · rw [mem_union]
      rcases hmono with hT | hF
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _, hT⟩)
      · exact Or.inr (mem_filter.mpr ⟨mem_univ _, hF⟩)
  -- Per-set bound: |M S b| ≤ 2^(N - C(k,2)) when S has card k.
  have hMbound : ∀ S ∈ powersetCard k univ, ∀ b,
      (M S b).card ≤ 2 ^ (N - k.choose 2) := by
    intro S hS b
    have hScard : S.card = k := (mem_powersetCard.mp hS).2
    -- `IsMono c S b` forces `c` constant `b` on `edgesWithin S`.
    have hsub : M S b ⊆ univ.filter (fun c : Coloring n => ∀ e ∈ edgesWithin S, c e = b) := by
      intro c hc
      rw [mem_filter] at hc ⊢
      refine ⟨hc.1, ?_⟩
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hx, hy, hxy⟩ := Finset.mem_offDiag.mp hp
      exact hc.2 p.1 hx p.2 hy hxy
    calc (M S b).card
        ≤ (univ.filter (fun c : Coloring n => ∀ e ∈ edgesWithin S, c e = b)).card :=
          Finset.card_le_card hsub
      _ ≤ 2 ^ (N - (edgesWithin S).card) := constOn_card_le _ _
      _ = 2 ^ (N - k.choose 2) := by rw [card_edgesWithin, hScard]
  -- Assemble the union bound.
  have hbig : (univ : Finset (Coloring n)).card ≤ 2 * n.choose k * 2 ^ (N - k.choose 2) := by
    calc (univ : Finset (Coloring n)).card
        ≤ ∑ S ∈ powersetCard k univ, (M S true ∪ M S false).card :=
          le_trans (Finset.card_le_card cover) (Finset.card_biUnion_le)
      _ ≤ ∑ S ∈ powersetCard k univ, 2 * 2 ^ (N - k.choose 2) := by
          apply Finset.sum_le_sum
          intro S hS
          calc (M S true ∪ M S false).card
              ≤ (M S true).card + (M S false).card := Finset.card_union_le _ _
            _ ≤ 2 ^ (N - k.choose 2) + 2 ^ (N - k.choose 2) :=
                Nat.add_le_add (hMbound S hS true) (hMbound S hS false)
            _ = 2 * 2 ^ (N - k.choose 2) := by ring
      _ = (powersetCard k univ).card * (2 * 2 ^ (N - k.choose 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = n.choose k * (2 * 2 ^ (N - k.choose 2)) := by
          rw [Finset.card_powersetCard]; simp [Fintype.card_fin]
      _ = 2 * n.choose k * 2 ^ (N - k.choose 2) := by ring
  -- But the total count is `2^N`, and the hypothesis makes the bound too small.
  have htot : (univ : Finset (Coloring n)).card = 2 ^ N := by
    rw [hN, Finset.card_univ]
    simp [Coloring, Fintype.card_fun]
  rw [htot] at hbig
  -- `2 * C(n,k) * 2^(N-C(k,2)) < 2^(C(k,2)) * 2^(N-C(k,2)) = 2^N`, contradiction.
  have hpos : 0 < 2 ^ (N - k.choose 2) := pow_pos (by norm_num) _
  have hlt : 2 * n.choose k * 2 ^ (N - k.choose 2) < 2 ^ (k.choose 2) * 2 ^ (N - k.choose 2) :=
    mul_lt_mul_of_pos_right h hpos
  have heq : 2 ^ (k.choose 2) * 2 ^ (N - k.choose 2) = 2 ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hkN]
  rw [heq] at hlt
  exact absurd (lt_of_le_of_lt hbig hlt) (lt_irrefl _)

/-!
## Consequences

The counting bound gives concrete Ramsey lower bounds: if `2·C(n,k) < 2^{C(k,2)}`
then every red/blue coloring evading a monochromatic `K_k` exists on `K_n`, so the
Ramsey number `R(k) > n`. For example `R(3) > 3` and the asymptotic
`R(k) ≥ (1+o(1))·(k/e)·2^{k/2}` both follow from this single inequality.
-/

/-- `R(3) > 3`: there is a 2-coloring of `K_3` with no monochromatic triangle. -/
theorem exists_good_coloring_three : ∃ c : Coloring 3, ¬ HasMonoClique c 3 := by
  apply exists_good_coloring
  decide

end Erdos1029LB
