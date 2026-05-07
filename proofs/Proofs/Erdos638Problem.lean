/-
# Erdős Problem 638: Ramsey Families and Infinite Cardinals

Let `S` be a family of finite graphs such that for every `n`, there exists
some `G_n ∈ S` where every `n`-colouring of the edges of `G_n` yields a
monochromatic triangle.

For every infinite cardinal `ℵ`, does there exist a graph `G` such that
every finite subgraph of `G` belongs to `S`, and every `ℵ`-colouring of
the edges of `G` yields a monochromatic triangle?

Erdős notes: "if the answer is affirmative many extensions and
generalisations will be possible."

*Reference:* [erdosproblems.com/638](https://www.erdosproblems.com/638)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

open SimpleGraph

/- ## Ramsey property for triangles -/

/-- A colouring of edges yields a monochromatic triangle if there exist
three mutually adjacent vertices whose edges all receive the same colour. -/
def HasMonoTriangle {V : Type*} {α : Type*} (G : SimpleGraph V)
    (c : V → V → α) : Prop :=
    ∃ (a b d : V), a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
      G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
      c a b = c b d ∧ c b d = c a d

/-- A graph `G` has the `n`-colour Ramsey property for triangles if every
colouring of its vertex pairs with `n` colours yields a monochromatic
triangle. -/
def HasTriangleRamsey {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∀ c : V → V → Fin n, HasMonoTriangle G c

/- ## Ramsey families -/

/-- A Ramsey family is a collection of finite graphs (indexed by vertex
count) such that for every `n`, some member has the `n`-colour triangle
Ramsey property. -/
def IsRamseyFamily (S : (m : ℕ) → Set (SimpleGraph (Fin m))) : Prop :=
    ∀ n : ℕ, 1 ≤ n →
      ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
        G ∈ S m ∧ HasTriangleRamsey G n

/-- A graph has the `κ`-colour triangle Ramsey property (for any type of
`κ` colours). -/
def HasCardinalTriangleRamsey {V : Type*} (G : SimpleGraph V)
    (κ : Type*) : Prop :=
    ∀ c : V → V → κ, HasMonoTriangle G c

/- ## Main conjecture -/

/-- Erdős Problem 638: For every Ramsey family `S` and every infinite
colour type, there exists a graph with the appropriate Ramsey property. -/
def ErdosProblem638 : Prop :=
    ∀ (S : (m : ℕ) → Set (SimpleGraph (Fin m))),
      IsRamseyFamily S →
        ∀ (κ : Type), Infinite κ →
          ∃ (V : Type) (G : SimpleGraph V),
            HasCardinalTriangleRamsey G κ

/- ## Basic observations -/

/-- For 1 colour, K_3 has the triangle Ramsey property: every 1-colouring
    trivially yields a monochromatic triangle (Fin 1 is a subsingleton). -/
theorem ramsey_triangle_base :
    HasTriangleRamsey (⊤ : SimpleGraph (Fin 3)) 1 := by
  intro c
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | simp [SimpleGraph.top_adj] | exact Subsingleton.elim _ _

/-- The n = 1 case of ramsey_triangle, proved without using any axiom. -/
theorem ramsey_triangle_one_proved :
    ∃ N : ℕ, HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) 1 :=
  ⟨3, ramsey_triangle_base⟩

/-- Monotonicity: if `G` has the `n`-colour property and `m ≤ n`, then
`G` also has the `m`-colour property. Proved by embedding Fin m into
Fin n via castLE; injectivity preserves monochromaticity. -/
theorem triangle_ramsey_mono {V : Type*} (G : SimpleGraph V) (m n : ℕ)
    (hmn : m ≤ n) (h : HasTriangleRamsey G n) : HasTriangleRamsey G m := by
  intro c
  obtain ⟨a, b, d, hab, hbd, had, eab, ebd, ead, hc1, hc2⟩ :=
    h (fun v w => (c v w).castLE hmn)
  have hInj : Function.Injective (Fin.castLE hmn) := Fin.castLE_injective hmn
  exact ⟨a, b, d, hab, hbd, had, eab, ebd, ead, hInj hc1, hInj hc2⟩

/- ## Helpers for Ramsey inductive step -/

/-- Remove one element from Fin (m+1), producing Fin m. Given i₀ and j with j ≠ i₀,
    returns a value in Fin m by shifting indices above i₀ down by 1. -/
private def shrinkFin {m : ℕ} (i₀ j : Fin (m + 1)) (hj : j ≠ i₀) : Fin m :=
  if j.val < i₀.val then
    ⟨j.val, by omega⟩
  else
    ⟨j.val - 1, by
      have := j.isLt; have : j.val ≠ i₀.val := Fin.val_ne_of_ne hj; omega⟩

/-- shrinkFin is injective: distinct inputs (both ≠ i₀) produce distinct outputs. -/
private theorem shrinkFin_injective {m : ℕ} (i₀ : Fin (m + 1))
    {j₁ j₂ : Fin (m + 1)} (hj₁ : j₁ ≠ i₀) (hj₂ : j₂ ≠ i₀)
    (heq : shrinkFin i₀ j₁ hj₁ = shrinkFin i₀ j₂ hj₂) : j₁ = j₂ := by
  have hv1 : j₁.val ≠ i₀.val := Fin.val_ne_of_ne hj₁
  have hv2 : j₂.val ≠ i₀.val := Fin.val_ne_of_ne hj₂
  have heq' := congrArg Fin.val heq
  unfold shrinkFin at heq'
  split_ifs at heq' with h₁ h₂ h₁ h₂
  · exact Fin.ext heq'
  · omega
  · omega
  · exact Fin.ext (by omega)

/- ## Classical Ramsey theorem -/

/-- Transferring Ramsey property to larger complete graphs. If K_N has the
    n-colour Ramsey property and M ≥ N, then K_M also does. -/
theorem ramsey_mono {N M : ℕ} (h : N ≤ M) {n : ℕ}
    (hN : HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) n) :
    HasTriangleRamsey (⊤ : SimpleGraph (Fin M)) n := by
  intro c
  obtain ⟨a, b, d, hab, hbd, had, eab, ebd, ead, hc1, hc2⟩ :=
    hN (fun i j => c (Fin.castLE h i) (Fin.castLE h j))
  refine ⟨Fin.castLE h a, Fin.castLE h b, Fin.castLE h d,
    fun heq => hab (Fin.castLE_injective h heq),
    fun heq => hbd (Fin.castLE_injective h heq),
    fun heq => had (Fin.castLE_injective h heq), ?_, ?_, ?_, hc1, hc2⟩
  all_goals simp [SimpleGraph.top_adj, Fin.castLE_injective h |>.ne_iff] <;> assumption

/-- The inductive step of the Ramsey theorem: given a coloring of K_N with
    n+2 colors and a Ramsey bound M for n+1 colors, find a monochromatic
    triangle.

    Proof: Fix vertex v₀. By pigeonhole on N-1 ≥ (n+2)(M-1)+1 neighbors,
    some color class has ≥ M vertices. If any edge within that class matches
    v₀'s color, we get a triangle through v₀. Otherwise, those M vertices
    use only n+1 colors among themselves, and the IH yields a triangle. -/
private theorem ramsey_inductive_step
    {N n : ℕ} (c : Fin N → Fin N → Fin (n + 2))
    (M : ℕ) (hM : HasTriangleRamsey (⊤ : SimpleGraph (Fin M)) (n + 1))
    (hN : (n + 2) * (M - 1) + 2 ≤ N) :
    HasMonoTriangle (⊤ : SimpleGraph (Fin N)) c := by
  -- Step 1: Fix distinguished vertex v₀
  set v₀ : Fin N := ⟨0, by omega⟩
  -- Step 2: Non-v₀ vertices, colored by edge to v₀
  set S := Finset.univ.erase v₀
  have hS_card : S.card = N - 1 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ v₀)]
  -- Step 3: Pigeonhole — some color class has > M-1 (i.e. ≥ M) vertices
  have hpig : (Finset.univ : Finset (Fin (n + 2))).card * (M - 1) < S.card := by
    simp [Finset.card_fin, hS_card]; omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun (a : Fin N) _ => Finset.mem_univ (c v₀ a)) hpig
  -- A = monochromatic neighborhood of v₀ with color i₀
  set A := S.filter (fun v => c v₀ v = i₀)
  have hA_card : M ≤ A.card := by omega
  have hA_color : ∀ a ∈ A, c v₀ a = i₀ :=
    fun a ha => (Finset.mem_filter.mp ha).2
  have hA_ne : ∀ a ∈ A, a ≠ v₀ :=
    fun a ha => Finset.ne_of_mem_erase (Finset.mem_filter.mp ha).1
  -- Step 4: Case split — does any pair within A share color i₀?
  by_cases hcase : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂ ∧ c a₁ a₂ = i₀
  · -- Case 1: Found a same-color pair → triangle (v₀, a₁, a₂)
    obtain ⟨a₁, ha₁, a₂, ha₂, hne, hcol⟩ := hcase
    exact ⟨v₀, a₁, a₂,
      (hA_ne a₁ ha₁).symm, hne, (hA_ne a₂ ha₂).symm,
      top_adj.mpr (hA_ne a₁ ha₁).symm,
      top_adj.mpr hne,
      top_adj.mpr (hA_ne a₂ ha₂).symm,
      by rw [hA_color a₁ ha₁, hcol],
      by rw [hcol, hA_color a₂ ha₂]⟩
  · -- Case 2: No pair in A has color i₀ → restricted to n+1 colors → use IH
    push_neg at hcase
    have hA_avoid : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → c a₁ a₂ ≠ i₀ :=
      fun a₁ ha₁ a₂ ha₂ hne => hcase a₁ ha₁ a₂ ha₂ hne
    -- By ramsey_mono, K_{A.card} has (n+1)-color Ramsey since M ≤ A.card
    have hA_ramsey := ramsey_mono hA_card hM
    -- Embed Fin A.card into Fin N via the ordered elements of A
    set emb := A.orderIsoOfFin rfl
    have he_mem : ∀ i : Fin A.card, (emb i).val ∈ A := fun i => (emb i).property
    -- Build (n+1)-coloring on Fin A.card by removing color i₀
    set c' : Fin A.card → Fin A.card → Fin (n + 1) := fun i j =>
      if h : (emb i : Fin N) = (emb j : Fin N) then ⟨0, by omega⟩
      else shrinkFin i₀ (c (emb i) (emb j))
        (hA_avoid _ (he_mem i) _ (he_mem j) h)
    -- Apply Ramsey IH
    obtain ⟨a, b, d, hab, hbd, had, _, _, _, hc1', hc2'⟩ := hA_ramsey c'
    -- Distinct vertices in A map to distinct vertices in Fin N
    have hab' : (emb a : Fin N) ≠ emb b := by
      intro h; exact hab (emb.injective (Subtype.val_injective h))
    have hbd' : (emb b : Fin N) ≠ emb d := by
      intro h; exact hbd (emb.injective (Subtype.val_injective h))
    have had' : (emb a : Fin N) ≠ emb d := by
      intro h; exact had (emb.injective (Subtype.val_injective h))
    -- Extract original color equalities via shrinkFin injectivity
    have hc'_ab : c' a b = shrinkFin i₀ (c (emb a) (emb b))
        (hA_avoid _ (he_mem a) _ (he_mem b) hab') := dif_neg hab'
    have hc'_bd : c' b d = shrinkFin i₀ (c (emb b) (emb d))
        (hA_avoid _ (he_mem b) _ (he_mem d) hbd') := dif_neg hbd'
    have hc'_ad : c' a d = shrinkFin i₀ (c (emb a) (emb d))
        (hA_avoid _ (he_mem a) _ (he_mem d) had') := dif_neg had'
    rw [hc'_ab, hc'_bd] at hc1'
    rw [hc'_bd, hc'_ad] at hc2'
    exact ⟨(emb a).val, (emb b).val, (emb d).val,
      hab', hbd', had',
      top_adj.mpr hab', top_adj.mpr hbd', top_adj.mpr had',
      shrinkFin_injective i₀ (hA_avoid _ (he_mem a) _ (he_mem b) hab')
        (hA_avoid _ (he_mem b) _ (he_mem d) hbd') hc1',
      shrinkFin_injective i₀ (hA_avoid _ (he_mem b) _ (he_mem d) hbd')
        (hA_avoid _ (he_mem a) _ (he_mem d) had') hc2'⟩

/-- **The n-colour Ramsey theorem for triangles** (proved by induction):
    for every n ≥ 1, there exists N such that every n-colouring of K_N
    contains a monochromatic triangle.

    The bound is R(1) = 3, R(n+1) ≤ (n+1)·(R(n)-1) + 2. -/
theorem ramsey_triangle (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      exact ⟨3, ramsey_triangle_base⟩
    | succ n =>
      obtain ⟨M, hM⟩ := ih (by omega : 1 ≤ n + 1)
      exact ⟨(n + 2) * (M - 1) + 2,
        fun c => ramsey_inductive_step c M hM le_rfl⟩

/-- The family of complete graphs is a Ramsey family.
    Proved from ramsey_triangle. -/
theorem complete_graphs_ramsey :
    IsRamseyFamily (fun m => ({⊤} : Set (SimpleGraph (Fin m)))) := by
  intro n hn
  obtain ⟨N, hN⟩ := ramsey_triangle n hn
  exact ⟨N, ⊤, Set.mem_singleton _, hN⟩

/- ## Partial results toward Erdős Problem #638

These lemmas locate the precise threshold at which the cardinal-Ramsey question
becomes nontrivial. For the complete-graph family, the answer is YES whenever the
colour count is finite (sec. complete_omega_finite_ramsey, immediate from the
finite Ramsey theorem) but NO for ω vertices and ℵ₀ colours (sec.
complete_omega_no_nat_ramsey, via an explicit min-coloring counterexample). The
Erdős–Rado theorem `(2^ℵ₀)⁺ → (ℵ₁)²_ℵ₀` would establish the conjecture for the
complete-graph family at every infinite cardinal κ, but the required vertex set
must be at least `(2^|κ|)⁺` — strictly more than κ. Bridging the finite/infinite
threshold for general Ramsey families is what makes Problem #638 open.
-/

/-- **Positive partial result**: The complete graph on ℕ has the n-colour
    triangle Ramsey property for any n ≥ 1.

    This is an immediate corollary of the finite Ramsey theorem: the first
    R(n) values of ℕ form a copy of K_{R(n)}, so any n-colouring of K_ℕ
    restricted there yields a monochromatic triangle. Establishes that the
    finite Ramsey theorem lifts to ω vertices whenever the colour count is
    finite. -/
theorem complete_omega_finite_ramsey (n : ℕ) (hn : 1 ≤ n) :
    HasTriangleRamsey (⊤ : SimpleGraph ℕ) n := by
  intro c
  obtain ⟨N, hN⟩ := ramsey_triangle n hn
  obtain ⟨a, b, d, hab, hbd, had, _, _, _, hc1, hc2⟩ :=
    hN (fun i j => c i.val j.val)
  refine ⟨a.val, b.val, d.val, ?_, ?_, ?_, ?_, ?_, ?_, hc1, hc2⟩
  · exact fun h => hab (Fin.ext h)
  · exact fun h => hbd (Fin.ext h)
  · exact fun h => had (Fin.ext h)
  · exact top_adj.mpr (fun h => hab (Fin.ext h))
  · exact top_adj.mpr (fun h => hbd (Fin.ext h))
  · exact top_adj.mpr (fun h => had (Fin.ext h))

/-- **Negative partial result**: The complete graph on ℕ does NOT have the
    ℕ-cardinal triangle Ramsey property.

    The symmetric coloring `c i j = min i j` admits no monochromatic triangle:
    for any three distinct vertices a, b, d, two of the three pairwise mins
    equal the smallest of the trio while the third is strictly larger, so all
    three colours cannot coincide.

    This identifies the precise obstruction in Erdős Problem #638: at the
    countable cardinal threshold, ω vertices are insufficient to force
    monochromatic triangles. The Erdős–Rado theorem requires at least
    `(2^ℵ₀)⁺` vertices for the ℵ₀-colour case. -/
theorem complete_omega_no_nat_ramsey :
    ¬ HasCardinalTriangleRamsey (⊤ : SimpleGraph ℕ) ℕ := by
  intro h
  obtain ⟨a, b, d, hab, hbd, had, _, _, _, hc1, hc2⟩ :=
    h (fun i j => min i j)
  -- hc1 : min a b = min b d, hc2 : min b d = min a d
  -- Three distinct naturals cannot have all three pairwise mins equal.
  simp only at hc1 hc2
  omega
