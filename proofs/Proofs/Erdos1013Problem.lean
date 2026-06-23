/-
# Erdős Problem #1013: Triangle-Free Chromatic Threshold

Let h₃(k) be the smallest n such that there exists a triangle-free graph
on n vertices with chromatic number k. Find an asymptotic formula for h₃(k).
Is it true that h₃(k+1)/h₃(k) → 1?

## Key Results

- **Lower bound**: h₃(k) ≥ (1/2 − o(1))·k²·log k
- **Upper bound**: h₃(k) ≤ (1 + o(1))·k²·log k
- **Graver–Yackel** (1968): h₃(k) ≫ (log k / log log k)·k²
- **Open**: exact asymptotic constant and ratio convergence

## References

- Graver, Yackel (1968)
- Related: Problem #1104 (dual function f(n)), Problem #920 (K_r-free)
- OEIS A292528
- <https://erdosproblems.com/1013>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A graph is triangle-free if it contains no clique of size 3. -/
def IsTriangleFree (G : SimpleGraph (Fin n)) : Prop :=
  ¬∃ (a b c : Fin n), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A proper k-coloring of graph G: assignment of colors 1..k to vertices
    such that adjacent vertices get different colors. -/
def HasProperColoring (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ f : Fin n → Fin k, ∀ (u v : Fin n), G.Adj u v → f u ≠ f v

/-- The chromatic number of G: the minimum k for which a proper k-coloring exists. -/
noncomputable def chromaticNumber (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ¬HasProperColoring G k} + 1

/-- h₃(k): the smallest n such that there exists a triangle-free graph
    on n vertices with chromatic number ≥ k. -/
noncomputable def triangleFreeChromThreshold (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), IsTriangleFree G ∧ ¬HasProperColoring G (k - 1)}

/- ## Main Conjecture -/

/-- **Erdős's Conjecture (Asymptotic, OPEN)**: h₃(k) ~ c·k²·log k for some
    constant c. Combined with known bounds, c ∈ [1/2, 1].
    Stated as a definition since this is an open problem. -/
def Erdos1013Asymptotic : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun k => (triangleFreeChromThreshold k : ℝ) / ((k : ℝ) ^ 2 * Real.log k))
      Filter.atTop (nhds c)

/-- **Ratio Convergence (OPEN)**: h₃(k+1)/h₃(k) → 1 as k → ∞.
    The threshold grows smoothly without large jumps.
    Stated as a definition since this is part of the open problem. -/
def Erdos1013RatioConvergence : Prop :=
  Filter.Tendsto
    (fun k => (triangleFreeChromThreshold (k + 1) : ℝ) /
              (triangleFreeChromThreshold k : ℝ))
    Filter.atTop (nhds 1)

/- ## Known Bounds -/

/-- **Lower bound**: h₃(k) ≥ (1/2 − o(1))·k²·log k.
    No triangle-free graph on fewer vertices can have chromatic number k. -/
/-- **Upper bound**: h₃(k) ≤ (1 + o(1))·k²·log k.
    There exist triangle-free graphs achieving chromatic number k
    on this many vertices. -/
/-- **Graver–Yackel** (1968): h₃(k) ≫ (log k / log log k)·k².
    Early lower bound using probabilistic deletion.

    Note: The previous statement used `c > 0 →` (implication) inside
    the existential, making it trivially true by picking c ≤ 0.
    Fixed to use `c > 0 ∧` (conjunction). -/
/- ## Helper Lemmas -/

/-- Coloring monotonicity: k-colorable implies m-colorable for k ≤ m. -/
private theorem coloring_le_mono {m : ℕ} (G : SimpleGraph (Fin m)) {j k : ℕ}
    (hjk : j ≤ k) (h : HasProperColoring G j) : HasProperColoring G k := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun v => ⟨(f v).val, Nat.lt_of_lt_of_le (f v).isLt hjk⟩, fun u v hadj heq => ?_⟩
  simp only [Fin.mk.injEq] at heq
  exact hf u v hadj (Fin.val_injective heq)

/-- Any graph on Fin 1 is triangle-free (only one vertex). -/
private theorem fin1_triangle_free (G : SimpleGraph (Fin 1)) : IsTriangleFree G := by
  intro ⟨a, b, _, hab, _, _, _⟩
  exact absurd (Subsingleton.elim a b) hab

/-- Any graph on Fin 1 is 1-colorable (no edges possible). -/
private theorem fin1_one_colorable (G : SimpleGraph (Fin 1)) : HasProperColoring G 1 :=
  ⟨fun _ => 0, fun u v hadj => absurd (Subsingleton.elim u v) hadj.ne⟩

/-- Mycielski's construction: for each k ≥ 2, there exists a triangle-free
    graph with chromatic number k. This proves h₃(k) is finite. -/
axiom mycielski_construction :
  ∀ k : ℕ, k ≥ 2 → ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    IsTriangleFree G ∧ ¬HasProperColoring G (k - 1)

/-- The threshold set {n | ∃ TF graph on n vertices not (k-1)-colorable} is always nonempty. -/
private lemma threshold_set_nonempty (k : ℕ) :
    Set.Nonempty {n : ℕ | ∃ G : SimpleGraph (Fin n),
      IsTriangleFree G ∧ ¬HasProperColoring G (k - 1)} := by
  rcases k with _ | _ | k
  · exact ⟨1, ⊥, fin1_triangle_free _, fun ⟨f, _⟩ => absurd (f 0).isLt (by omega)⟩
  · exact ⟨1, ⊥, fin1_triangle_free _, fun ⟨f, _⟩ => absurd (f 0).isLt (by omega)⟩
  · exact mycielski_construction (k + 2) (by omega)

/- ## Structural Properties -/

/-- Monotonicity: h₃ is non-decreasing. Higher chromatic number needs more vertices. -/
theorem threshold_mono :
    ∀ j k : ℕ, j ≤ k → triangleFreeChromThreshold j ≤ triangleFreeChromThreshold k := by
  intro j k hjk
  unfold triangleFreeChromThreshold
  apply csInf_le_csInf (OrderBot.bddBelow _)
  · exact threshold_set_nonempty k
  · intro n ⟨G, hTF, hG⟩
    exact ⟨G, hTF, fun hcolor => hG (coloring_le_mono G (by omega : j - 1 ≤ k - 1) hcolor)⟩

/-- h₃(1) = 1: a single vertex graph has chromatic number 1 and is triangle-free. -/
theorem threshold_one :
    triangleFreeChromThreshold 1 = 1 := by
  unfold triangleFreeChromThreshold
  simp only [show (1 : ℕ) - 1 = 0 from rfl]
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _)
      ⟨⊥, fin1_triangle_free _, fun ⟨f, _⟩ => absurd (f 0).isLt (by omega)⟩
  · apply le_csInf (threshold_set_nonempty 1)
    intro n ⟨_, _, hG⟩
    rcases Nat.eq_zero_or_pos n with rfl | h_pos
    · exact absurd ⟨Fin.elim0, fun v => v.elim0⟩ hG
    · exact h_pos

/-- h₃(2) = 2: K₂ (a single edge) is the smallest triangle-free graph
    with chromatic number ≥ 2. -/
theorem threshold_two :
    triangleFreeChromThreshold 2 = 2 := by
  unfold triangleFreeChromThreshold
  simp only [show (2 : ℕ) - 1 = 1 from rfl]
  have h_tf : IsTriangleFree (⊤ : SimpleGraph (Fin 2)) := by
    intro ⟨a, b, c, hab, _, hac, _, _, _⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  have h_nc : ¬HasProperColoring (⊤ : SimpleGraph (Fin 2)) 1 := by
    intro ⟨f, hf⟩
    have hadj : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by
      show (0 : Fin 2) ≠ 1; decide
    exact absurd (Subsingleton.elim (f 0) (f 1)) (hf 0 1 hadj)
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) ⟨⊤, h_tf, h_nc⟩
  · apply le_csInf (threshold_set_nonempty 2)
    intro n ⟨G, _, hG⟩
    by_contra h_lt
    push_neg at h_lt
    interval_cases n
    · exact hG ⟨Fin.elim0, fun v => v.elim0⟩
    · exact hG (fin1_one_colorable G)

/-- h₃(3) = 5: the Mycielski graph M₃ (cycle C₅) has 5 vertices, is triangle-free,
    and has chromatic number 3. -/
/-- h₃(4) = 11: the Mycielski graph M₄ (Grötzsch graph) has 11 vertices,
    is triangle-free, with chromatic number 4. -/
/- ## Proved Results -/

/-- **Any graph can be n-colored using n colors** (one color per vertex). -/
theorem trivial_n_coloring (n : ℕ) (G : SimpleGraph (Fin n)) :
    HasProperColoring G n := by
  exact ⟨id, fun u v hadj => G.ne_of_adj hadj⟩

/-- **Proper coloring monotonicity:** if G has a k-coloring, it has a (k+1)-coloring. -/
theorem coloring_monotone (n k : ℕ) (G : SimpleGraph (Fin n))
    (h : HasProperColoring G k) : HasProperColoring G (k + 1) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun v => (f v).castSucc, fun u v hadj => by
    simp [Fin.castSucc]
    exact hf u v hadj⟩

/-- **The empty graph (0 vertices) is trivially k-colorable for any k.** -/
theorem empty_graph_colorable (k : ℕ) (G : SimpleGraph (Fin 0)) :
    HasProperColoring G k := by
  exact ⟨fun v => v.elim0, fun v => v.elim0⟩

/-- **The empty graph is triangle-free.** -/
theorem empty_graph_triangle_free (G : SimpleGraph (Fin 0)) :
    IsTriangleFree G := by
  intro ⟨a, _, _, _, _, _, _⟩
  exact a.elim0

/-- **A single-vertex graph is triangle-free.** -/
theorem single_vertex_triangle_free (G : SimpleGraph (Fin 1)) :
    IsTriangleFree G := by
  intro ⟨a, b, _, hab, _, _, _⟩
  exact absurd (Subsingleton.elim a b) hab
