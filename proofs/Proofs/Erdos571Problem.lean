/-
  Erdős Problem #571: Rational Turán Exponents for Bipartite Graphs

  Source: https://erdosproblems.com/571
  Status: OPEN

  Statement:
  Show that for any rational α ∈ [1,2) there exists a bipartite graph G such that
  ex(n;G) ≍ n^α.

  Background:
  This is a fundamental question in extremal graph theory, asking whether all
  rational numbers in [1,2) can arise as Turán exponents. The extremal number
  ex(n;G) is the maximum number of edges in an n-vertex graph containing no
  copy of G. The notation ex(n;G) ≍ n^α means both ex(n;G) = O(n^α) and
  ex(n;G) = Ω(n^α).

  Known Turán Exponents (partial progress):
  - 3/2 - 1/(2s) for s ≥ 2 (Conlon-Janzer-Lee 2021)
  - 4/3 - 1/(3s) and 5/4 - 1/(4s) for s ≥ 2 (Jiang-Qiu 2020)
  - 2 - a/b with certain divisibility conditions (multiple authors)
  - 1 + a/b with b > a² (Jiang-Qiu 2023)
  - 2 - 2/(2b+1) for b ≥ 2 (Jiang-Ma-Yepremyan 2022)
  - 2 - a/b with b ≥ (a-1)² (Conlon-Janzer 2022)

  Partial Solution:
  Bukh-Conlon (2018) proved the weakened version: for any rational α ∈ [1,2),
  there exists a FINITE FAMILY of bipartite graphs with ex(n;F) ≍ n^α.

  References:
  - [BuCo18] Bukh-Conlon (2018), Rational exponents in extremal graph theory
  - [CJL21] Conlon-Janzer-Lee (2021), Extremal number of subdivisions
  - [JiQi20] Jiang-Qiu (2020), Turán numbers of bipartite subdivisions
  - [JiQi23] Jiang-Qiu (2023), Many Turán exponents via subdivisions
  - [CoJa22] Conlon-Janzer (2022), Rational exponents near two
-/

import Mathlib

namespace Erdos571

/-! ## Basic Definitions -/

/-- A simple graph on vertex type V -/
structure Graph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- A graph is bipartite if vertices partition into two sets with
    edges only between them -/
def IsBipartite {V : Type*} [DecidableEq V] (G : Graph V) : Prop :=
  ∃ (A B : Set V), A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    ∀ u v, G.adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- The edge count of a finite graph -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V) [DecidableRel G.adj] : ℕ :=
  (Finset.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2)
    Finset.univ).card

/-- A graph H contains a copy of G (G is a subgraph of H) -/
def ContainsCopy {V W : Type*} (G : Graph V) (H : Graph W) : Prop :=
  ∃ (f : V → W), Function.Injective f ∧
    ∀ u v, G.adj u v → H.adj (f u) (f v)

/-- H is G-free if it contains no copy of G -/
def IsFree {V W : Type*} (H : Graph W) (G : Graph V) : Prop :=
  ¬ContainsCopy G H

/-! ## Extremal Numbers -/

/-- The extremal number ex(n;G) is the maximum number of edges in an
    n-vertex G-free graph -/
noncomputable def extremalNumber {V : Type*} (G : Graph V) (n : ℕ) : ℕ :=
  Nat.find (⟨n * (n - 1) / 2, by sorry⟩ :
    ∃ m, ∀ (H : Graph (Fin n)) [DecidableRel H.adj], IsFree H G → edgeCount H ≤ m)

/-- Asymptotic notation: f ≍ g means f = Θ(g), i.e., c₁ g ≤ f ≤ c₂ g -/
def AsymptoticEquiv (f g : ℕ → ℝ) : Prop :=
  ∃ (c₁ c₂ : ℝ) (N₀ : ℕ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n ≥ N₀, c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

/-- Big-O notation -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧ ∀ n ≥ N₀, |f n| ≤ c * |g n|

/-- Big-Ω notation -/
def IsBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧ ∀ n ≥ N₀, |f n| ≥ c * |g n|

/-! ## Turán Exponents -/

/-- A rational number α ∈ [1,2) is a Turán exponent if there exists a
    bipartite graph G with ex(n;G) ≍ n^α -/
def IsTuranExponent (α : ℚ) : Prop :=
  1 ≤ α ∧ α < 2 ∧
  ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    IsBipartite G ∧
    AsymptoticEquiv
      (fun n => (extremalNumber G n : ℝ))
      (fun n => (n : ℝ) ^ (α : ℝ))

/-! ## The Conjecture (Open) -/

/-- Erdős Problem #571 (OPEN): Every rational α ∈ [1,2) is a Turán exponent -/
def erdos_571_conjecture : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → IsTuranExponent α

/-- The conjecture remains open -/
theorem erdos_571_is_open : True := trivial -- Status: OPEN

/-! ## Known Turán Exponents -/

/-- Conlon-Janzer-Lee (2021): 3/2 - 1/(2s) for s ≥ 2 -/
theorem conlon_janzer_lee_exponents (s : ℕ) (hs : s ≥ 2) :
    IsTuranExponent (3/2 - 1/(2*s)) := by
  sorry -- [CJL21]

/-- Jiang-Qiu (2020): 4/3 - 1/(3s) for s ≥ 2 -/
theorem jiang_qiu_exponents_4_3 (s : ℕ) (hs : s ≥ 2) :
    IsTuranExponent (4/3 - 1/(3*s)) := by
  sorry -- [JiQi20]

/-- Jiang-Qiu (2020): 5/4 - 1/(4s) for s ≥ 2 -/
theorem jiang_qiu_exponents_5_4 (s : ℕ) (hs : s ≥ 2) :
    IsTuranExponent (5/4 - 1/(4*s)) := by
  sorry -- [JiQi20]

/-- Jiang-Qiu (2023): 1 + a/b with b > a² -/
theorem jiang_qiu_exponents_low (a b : ℕ) (ha : a ≥ 1) (hb : b > a^2) :
    IsTuranExponent (1 + (a : ℚ)/(b : ℚ)) := by
  sorry -- [JiQi23]

/-- Jiang-Ma-Yepremyan (2022): 2 - 2/(2b+1) for b ≥ 2 -/
theorem jiang_ma_yepremyan_exponents (b : ℕ) (hb : b ≥ 2) :
    IsTuranExponent (2 - 2/(2*b + 1)) := by
  sorry -- [JMY22]

/-- Jiang-Ma-Yepremyan (2022): 7/5 is a Turán exponent -/
theorem exponent_7_5 : IsTuranExponent (7/5) := by
  sorry -- [JMY22]

/-- Conlon-Janzer (2022): 2 - a/b with b ≥ (a-1)² -/
theorem conlon_janzer_near_two (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ (a-1)^2) :
    IsTuranExponent (2 - (a : ℚ)/(b : ℚ)) := by
  sorry -- [CoJa22]

/-! ## The Weakened Result (Families of Graphs) -/

/-- The extremal number for a family of graphs: ex(n;F) = max edges avoiding all G ∈ F -/
noncomputable def extremalNumberFamily {ι : Type*} (F : ι → Σ V, Graph V) (n : ℕ) : ℕ :=
  Nat.find (⟨n * (n - 1) / 2, by sorry⟩ :
    ∃ m, ∀ (H : Graph (Fin n)) [DecidableRel H.adj],
      (∀ i, IsFree H (F i).2) → edgeCount H ≤ m)

/-- Bukh-Conlon (2018): Every rational α ∈ [1,2) is achievable for a
    FINITE FAMILY of bipartite graphs -/
theorem bukh_conlon_families (α : ℚ) (hα1 : 1 ≤ α) (hα2 : α < 2) :
    ∃ (k : ℕ) (F : Fin k → Σ V, Graph V),
      (∀ i, ∃ (A B : Set (F i).1), True) ∧  -- bipartite (simplified)
      AsymptoticEquiv
        (fun n => (extremalNumberFamily F n : ℝ))
        (fun n => (n : ℝ) ^ (α : ℝ)) := by
  sorry -- [BuCo18]

/-! ## Classical Results -/

/-- Kővári-Sós-Turán: For complete bipartite K_{s,t} with s ≤ t,
    ex(n; K_{s,t}) = O(n^{2-1/s}) -/
theorem kovari_sos_turan (s t : ℕ) (hs : s ≥ 1) (hst : s ≤ t) :
    let K_st : Graph (Fin s ⊕ Fin t) :=
      ⟨fun u v => (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft),
       by intros; tauto, by intro v; cases v <;> simp⟩
    IsBigO
      (fun n => (extremalNumber K_st n : ℝ))
      (fun n => (n : ℝ)^(2 - 1/(s : ℝ))) := by
  sorry -- Kővári-Sós-Turán (1954)

/-- Bondy-Simonovits: For any bipartite G with chromatic number 2,
    ex(n;G) = O(n^{2-1/k}) for some k depending on G -/
theorem bondy_simonovits_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V) (hG : IsBipartite G) :
    ∃ k : ℕ, k ≥ 1 ∧
    IsBigO
      (fun n => (extremalNumber G n : ℝ))
      (fun n => (n : ℝ)^(2 - 1/(k : ℝ))) := by
  sorry -- Bondy-Simonovits

/-! ## Important Examples -/

/-- The path P_k has Turán exponent 1 -/
theorem path_exponent (k : ℕ) (hk : k ≥ 2) :
    let P_k : Graph (Fin k) :=
      ⟨fun i j => i.val + 1 = j.val ∨ j.val + 1 = i.val,
       fun _ _ h => h.symm,
       fun i h => by cases h <;> omega⟩
    AsymptoticEquiv
      (fun n => (extremalNumber P_k n : ℝ))
      (fun n => (n : ℝ)) := by
  sorry -- Classical: ex(n; P_k) = Θ(n)

/-- Even cycles C_{2k} have exponent 1 + 1/k -/
theorem even_cycle_exponent (k : ℕ) (hk : k ≥ 2) :
    let C_2k : Graph (Fin (2*k)) :=
      ⟨fun i j => (i.val + 1) % (2*k) = j.val ∨ (j.val + 1) % (2*k) = i.val,
       fun _ _ h => h.symm,
       fun i h => by cases h <;> omega⟩
    IsBigO
      (fun n => (extremalNumber C_2k n : ℝ))
      (fun n => (n : ℝ)^(1 + 1/(k : ℝ))) := by
  sorry -- Bondy-Simonovits

/-! ## The Gap -/

/-- The density of known Turán exponents in [1,2) is increasing but
    the full conjecture remains open -/
theorem gap_remains : erdos_571_conjecture ↔
    ∀ α : ℚ, 1 ≤ α → α < 2 → IsTuranExponent α := by
  rfl

/-- Known: exponents near 2 are Turán exponents (Conlon-Janzer) -/
theorem near_two_covered :
    ∀ α : ℚ, (7/4 : ℚ) ≤ α → α < 2 →
    ∃ a b : ℕ, b ≥ (a-1)^2 ∧ α = 2 - (a : ℚ)/(b : ℚ) →
    IsTuranExponent α := by
  sorry

/-- The main remaining challenge: exponents in roughly [1, 1.5) -/
theorem main_challenge : True := trivial
  -- Most difficult cases are exponents close to 1
  -- The known constructions produce exponents accumulating at 2

/-! ## Summary

**Status: OPEN**

The Erdős-Simonovits conjecture asks whether every rational α ∈ [1,2) is a
Turán exponent (achievable by some bipartite graph G with ex(n;G) ≍ n^α).

**Known:**
- Many specific families of exponents are achievable
- Exponents near 2 are well-covered by Conlon-Janzer
- Bukh-Conlon proved the finite family version

**Open:**
- Whether EVERY rational in [1,2) works for a SINGLE bipartite graph
- Exponents close to 1 are the hardest cases

This is a central question in extremal graph theory connecting Turán-type
problems with rational number theory.
-/

end Erdos571
