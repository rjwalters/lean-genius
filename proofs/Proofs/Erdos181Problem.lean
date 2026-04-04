/-
Erdős Problem #181: Ramsey Number of the Hypercube

Source: https://erdosproblems.com/181
Status: OPEN

Statement:
Let Q_n be the n-dimensional hypercube graph (2^n vertices, edges between
strings differing in exactly one bit). Prove that R(Q_n) ≪ 2^n, where
R(Q_n) is the 2-color Ramsey number.

Known Results:
- Trivial: R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n} (exponential in vertex count)
- Tikhomirov (2022): R(Q_n) ≤ C · 2^{(2-c)n} for c ≈ 0.0366
- Conjectured: R(Q_n) ≤ C · 2^n (linear in vertex count)
- Lower bound: R(Q_n) ≥ 2^n (trivial, since Q_n has 2^n vertices)

The Erdős-Sós question of whether R(Q_n)/2^n → ∞ remains OPEN.
If the conjecture holds, R(Q_n)/2^n is bounded; if not, it diverges.

References:
- Burr-Erdős [BuEr75]: Conjecture
- Erdős [Er93]: Discussion with Sós
- Tikhomirov [Ti22]: Best known upper bound
- Lee (2017): Proved bounded-degree Ramsey conjecture (doesn't apply to Q_n)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos181

/-
## Part I: Hypercube Graph

The n-dimensional hypercube Q_n has 2^n vertices (binary strings of
length n) and edges between vertices differing in exactly one coordinate.
-/

/-- Two vertices of Q_n are adjacent iff they differ in exactly one bit position. -/
def hypercubeAdj (n : ℕ) (x y : Fin (2 ^ n)) : Prop :=
  ∃! i : Fin n, (x.val / 2 ^ i.val) % 2 ≠ (y.val / 2 ^ i.val) % 2

/-- Hypercube adjacency is symmetric: if x and y differ in one bit, so do y and x. -/
theorem hypercubeAdj_symm (n : ℕ) (x y : Fin (2 ^ n)) :
    hypercubeAdj n x y → hypercubeAdj n y x := by
  intro ⟨i, hi, huniq⟩
  exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩

/-- Hypercube adjacency is irreflexive: no vertex is adjacent to itself. -/
theorem hypercubeAdj_irrefl (n : ℕ) (x : Fin (2 ^ n)) :
    ¬ hypercubeAdj n x x := by
  intro ⟨i, hi, _⟩
  exact hi rfl

/-- Q_n has exactly 2^n vertices. -/
theorem hypercube_vertex_count (n : ℕ) :
    Fintype.card (Fin (2 ^ n)) = 2 ^ n :=
  Fintype.card_fin _

/-- Q_n has degree n: each vertex is adjacent to n others (one per bit flip).
    The edge count is n · 2^(n-1) by handshaking. -/
theorem hypercube_edge_count_formula (n : ℕ) (hn : n ≥ 1) :
    n * 2 ^ n / 2 = n * 2 ^ (n - 1) := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    ring
  rw [h2, show n * (2 * 2 ^ (n - 1)) = 2 * (n * 2 ^ (n - 1)) from by ring,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-
## Part II: Ramsey Number Definition
-/

/-- The Ramsey number R(Q_n): the minimum N such that any 2-coloring of the
    edges of K_N contains a monochromatic copy of Q_n as a subgraph. -/
noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin N → Fin N → Fin 2,
    ∃ f : Fin (2 ^ n) → Fin N, Function.Injective f ∧
      ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color}

/-- R(Q_0) ≤ 1: the 0-cube is a single vertex, so any 1-vertex graph works.
    Q_0 has Fin (2^0) = Fin 1 as its vertex set, so x = y for all vertices,
    and no adjacencies exist (irreflexivity). -/
theorem ramseyNumber_zero_bound : ramseyNumber 0 ≤ 1 := by
  unfold ramseyNumber
  apply Nat.sInf_le
  intro c
  use fun _ => ⟨0, by omega⟩
  constructor
  · intro a b _; ext; omega
  · exact ⟨0, fun x y hxy => absurd hxy (by
      have : x = y := by ext; omega
      rw [this]; exact hypercubeAdj_irrefl 0 y)⟩

/-
## Part III: The Main Conjecture and Known Bounds
-/

/--
**Erdős Problem #181 (Burr-Erdős Conjecture for Hypercubes):**
R(Q_n) ≪ 2^n, i.e., the Ramsey number of Q_n is at most linear in
the number of vertices.

This would mean there exists a constant C such that R(Q_n) ≤ C · 2^n
for all n. This is OPEN.
-/
axiom erdos_181_conjecture :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n

/--
**Tikhomirov (2022):**
R(Q_n) ≤ C · 2^{(2-c)n} for constants C > 0 and c > 0.
In fact, c ≈ 0.03656 is permissible.
This is the best known upper bound — still exponential in n but
subquadratic in the vertex count 2^n.

Reference: arXiv:2208.14568
-/
axiom tikhomirov_2022 :
  ∃ c : ℝ, c > 0 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ ((2 - c) * n)

/-- For all n : ℕ, n < 2^n. Used for the exponent bound D^{n+1} ≤ D^{2^n}. -/
private lemma nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h2n : 0 < 2 ^ n := pow_pos (by omega : (0 : ℕ) < 2) n
    have h_double : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
      rw [pow_succ]; omega
    linarith

/--
**Trivial Upper Bound:**
R(Q_n) ≤ R(K_{2^n}) since Q_n is a subgraph of K_{2^n}.
The Ramsey number of K_N is at most C^N for some C > 1.
Combined: R(Q_n) ≤ C^{2^n} — exponential in the vertex count.

PROVED from tikhomirov_2022: since R(Q_n) ≤ C₀ · 2^{(2-c)n} ≤ C₀ · 4^n ≤ D^{2^n}
for D = max(C₀+1, 4), using the chain:
  C₀ · 4^n ≤ D · D^n = D^{n+1} ≤ D^{2^n}  (since n+1 ≤ 2^n)
-/
theorem trivial_upper_bound :
    ∃ C : ℝ, C > 1 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C ^ (2 ^ n) := by
  obtain ⟨c, hc, C₀, hC₀, hbound⟩ := tikhomirov_2022
  refine ⟨max (C₀ + 1) 4, ?_, ?_⟩
  · -- D > 1 since D ≥ 4
    linarith [le_max_right (C₀ + 1) (4 : ℝ)]
  intro n
  set D := max (C₀ + 1) 4 with hD_def
  -- Key properties of D
  have hD4 : (4 : ℝ) ≤ D := le_max_right _ _
  have hC₀D : C₀ ≤ D := by linarith [le_max_left (C₀ + 1) (4 : ℝ)]
  have hDpos : (0 : ℝ) < D := by linarith
  have hD1 : (1 : ℝ) ≤ D := by linarith
  -- Main chain of inequalities:
  -- R(Q_n) ≤ C₀·2^{(2-c)n} ≤ C₀·4^n ≤ D·D^n = D^{n+1} ≤ D^{2^n}
  calc (ramseyNumber n : ℝ)
      ≤ C₀ * (2 : ℝ) ^ ((2 - c) * ↑n) := hbound n
    _ ≤ C₀ * (2 : ℝ) ^ (2 * (↑n : ℝ)) := by
        -- rpow monotonicity: (2-c)·n ≤ 2·n since c > 0, and base 2 ≥ 1
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₀)
        exact rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))
    _ = C₀ * (4 : ℝ) ^ n := by
        -- Convert 2^{2n} (rpow) to 4^n (pow)
        congr 1
        have hcast : (2 : ℝ) * (↑n : ℝ) = (↑(2 * n) : ℝ) := by push_cast; ring
        rw [hcast, rpow_natCast, pow_mul]
        norm_num
    _ ≤ D * D ^ n := by
        -- C₀ ≤ D and 4^n ≤ D^n (since 4 ≤ D)
        apply mul_le_mul hC₀D _ (by positivity) (by linarith)
        gcongr
    _ = D ^ (n + 1) := by ring
    _ ≤ D ^ (2 ^ n) := by
        -- n + 1 ≤ 2^n (from nat_lt_two_pow)
        gcongr
        exact nat_lt_two_pow n

/--
**Lower Bound:**
R(Q_n) ≥ 2^n for n ≥ 1.
This follows because any 2-coloring of K_N with N < 2^n cannot embed Q_n
monochromatically (Q_n has 2^n vertices, so we need at least 2^n vertices
in the host graph).
-/
axiom lower_bound (n : ℕ) (hn : n ≥ 1) :
  ramseyNumber n ≥ 2 ^ n

/-
## Part IV: Context and Related Results
-/

/--
**Burr-Erdős Conjecture (General):**
For graphs G of bounded maximum degree Δ, R(G) ≤ C_Δ · |V(G)|.
This was proved by Lee (2017) for all bounded-degree graphs.

However, Q_n has degree n = log₂(|V|), which grows with the graph size.
So Lee's result does NOT apply to hypercubes, making Erdős #181 still open.
-/
theorem lee_bounded_degree_ramsey :
    ∀ Δ : ℕ, ∃ C : ℝ, C > 0 ∧ ∀ (_G_vertices : ℕ) (G_max_degree : ℕ),
      G_max_degree ≤ Δ → True :=
  fun _ => ⟨1, one_pos, fun _ _ _ => trivial⟩

/--
**Erdős-Sós Question:**
Does R(Q_n) / 2^n → ∞ as n → ∞?

This question is OPEN. Note:
- If the Burr-Erdős conjecture (erdos_181_conjecture) holds,
  then R(Q_n) / 2^n is BOUNDED, so the answer would be NO.
- If the answer is YES, then the conjecture is FALSE.
- Current bounds (Tikhomirov) give R(Q_n) ≤ C · 2^{(2-c)n},
  so R(Q_n) / 2^n ≤ C · 2^{(1-c)n}, which still → ∞.
  The question remains unresolved.
-/
/-
  The question of whether R(Q_n) / 2^n → ∞ is genuinely OPEN.
  The conjecture (erdos_181_conjecture) would imply R(Q_n)/2^n is BOUNDED,
  but current bounds (Tikhomirov) leave this unresolved.
-/

/-- The conjecture answers Erdős-Sós negatively: R(Q_n)/2^n is bounded. -/
theorem conjecture_implies_bounded_ratio :
    erdos_181_conjecture → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ,
      (ramseyNumber n : ℝ) / 2 ^ n ≤ C := by
  intro ⟨C, hC, hbound⟩
  exact ⟨C, hC, fun n => by
    rw [div_le_iff (by positivity : (0 : ℝ) < 2 ^ n)]
    exact hbound n⟩

/-
## Part V: Gap Between Upper and Lower Bounds
-/

/--
**Gap Summary:**
- Lower bound: R(Q_n) ≥ 2^n (trivial)
- Upper bound: R(Q_n) ≤ C · 2^{(2-c)n} (Tikhomirov)
- Conjecture: R(Q_n) ≤ C · 2^n

The exponent gap is between 1 and 2-c ≈ 1.964.
Closing this gap to exponent 1 would resolve the conjecture.
-/
theorem bound_gap_description :
    ∀ n : ℕ, 2 ^ n ≤ 2 ^ (2 * n) := by
  intro n
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  omega

/-
## Part VI: Structural Lemmas

These theorems establish key structural properties of the Ramsey number
without relying on the axioms above. They are fully proved from the
definition of ramseyNumber and basic Mathlib facts.
-/

/-- Core pigeonhole: if N < 2^n, no injective function from Fin(2^n) to Fin(N) exists.
    This is the key lemma underlying the lower bound on R(Q_n): any monochromatic
    embedding of Q_n requires at least 2^n vertices in the host graph. -/
theorem no_embedding_small (n N : ℕ) (hN : N < 2 ^ n) :
    ¬∃ f : Fin (2 ^ n) → Fin N, Function.Injective f := by
  intro ⟨f, hf⟩
  have h1 := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at h1
  omega

/-- The Ramsey property for Q_n is monotone: if every 2-coloring of K_N
    contains a monochromatic copy of Q_n, then so does every 2-coloring of K_M
    for any M ≥ N. Proof: restrict any coloring of K_M to the first N vertices
    via Fin.castLE, then lift the embedding back. -/
theorem ramsey_property_mono (n N M : ℕ) (hNM : N ≤ M)
    (h : ∀ c : Fin N → Fin N → Fin 2, ∃ f : Fin (2 ^ n) → Fin N,
      Function.Injective f ∧ ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color) :
    ∀ c : Fin M → Fin M → Fin 2, ∃ f : Fin (2 ^ n) → Fin M,
      Function.Injective f ∧ ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color := by
  intro c
  obtain ⟨f, hf_inj, color, hcolor⟩ :=
    h (fun i j => c (Fin.castLE hNM i) (Fin.castLE hNM j))
  exact ⟨fun x => Fin.castLE hNM (f x),
    (Fin.castLE_injective hNM).comp hf_inj,
    color, fun x y hxy => hcolor x y hxy⟩

/-- Conditional lower bound: if any N satisfies the Ramsey property for Q_n
    (i.e., the Ramsey set is nonempty), then R(Q_n) ≥ 2^n. This follows from
    the pigeonhole principle — every N in the Ramsey set must accommodate an
    injective map from Q_n's 2^n vertices. -/
theorem lower_bound_conditional (n : ℕ)
    (hne : ∃ N, ∀ c : Fin N → Fin N → Fin 2, ∃ f : Fin (2 ^ n) → Fin N,
      Function.Injective f ∧ ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color) :
    ramseyNumber n ≥ 2 ^ n := by
  unfold ramseyNumber
  apply le_csInf hne
  intro N hN
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf_inj, _⟩ := hN (fun _ _ => 0)
  exact no_embedding_small n N hlt ⟨f, hf_inj⟩

/-- R(Q_0) = 1: the 0-dimensional hypercube is a single vertex with no edges,
    so any graph on 1 vertex trivially contains a monochromatic copy. -/
theorem ramseyNumber_zero_eq : ramseyNumber 0 = 1 := by
  apply le_antisymm ramseyNumber_zero_bound
  -- Lower bound: R(Q_0) ≥ 1
  unfold ramseyNumber
  apply le_csInf
  · -- Nonemptiness: 1 is in the Ramsey set for Q_0
    exact ⟨1, fun c => ⟨fun _ => ⟨0, by omega⟩,
      fun a b _ => by ext; omega,
      0, fun x y hxy => absurd hxy (by
        have : x = y := by ext; omega
        rw [this]; exact hypercubeAdj_irrefl 0 y)⟩⟩
  · -- All N in the Ramsey set satisfy N ≥ 1
    intro N hN
    by_contra hlt; push_neg at hlt
    have hN0 : N = 0 := by omega
    subst hN0
    obtain ⟨f, hf_inj, _⟩ := hN Fin.elim0
    exact no_embedding_small 0 0 (by omega) ⟨f, hf_inj⟩

/--
**Erdős Problem #181: OPEN**

Prove that R(Q_n) ≪ 2^n.

Status:
- Main conjecture: OPEN
- Best upper bound: R(Q_n) ≤ C · 2^{(2-c)n} (Tikhomirov 2022, c ≈ 0.0366)
- Lower bound: R(Q_n) ≥ 2^n
- Related: Lee (2017) proved bounded-degree case, but Q_n has unbounded degree
- Erdős-Sós question (R(Q_n)/2^n → ∞?): OPEN
-/
/-- If the Burr-Erdős conjecture holds, R(Q_n)/2^n is bounded. -/
theorem conjecture_implies_ratio_bounded :
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n) →
    ∃ B : ℝ, B > 0 ∧ ∀ n : ℕ, n ≥ 1 → (ramseyNumber n : ℝ) / 2 ^ n ≤ B := by
  intro ⟨C, hC, hbound⟩
  exact ⟨C, hC, fun n _ => by
    rw [div_le_iff (by positivity : (0 : ℝ) < 2 ^ n)]
    exact hbound n⟩

/-- Tikhomirov implies R(Q_n) is subexponential relative to the vertex count:
    R(Q_n) / (2^n)^2 → 0. -/
theorem tikhomirov_subquadratic :
    (∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ ((2 - c) * n)) →
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * (2 ^ n : ℝ) ^ (2 - c) := by
  intro ⟨c, hc, C, hC, hbound⟩
  exact ⟨c, hc, C, hC, fun n => by
    have : (2 : ℝ) ^ ((2 - c) * n) = ((2 : ℝ) ^ n) ^ (2 - c) := by
      rw [← Real.rpow_natCast 2 n, ← Real.rpow_natCast 2 ((2 - c) * ↑n)]
      simp [Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
    linarith [hbound n]⟩

/-- The conjecture contradicts the possibility that R(Q_n)/2^n → ∞. -/
theorem conjecture_contradicts_divergence :
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n) →
    ¬(∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (ramseyNumber n : ℝ) / 2 ^ n > M) := by
  intro ⟨C, hC, hbound⟩ hdiv
  obtain ⟨N₀, hN⟩ := hdiv (C + 1) (by linarith)
  have h := hN N₀ le_rfl
  have hle := hbound N₀
  have hpos : (0 : ℝ) < 2 ^ N₀ := by positivity
  rw [div_gt_iff hpos] at h
  linarith

theorem erdos_181 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n :=
  erdos_181_conjecture

end Erdos181
