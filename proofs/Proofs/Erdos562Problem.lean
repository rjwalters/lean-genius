/-!
# Erdős Problem #562 — Hypergraph Ramsey Number Tower Growth

Let R_r(n) denote the r-uniform hypergraph Ramsey number: the minimal m
such that every 2-coloring of the complete r-uniform hypergraph on m
vertices contains a monochromatic complete r-uniform hypergraph on n vertices.

**Conjecture (Erdős–Hajnal–Rado):** For r ≥ 3,
  log_{r-1} R_r(n) ≍ n
where log_{r-1} is the (r-1)-fold iterated logarithm. Equivalently,
R_r(n) grows like a tower of exponentials of height r-1.

**Status: OPEN.**

Known:
- r = 2: R_2(n) = R(n,n) satisfies 2^{n/2} ≤ R(n,n) ≤ 4^n (Erdős–Szekeres)
- Upper bound: R_r(n) ≤ twr_{r-1}(c_r · n²) (Erdős–Rado stepping-up)
- Lower bound for r = 3: R_3(n) ≥ twr_2(c · n²) (Erdős–Hajnal)

Reference: https://erdosproblems.com/562
-/

import Mathlib.Combinatorics.Ramsey
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Tower Function -/

/-- The tower function: twr(0, n) = n, twr(k+1, n) = 2^{twr(k, n)}.
    This is the iterated exponential of height k starting from n. -/
def twr : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => 2 ^ twr k n

/-- twr(1, n) = 2^n. -/
theorem twr_one (n : ℕ) : twr 1 n = 2 ^ n := rfl

/-- twr(2, n) = 2^{2^n}. -/
theorem twr_two (n : ℕ) : twr 2 n = 2 ^ (2 ^ n) := rfl

/-! ## Hypergraph Ramsey Numbers -/

/-- The r-uniform hypergraph Ramsey number R_r(n): the minimal m such
    that every 2-coloring of the edges of K_m^(r) contains a
    monochromatic K_n^(r). -/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ (χ : Finset.powersetCard r (Finset.range m) → Fin 2),
    ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.card = n ∧
      ∃ c : Fin 2, ∀ e ∈ S.powersetCard r, χ e = c }

/-! ## Classical Graph Ramsey (r = 2) -/

/-- Erdős–Szekeres lower bound: R(n,n) ≥ 2^{n/2}. -/
axiom erdos_szekeres_lower (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n / 2) ≤ hypergraphRamsey 2 n

/-- Erdős–Szekeres upper bound: R(n,n) ≤ C(2n-2, n-1) < 4^n. -/
axiom erdos_szekeres_upper (n : ℕ) (hn : 2 ≤ n) :
    hypergraphRamsey 2 n ≤ 4 ^ n

/-- For r = 2, log R_2(n) ≍ n. This is the Erdős–Szekeres result. -/
theorem graph_ramsey_exponential (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n / 2) ≤ hypergraphRamsey 2 n ∧ hypergraphRamsey 2 n ≤ 4 ^ n :=
  ⟨erdos_szekeres_lower n hn, erdos_szekeres_upper n hn⟩

/-! ## Erdős–Rado Stepping-Up Upper Bound -/

/-- Erdős–Rado stepping-up lemma (1952): bounds R_r in terms of R_{r-1}.
    This gives R_r(n) ≤ twr_{r-1}(c_r · n²). -/
axiom erdos_rado_stepping_up (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      hypergraphRamsey r n ≤ twr (r - 1) (c * n ^ 2)

/-! ## Lower Bounds -/

/-- Erdős–Hajnal lower bound for r = 3:
    R_3(n) ≥ twr_2(c · n²) = 2^{2^{cn²}}. -/
axiom erdos_hajnal_r3_lower :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      twr 2 (c * n ^ 2) ≤ hypergraphRamsey 3 n

/-- General lower bound for r ≥ 3: R_r(n) ≥ twr_{r-1}(c · n).
    This is known for all r but the constant is not optimal. -/
axiom general_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      twr (r - 1) (c * n) ≤ hypergraphRamsey r n

/-! ## The Main Conjecture -/

/-- **Erdős Problem #562**: log_{r-1} R_r(n) ≍ n for r ≥ 3.
    Equivalently, R_r(n) = twr_{r-1}(Θ(n)).
    The upper bound gives twr_{r-1}(O(n²)) and the lower bound
    gives twr_{r-1}(Ω(n)). The conjecture is that both can be
    tightened to twr_{r-1}(Θ(n)). -/
axiom erdos_562_conjecture (r : ℕ) (hr : 3 ≤ r) :
    ∃ c₁ c₂ : ℕ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      twr (r - 1) (c₁ * n) ≤ hypergraphRamsey r n ∧
      hypergraphRamsey r n ≤ twr (r - 1) (c₂ * n)

/-! ## Small Cases -/

/-- R_3(4) is known: R_3(4) = 13. -/
axiom r3_4 : hypergraphRamsey 3 4 = 13
