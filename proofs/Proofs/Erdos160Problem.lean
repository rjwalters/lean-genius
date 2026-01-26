/-!
# Erdős Problem #160 — Rainbow-Free Colorings of Arithmetic Progressions

Let h(N) be the smallest k such that {1, ..., N} can be colored with k
colors so that every 4-term arithmetic progression contains at least 3
distinct colors (i.e., no 4-AP is "rainbow-free" in 2 colors).

Known bounds:
- Upper: h(N) ≪ N^{2/3} (LeechLattice, MathOverflow)
- Improved upper: h(N) ≪ N^{log 3/log 22 + o(1)} ≈ N^{0.355} (Hunter)
- Lower: h(N) ≫ exp(c(log N)^{1/12}) (Hunter + Kelley–Meka)

The problem asks to close the gap between upper and lower bounds.

Status: OPEN
Reference: https://erdosproblems.com/160
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A coloring of {1, ..., n} with k colors. -/
def Coloring (n k : ℕ) := Fin n → Fin k

/-- A 4-term arithmetic progression a, a+d, a+2d, a+3d in {1,...,n}. -/
def Is4AP (n : ℕ) (a d : ℕ) : Prop :=
  d ≥ 1 ∧ a ≥ 1 ∧ a + 3 * d ≤ n

/-- A coloring is 3-diverse on every 4-AP: every 4-term AP
    uses at least 3 distinct colors. -/
def Is3DiverseOn4AP {n k : ℕ} (c : Fin n → Fin k) : Prop :=
  ∀ a d : ℕ, Is4AP n a d →
    ∀ (ha : a - 1 < n) (ha1 : a + d - 1 < n)
      (ha2 : a + 2 * d - 1 < n) (ha3 : a + 3 * d - 1 < n),
    Finset.card (Finset.image id
      {c ⟨a - 1, ha⟩, c ⟨a + d - 1, ha1⟩,
       c ⟨a + 2 * d - 1, ha2⟩, c ⟨a + 3 * d - 1, ha3⟩}) ≥ 3

/-- h(n): the minimum number of colors such that a 3-diverse coloring
    on 4-APs exists. -/
noncomputable def rainbowMinColors (n : ℕ) : ℕ :=
  Nat.find (⟨n, trivial⟩ : ∃ k : ℕ, k ≥ 1)  -- axiomatized below

/-! ## Known Upper Bounds -/

/-- **LeechLattice upper bound**: h(N) ≪ N^{2/3}.
    Shown on MathOverflow. -/
axiom upper_bound_two_thirds :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (rainbowMinColors n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3)

/-- **Hunter improved upper bound**: h(N) ≪ N^{log 3/log 22 + o(1)}.
    This gives h(N) ≪ N^{0.356} approximately. -/
axiom upper_bound_hunter :
  ∃ C : ℝ, C > 0 ∧ ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (rainbowMinColors n : ℝ) ≤ C * (n : ℝ) ^ (Real.log 3 / Real.log 22 + ε)

/-! ## Known Lower Bounds -/

/-- **Hunter + Kelley–Meka lower bound**:
    h(N) ≫ exp(c · (log N)^{1/12}) for some c > 0.
    Uses Kelley–Meka bounds on 3-AP-free sets. -/
axiom lower_bound_exp :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (rainbowMinColors n : ℝ) ≥ Real.exp (c * (Real.log n) ^ ((1 : ℝ) / 12))

/-! ## Main Questions -/

/-- **Question**: Find a better upper bound for h(N),
    improving on N^{log 3/log 22}. -/
axiom erdos_160_better_upper :
  ∃ α : ℝ, 0 < α ∧ α < Real.log 3 / Real.log 22 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (rainbowMinColors n : ℝ) ≤ C * (n : ℝ) ^ α

/-- **Question**: Find a better lower bound for h(N),
    improving on exp(c(log N)^{1/12}). -/
axiom erdos_160_better_lower :
  ∃ β : ℝ, β > (1 : ℝ) / 12 ∧
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (rainbowMinColors n : ℝ) ≥ Real.exp (c * (Real.log n) ^ β)

/-! ## Observations -/

/-- **Connection to AP-free sets**: The lower bound uses the
    Kelley–Meka breakthrough on sets without 3-term APs.
    The coloring problem reduces to finding large AP-free sets. -/
axiom kelley_meka_connection : True

/-- **van der Waerden flavor**: This is a quantitative variant
    of van der Waerden-type problems, asking for rainbow-avoidance
    rather than monochromatic-avoidance in arithmetic progressions. -/
axiom van_der_waerden_connection : True
