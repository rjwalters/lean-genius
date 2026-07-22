/-
  The Dinitz–Garg–Goemans (DGG) unsplittable-flow separation — a finite,
  machine-verified certificate.

  Sources:
    * Dmitry Rybin (@DmitryRybin1), 2026 announcement (found with GPT-5.6 Pro):
      https://x.com/DmitryRybin1/status/2079904005652893709
    * Dinitz, Garg, Goemans, "On the single-source unsplittable flow problem",
      Combinatorica 19 (1999).

  ## What this file proves

  For one explicit single-source instance (7 vertices, 9 arcs, 3 demands) we
  encode, in pure integer arithmetic, three finite facts and discharge them by
  plain kernel `decide` (NOT `native_decide`), so the file is **0-axiom** —
  `#print axioms` lists only `propext` / `Quot.sound`, with no `Lean.ofReduceBool`
  and no `sorryAx`:

    1. `fractional_cost_eq` : the given fractional flow has cost `cᵀx = 58`.
    2. `fractional_feasible` : that fractional flow satisfies flow conservation at
       every internal node, delivers each demand at its terminal, and respects the
       arc capacities `u_a = x_a`.
    3. `every_capgood_routing_costly` : **every** unsplittable routing whose arc
       loads stay within `x_a + D` (capacity violation ≤ `D = dmax = 15`) has cost
       `≥ 60`; and `capgood_optimum_is_60` exhibits a capacity-good routing of cost
       exactly `60`, so the unsplittable optimum under this rule is `60`.

  Since `60 > 58`, the unsplittable optimum strictly exceeds the fractional cost
  even when a capacity violation up to the maximum demand `D` is allowed. This is
  the exact quantity the DGG "cost + congestion" guarantee (the exact-`D` reading)
  would forbid, so the certificate *separates* that bound.

  ## The instance

  Vertices `s, u, v, w, t1, t2, t3`; source `s`. Demands `d1 = 15, d2 = 10,
  d3 = 15`, so `D = dmax = 15`. Arcs `(x_a fractional load, c_a unit cost)`, with
  capacities `u_a = x_a`:

      s→t1 (10,2)  s→t2 (6,3)  s→u (24,0)  u→t3 (10,2)  u→v (14,0)
      v→t1 (5,0)   v→w (9,0)   w→t2 (4,0)  w→t3 (5,0)

  Each terminal `t_i` is reachable by exactly two `s`→`t_i` paths (the underlying
  undirected graph is a subdivision of `K₄`, so there are no hidden splice paths):

      E1 = s→t1              Z1 = s→u→v→t1
      E2 = s→t2              Z2 = s→u→v→w→t2
      E3 = s→u→t3            Z3 = s→u→v→w→t3

  Each direct path `E_i` costs `d_i · c(E_i) = 30`; each long path `Z_i` costs `0`.
  A routing chooses one path per terminal (`2³ = 8` routings). The capacity rule
  `y_a ≤ x_a + D` allows **at most one** `Z_i` (any two overload a shared arc:
  `Z2+Z3` overloads `v→w` at `25 > 24`; `Z1+Z3` overloads `u→v` at `30 > 29`;
  `Z1+Z2` overloads `s→u` at `40 > 39`), so every capacity-good routing uses at
  least two cost-`30` paths ⇒ cost `≥ 60`.

  ## Audit caveat (IMPORTANT — read before citing)

  This entry records a **recently-announced finite certificate** (Rybin 2026),
  reproduced here as machine-checkable integer facts. The *finite facts below are
  solid and independently re-derived*. However, the announcement itself notes that
  the latest primary source (Jan 2026) still lists the DGG conjecture as **open**,
  and that the counterexample "should be independently audited before being
  announced as an established result." Accordingly this file proves only the
  self-contained separation statement for this explicit instance; it does **not**
  claim to settle the DGG conjecture. The interpretation "refutes DGG Conjecture
  1.3" is deferred to independent audit against the exact conjecture statement.
-/

import Mathlib

namespace DinitzGargGoemans

/-! ## The instance: arcs, capacities, unit costs -/

/-- The nine arcs of the instance. -/
inductive Arc
  | st1 | st2 | su | ut3 | uv | vt1 | vw | wt2 | wt3
  deriving DecidableEq

/-- All nine arcs, as a list (used for bounded quantification in `decide`). -/
def allArcs : List Arc :=
  [.st1, .st2, .su, .ut3, .uv, .vt1, .vw, .wt2, .wt3]

/-- Fractional load `x_a` on each arc; the arc capacity is `u_a = x_a`. -/
def xflow : Arc → ℕ
  | .st1 => 10 | .st2 => 6 | .su => 24 | .ut3 => 10 | .uv => 14
  | .vt1 => 5  | .vw => 9  | .wt2 => 4 | .wt3 => 5

/-- Unit cost `c_a` on each arc. -/
def ucost : Arc → ℕ
  | .st1 => 2 | .st2 => 3 | .su => 0 | .ut3 => 2 | .uv => 0
  | .vt1 => 0 | .vw => 0 | .wt2 => 0 | .wt3 => 0

/-! ## Nodes and the fractional flow's conservation -/

/-- The seven vertices. -/
inductive Node
  | s | u | v | w | t1 | t2 | t3
  deriving DecidableEq

/-- Tail (origin) of each arc. -/
def tail : Arc → Node
  | .st1 => .s | .st2 => .s | .su => .s | .ut3 => .u | .uv => .u
  | .vt1 => .v | .vw => .v | .wt2 => .w | .wt3 => .w

/-- Head (destination) of each arc. -/
def head : Arc → Node
  | .st1 => .t1 | .st2 => .t2 | .su => .u | .ut3 => .t3 | .uv => .v
  | .vt1 => .t1 | .vw => .w | .wt2 => .t2 | .wt3 => .t3

/-- Total fractional flow leaving a node. -/
def outflow (n : Node) : ℕ :=
  (allArcs.filter (fun a => tail a = n)).foldr (fun a s => xflow a + s) 0

/-- Total fractional flow entering a node. -/
def inflow (n : Node) : ℕ :=
  (allArcs.filter (fun a => head a = n)).foldr (fun a s => xflow a + s) 0

/-- Demands `d_i`; `D = dmax = 15`. -/
def d1 : ℕ := 15
def d2 : ℕ := 10
def d3 : ℕ := 15
def D : ℕ := 15

/-- The fractional flow is **feasible**: conservation holds at every internal node
`u, v, w`; each terminal receives exactly its demand; the source emits the total
demand; and every arc respects its capacity `u_a = x_a` (`x_a ≤ x_a`, trivially).
Marked `@[reducible]` so `decide`'s instance synthesis sees the decidable body. -/
@[reducible] def FractionalFeasible : Prop :=
  inflow .u = outflow .u ∧ inflow .v = outflow .v ∧ inflow .w = outflow .w ∧
  inflow .t1 = d1 ∧ inflow .t2 = d2 ∧ inflow .t3 = d3 ∧
  outflow .s = d1 + d2 + d3 ∧
  (∀ a ∈ allArcs, xflow a ≤ xflow a)

/-- The fractional cost `cᵀx = Σ_a c_a · x_a`. -/
def fractionalCost : ℕ := (allArcs.map (fun a => ucost a * xflow a)).foldr (· + ·) 0

/-! ## Unsplittable routings -/

/-- A routing is one path choice per terminal, encoded as `(b1, b2, b3) : Bool³`
where `b_i = true` selects the long path `Z_i` and `b_i = false` the direct `E_i`. -/
abbrev Routing := Bool × Bool × Bool

/-- Arcs used by the chosen `s`→`t1` path. -/
def path1 (b : Bool) : List Arc := if b then [.su, .uv, .vt1] else [.st1]
/-- Arcs used by the chosen `s`→`t2` path. -/
def path2 (b : Bool) : List Arc := if b then [.su, .uv, .vw, .wt2] else [.st2]
/-- Arcs used by the chosen `s`→`t3` path. -/
def path3 (b : Bool) : List Arc := if b then [.su, .uv, .vw, .wt3] else [.su, .ut3]

/-- Load on arc `a` under routing `r`: the sum of the demands of the terminals
whose chosen path traverses `a`. -/
def load (a : Arc) (r : Routing) : ℕ :=
  (if a ∈ path1 r.1 then d1 else 0) +
  (if a ∈ path2 r.2.1 then d2 else 0) +
  (if a ∈ path3 r.2.2 then d3 else 0)

/-- The unit cost of a path (sum of its arcs' unit costs). -/
def pathCost (p : List Arc) : ℕ := (p.map ucost).foldr (· + ·) 0

/-- Cost of a routing: `Σ_i d_i · c(chosen path_i)`. -/
def routingCost (r : Routing) : ℕ :=
  d1 * pathCost (path1 r.1) + d2 * pathCost (path2 r.2.1) + d3 * pathCost (path3 r.2.2)

/-- A routing is **capacity-good** if every arc load stays within `x_a + D`
(capacity violation at most the maximum demand `D`). Marked `@[reducible]` so
`decide`'s instance synthesis sees the bounded quantifier over `allArcs`. -/
@[reducible] def CapGood (r : Routing) : Prop := ∀ a ∈ allArcs, load a r ≤ xflow a + D

/-! ## The three verified facts (plain kernel `decide`, 0 axioms) -/

/-- **(1)** The fractional flow has cost `cᵀx = 58`. -/
theorem fractional_cost_eq : fractionalCost = 58 := by decide

/-- **(2)** The fractional flow is feasible (conservation, demands, capacities). -/
theorem fractional_feasible : FractionalFeasible := by decide

/-- **(3a)** Every capacity-good unsplittable routing costs at least `60`. -/
theorem every_capgood_routing_costly : ∀ r : Routing, CapGood r → 60 ≤ routingCost r := by
  decide

/-- **(3b)** The bound is tight: the routing `(E, E, Z) = (false, false, true)` is
capacity-good and has cost exactly `60`, so the unsplittable optimum is `60`. -/
theorem capgood_optimum_is_60 :
    ∃ r : Routing, CapGood r ∧ routingCost r = 60 :=
  ⟨(false, false, true), by decide, by decide⟩

/-- **The DGG separation.** For this explicit instance the fractional optimum is
`58` while every capacity-good (violation ≤ `D`) unsplittable routing costs `≥ 60`,
with `60` attained. Hence the unsplittable optimum `60` strictly exceeds the
fractional cost `58` even allowing a capacity violation up to the maximum demand —
separating the exact-`D` DGG cost guarantee. -/
theorem dgg_separation :
    fractionalCost = 58 ∧ FractionalFeasible ∧
    (∀ r : Routing, CapGood r → 60 ≤ routingCost r) ∧
    (∃ r : Routing, CapGood r ∧ routingCost r = 60) ∧
    fractionalCost < 60 :=
  ⟨fractional_cost_eq, fractional_feasible, every_capgood_routing_costly,
    capgood_optimum_is_60, by decide⟩

-- Axiom audit: plain `decide` (NOT `native_decide`) ⇒ foundational axioms only
-- (propext / Quot.sound); no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms dgg_separation

end DinitzGargGoemans
