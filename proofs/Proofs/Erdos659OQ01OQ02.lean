/-
# Erdős Problem #659 OQ-01-OQ-02 — d ≥ 3 extension: axis-vs-plane scaffold

This file is the S3 ACT **scaffold** for the open question

> Can the O(n/√(log n)) sharp-distance-bound theorem for ℝ² (parent
> `erdos-659-oq-01`) be extended to ℝ^d for `d ≥ 3`?

The plan (per S1c OBSERVE PR #18431 + S2a OBSERVE PR #18494 + S2b PREP
PR #18554) is to ship a Pell-equation-safe sub-lattice family
`L_{p, q} := { (δ₁, δ₂√p, δ₃√q) : δᵢ ∈ ℤ }` for selected squarefree
prime pairs `(p, q)`, then derive the Θ(n^{2/3}) rate.

S2b PREP §4–§6 isolated the **axis-vs-plane** half of the safety
predicate into three equations in three unknowns:

```
(A)   5 c² = a² + 2 b²
(B)   2 b² = a² + 5 c²
(C)   a²    = 2 b² + 5 c²
```

A solution `(a, b, c) ≠ (0, 0, 0)` to any of A/B/C corresponds to an
axis-vs-plane equidistant 4-tuple in `L_{2, 5}`. The S2b §4–§5 QR-descent
template proves all three have only the trivial integer solution by
reducing mod 5 and applying the quadratic-non-residue status of `2` and
`−2` mod 5.

This file ships the **outer scaffold** — the three predicates,
their composite, and the named theorem statements — with the descent
**bodies deferred to S4 ACT** as three strategic sorries. The
descent recipe is fully written out in
`research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md`
§5 (the Lean template) and §7 (generalisation pointer for the other
six safe pairs identified by S2a).

**Scope.** Axis-vs-plane only. Full-rank safety (per S2c PREP §6.1) is
deferred to a separate axiomatisation pending Mathlib Hasse-Minkowski
infrastructure that does not yet exist at v4.26.0.

**Sorries / axioms.** 3 strategic sorries (one per equation); 0 axioms
in this file. Build pending convention applies (recursive `.lake`
symlink in the researcher worktree precludes local `lake build`; the
auditor / next ACT session is expected to verify via the Docker
wrapper).
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Defs

namespace Erdos659OQ01OQ02

/-- Equation A predicate for the prime pair `(p, q) = (2, 5)`:
    `5 c² = a² + 2 b²` has only the trivial integer solution.

    Geometric meaning: an axis-vs-plane equidistant 4-tuple in
    `L_{2, 5}` projecting onto coordinate axis 1 and the (axis 2,
    axis 3) plane would give a non-trivial solution.

    Discharge plan (S4 ACT, ~30 LOC): reduce mod 5 to deduce
    `5 ∣ a.natAbs` and `5 ∣ b.natAbs` (using `−2` not a square mod 5);
    substitute and rearrange to deduce `5 ∣ c.natAbs`; descend by
    `Nat.strongRecOn` on `c.natAbs`. See S2b PREP §4.1 + §5. -/
def safe_A : Prop :=
  ∀ a b c : ℤ, (5 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- Equation B predicate for the prime pair `(p, q) = (2, 5)`:
    `2 b² = a² + 5 c²` has only the trivial integer solution.

    Discharge plan (S4 ACT, ~30 LOC): analogous to `safe_A` with
    `b` ↔ `c` (mod-5 reduction via `2` not a square mod 5). See
    S2b PREP §4.2. -/
def safe_B : Prop :=
  ∀ a b c : ℤ, (2 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- Equation C predicate for the prime pair `(p, q) = (2, 5)`:
    `a² = 2 b² + 5 c²` has only the trivial integer solution.

    Discharge plan (S4 ACT, ~30 LOC): analogous to `safe_A` with
    `a` ↔ `c`. See S2b PREP §4.3. -/
def safe_C : Prop :=
  ∀ a b c : ℤ, a ^ 2 = (2 : ℤ) * b ^ 2 + 5 * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation A).**
    `5 c² = a² + 2 b²` has only `(0, 0, 0)`.

    Proof (deferred): see this file's docstring + S2b PREP §5 template. -/
theorem safe_A_holds : safe_A := by
  intro a b c _heq
  sorry

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation B).**
    `2 b² = a² + 5 c²` has only `(0, 0, 0)`.

    Proof (deferred): analogous to `safe_A_holds`; see S2b PREP §4.2. -/
theorem safe_B_holds : safe_B := by
  intro a b c _heq
  sorry

/-- **(STRATEGIC SORRY — S4 ACT, axis-vs-plane equation C).**
    `a² = 2 b² + 5 c²` has only `(0, 0, 0)`.

    Proof (deferred): analogous to `safe_A_holds`; see S2b PREP §4.3. -/
theorem safe_C_holds : safe_C := by
  intro a b c _heq
  sorry

/-- The axis-vs-plane safety predicate for a prime pair `(p, q)`.
    Asserts that none of the three QR equations A/B/C admits a
    non-trivial integer solution. This is the **necessary** condition
    on `(p, q)` for the lattice `L_{p, q}` to satisfy the
    `fourPointProperty` along axis-vs-plane equidistant 4-tuples.

    Per S2c PREP §6.1, the corresponding full-rank safety statement is
    separately axiomatized (Mathlib v4.26.0 lacks the ternary
    Hasse-Minkowski infrastructure to discharge it as a theorem). -/
def SafePrimePair_AxisVsPlane (p q : ℕ) : Prop :=
  (∀ a b c : ℤ, (q : ℤ) * c ^ 2 = a ^ 2 + (p : ℤ) * b ^ 2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, (p : ℤ) * b ^ 2 = a ^ 2 + (q : ℤ) * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ a b c : ℤ, a ^ 2 = (p : ℤ) * b ^ 2 + (q : ℤ) * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0)

/-- **The main axis-vs-plane safety theorem for the prime pair
    `(p, q) = (2, 5)`.**

    Derived as the conjunction of `safe_A_holds`, `safe_B_holds`, and
    `safe_C_holds`. Each conjunct is currently a strategic sorry;
    closing all three via the S2b §5 QR-descent template completes the
    axis-vs-plane half of the `L_{2, 5}` safety story. The full-rank
    half is axiomatised separately per S2c PREP §6.1. -/
theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5 :=
  ⟨safe_A_holds, safe_B_holds, safe_C_holds⟩

end Erdos659OQ01OQ02
