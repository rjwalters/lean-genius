# S3b-act-2 PREP — Case (a) witness for `exists_nonvertex_lattice_point`

**Date**: 2026-06-04
**Agent**: researcher-1
**Phase**: PREP (paste-ready code authored; no Lean changes shipped)
**Status**: Builds on S3b-act-1 ACT (PR #21155 merged 2026-05-30) and S4
STATE-SYNC (2026-06-02 Docker GREEN unblocking).

---

## Target

S3b PREP §4.1 case (a): given a `LatticeTriangle T` and an edge `i : Fin 3`
with `edgeGCD T i ≥ 2`, witness a lattice point in the STRICT INTERIOR of
edge `i` (i.e. distinct from both endpoints of the edge). The witness is
the parameter-`k = 1` point on the gcd-parametrised segment, which sits
strictly between `(vᵢ, vᵢ₊₁)` when `g ≥ 2`.

This is the geometric content needed to close Case (a) of
`exists_nonvertex_lattice_point` (S3b PREP §4.1). Case (b) (Minkowski-style
interior witness for primitive triangles with twiceArea ≥ 2) remains a
separate, harder sub-task.

---

## Paste-ready code (~50 LOC including `OnStrictEdgeInterior` predicate)

Insert AFTER `card_latticeSegmentPoints` (current line 719) and BEFORE the
final `end PicksTheoremOQ01OQ01OQ01` (current line 721).

```lean
namespace LatticeTriangle

/-- Edge `i` of `T` connects vertex `vEdgeStart i` to vertex `vEdgeEnd i`,
    where vEdgeStart/End follow the same convention as `edgeDelta`:
    edge 0 = v1→v2, edge 1 = v2→v3, edge 2 = v3→v1. -/
@[reducible] def vEdgeStart (T : LatticeTriangle) : Fin 3 → ℤ × ℤ
  | 0 => T.v1
  | 1 => T.v2
  | 2 => T.v3

@[reducible] def vEdgeEnd (T : LatticeTriangle) : Fin 3 → ℤ × ℤ
  | 0 => T.v2
  | 1 => T.v3
  | 2 => T.v1

/-- `p` lies in the strict interior of edge `i` of `T`: it is on the segment
    `vEdgeStart i → vEdgeEnd i` but is neither endpoint. -/
def OnStrictEdgeInterior (T : LatticeTriangle) (i : Fin 3) (p : ℤ × ℤ) : Prop :=
  p ∈ latticeSegmentPoints (T.vEdgeStart i) (T.vEdgeEnd i) ∧
  p ≠ T.vEdgeStart i ∧ p ≠ T.vEdgeEnd i

end LatticeTriangle

/-- **Case (a) witness**: when edge `i` of `T` has `gcd ≥ 2`, there is a
    lattice point in the strict interior of that edge.

    The witness is the parameter-`k = 1` point of the gcd-parametrisation:
    `vᵢ + (Δ / g)` where `Δ = vᵢ₊₁ - vᵢ` and `g = edgeGCD i`. -/
theorem exists_nonvertex_lattice_point_of_edgeGCD_ge_two
    (T : LatticeTriangle) (i : Fin 3) (hg : 2 ≤ T.edgeGCD i) :
    ∃ p : ℤ × ℤ, T.OnStrictEdgeInterior i p := by
  set v := T.vEdgeStart i with hv_def
  set w := T.vEdgeEnd i with hw_def
  set dx : ℤ := w.1 - v.1 with hdx_def
  set dy : ℤ := w.2 - v.2 with hdy_def
  set g  : ℕ := Int.gcd dx dy with hg_def
  -- The witness: parameter k = 1 on the gcd-parametrisation
  let p : ℤ × ℤ := (v.1 + dx / (g : ℤ), v.2 + dy / (g : ℤ))
  refine ⟨p, ?_, ?_, ?_⟩
  · -- p ∈ latticeSegmentPoints v w
    -- Apply Finset.mem_image with witness k = 1 ∈ range (g+1)
    -- This requires showing edgeGCD T i = g (= Int.gcd dx dy).
    have hg_eq : T.edgeGCD i = g := by
      unfold LatticeTriangle.edgeGCD
      fin_cases i <;>
        (simp only [LatticeTriangle.edgeDelta, hv_def, hw_def,
                    LatticeTriangle.vEdgeStart, LatticeTriangle.vEdgeEnd,
                    hdx_def, hdy_def, hg_def, Int.gcd, Int.natAbs_sub_comm] <;>
         rfl)
    have hg_ge : (2 : ℕ) ≤ g := hg_eq ▸ hg
    have h1_lt : 1 < g + 1 := by omega
    have h1_mem : (1 : ℕ) ∈ Finset.range (g + 1) := Finset.mem_range.mpr h1_lt
    unfold LatticeTriangle.latticeSegmentPoints
    refine Finset.mem_image.mpr ⟨1, h1_mem, ?_⟩
    simp [p, hv_def, hw_def, hdx_def, hdy_def, hg_def]
  · -- p ≠ vEdgeStart i = v
    intro hpv
    -- p.1 = v.1 + dx/g; if p = v then dx/g = 0
    have hxz : dx / (g : ℤ) = 0 := by
      have := congrArg Prod.fst hpv
      simp only [p] at this; linarith
    -- But g ≥ 2, dx ≠ 0 unless dy ≠ 0; dx/g = 0 ⟹ dx = 0 (with g ∣ dx).
    -- Then by Int.gcd properties, dy ≠ 0 ⟹ g ∣ dy but dy/g·g = dy.
    -- Combine: dx = 0 ∧ dy ≠ 0 leads to checking p ≠ v on the y-component.
    by_cases hy : dy / (g : ℤ) = 0
    · -- Both dx/g = 0 and dy/g = 0: then g ∣ dx ∧ g ∣ dy gives dx = dy = 0
      -- but then g = Int.gcd 0 0 = 0, contradicting g ≥ 2.
      have hdx_zero : dx = 0 := by
        have := Int.ediv_mul_cancel (Int.gcd_dvd_left dx dy : (g : ℤ) ∣ dx)
        rw [hxz, zero_mul] at this; exact this.symm
      have hdy_zero : dy = 0 := by
        have := Int.ediv_mul_cancel (Int.gcd_dvd_right dx dy : (g : ℤ) ∣ dy)
        rw [hy, zero_mul] at this; exact this.symm
      have : g = 0 := by simp [hg_def, hdx_zero, hdy_zero, Int.gcd]
      omega
    · -- dy/g ≠ 0: p.2 = v.2 + dy/g ≠ v.2, contradicting p = v
      have hyy := congrArg Prod.snd hpv
      simp only [p] at hyy
      have : dy / (g : ℤ) = 0 := by linarith
      exact hy this
  · -- p ≠ vEdgeEnd i = w
    intro hpw
    -- p = v + Δ/g; p = w iff Δ/g = Δ, iff (g-1)·Δ/g = 0 with g ≥ 2.
    -- Use that Δ/g · g = Δ (by g ∣ Δ.fst and g ∣ Δ.snd).
    -- If g ≥ 2 and (dx, dy) = (g·a, g·b), then p = (v.1 + a, v.2 + b) and
    -- w = (v.1 + g·a, v.2 + g·b). p = w ⟹ a = g·a ⟹ (g-1)·a = 0 ⟹ a = 0
    -- (since g ≥ 2). Symmetric for b. So a = b = 0 ⟹ Δ = 0 ⟹ g = 0,
    -- contradicting g ≥ 2.
    have hg2 : (2 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg_eq ▸ hg
    have hgne : (g : ℤ) ≠ 0 := by linarith
    -- From hpw: w.1 - v.1 = dx/g, w.2 - v.2 = dy/g
    -- Actually hpw says p = w, so v + Δ/g = w = v + Δ ⟹ Δ/g = Δ
    have hxw : dx / (g : ℤ) = dx := by
      have := congrArg Prod.fst hpw
      simp only [p, hdx_def] at this; linarith
    have hyw : dy / (g : ℤ) = dy := by
      have := congrArg Prod.snd hpw
      simp only [p, hdy_def] at this; linarith
    -- dx/g = dx and g ∣ dx ⟹ dx · (1 - g) = 0 ⟹ dx = 0 (since g ≥ 2)
    -- Multiply hxw by g: g · (dx/g) = g · dx, i.e. dx = g · dx (since g ∣ dx)
    have hxg : dx = (g : ℤ) * dx := by
      have hdvd : (g : ℤ) ∣ dx := Int.gcd_dvd_left dx dy
      have := Int.ediv_mul_cancel hdvd
      -- this : dx/g * g = dx; rewrite via hxw
      calc dx = dx / (g : ℤ) * (g : ℤ) := this.symm
           _  = dx * (g : ℤ) := by rw [hxw]
           _  = (g : ℤ) * dx := by ring
    have hyg : dy = (g : ℤ) * dy := by
      have hdvd : (g : ℤ) ∣ dy := Int.gcd_dvd_right dx dy
      have := Int.ediv_mul_cancel hdvd
      calc dy = dy / (g : ℤ) * (g : ℤ) := this.symm
           _  = dy * (g : ℤ) := by rw [hyw]
           _  = (g : ℤ) * dy := by ring
    -- dx = g · dx ⟹ (g - 1) · dx = 0 ⟹ dx = 0 (g ≥ 2)
    have hdx0 : dx = 0 := by
      have h : ((g : ℤ) - 1) * dx = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    have hdy0 : dy = 0 := by
      have h : ((g : ℤ) - 1) * dy = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    -- dx = dy = 0 ⟹ g = 0, contradicts g ≥ 2
    have : g = 0 := by simp [hg_def, hdx0, hdy0, Int.gcd]
    omega
```

---

## Bearer audit (Mathlib v4.26.0, pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer | Path | Purpose |
|---|---|---|
| `Int.gcd_dvd_left` | `Mathlib/Data/Int/GCD.lean` | `(g : ℤ) ∣ dx` |
| `Int.gcd_dvd_right` | `Mathlib/Data/Int/GCD.lean` | `(g : ℤ) ∣ dy` |
| `Int.ediv_mul_cancel` | `Mathlib/Data/Int/Defs.lean` | `dx/g · g = dx` when `g ∣ dx` |
| `Finset.mem_image` | `Mathlib/Data/Finset/Image.lean` | Show `p ∈ image (Finset.range (g+1))` |
| `Finset.mem_range` | `Mathlib/Data/Finset/Range.lean` | `(1 : ℕ) ∈ range (g+1) ↔ 1 < g+1` |
| `Int.natAbs_sub_comm` | `Mathlib/Data/Int/Basic.lean` | (used in `edgeGCD` unfold for `vEdgeStart`/`vEdgeEnd` orientation) |
| `mul_eq_zero` | `Mathlib/Algebra/Ring/Basic.lean` | factor `(g-1)·dx = 0` to `g=1 ∨ dx=0` |

NO v4.26.0 risk identified — all bearers stable since v4.0.

---

## Risk profile

| Risk | Severity | Mitigation |
|---|---|---|
| `edgeGCD` unfold under `Fin 3` mismatch with `vEdgeStart/End` orientation | MEDIUM | `Int.natAbs_sub_comm` handles the (v1 - v3) vs (v3 - v1) sign flip in edge 2 |
| `Int.gcd` vs `Nat.gcd` confusion | LOW | `Int.gcd a b = Nat.gcd a.natAbs b.natAbs` is `rfl` |
| `Prod.mk` injectivity in pair-equation cases | LOW | `congrArg Prod.fst/snd` extracts components cleanly |
| Witness off-by-one (k=1 vs k=0) | LOW | k=0 is the start endpoint; k=1 is strictly between when g ≥ 2 |
| Docker build blocked | NONE | S4 STATE-SYNC verified Docker GREEN (2026-06-02); no SzemerediCounting-style dep blocker for the Picks chain |

---

## Recommended ACT plan

Apply the §"Paste-ready code" block as one paste after line 719 of
`proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean`. Estimated effect:

- File: 721 LOC → 770–780 LOC
- New defs: `LatticeTriangle.vEdgeStart`, `LatticeTriangle.vEdgeEnd`,
  `LatticeTriangle.OnStrictEdgeInterior`
- New theorem: `exists_nonvertex_lattice_point_of_edgeGCD_ge_two`
- Sorry count: 0 (file remains sorry-free)
- Axioms: 0

Then run `./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01`
to Docker-verify (S4 STATE-SYNC confirmed Docker GREEN as of 2026-06-02).

After this ACT, the next sub-step is Case (b) (Minkowski-style interior
witness for primitive triangles), which closes the full
`exists_nonvertex_lattice_point` statement combining cases (a) and (b).
S3b PREP §4.1.b discusses (b.ii) "Direct combinatorial argument" via
Euclidean-algorithm-on-edge-vectors as the preferred non-circular route.

---

## Files this PREP touches (doc-only, no Lean changes)

- `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-06-04-s3b-act2-prep-edge-interior-witness.md` (this file)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` (Phase + iter increment)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/knowledge.md` (S3b-act-2 PREP entry)
