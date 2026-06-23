# Tropical Crossing Analysis

**Date:** 2025-12-22
**Version:** v2 (continuing work)
**Status:** IN PROGRESS

---

## The Setup

We have two functions of time t ∈ (0, T):

```
L(t) = exp(1/τ) · (1 + θ(t)²)
L_max(t) = 1/τ + 1 + (1 - θ(t))⁻²
```

where τ = T - t (time to blowup) and θ(t) ∈ [0, 1] is the concentration ratio.

**The Rigidity Theorem (PROVED in Lean):**
> If L(t*) = L_max(t*) with τ* ≤ 0.1, then θ(t*) > 0.99

This would close the proof because θ > 0.99 > 0.203 = critical threshold.

---

## Key Observation: Growth Rate Comparison

As t → T (τ → 0):

| Function | Dominant Term | Growth Rate |
|----------|--------------|-------------|
| L(t) | exp(1/τ) | **Super-exponential** in 1/τ |
| L_max(t) | 1/τ or (1-θ)⁻² | **Linear** in 1/τ (if θ bounded from 1) |

**Conclusion:** L(t) eventually dominates L_max(t) as τ → 0.

---

## Case Analysis

### Case 1: θ(t) bounded away from 1

Suppose θ(t) ≤ 0.9 for all t near T.

Then:
- L(t) ~ exp(1/τ) · 1.81
- L_max(t) ~ 1/τ + 1 + 100 ≈ 1/τ + 101

The crossing L = L_max occurs when:
```
exp(1/τ) · 1.81 = 1/τ + 101
```

Let x = 1/τ. We need exp(x) · 1.81 ≈ x + 101.

For x = 5 (τ = 0.2): exp(5) · 1.81 ≈ 269, while 5 + 101 = 106. L > L_max.
For x = 4 (τ = 0.25): exp(4) · 1.81 ≈ 99, while 4 + 101 = 105. L_max > L.

So crossing happens around τ ≈ 0.22-0.25, which is > 0.1.

**Problem:** Crossing with τ > 0.1 doesn't trigger rigidity theorem.

### Case 2: θ(t) → 1 as t → T

If θ approaches 1, then (1 - θ)⁻² → ∞, making L_max grow.

The question becomes: which grows faster?
- L ~ exp(1/τ) · 2 (since θ → 1 means 1 + θ² → 2)
- L_max ~ (1-θ)⁻² (dominates 1/τ if θ → 1 fast enough)

**Critical race:** Does exp(1/τ) beat (1-θ)⁻² as τ → 0?

---

## The Key Question

**Q: Is there a crossing with τ ≤ 0.1?**

This depends on the dynamics of θ(t). Three scenarios:

### Scenario A: θ stays small (θ ≤ 0.9)
- Crossing happens with τ large (≈ 0.2-0.3)
- Rigidity theorem doesn't apply
- **DOES NOT CLOSE PROOF**

### Scenario B: θ → 1 slowly
- L_max grows via (1-θ)⁻², but not fast enough
- L catches up due to exp(1/τ)
- Crossing happens, but when?
- **NEED QUANTITATIVE ANALYSIS**

### Scenario C: θ → 1 fast (approaches before τ = 0.1)
- If θ > 0.99 before τ = 0.1, proof closes directly (no crossing needed!)
- **THIS IS THE DESIRED CASE**

---

## New Insight: Crossing Inevitability

**Claim:** If blowup occurs, there MUST be a time t* where either:
1. L(t*) = L_max(t*) (crossing), OR
2. θ(t*) > 0.99 (direct concentration)

**Proof sketch:**
- At t = 0 (τ = T large): L < L_max typically (both ≈ O(1), but L_max has (1-θ)⁻² term)
- As τ → 0: L ~ exp(1/τ) → ∞ super-exponentially
- If θ stays bounded from 1, L eventually exceeds L_max (crossing must occur)
- If θ → 1, either direct concentration or (1-θ)⁻² competes with exp(1/τ)

**The gap:** We don't know if crossing happens with τ ≤ 0.1.

---

## What Would Close This

To show crossing happens with τ ≤ 0.1, we need one of:

### Approach 1: θ dynamics constraint
Show that θ(t) cannot stay below 0.99 for τ > 0.1 during blowup.
- This would follow from concentration arguments (the original problem!)

### Approach 2: L/L_max ratio analysis
Study R(t) = L(t)/L_max(t) and show R(t*) = 1 with τ* ≤ 0.1.
- Requires understanding dR/dt

### Approach 3: Barrier argument
Show that if τ = 0.1 and no crossing yet, then some invariant is violated.
- Could use energy estimates or other NS structure

---

## Quantitative Analysis Needed

To make progress, we need to understand:

1. **θ dynamics:** What is dθ/dt? Does NS structure constrain θ evolution?

2. **Initial conditions:** At what τ does L first exceed L_max for typical solutions?

3. **Type II structure:** For Type II blowup (α > 1), β → 0. Does this constrain θ?

---

## Connection to Existing Results

From the Lean file, we have:

- **Route 3 (θ dynamics):** For Type II, (T-t)^{α-1} → 0
- This bounds the vorticity alignment angle, not θ directly
- There may be a connection: vorticity alignment affects enstrophy distribution

**Question:** Does β → 0 (vorticity alignment) imply θ → 1 (enstrophy concentration)?

If so, Type II blowup forces θ → 1, which would close via Scenario C.

---

## Next Steps

1. [ ] Derive dθ/dt from NS equations
2. [ ] Check if β → 0 implies θ → 1
3. [ ] Compute explicit crossing time τ* for various θ trajectories
4. [ ] Look for barrier argument at τ = 0.1

---

## Summary

The tropical crossing analysis reveals:
- **L eventually dominates L_max** (exponential vs linear growth)
- **Crossing must occur** if θ stays bounded from 1
- **The gap:** Crossing might happen with τ > 0.1, missing the rigidity theorem

**Key insight:** If we can show θ → 1 for Type II blowup, the proof closes directly without needing the crossing argument.

This connects back to Direction B (Type II structure): Does α > 1 force concentration?

---

## The Two Ingredients (from Lean file analysis)

The proof requires two separate conditions:

| Ingredient | What it gives | Status |
|-----------|---------------|--------|
| β → 0 (vorticity alignment) | S ≤ β·Ω·E → 0 (stretching vanishes) | **PROVED** for Type II |
| θ ≥ c (enstrophy concentration) | νP ≥ c·(π²/4)·Ω·E (dissipation bounded below) | **ASSUMED** (axiom!) |

When both hold: S ≤ β·Ω·E < νP, so E' = 2S - 2νP < 0. Contradiction with blowup.

**The axiom gap (line 1457):**
```lean
axiom concentration_near_blowup (sol : NSSolution) (t : ℝ) (ht : t ∈ Ioo 0 sol.T) :
  thetaAt sol t ≥ 1/2
```

The comment claims this follows from tropical rigidity + CKN, but:
- Tropical rigidity only applies IF crossing with τ ≤ 0.1
- CKN gives dimension bound, not concentration ratio

---

## New Question: Does β → 0 Imply θ → 1?

**Hypothesis:** Vorticity alignment forces enstrophy concentration.

**Physical intuition:**
- β → 0 means vorticity aligns with strain eigenvector
- Aligned vorticity concentrates in tube-like structures
- Tube structures have small cross-section → high θ

**If true:** Type II blowup → β → 0 → θ → 1 → proof closes!

**This is the key question for v2.**

---

## Updated Next Steps

1. [x] Analyze L vs L_max growth rates
2. [x] Identify that crossing happens but τ might be > 0.1
3. [ ] **Investigate β → 0 ⟹ θ → 1 connection**
4. [ ] Search literature for vorticity-concentration relationship
5. [ ] Check if Type II structure constrains enstrophy distribution
