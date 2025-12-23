# CKN + Enstrophy: The Right Formulation

**Date:** 2025-12-22
**Status:** FORMULATING - targeting correct object

---

## The CKN ε-Regularity Criterion

**Source:** L. Caffarelli, R. Kohn, L. Nirenberg, "Partial regularity of suitable
weak solutions of the Navier-Stokes equations," Comm. Pure Appl. Math. 35 (1982),
771–831. Modern treatment: [Ożański 2019](https://link.springer.com/book/10.1007/978-3-030-26661-5).

### Suitable Weak Solutions

A weak solution (u,p) is "suitable" if it satisfies the **local energy inequality**:
```
∂ₜ(½|u|²) + div((½|u|² + p)u) + ν|∇u|² ≤ ν∆(½|u|²)
```
in the sense of distributions, tested against non-negative functions.

### ε-Regularity Criterion

**Theorem (CKN):** There exists ε₀ > 0 (universal) such that if (u,p) is a
suitable weak solution on Q₁ = B₁ × (-1, 0) and the scale-invariant quantities:
```
A(1) = ∫_{Q₁} |∇u|² dx dt
C(1) = ∫_{Q₁} |u|³ dx dt
D(1) = ∫_{Q₁} |p|^{3/2} dx dt
```
satisfy A(1) + C(1) + D(1) < ε₀, then u is bounded near the origin.

**Parabolic cylinder:** Q_r(t,x) = B_r(x) × (t-r², t)

**Contrapositive:** If (0,0) is singular, then for all small r:
```
A(r) + C(r) + D(r) ≥ ε₀
```
where A(r) = (1/r)∫_{Q_r}|∇u|², etc. (scaled versions).

---

## What CKN Actually Gives

The scale-invariant quantity is:
```
A(r) := (1/r) ∫_{Q_r} |∇u|² dx dt
```

Unpacking this:
- Time integral over [t-r², t] (length r²)
- Space integral over B_r
- Divided by r

Roughly: A(r) ~ r · (time-averaged local enstrophy)

**CKN says:** A(r) ≥ ε₃ for all r near a singularity.

This is an **ABSOLUTE** lower bound, not a **RATIO** bound!

---

## Why θ = E_loc/E Is the Wrong Target

Even with CKN giving A(r) ≥ ε₃, the total enstrophy E(t) could be:
- Spread over many bubbles
- Located "at infinity"
- Oscillating at high frequencies over large volume

So θ = E_loc(r)/E_total is NOT bounded below by CKN alone.

---

## The Right Target: Critical Norm Concentration

Instead of enstrophy ratio θ, work with **critical norms**.

**The critical norm for NS is L³** (or Lorentz L^{3,∞}).

**Barker-Prange result (Type I):**
```
||u(·,t)||_{L³(B_R)} ≥ γ_univ
```
at scale R ~ √(T*-t) near Type I blowup.

**Why L³ is critical:** Under NS scaling u → λu(λx, λ²t), the L³ norm is invariant.

---

## A Better Formulation

**What we want to show:**

If NS blows up at (x*, T*), then at scale R = √(ν/Ω):
```
||u||_{L³(B_R)} ≥ c   or   some scale-invariant quantity ≥ c
```

**The problem:** Barker-Prange's result is at scale √(T*-t), not at √(ν/Ω).

For Type I: these scales match.
For Type II: √(ν/Ω) << √(T*-t).

---

## What CKN + Enstrophy Can Give

### From CKN:
At scale r, if singular: (1/r)∫_{Q_r}|∇u|² ≥ ε₃

### From enstrophy ODE:
Global bound: E(t) ≤ C(T*-t)^{-1/2}

### Combining:
At the diffusion scale R = √(ν/Ω):
- CKN: R · (time-averaged E_loc(R)) ≥ ε₃
- So: E_loc(R) ≥ ε₃/R = ε₃ · √(Ω/ν)

This is a LOWER bound on local enstrophy at diffusion scale!

### The ratio:
```
θ(R) = E_loc(R)/E(t) ≥ (ε₃ √(Ω/ν)) / E(t)
```

For concentrated vorticity: E ~ Ω² R³ = ν^{3/2} √Ω
So: θ ≥ (ε₃ √(Ω/ν)) / (ν^{3/2} √Ω) = ε₃ / (ν² Ω)

As Ω → ∞, this goes to 0. **Not bounded!**

### Why it fails:
Total enstrophy E(t) can grow with Ω, making the ratio small.
CKN gives a lower bound on LOCAL enstrophy, but not on the RATIO.

---

## The Missing Piece: Anti-Escape

To get θ ≥ c, we need to show:
```
E_total(t) ≤ C · E_loc(R) for some C
```

This is an **anti-escape** or **localization** statement.

**Possible sources:**
1. Energy conservation (bounds total kinetic energy)
2. LPS-type conditions (Seregin uses this)
3. One-bubble hypothesis
4. Concentration compactness

---

## Best Possible Theorem (Conjectured)

**Hypothesis:**
- (u,p) suitable weak solution
- Blows up at (0, T*)
- **Anti-escape:** For all t ∈ [T*-δ, T*), at least fraction θ₀ > 0 of
  enstrophy is in the ball B_{R(t)} where R(t) = √(ν/Ω(t))

**Conclusion:**
- Blowup is Type I (Ω ~ (T*-t)^{-1})

**Proof sketch:**
1. CKN gives E_loc(R) ≥ ε₃/R
2. Anti-escape gives E_total ≤ E_loc/θ₀
3. So E_total ≤ ε₃/(θ₀ R)
4. Enstrophy ODE: dE/dt ≤ CE³
5. Solve: E ~ (T*-t)^{-1/2} at worst
6. With R = √(ν/Ω), get constraint on Ω
7. Show Ω ~ (T*-t)^{-1} (Type I)

**The question:** Can we prove anti-escape without assuming it?

---

## Connection to Our Original Proof

Our proof assumed θ ≥ c at diffusion scale. This is exactly the anti-escape hypothesis!

The question becomes: Is anti-escape a THEOREM or an AXIOM?

**Barker-Prange (Type I):** Proves concentration at √(T*-t).
For Type I, this IS the diffusion scale, so anti-escape is proven.

**Type II:** The scales don't match. Anti-escape at diffusion scale is NOT proven.

---

## Reformulating Our Goal

**Option 1:** Accept anti-escape as a physical assumption.
- Justified by numerical simulations (Hou, Kang-Protas)
- Reflects the physics of vortex dynamics
- Our proof becomes: anti-escape → no Type II → regularity

**Option 2:** Prove anti-escape for Type II.
- This is the missing theorem
- Likely requires additional structure (axisymmetry, LPS, etc.)
- Seregin's work goes this direction with LPS

**Option 3:** Find a different route.
- Use critical norm concentration instead of enstrophy ratio
- Connect directly to Barker-Prange without going through θ

---

---

## The Correct Framing: Conditional Regularity

### What We Now Understand

1. **Anti-escape is the missing heart** - proving it unconditionally would be a
   major breakthrough (equivalent to ruling out cascade/escape mechanisms).

2. **CKN + enstrophy ODE alone cannot give θ ≥ c** because:
   - CKN gives local bounds at singular points
   - Enstrophy ODE gives global timing constraint
   - Neither prevents enstrophy from "escaping" to other regions

3. **The right formulation is conditional:**
   - State anti-escape as a hypothesis (physically motivated)
   - Prove: anti-escape ⟹ Type I only ⟹ regularity

---

## Minimal Anti-Escape Hypotheses (Ordered by Strength)

### Weakest: One-Bubble Concentration
**Hypothesis A:** Near blowup time T*, there exists a single point x* such that
for some γ > 0:
```
∫_{B_{c√(T*-t)}(x*)} |u|³ dx ≥ γ  for all t ∈ [T*-δ, T*)
```

This is exactly what Barker-Prange prove for Type I. For Type II, it would need
to be assumed or proven from additional structure.

### Medium: Bounded Bubble Count
**Hypothesis B:** There exists N < ∞ and c > 0 such that near T*, the enstrophy
is carried by at most N balls of radius c√(T*-t):
```
E(t) ≤ C · ∑_{i=1}^N E_loc(B_{c√(T*-t)}(x_i(t)))
```

This allows multiple concentration centers but bounds their number.

### Stronger: Fraction of Enstrophy at Diffusion Scale
**Hypothesis C:** There exists θ₀ > 0 such that:
```
E_loc(R(t)) ≥ θ₀ · E(t)  where R(t) = √(ν/Ω(t))
```

This is our original assumption. It's stronger because R(t) << √(T*-t) for Type II.

### Comparison to LPS
**Seregin's LPS-type condition:**
```
v ∈ L_{s,l}(Q) with 3/s + (α+1)/l = α
```

This is a space-time integrability condition. It's not directly comparable to
the geometric hypotheses above, but serves a similar role: preventing escape.

---

## The Conditional Theorem (Correct Formulation)

**Theorem (Conditional):** Let (u,p) be a suitable weak solution to NS on
ℝ³ × [0, T*) with finite energy. Assume:

1. **Enstrophy ODE:** dE/dt ≤ CE³ (standard, follows from NS)
2. **Anti-escape (Hypothesis A, B, or C)**

Then:
- If T* is a blowup time, blowup is Type I (Ω ~ (T*-t)^{-1})
- Combined with ESŠ 2003, this implies regularity (no blowup)

**Proof sketch:**
1. Anti-escape + CKN gives: concentration at some ball B_R with critical norms ≥ ε₀
2. Enstrophy ODE gives: E ~ (T*-t)^{-1/2} at worst
3. For Type II (Ω ~ (T*-t)^{-α}, α > 1), the concentration scale implied by
   enstrophy bound contradicts the anti-escape hypothesis
4. Therefore blowup must be Type I
5. Type I + Barker-Prange concentration + ESŠ backward uniqueness ⟹ regularity

---

## Physical Justification for Anti-Escape

**Numerical evidence (Hou, Kang-Protas):**
- Extreme vorticity amplification occurs at vortex reconnection sites
- Enstrophy concentrates in thin tubes/sheets, not spread over large volumes
- Maximum enstrophy growth is localized

**Physical intuition:**
- Vortex stretching is a local phenomenon (requires alignment)
- Spread-out enstrophy doesn't support intense stretching
- Blowup (if it exists) must be concentrated

**Turbulence phenomenology:**
- Energy cascades to small scales
- But the cascade is through LOCALIZED structures (vortex tubes)
- This is NOT the "escape" scenario that breaks anti-escape

---

## Status of the Proof

| Component | Status | Notes |
|-----------|--------|-------|
| CKN ε-regularity | ✓ Proven | CKN 1982 |
| Enstrophy ODE | ✓ Proven | Standard |
| Anti-escape | ◐ Hypothesis | Physically motivated |
| Type I concentration | ✓ Proven | Barker-Prange 2020 |
| ESŠ backward uniqueness | ✓ Proven | ESŠ 2003 |

**The gap:** Anti-escape is assumed, not proven.

**Resolution options:**
1. Accept as physical axiom (reasonable for applications)
2. Prove in restricted classes (axisymmetric, etc.)
3. Find weaker sufficient condition
4. Prove from additional structure (à la Seregin)

---

## References

- [CKN 1982](https://onlinelibrary.wiley.com/doi/10.1002/cpa.3160350604): Original partial regularity
- [Ożański 2019](https://link.springer.com/book/10.1007/978-3-030-26661-5): Modern CKN treatment
- [Barker-Prange 2020](https://arxiv.org/abs/1812.09115): Type I concentration
- [Seregin 2025](https://arxiv.org/abs/2507.08733): Type II exclusion with LPS
- [ESŠ 2003](https://doi.org/10.1070/RM2003v058n02ABEH000609): Backward uniqueness
- [Tao blog](https://terrytao.wordpress.com/2007/03/18/why-global-regularity-for-navier-stokes-is-hard/): Why regularity is hard
