# Converting CKN ε-Regularity to Enstrophy Ratio θ

**Date:** 2025-12-22
**Status:** IN PROGRESS - Key technical step

---

## The Goal

**CKN gives:** At a singular point, scale-invariant quantities ≥ ε₀ (universal).

**We need:** θ = E_loc/E ≥ c where c ≥ 2/π² ≈ 0.203.

**Question:** Does CKN's ε₀ imply our θ ≥ c?

---

## CKN Scale-Invariant Quantities

Over a parabolic cylinder Q_r = B_r(x₀) × (t₀ - r², t₀):

```
A(r) = (1/r) ∫∫_{Q_r} |∇u|² dx dt    (scaled dissipation)
C(r) = (1/r²) ∫∫_{Q_r} |u|³ dx dt   (scaled velocity)
D(r) = (1/r²) ∫∫_{Q_r} |p|^{3/2} dx dt (scaled pressure)
```

**CKN Criterion:** If A(r) + C(r) + D(r) < ε₀, then (x₀, t₀) is regular.

**Contrapositive:** If (x₀, t₀) is singular, then A(r) + C(r) + D(r) ≥ ε₀ for all r > 0.

---

## Key Observation: A(r) IS Local Enstrophy!

Since ω = ∇ × u and for divergence-free u:
```
|∇u|² ~ |ω|²  (up to boundary terms)
```

So:
```
A(r) = (1/r) ∫∫_{Q_r} |∇u|² dx dt ≈ (1/r) ∫_{t₀-r²}^{t₀} ∫_{B_r} |ω|² dx dt
```

If we assume time-averaging gives a representative value:
```
A(r) ≈ (1/r) · r² · ∫_{B_r} |ω|² dx = r · E_loc(r)
```

where E_loc(r) = ∫_{B_r} |ω|² is the local enstrophy in ball of radius r.

---

## The Bound from CKN

If (x₀, t₀) is singular and A(r) ≥ ε₀/3 (getting 1/3 of the total ε₀):

```
r · E_loc(r) ≥ ε₀/3
⟹ E_loc(r) ≥ ε₀/(3r)
```

This is a LOWER BOUND on local enstrophy!

---

## Converting to θ = E_loc/E

**Definition:** θ(r) = E_loc(r) / E = ∫_{B_r} |ω|² / ∫ |ω|²

From CKN: E_loc(r) ≥ ε₀/(3r)

So:
```
θ(r) = E_loc(r)/E ≥ ε₀/(3rE)
```

**The issue:** This bound depends on r and E (total enstrophy).

For blowup, E → ∞, which makes the lower bound θ ≥ ε₀/(3rE) → 0!

---

## The Problem: Competing Scales

Near blowup at time T:
- Total enstrophy E(t) → ∞ as t → T
- The singular point concentrates energy

The question is whether E_loc grows at least as fast as E.

**What CKN actually says:**
- A(r) ≥ ε₀/3 for some component
- But A(r) is time-integrated over Q_r = B_r × (t-r², t)
- As r → 0, the time interval shrinks too

This is parabolic scaling, which matches the diffusion scale!

---

## The Right Scale: r = R = √(ν/Ω)

**Crucial insight:** The diffusion scale R = √(ν/Ω) is exactly where:
- Viscous and convective effects balance
- CKN's parabolic cylinders Q_R have natural NS scaling
- This is the scale where we need θ ≥ c

At scale R = √(ν/Ω):
- Time interval is R² = ν/Ω
- Spatial ball is B_R

**CKN at diffusion scale:**
```
A(R) = (1/R) ∫_{t-R²}^{t} ∫_{B_R} |ω|² dx dt ≥ ε₀/3 (if singular)
```

Simplifying (assuming steady-state in time):
```
A(R) ≈ R · E_loc(R) ≥ ε₀/3
⟹ E_loc(R) ≥ ε₀/(3R) = ε₀√(Ω/ν)/3
```

---

## The Enstrophy Scaling Near Blowup

For blowup with Ω(t) → ∞:
- Total enstrophy E ~ Ω · Volume_of_concentration
- If concentration is in ball of radius ~ R, then E ~ Ω · R³

With R = √(ν/Ω):
```
E ~ Ω · (ν/Ω)^{3/2} = ν^{3/2} / √Ω
```

**Wait, this says E → 0 as Ω → ∞!**

That's wrong. Let me reconsider.

---

## Reconsidering the Scaling

For Navier-Stokes:
- Ω = ‖ω‖_{L^∞} (maximum vorticity)
- E = ‖ω‖_{L²}² (total enstrophy)

Near blowup:
- Ω → ∞
- E can grow, but energy ½∫|u|² is bounded

The relationship between Ω and E depends on the spatial structure.

**For concentrated vorticity in a ball of radius r:**
- ω ~ Ω in B_r, ω ~ 0 outside
- E ~ Ω² · r³

**If r = R = √(ν/Ω):**
```
E ~ Ω² · (ν/Ω)^{3/2} = Ω² · ν^{3/2} · Ω^{-3/2} = ν^{3/2} · √Ω
```

So E ~ √Ω, which DOES grow with Ω. Good.

---

## The Ratio θ at Diffusion Scale

If vorticity is concentrated in B_R:
```
E_loc(R) = ∫_{B_R} |ω|² ≈ Ω² · R³ = Ω² · (ν/Ω)^{3/2} = ν^{3/2} · √Ω
E_total ≈ E_loc (if all enstrophy is in B_R)
```

In this case θ = E_loc/E ≈ 1.

**But what if enstrophy is spread out?**

If enstrophy is in a larger region of radius L > R:
```
E_loc(R) ~ Ω² · R³
E_total ~ Ω² · L³
θ = E_loc/E ~ (R/L)³
```

If L >> R, then θ << 1.

---

## What CKN Actually Gives

CKN says: If singular at (x₀, t₀), then at ALL scales r:
```
A(r) + C(r) + D(r) ≥ ε₀
```

At the diffusion scale r = R:
```
A(R) + C(R) + D(R) ≥ ε₀
```

If A(R) ≥ ε₀/3:
```
(1/R) ∫_{Q_R} |∇u|² ≥ ε₀/3
```

This is a bound on the INTEGRATED enstrophy over Q_R, not on θ directly.

---

## The Missing Link

**What we need to show:**
```
CKN's ε₀ at scale R = √(ν/Ω)  ⟹  θ = E_loc(R)/E ≥ c
```

**The challenge:**
- CKN gives ∫_{Q_R} |∇u|² ≥ ε₀ · R (dimensional bound)
- This is a bound on local enstrophy INTEGRAL
- We need a bound on the local/global RATIO θ

**The gap:**
- CKN doesn't directly bound the ratio
- The total enstrophy E could be large, making θ small
- But... does the CKN condition at ALL scales help?

---

## Using CKN at Multiple Scales

CKN is special: it holds at ALL scales r, not just one.

For any scale r between 0 and some R₀:
```
A(r) + C(r) + D(r) ≥ ε₀
```

If we integrate this condition over scales... we might get a cumulative bound.

**Heuristic:**
- At scale r, local enstrophy E_loc(r) ≥ ε₀ r / 3
- This must hold for ALL r
- The total enstrophy E = limit of E_loc(r) as r → ∞

But actually, E_loc(r) is monotonic in r (larger ball = more enstrophy).

So E = E_loc(∞) ≥ E_loc(R) ≥ ε₀ R / 3.

This gives E ≥ ε₀ R / 3, but doesn't give θ ≥ c.

---

## A Different Approach: Concentration Compactness

**Idea:** Use the fact that ε₀ is UNIVERSAL and applies at ALL scales.

If enstrophy were spread uniformly in a large ball of radius L:
- E_loc(r) ~ E · (r/L)³ for r < L
- A(r) ~ r · E_loc(r) ~ E · r⁴ / L³

For this to satisfy A(r) ≥ ε₀/3 at all scales:
- ε₀/3 ≤ E · r⁴ / L³ for all r
- This fails for small r unless L ~ r (concentration!)

**Conclusion:** Uniform spread of enstrophy VIOLATES CKN at small scales!

Therefore: CKN forces concentration. The question is whether it forces θ ≥ c.

---

## Quantitative Version

Suppose enstrophy is distributed with density profile ρ(x) = |ω(x)|²:

```
E_loc(r) = ∫_{B_r} ρ(x) dx
E_total = ∫ ρ(x) dx
```

CKN at scale r requires:
```
r · E_loc(r) ≥ ε₀/3
```

For a power-law decay ρ(x) ~ |x|^{-α}:
- E_loc(r) ~ r^{3-α}
- CKN: r · r^{3-α} = r^{4-α} ≥ ε₀/3

For this to hold as r → 0, we need 4 - α ≥ 0, so α ≤ 4.

But for total enstrophy to be finite: 3 - α > -3, so α < 6. (Actually α < 3 for convergence.)

**If α < 3:** E_total is finite, E_loc(r) ~ r^{3-α}, and:
```
θ(r) = E_loc(r)/E_total ~ r^{3-α}
```

This can be small for small r if α < 3.

**But CKN requires:** r · E_loc(r) ≥ ε₀/3, i.e., r^{4-α} ≥ ε₀/3.

At the diffusion scale r = R:
```
R^{4-α} ≥ ε₀/3
⟹ R ≥ (ε₀/3)^{1/(4-α)}
```

This is a LOWER BOUND on R in terms of the enstrophy profile.

---

## The Key Insight

**CKN constrains the enstrophy PROFILE, not just the local value.**

If enstrophy decays like r^{3-α} from the singular point:
- CKN at scale r: r^{4-α} ≥ ε₀/3
- This must hold for all r down to the diffusion scale R

**If α is close to 3 (enstrophy concentrated):**
- θ(R) ~ R^{3-α} is large (close to 1)
- CKN is easily satisfied

**If α is close to 0 (enstrophy spread):**
- θ(R) ~ R³ can be small
- CKN requires R^4 ≥ ε₀/3, limiting how small R can be

**The constraint:** The diffusion scale R can't be too small given the enstrophy profile.

---

## Does This Give θ ≥ c?

**Not directly.** CKN constrains (R, α) jointly, but doesn't give θ ≥ c universally.

However, there's additional structure:

1. **R is not free:** R = √(ν/Ω), determined by the solution
2. **α is not free:** The enstrophy profile is constrained by NS dynamics
3. **Near blowup:** Both Ω → ∞ and the profile evolve together

**The physics:** As Ω → ∞ and R → 0, CKN forces the profile to become MORE concentrated (smaller α), which INCREASES θ.

This is a DYNAMIC constraint, not a static one.

---

## Conclusion: Partial Answer

**CKN gives:** Universal ε₀ constraint at all scales, forcing concentration.

**But:** CKN alone doesn't immediately give θ ≥ c; it constrains the enstrophy PROFILE.

**The missing piece:** Show that NS dynamics near blowup force the profile to concentrate at the diffusion scale, giving θ ≥ c.

**Promising direction:**
- Barker-Prange's γ_univ result may be the rigorous version
- Their Type I result shows θ ≥ γ_univ at diffusion scale
- Extending to Type II remains the key open question

---

## Next Steps

1. [ ] Examine Barker-Prange proof to see how they get γ_univ from CKN + dynamics
2. [ ] Check if their argument is Type I specific or can extend
3. [ ] Look for results on enstrophy profile evolution near blowup
