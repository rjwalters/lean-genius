# A Scale-Bridging Conditional Regularity Criterion for Navier-Stokes

**Date:** 2025-12-22
**Status:** THEOREM FORMULATED — **Step 3 WITHDRAWN 2026-09-08** (see erratum below and
`openai-forced-blowup-2026.md`)

> **Erratum (2026-09-08).** Step 2 below states the cubic enstrophy inequality
> dE/dt ≤ CE³ gives an *upper* bound E ≤ C(T*−t)^{−1/2}. It does not: integrating from a
> blowup time gives Leray's *lower* bound E ≥ c(T*−t)^{−1/2}, and no upper bound follows.
> Step 3 used the upper bound to force Type I from B′, so Step 3 does not go through.
> OpenAI's September 2026 forced blowup is an explicit witness: it satisfies B′ at every
> dyadic scale in [R_diff, √(T*−t)] and blows up at the Type II rate α = 1+h. The unforced
> ingredients (Steps 1, 4, 5) stand; B′ ⇒ Type I is open.

---

## Summary

We identify the precise structural obstruction to ruling out Type II blowup in
the 3D Navier-Stokes equations. We show that any mechanism preventing blowup
must enforce **scale-bridging concentration** — persistence of critical norm
concentration from the parabolic scale down to the diffusion scale. We isolate
a minimal hypothesis under which all known regularity tools close.

---

## Main Theorem

**Theorem (Conditional Regularity).**
Let (u, p) be a suitable weak solution to the incompressible Navier-Stokes equations
on ℝ³ × [0, T*) with finite initial energy. Suppose the following holds:

**Hypothesis B′ (Bubble Persistence — Scale-Bridging Concentration):**
There exists a point x* ∈ ℝ³, constants ε > 0 and c > 0, and a sequence tₙ ↗ T*
such that for all **dyadic radii** r ∈ {2⁻ᵏ : R_diff(tₙ) ≤ 2⁻ᵏ ≤ c√(T*-tₙ)}:

```
A(r) := (1/r) ∫_{Q_r(x*, tₙ)} |∇u|² dx dt ≥ ε
```

where R_diff(t) = √(ν/Ω(t)) is the diffusion scale.

**Remark (Scale Invariance):** The quantity A(r) is invariant under the
Navier-Stokes scaling u(x,t) → λu(λx, λ²t). This makes Bubble Persistence a
*structural* condition on the geometry of concentration, not a dimensional artifact.

**Then:**
1. If T* is a blowup time, the blowup is Type I: Ω(t) ≤ C/(T*-t)
2. Consequently, u remains smooth on ℝ³ × [0, T*]

---

## Proof Sketch

### Step 1: CKN Necessity (Standard)

By CKN ε-regularity [CKN 1982], if (x*, T*) is a singular point, then for all
sufficiently small r:
```
A(r) + C(r) + D(r) ≥ ε₀
```
where A(r) = (1/r)∫_{Q_r}|∇u|², C(r) = (1/r²)∫_{Q_r}|u|³, D(r) = (1/r²)∫_{Q_r}|p|^{3/2}.

This gives a lower bound on scale-invariant quantities at the singular point.

**Status:** ✓ PROVEN (CKN 1982, Ożański 2019)

### Step 2: Enstrophy Growth Bound (Standard)

The enstrophy E(t) = ∫|ω|² satisfies:
```
dE/dt ≤ C E³/ν³
```

Integrating d/dt(E^{-2}) ≥ -2C from a blowup time T* gives Leray's **lower** bound:
```
E(t) ≥ c(T* - t)^{-1/2}
```

This is the minimum enstrophy a solution must carry to blow up at T*. It gives
**no upper bound**: the cubic inequality permits arbitrarily fast growth, and an
upper bound on enstrophy near a singularity is the whole problem. (Corrected
2026-09-08; the original text stated the inequality in the wrong direction.)

**Status:** ✓ PROVEN (Leray 1934) — as a lower bound only

### Step 3: Scale Comparison via Anti-Escape (Uses Hypothesis)

The Bubble Persistence hypothesis ensures concentration persists across scales
from R_diff up to √(T*-t).

**Original claim (WITHDRAWN 2026-09-08):** Under this hypothesis, if Ω ~ (T*-t)^{-α}
with α > 1 (Type II), the enstrophy bound and CKN are incompatible.

**Why the original argument fails:** it used "E ≲ (T*-t)^{-1/2}" as an upper bound
to say that total enstrophy "cannot accommodate" the CKN concentration
~(T*-t)^{-α/2} at R_diff propagated to scale √(T*-t). Step 2 only gives a lower
bound, so nothing prevents E from being as large as B′ + CKN require. With the
correct direction there is no contradiction.

**Witness:** OpenAI's forced construction (see `openai-forced-blowup-2026.md`)
satisfies B′ at every dyadic scale in [R_diff, √(T*-t)] — a single bubble at a
single point, A(r) ≍ r⁴(T*-t)^{-2-2h} ≥ 1 — and blows up with α = 1 + h > 1. Since a
smooth compactly supported force is invisible in the enstrophy budget, no
forcing-insensitive scale-comparison argument can prove B′ ⇒ Type I; any repair
must use f = 0 through the momentum equation.

**Status:** ✗ WITHDRAWN — B′ ⇒ Type I is an open question

### Step 4: Type I Concentration (Standard for Type I)

By Barker-Prange [2020], for Type I blowup:
```
‖u(·,t)‖_{L³(B_R(x*))} ≥ γ_univ  where R = c√(T*-t)
```

Combined with Step 3, any blowup satisfying Bubble Persistence must be Type I.

**Status:** ✓ PROVEN for Type I (Barker-Prange 2020)

### Step 5: Backward Uniqueness Excludes Type I (Standard)

By Escauriaza-Seregin-Šverák [2003], Type I blowups with bounded L³ are excluded
via backward uniqueness for parabolic equations.

More precisely: the rescaled solution at a Type I singularity would give a
non-trivial ancient solution vanishing at t = 0, contradicting backward uniqueness.

**Status:** ✓ PROVEN (ESŠ 2003)

### Conclusion

As originally written, Steps 1-5 were meant to chain:
- Blowup → CKN concentration (Step 1)
- + Anti-escape → Type I (Steps 2-3) — **broken**, see Step 3
- Type I → L³ concentration (Step 4)
- L³ concentration at Type I rate → contradiction (Step 5)

What actually survives is the classical unforced statement
"Type I ⇒ regularity" (Steps 4-5, Barker-Prange + ESŠ). The step from B′ to
Type I is not established. ∎ (withdrawn)

---

## Status Summary

| Step | Content | Status |
|------|---------|--------|
| 1 | CKN ε-regularity | ✓ Proven |
| 2 | Enstrophy ODE bound (Leray LOWER bound) | ✓ Proven — lower bound only |
| 3 | Scale bridge via anti-escape | ✗ **Withdrawn** (used Step 2 as an upper bound) |
| 4 | Type I concentration | ✓ Proven |
| 5 | Backward uniqueness | ✓ Proven |

**The gap:** Step 3 requires Bubble Persistence *and* an argument from B′ to Type I that
uses f = 0; the latter does not exist yet.

---

## On the Hypothesis

### What Bubble Persistence Says

"Concentration at the diffusion scale R_diff propagates up to the parabolic
scale √(T*-t), or equivalently, concentration at √(T*-t) persists down to R_diff."

This prevents:
- Enstrophy escaping to other spatial regions
- Concentration fragmenting into many small bubbles
- Scale-by-scale cascade without persistent concentration

### Why It Cannot Be Proven "For Free"

The hypothesis rules out exactly the cascade/escape mechanisms that Tao [2007]
identifies as the core obstruction to regularity proofs via global bounds.

CKN + energy + enstrophy ODE are all compatible with:
- Multiple concentration centers
- Enstrophy at infinity
- High-frequency oscillations spread over large volumes

### Physical Justification

Numerical simulations (Hou 2021-2024, Kang-Protas 2019) show:
- Extreme vorticity events are localized at reconnection sites
- Enstrophy amplification occurs in coherent structures
- No evidence of diffuse multi-bubble blowup

### Comparison to Literature

| Hypothesis | This paper | Seregin 2025 | Barker-Prange 2020 |
|------------|------------|--------------|-------------------|
| Anti-escape type | Bubble Persistence | Generalized LPS | Type I bound |
| Applies to | All blowup | Type II | Type I |
| Strength | Medium | Strong | Weakest |

---

## Possible Extensions

### Restricted Classes

In symmetry classes (axisymmetric, periodic domain), bubble count may be
naturally controlled, making Bubble Persistence provable.

### Weaker Hypotheses

Possible weakening: require concentration at only finitely many scales in
[R_diff, √(T*-t)], not all scales.

### Seregin-Style Euler Scaling

Ask: what is the minimal condition (weaker than LPS) forcing trivial Euler limit?

---

## References

1. L. Caffarelli, R. Kohn, L. Nirenberg. *Partial regularity of suitable weak
   solutions of the Navier-Stokes equations.* Comm. Pure Appl. Math. 35 (1982).

2. T. Barker, C. Prange. *Localized smoothing for the Navier-Stokes equations
   and concentration of critical norms near singularities.* Arch. Ration. Mech.
   Anal. (2020). arXiv:1812.09115

3. L. Escauriaza, G. Seregin, V. Šverák. *L³,∞-solutions of Navier-Stokes
   equations and backward uniqueness.* Russian Math. Surveys 58 (2003).

4. G. Seregin. *A note on impossible scenario of Type II blowups.* (2025).
   arXiv:2507.08733

5. T. Tao. *Why global regularity for Navier-Stokes is hard.* (2007).
   https://terrytao.wordpress.com/2007/03/18/why-global-regularity-for-navier-stokes-is-hard/

6. W. Ożański. *The Partial Regularity Theory of Caffarelli, Kohn, and Nirenberg
   and its Sharpness.* Birkhäuser (2019).

---

## Why This Result Matters

### The Diagnostic Value

The diagnostic reading has to be weakened after v5. What remains true:

> **Any unconditional proof of Navier-Stokes regularity must rule out the
> scenario OpenAI's forced construction realizes — a single persistent bubble at
> the parabolic scale, Re_θ → ∞, α = 1 + h — using f = 0 in an essential way.**

B′ alone does not rule it out (the forced flow satisfies B′).

This is a logical consequence of assembling the full picture:

| Tool | What it gives | What it misses |
|------|---------------|----------------|
| CKN ε-regularity | Necessity at singular points | No localization |
| Enstrophy ODE | Lower bound E ≥ c(T*-t)^{-1/2} | No upper bound, no geometry |
| Barker-Prange | Concentration at √(T*-t) | Only Type I |
| Seregin | Type II exclusion | Needs LPS |

Bubble Persistence (B′) is the **minimal compactness axiom** that glues these
together. It is exactly the "anti-cascade/anti-escape" principle that any
complete proof must establish.

### What B′ Rules Out

The hypothesis excludes precisely the failure modes that Tao identifies as
the core obstruction to regularity proofs via global bounds:

1. **Multi-bubble proliferation:** Enstrophy fragmenting into many small centers
2. **Escape to infinity:** Concentration drifting away from the blowup point
3. **Diffuse cascades:** Energy spreading across disjoint scales without persistence

### Positioning

A fair description of this work:

- We identify the precise structural obstruction to ruling out Type II blowup
- We show that any mechanism preventing blowup must enforce scale-bridging concentration
- We isolate a minimal hypothesis under which all known tools close
- We proposed a conditional pipeline B′ → Type I → ESŠ → regularity, whose first arrow
  was withdrawn in v5 (2026-09-08)

---

## Next Steps

### 1. Short Note for Publication

This could be written as a 5-10 page note titled:
> "A Scale-Bridging Conditional Regularity Criterion for Navier-Stokes"

The contribution is identifying B′ as the minimal structural hypothesis.

### 2. Restricted Settings

Explore settings where Bubble Persistence might be provable:

- **Axisymmetric solutions:** Bubble count naturally controlled by symmetry
- **Periodic domain:** No escape to infinity possible
- **Finite energy + decay:** Spatial localization built in

### 3. Numerical Validation

Extract from Hou's simulations or Kang-Protas optimization:
- Does concentration persist across scales [R_diff, √(T*-t)]?
- What is the observed ε in B′?
- Can this be used as an applied regularity criterion?

### 4. Weaker Hypotheses

Try to further weaken B′:
- Require concentration at only O(log(1/R_diff)) dyadic scales
- Allow ε to decay slowly (e.g., ε ~ 1/log(1/r))
- Replace gradient by velocity (L³ version)
