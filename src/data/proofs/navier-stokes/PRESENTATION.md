# Navier-Stokes: Anatomy of a Proof Attempt

## The Story

In December 2025, a sophisticated proof attempt for Navier-Stokes global regularity
went viral on Twitter. The proof appeared rigorous — it used enstrophy balances,
Faber-Krahn eigenvalue bounds, tropical dynamics, and CKN partial regularity.

We analyzed it. What we found is instructive not just for what's wrong, but for
what it reveals about why NS regularity is genuinely hard.

---

## The Journey

### Act 1: The Claim

A Twitter thread by @davidmbudden presented a proof with this structure:
1. For Type II blowup, the alignment parameter β → 0
2. If concentration θ ≥ c, then Faber-Krahn gives νP ≥ (π²/4)θΩE
3. When β → 0 and θ bounded below, eventually S < νP
4. This contradicts enstrophy blowup

**The hidden assumption:** Step 2 assumes θ ≥ c without proof.

### Act 2: The Initial Analysis

We identified that concentration (θ ≥ c) is essentially what needs to be proven
for NS regularity. The proof assumes its conclusion.

But we didn't stop there. We asked: *Is this assumption close to provable?*

### Act 3: The Exploration

Over multiple sessions, we explored fixes:

| Approach | Result |
|----------|--------|
| **θₖ refactor** | K-ball concentration is weaker, but K could be unbounded |
| **Tropical crossing** | Crossings must occur, but timing is uncertain |
| **β → θ hypothesis** | Ruled out — they're independent properties |
| **Diffusion-scale matching** | Promising but needs rigorous argument |

Each dead end taught us something about the problem structure.

### Act 4: The Deep Dive

We connected to the serious mathematical literature:

- **Caffarelli-Kohn-Nirenberg (1982):** ε-regularity gives concentration at singular points
- **Barker-Prange (2020):** Concentration at parabolic scale √(T*-t) for Type I
- **Seregin (2025):** Type II exclusion requires LPS-type conditions
- **Escauriaza-Seregin-Šverák (2003):** Backward uniqueness kills Type I blowup

**The key insight:** There's a **scale mismatch**.

For Type I: The diffusion scale R_diff ≈ √(T*-t). Everything works.

For Type II: R_diff << √(T*-t). The smoothing lemma can't reach the diffusion scale.

### Act 5: The Conditional Theorem

We formulated the **minimal hypothesis** that would fix the proof:

**Hypothesis B′ (Bubble Persistence):**
Concentration persists across dyadic scales from R_diff to √(T*-t).

**Theorem (as stated in v3; first arrow withdrawn in v5):** B′ → Type I only → regularity

This was meant to be honest:
- All steps except B′ were believed proven (CKN, enstrophy ODE, Barker-Prange, ESŠ) —
  but the enstrophy ODE step was used in the wrong direction (see Act 6)
- B′ is exactly the anti-cascade/anti-escape principle Tao identifies as the core obstruction
- Any unconditional proof must, in some form, establish B′

### Act 6: The Forced Counterexample (September 2026)

On 2026-09-08 OpenAI announced a Lean-certified finite-time blowup for 3D Navier-Stokes
**with a smooth, compactly supported force** and zero initial data, for every viscosity, with
bounded kinetic energy — Fefferman's breakdown alternatives (C)/(D). The unforced
alternatives (A)/(B), which this entry is about, remain open.

We ran the construction through our enstrophy variables (`analysis/openai-forced-blowup-2026.md`):

| Ours | On the OpenAI core (τ = T*−t, 0 < h < 1/100) |
|------|------------------------------------------------|
| Ω, blowup exponent | τ^{−1−h}, α = 1 + h — Type II, barely |
| E | τ^{−1/2−3h} — above Leray's floor τ^{−1/2} |
| core radius vs R_diff | √τ vs τ^{1/2+h/2}: ratio Re_θ^{1/2} → ∞ |
| β = S/(ΩE) | τ^{h} = (T−t)^{α−1} → 0 (our `eff_beta_vanishes`, realized) |
| NSAxioms | 4 of 5 hold; only `spectral_gap` fails |
| Bubble Persistence B′ | satisfied — a single bubble, no cascade, no escape |

**Two lessons.** First, forcing is invisible in the enstrophy budget
(|∫ω·curl f| ≲ E^{1/2} ≪ E′), so no argument built only from scalar enstrophy inequalities
can tell forced from unforced; f = 0 has to enter through the momentum equation. Second, we
found an error of our own: v3 read dE/dt ≤ CE³ as an *upper* bound E ≲ τ^{−1/2}. It is Leray's
*lower* bound. That upper bound was the engine of Step 3 (B′ ⇒ Type I), and the OpenAI flow —
B′ satisfied, Type II — is the witness that Step 3 cannot be repaired without using f = 0.
Step 3 is withdrawn.

The construction is not a stability result and is not yet peer reviewed; its credit is
disputed (Córdoba–Martínez-Zoroa, Alpöge–Buckmaster). We record, we do not adjudicate.

---

## What We Learned

### 1. Why the Original Proof Fails

The concentration assumption θ ≥ c is logically stronger than what CKN + energy +
enstrophy ODE can force. It rules out:
- Multi-bubble proliferation
- Escape to infinity
- Diffuse cascades across scales

### 2. What Would Fix It

Bubble Persistence (B′) is the minimal compactness condition. It says:
"Concentration at the parabolic scale propagates down to the diffusion scale."

This is weaker than:
- Full anti-escape (fraction of total enstrophy)
- LPS-type conditions (Seregin)
- Type I bounds (Barker-Prange)

But it's still not provable from basic axioms.

### 3. The Diagnostic Value

We've shown exactly what any complete proof must address. This isn't rhetoric —
it's a logical consequence of assembling all known tools.

---

## Status

| Aspect | Status |
|--------|--------|
| Original Twitter proof | ❌ Flawed (assumes θ ≥ c; equivalently, bounded local Reynolds number at R_diff) |
| Conditional theorem B′ → regularity | ◐ Step 3 (B′ ⇒ Type I) withdrawn 2026-09-08; unforced tail (Barker-Prange + ESŠ) stands |
| Bubble Persistence (B′) | ◐ Hypothesis — satisfied by OpenAI's forced Type II singularity, so not sufficient on its own |
| Millennium Prize — forced breakdown (C)/(D) | ◐ Claimed by OpenAI (2026-09-08), Lean-certified, under community review |
| Millennium Prize — unforced regularity (A)/(B) | ⬜ Open |

---

## The Honest Summary

We did not solve the Navier-Stokes Millennium Problem.

What we did:
1. Analyzed a sophisticated but flawed proof attempt
2. Explored multiple avenues to fix it
3. Connected to the mathematical literature
4. Identified the exact gap: scale-bridging concentration (B′)
5. Formulated a clean conditional theorem
6. Showed what any complete proof must address

The Millennium Problem remains open. But we understand the obstacle better.

---

## Educational Value

This case study demonstrates:

1. **How to analyze proof attempts rigorously**
   - Don't just say "it's wrong" — find the exact flaw
   - Explore whether the flaw is fixable
   - Connect to existing literature

2. **The value of conditional theorems**
   - Even if we can't prove the hypothesis, the conditional result is useful
   - It identifies what's missing
   - It provides a framework for future work

3. **Why NS regularity is genuinely hard**
   - It's not just "we haven't found the right trick"
   - The scale mismatch is a fundamental structural obstacle
   - Any proof must address anti-cascade/anti-escape

4. **Honest mathematical scholarship**
   - Clearly distinguish proven from assumed
   - Don't oversell conditional results
   - Credit the existing literature

---

## Files

| File | Purpose |
|------|---------|
| `analysis/conditional-regularity-theorem.md` | The main theorem |
| `analysis/ASSESSMENT.md` | Honest assessment of contributions |
| `analysis/ckn-critical-concentration.md` | CKN analysis |
| `analysis/type-ii-extension.md` | Type II analysis |
| `analysis/enstrophy-type-ii-exclusion.md` | Enstrophy argument |
| `CHANGELOG.md` | Session-by-session history |
| `papers/INDEX.md` | Literature references |

---

## References

1. Caffarelli, Kohn, Nirenberg. *Partial regularity of suitable weak solutions.*
   Comm. Pure Appl. Math. 35 (1982).

2. Barker, Prange. *Localized smoothing and concentration of critical norms.*
   Arch. Ration. Mech. Anal. (2020). [arXiv:1812.09115](https://arxiv.org/abs/1812.09115)

3. Seregin. *A note on impossible scenario of Type II blowups.* (2025).
   [arXiv:2507.08733](https://arxiv.org/abs/2507.08733)

4. Escauriaza, Seregin, Šverák. *L³,∞-solutions and backward uniqueness.*
   Russian Math. Surveys 58 (2003).

5. Tao. *Why global regularity for Navier-Stokes is hard.* (2007).
   [Blog post](https://terrytao.wordpress.com/2007/03/18/why-global-regularity-for-navier-stokes-is-hard/)
