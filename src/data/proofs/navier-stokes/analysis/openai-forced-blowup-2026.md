# OpenAI's Forced Finite-Time Blowup (September 2026) vs. Our Enstrophy Framework

**Date:** 2026-09-08
**Status:** ANALYSIS — connects an external result to the v1–v4 enstrophy arguments; contains an erratum to v3

---

## 1. What was announced

On 2026-09-08 OpenAI published *On the Navier–Stokes Millennium Prize Problem*
(https://openai.com/index/navier-stokes-solution/) together with a 165-page paper,
*Finite time blowup for Navier–Stokes* (author line: "OpenAI";
https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf),
and a Lean 4 certificate repository, https://github.com/openai/NavierStokesAndEuler
(Lean `v4.34.0-rc2`, Mathlib; `formalization.yaml` reports 0 sorries and only
`propext` / `Classical.choice` / `Quot.sound` in `#print axioms`; review status
"self-assessed"). The certified statements are checked against the DeepMind
*Formal Conjectures* reference formalization of the Clay problem text, via the
Comparator tool.

**Theorem 1.1 (verbatim).** For every ν > 0 there exist a force f ∈ C_c^∞(ℝ³ × (0,∞); ℝ³),
a compact set K ⊂ ℝ³, and smooth velocity and pressure fields u, p on ℝ³ × [0,1) satisfying

```
∂_t u + (u·∇)u − ν∆u + ∇p = f,   ∇·u = 0,   u(·,0) = 0,
```

such that supp u(·,t) ∪ supp p(·,t) ⊂ K for every 0 ≤ t < 1,

```
sup_{0≤t<1} ‖u(t)‖_{L²(ℝ³)} < ∞,      limsup_{t↑1} ‖u(t)‖_{L^∞(ℝ³)} = ∞.
```

Consequently there is no smooth solution on ℝ³ × [0,∞) with the same force and initial
datum whose kinetic energy is uniformly bounded. Compact support gives the periodic
version (Corollary 10.6).

### 1.1 Which Clay alternative this is

Fefferman's problem statement has four alternatives: (A)/(B) global existence and
smoothness on ℝ³ / 𝕋³ **with f = 0**, and (C)/(D) *breakdown* on ℝ³ / 𝕋³, where the
breakdown alternatives explicitly allow a smooth external force f satisfying decay
conditions. OpenAI claims **(C) and (D)**. Their construction has zero initial velocity;
the singularity is driven entirely by a smooth, compactly supported force.

The unforced questions (A) and (B) are **not** addressed and remain open. This matters for
our entry: Part LVI of `NavierStokes.lean` (`ClayMillennium` namespace) documents only
alternatives (A) and (B) in its docstring; the gallery text has been updated to record
all four.

### 1.2 Verification status (as of 2026-09-08)

- Lean-checked by OpenAI; the alignment between the Lean statement and the Clay text is
  what humans still have to sign off on (Quanta, quoting the community).
- Not peer reviewed; no arXiv posting at announcement time.
- Priority/credit is disputed. The method descends from Córdoba–Martínez-Zoroa's forced
  Euler singularities (arXiv:2410.22920) and their IPM work, and from
  Alpöge–Buckmaster's September 2026 preprints (forced IPM / Boussinesq / Euler with
  Lean formalizations), which Tao discusses in his 2026-09-07 post. We record the dispute
  and do not adjudicate it.

### 1.3 The physical picture (paper §2–3)

Writing τ = 1 − t and fixing 0 < h < 1/100:

| Quantity | Scale |
|----------|-------|
| core radius ℓ_r | τ^{1/2} (the parabolic scale) |
| core height ℓ_z | τ^{1/2−h}, so ℓ_r/ℓ_z ≍ τ^h → 0 (slender column) |
| azimuthal, axial speed | τ^{−1/2−h} |
| radial speed | O(τ^{−1/2}) |
| angular Reynolds number Re_θ = |u_θ|ℓ_r/ν | τ^{−h} → ∞ |
| radial Reynolds number Re_r | O(1) |
| core kinetic energy E_core | τ^{1/2−3h} → 0 |
| core dissipation ∫|∂_r u|² (paper's D_core) | τ^{−1/2−3h} |

An axisymmetric leading profile spirals inward with axial outflow. Joining the core to a
smooth exterior leaves an unbounded momentum residual in an annulus; the paper cancels the
singular part of that residual with the mean Reynolds stress of oscillatory pulses placed in
the annulus, then corrects to all orders so that the residual force f extends smoothly
through t = 1. The force is then *defined* as the residual. Rescaling
u_ν(x,t) = √ν u(x/√ν, t) handles every ν > 0.

### 1.4 On the word "stability"

The construction is not a stability statement about the singularity: OpenAI does not claim
the blowup persists under perturbation of the data or force, and the announcement says
nothing about dynamic stability. (Tao's post separately mentions an independent
PINN-based *stable* unforced Euler candidate by Ganeshram–Duruisseaux–Anandkumar, whose
rigorous stability verification is still open.) The one place "stability" enters *our*
entry is the enstrophy-budget notion "S ≤ νP eventually" (`typeII_eventual_stability`).
Section 3 below shows the OpenAI flow is a concrete counterexample to that mechanism once a
smooth force is allowed.

---

## 2. Dictionary: OpenAI's scales in our enstrophy variables

Our framework tracks E = ∫|ω|², P = ∫|∇ω|², S = ∫ ω·(∇u)ω, Ω = ‖ω‖_∞, the identity
E′ = 2S − 2νP, and R_diff = √(ν/Ω). The table below evaluates these on the OpenAI core
(order of magnitude, ν = 1, using only the scales the paper states; the oscillatory pulses
are lower order in these budgets — the paper's own energy accounting is done on the core).

| Ours | Evaluated on the OpenAI core | Note |
|------|------------------------------|------|
| Ω | u_θ/ℓ_r ≍ τ^{−1−h} | blowup exponent α = 1 + h: **Type II, barely** |
| E | Ω²·vol ≍ τ^{−2−2h}·τ^{3/2−h} = τ^{−1/2−3h} | matches the paper's D_core |
| P | (Ω/ℓ_r)²·vol ≍ τ^{−3/2−3h} | |
| S | (∂_z u_z ≍ τ^{−1})·Ω²·vol ≍ τ^{−3/2−3h} | consistent with E′ ≍ τ^{−3/2−3h} |
| R_diff | τ^{1/2+h/2} | |
| ℓ_r / R_diff | τ^{−h/2} = Re_θ^{1/2} → ∞ | **core is not at the diffusion scale** |
| β = S/(ΩE) | τ^{h} = (T−t)^{α−1} → 0 | our `eff_beta_vanishes` prediction, realized |
| ‖u‖_{L³}³ | τ^{−4h} → ∞ | slow critical-norm blowup, consistent with ESŠ |
| ∫Ω dt | diverges | consistent with BKM |

**Forcing is invisible in the enstrophy budget.** With a force the identity reads
E′ = 2S − 2νP + 2∫ω·curl f, and |∫ω·curl f| ≤ ‖curl f‖_{L²} E^{1/2} = O(τ^{−1/4−3h/2}),
which is negligible against E′ ≍ τ^{−3/2−3h}. The force does its work through the
momentum equation (it is the residual that keeps the collapsing vortex self-consistent),
not by injecting enstrophy. Consequently every scalar inequality in our framework that
mentions only E, P, S, Ω, ν can be tested on this flow.

---

## 3. Testing the five `NSAxioms` fields on the flow

| Field | Statement | On the OpenAI core | Verdict |
|-------|-----------|--------------------|---------|
| 1 `typeII_gt_one` | α > 1 | α = 1 + h | ✓ |
| 2 `spectral_gap` | νP ≥ c·Ω·E | τ^{−3/2−3h} vs τ^{−3/2−4h}: ratio τ^{h} → 0 | **✗ fails** |
| 3 `theta_bound` | S ≤ C(T−t)^{α−1}·Ω·E | β ≍ τ^{h} = (T−t)^{α−1} | ✓ (saturated) |
| 4 `blowup_rate` | Ω ≤ C(T−t)^{−α} | Ω ≍ τ^{−1−h} | ✓ |
| 5 `bkm` | bounded E ⇒ bounded Ω | E is unbounded, hypothesis vacuous | ✓ |

Exactly one field fails, and the failure has a clean meaning. `spectral_gap` says the
dissipation is at least what Faber–Krahn gives for vorticity concentrated in balls of radius
R_diff, i.e. that the vortex core lives at the diffusion scale, i.e. that the local Reynolds
number is bounded. The OpenAI core is Re_θ^{1/2} = τ^{−h/2} times wider than R_diff, so the
dissipation falls short of c·Ω·E by exactly that factor τ^{h}. Since β decays at the same
rate τ^{h}, stretching and dissipation stay in a fixed ratio S/νP = 1 + E′/(2νP) > 1 all the
way to blowup: "eventual stability" S ≤ νP never arrives, and enstrophy grows like
τ^{−1/2−3h}.

**What this does and does not say.** `navier_stokes_regularity` is a theorem: any solution
whose scalar functionals satisfy all five fields cannot blow up, and that is untouched. What
the OpenAI flow shows is that field 2 is *not* a consequence of "Navier–Stokes physics" in
any sense that ignores the force: here is a smooth solution of the momentum equation with a
smooth, bounded, compactly supported force that violates it. Any future derivation of
`spectral_gap` for the Clay problem must use f = 0 (or some global-in-time consequence of
it) in an essential way. The annotation on `NSAxioms` that called the fields "consequences
of NS physics" has been corrected.

The same lesson applies to the original December 2025 Twitter argument (v1): its
Faber–Krahn step νP ≥ κ·c_FK·θ·Ω·E was applied at radius R_diff. On the OpenAI flow the
fraction of enstrophy inside a ball of radius R_diff tends to zero like a power of τ, so
the hypothesis "θ ≥ c at the diffusion scale" was equivalent to a bounded local Reynolds
number — and this flow has Re_θ → ∞.

---

## 4. Erratum to v3: the direction of the enstrophy ODE bound

Our v3 documents (`conditional-regularity-theorem.md` Step 2, `enstrophy-type-ii-exclusion.md`
Steps 2 and 5, and the corresponding `meta.json` prose) stated that dE/dt ≤ C·E³ "limits
growth to E ≲ (T*−t)^{−1/2}" and used this as an **upper** bound on the enstrophy in Step 3.

This is backwards. Integrating d/dt(E^{−2}) ≥ −2C from a blowup time T* gives Leray's
classical **lower** bound

```
E(t) ≥ c·(T* − t)^{−1/2}      (equivalently ‖∇u‖_{L²} ≥ c(T*−t)^{−1/4}),
```

the minimum enstrophy a solution must carry to blow up at T*. The cubic ODE gives no upper
bound at all — an upper bound on enstrophy near a singularity is precisely what the whole
problem is about. (The Lean file already has the lower bounds right: `leray_L3_exponent`,
`h1_blowup_rate`; the error lived only in the prose analyses.)

The OpenAI flow makes the correct direction concrete: E ≍ τ^{−1/2−3h} sits *above*
Leray's floor τ^{−1/2} by the factor τ^{−3h}, and ∫E dτ < ∞ exactly because 3h < 1/2,
which is how the paper's global energy inequality survives.

**Consequence for the conditional theorem.** Step 3 of v3 argued: under Bubble
Persistence B′, a Type II rate α > 1 forces concentration ~(T*−t)^{−α/2} at scale R_diff,
which "total E ~ (T*−t)^{−1/2} cannot accommodate". With E only bounded *below*, there is no
contradiction, and Step 3 does not go through. The OpenAI flow is the witness:

- It satisfies B′. With |∇u| ≍ τ^{−1−h} throughout the core, the scale-invariant quantity
  A(r) = r^{−1}∫_{Q_r}|∇u|² is ≍ r⁴τ^{−2−2h}, which is ≍ 1 at r = R_diff and ≍ τ^{−2h} → ∞
  at r = √τ; so A(r) ≥ ε at every dyadic scale in [R_diff, c√(T*−t)]. This is a single
  bubble at a single point — no cascade, no escape, no proliferation.
- It blows up at a Type II rate, α = 1 + h.

So "B′ ⇒ Type I" cannot be proved by any argument that is insensitive to a smooth compactly
supported force, which Step 3 was. What survives of v3 is the *unforced* tail of the chain,
Barker–Prange concentration at the parabolic scale for Type I and ESŠ backward uniqueness —
classical results that use f = 0 — and the honest statement of B′ as a hypothesis. The
scale-mismatch diagnosis (R_diff ≪ √(T*−t) for Type II) stands and is, if anything,
sharpened: the OpenAI construction lives in the mismatch, with R_diff/√τ = τ^{h/2}.

---

## 5. What the connection buys us

1. **A calibrated example.** The construction sits at the edge of every classical
   constraint: α = 1 + h with h < 1/100, enstrophy a factor τ^{−3h} above Leray's floor,
   L³ norm diverging like τ^{−4h/3}, core at the parabolic scale, radial Reynolds number
   O(1), angular Reynolds number τ^{−h}. Any proposed regularity mechanism for the unforced
   problem can be tested against these scalings first.
2. **Which of our hypotheses is load-bearing.** Of the five `NSAxioms` fields only
   `spectral_gap` (bounded local Reynolds number at the diffusion scale) is falsified, and
   `theta_bound` is exactly saturated. The "β → 0" Type II dynamics that the entry proved in
   Lean is genuinely realized by the flow.
3. **Where f = 0 must enter.** Forcing does not enter the enstrophy budget at leading order.
   Any unforced regularity proof therefore cannot proceed by scalar enstrophy inequalities
   alone; it must use the unforced structure at the level of the momentum equation (this is a
   restatement of Tao's 2007 obstruction with a concrete example attached).
4. **A corrected v3.** The enstrophy-direction error is recorded, Step 3 is withdrawn, and
   B′ is downgraded from "bridges the gap" to "an open hypothesis that a forced Type II
   singularity satisfies".

---

## 6. Open questions raised

- Does the OpenAI core satisfy a *forced* analogue of Seregin's LPS condition
  3/s + (α+1)/l = α, and if not, is LPS the right forced/unforced discriminator?
- Can the "spectral gap at the diffusion scale" field be proved from f = 0 in the
  axisymmetric class, where the OpenAI leading profile lives?
- Is h → 0 an obstruction? The construction needs h > 0 (Re_θ → ∞); a proof that unforced
  solutions have bounded local Reynolds number would exclude this mechanism.

---

## References

- OpenAI, *On the Navier–Stokes Millennium Prize Problem* (2026-09-08).
  https://openai.com/index/navier-stokes-solution/
- OpenAI, *Finite time blowup for Navier–Stokes* (2026), 165 pp.
  https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf
- OpenAI, *NavierStokesAndEuler* Lean 4 certificates.
  https://github.com/openai/NavierStokesAndEuler
- Fefferman, *Existence and smoothness of the Navier–Stokes equation*, Clay Mathematics
  Institute problem description (alternatives (A)–(D)).
  https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf
- Córdoba, Martínez-Zoroa, forced 3D Euler singularities. arXiv:2410.22920.
- Alpöge, Buckmaster, finite-time blowup with smooth forcing for IPM, Boussinesq, Euler
  (preprints + Lean, September 2026); see Tao's discussion.
- Tao, *Finite time blowup with smooth forcing term for the incompressible porous medium,
  Boussinesq, and incompressible Euler equations* (2026-09-07).
  https://terrytao.wordpress.com/2026/09/07/finite-time-blowup-with-smooth-forcing-term-for-the-incompressible-porous-medium-boussinesq-and-incompressible-euler-equations/
- Quanta Magazine, *AI Has Solved One of Math's $1 Million Millennium Prize Problems*
  (2026-09-08). https://www.quantamagazine.org/ai-has-solved-one-of-maths-1-million-millennium-prize-problems-20260908/
- Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, Acta Math. 63 (1934)
  — the lower bound ‖∇u‖ ≥ c(T*−t)^{−1/4}.
- Tao, *Why global regularity for Navier-Stokes is hard* (2007).
