# Knowledge Base: infinitude-primes-4k3-oq-02

Insights accumulated during research on this problem.

Target: PNT-AP / Dirichlet density. For `gcd(a,d)=1`, the primes `p ≡ a (mod d)`
have natural density `1/φ(d)` among all primes. Quantitative refinement of the
parent's qualitative `d=4, a=3` Euclid argument.

---

## Problem Understanding

- The statement is the **Prime Number Theorem for arithmetic progressions**
  (PNT-AP) in its density form: `π(x;d,a)/π(x) → 1/φ(d)`.
- The standard textbook proof (Davenport, *Multiplicative Number Theory*) factors as:
  1. **Character orthogonality** (purely algebraic): over the finite abelian group
     `G = (ℤ/dℤ)ˣ` of order `φ(d)`,
     `𝟙[n ≡ a (mod d)] = (1/φ(d)) · Σ_{χ mod d} χ̄(a) χ(n)`.
  2. **Per-character analytic input** (the crux): for `χ ≠ χ₀`,
     `Σ_{p ≤ x} χ(p) = o(π(x))`, which follows from `L(1,χ) ≠ 0` plus a
     PNT-strength Tauberian/contour argument. The principal character `χ₀`
     contributes the main term `(1/φ(d)) π(x)` via ordinary PNT.
- So the proof is `(elementary orthogonality) + (φ(d)−1 copies of a PNT-AP-strength
  analytic asymptotic) + (ordinary PNT for the χ₀ term)`.

---

## Insights

### S1 (2026-06-14, ORIENT) — Mathlib gap survey: scaffold buildable, crux gated

**Mode**: FRESH (claimed from pool, score 0). Docker DOWN — no build performed;
this is a literature/API-grounded orientation only.

**What Mathlib already provides (verified via mathlib4 docs / PNT+ project notes):**
- Qualitative Dirichlet's theorem (infinitude in each coprime class):
  `Nat.setOf_prime_and_eq_mod_infinite` / `Nat.forall_exists_prime_gt_and_eq_mod`.
- Dirichlet characters and L-series: `Mathlib.NumberTheory.DirichletCharacter.*`,
  `Mathlib.NumberTheory.LSeries.*`.
- **Non-vanishing `L(1,χ) ≠ 0` for `χ ≠ χ₀`**: `Mathlib.NumberTheory.LSeries.Nonvanishing`.
- Ordinary Prime Number Theorem (`d = 1` density baseline), `Nat.totient`,
  finite-abelian-group `MulChar` machinery.

**The crux is NOT in Mathlib (confirmed):** the *quantitative* PNT-AP asymptotic
`π(x;d,a) = (1/φ(d)) Li(x) + o(·)` — equivalently `Σ_{p≤x} χ(p) = o(π(x))` for
`χ ≠ χ₀` — is an explicit **future** goal of the PNT+ project, not yet merged.
Mathlib stops at qualitative Dirichlet + `L(1,χ)≠0` + PNT(d=1); the Tauberian
transfer that upgrades `L(1,χ)≠0` to the density asymptotic is the missing piece.

**Decomposition by buildability:**
- **M1 — character-orthogonality indicator decomposition** (BUILDABLE, ~80–150 LOC):
  `𝟙[n ≡ a] = (1/φ(d)) Σ_χ χ̄(a) χ(n)` over `(ℤ/dℤ)ˣ`. This is standard
  finite-abelian-group character orthogonality (`Σ_χ χ(g) = |G|·𝟙[g=1]`). Mathlib's
  `MulChar` / dual-group infrastructure should make this routine — but it is pure
  **scaffold**: by itself it proves nothing about primes and does not touch the
  analytic obstruction.
- **M2 — per-character prime asymptotic** (GATED, >1000 LOC / multi-month):
  `Σ_{p≤x} χ(p) = o(π(x))`. Needs PNT-AP-strength analytic NT not yet packaged in
  Mathlib. Even the `d=4` milestone (`π(x;4,1) ∼ π(x;4,3) ∼ ½π(x)`) requires this
  asymptotic for the single non-principal quadratic character mod 4.

**Honest classification:** can be *stated* cleanly in Lean today; cannot be *proved*
until M2 lands. M1 is buildable but non-advancing alone, and is itself currently
gated by the Docker build blackout.

### S2 (2026-06-20, ORIENT re-grep) — M1 scaffold collapses to a Mathlib one-liner

**Mode**: continuation (claimed from pool, WEAK). Docker UP; re-grepped the live
Mathlib checkout at `proofs/.lake/packages/mathlib/`.

**Finding**: the M1 character-orthogonality indicator decomposition that S1 listed
as "BUILDABLE, ~80–150 LOC" is now a **direct Mathlib citation**, not buildable
content. `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean` provides:

- `DirichletCharacter.sum_characters_eq (a : ZMod n) :`
  `∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0`
- `DirichletCharacter.sum_char_inv_mul_char_eq (ha : IsUnit a) (b : ZMod n) :`
  `∑ χ, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0`

The second lemma **is exactly** the orthogonality relation underlying M1. The
"indicator decomposition" `𝟙[n≡a] = (1/φ(d)) Σ_χ χ̄(a) χ(n)` is just this lemma
divided by `φ(d)` (over `R = ℂ`, using `χ(a⁻¹)=χ̄(a)` for the unit `a`). That is a
one-line rearrangement — an auditor would (correctly) classify a standalone entry
built on it as a thin Mathlib re-export, badge `mathlib`, not original research.

**Consequence**: this problem now has **zero buildable sub-content**. It is purely
gated on M2 (the PNT-AP analytic asymptotic `Σ_{p≤x} χ(p)=o(π(x))` for `χ≠χ₀`),
still absent from Mathlib (PNT+ future goal). S1's hedge — "M1 buildable but
non-advancing" — is now sharper: M1 isn't even worth building. Correct status
remains `surveyed`; nothing ships until PNT+ lands M2.

### S3 (2026-06-20, ORIENT re-grep, researcher-12) — gap localized to ONE theorem: Wiener–Ikehara

**Mode**: continuation (claimed WEAK). Pin re-grepped at `proofs/.lake/packages/mathlib/`.

S2 left M2 as a vague "PNT+ multi-month" gate. Inspecting the pin more closely
**sharpens this to a single named missing theorem** and shows Mathlib is much closer
than previously documented:

- `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` (M. Stoll, 526 LOC) already builds the
  **von Mangoldt residue-class machinery**: `residueClass a`, its character decomposition
  `residueClass_eq` (= `(q.totient)⁻¹ • Σ_χ χ(a⁻¹)·(χ·Λ)`), the residue-class L-function,
  and crucially `continuousOn_LFunctionResidueClassAux` — the residue-class L-function is
  **continuous on `re s ≥ 1` except a simple pole at `s = 1` with residue `(q.totient)⁻¹`**.
  The `1/φ(d)` main term is therefore **already isolated analytically**.
- The file uses this only for the **qualitative** Dirichlet theorem
  (`infinite_setOf_prime_and_eq_mod`) via divergence of `Σ Λ(n)/n` over the class. Its own
  docstring (line 298) says the auxiliary function is exactly what one feeds to the
  **Wiener–Ikehara theorem** to obtain the quantitative asymptotic.
- **Wiener–Ikehara is NOT in the pin** — comment-only at `PrimesInAP.lean:298`; whole-pin
  grep for a `theorem … Wiener/Ikehara` = 0 hits. It exists in the external
  *PrimeNumberTheoremAnd* project (Kontorovich et al).
- **Correction to S1:** the pin also lacks the **ordinary PNT asymptotic** `ψ(x)~x`.
  `NumberTheory/Chebyshev.lean` has only Chebyshev *bounds* (e.g. `theta_le_log4_mul_x`),
  with a header note that parts were upstreamed from PrimeNumberTheoremAnd — the full PNT
  asymptotic has not been. So S1's "ordinary PNT (d=1 baseline) available" was too optimistic.

**Net:** both ordinary PNT and PNT-AP (M2) are gated on the **same single missing theorem,
Wiener–Ikehara**. Once it lands, M2 follows almost directly from the already-present
residue-class machinery (pole residue `(q.totient)⁻¹`) — far less remaining work than S1/S2
assumed. Still correctly `surveyed`: Wiener–Ikehara itself is a several-hundred-LOC
contour/complex-analysis build, a general-purpose Mathlib-bound result, not a one-session
deliverable.

---

## Dead Ends

- **"Reduce to Mathlib's qualitative Dirichlet"**: insufficient. Infinitude /
  `Σ 1/p` divergence per class does **not** give the density `1/φ(d)`; that needs
  the M2 asymptotic, which is exactly what is missing.
- **"Build M1 and call it progress"**: M1 (orthogonality scaffold) is real but does
  not move the proof toward the target; the target stands or falls on M2.

---

## Next Steps

1. When Docker returns: build M1 (orthogonality indicator decomposition) as a small
   self-contained file, citing the `MulChar` orthogonality lemma actually present in
   Mathlib (verify exact name on the live build, e.g. a `sum_..._eq` over the dual).
2. Watch the **PNT+ project** for the merged PNT-AP asymptotic (`Σ_{p≤x} χ(p)=o(π(x))`).
   When it lands in Mathlib, M2 unblocks and the `d=4` milestone becomes the first
   provable deliverable.
3. Until M2 is available, keep this `surveyed` — stated, approach pinned, crux gated.
