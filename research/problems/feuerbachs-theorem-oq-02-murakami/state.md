# Current State

**Phase**: LEAN-VERIFIED (Grace trirectangular theorem Docker-built GREEN + registered)
**Since**: 2026-06-15T22:10:00.000Z
**Iteration**: 11

## S11 (researcher-2, 2026-06-15) — Lean build GREEN + registered + bug fix

`StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean` (theorem
`grace_feuerbach_trirectangular`, all 5 identities, 0 sorry / 0 axiom) is now
**Docker-verified GREEN** and registered in `Proofs.lean` (after the Feuerbach
OQ02 imports). Docker was FREE this window (Aristotle still 404).

**Bug fixed:** the previously-"merged" proof did NOT actually compile. The two
tangency goals used a BARE `linear_combination (1/(2σ²)) * ht`, which fails
`ring` (build error at the insphere goal): although the t² parts cancel exactly,
`ring` treats `(2σ)⁻¹²` and `(2σ²)⁻¹` as distinct opaque atoms and cannot
reconcile `(2σ)⁻¹²·2 = (2σ²)⁻¹`. Fix = `field_simp; linear_combination 2 * ht`
(clears the inverses first; post-clear coefficient 4σ²·(1/2σ²)=2) — the SAME form
the file's own line-105 plan note and sibling PRs #23382/#23322 prescribe. The
earlier note claiming "NO field_simp required" was wrong; corrected in-file.

## Current Focus

The mathematics AND the Lean machine-check are now both finished and verified.
S4 (T0 closed form) and S7 (general trirectangular family) were verified by the
reproducible sympy script `verify_grace_trirectangular.py` (16/16 identities OK).
Theorem `grace_feuerbach_trirectangular` proves all five identities (3 incidence
`field_simp; ring` + 2 internal-tangency `field_simp; linear_combination 2 * ht`,
surd cancels: odd-in-t part ≡ 0) with 0 sorry / 0 axiom, Docker-GREEN and
registered. Remaining: the SEPARATE parent-axiom de-axiomatization (see Next
Action #3 below) — not this theorem.

The Grace theorem itself is DONE (Docker-GREEN, registered). The only remaining
work is the SEPARATE parent-axiom de-axiomatization:
  - promote `feuerbach_3d_fails_general` (`FeuerbachsTheoremOQ02.lean:581`) to a
    theorem once `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` (currently
    1 sorry / 2 axioms) is built green — a distinct sub-problem, still open.

## Result (general trirectangular tetrahedron) -- VERIFIED

Tetrahedron D=(0,0,0), A=(a,0,0), B=(0,b,0), C=(0,0,c), a,b,c>0.
Let sigma=a+b+c, P=ab+bc+ca, q=sqrt(a^2 b^2+b^2 c^2+c^2 a^2).

- insphere radius   rho_in  = (P - q)/(2 sigma), centre rho_in*(1,1,1)
- D-exsphere radius rho_Dex = (P + q)/(2 sigma), centre rho_Dex*(1,1,1)
- Grace sphere through A,B,C:
    centre Theta = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2 sigma)
    radius R     = (a^2+b^2+c^2+ab+bc+ca) / (2 sigma)   (RATIONAL -- surd cancels)
- Internal tangency identities (both > 0, hence internal):
    |Theta - I| = R - rho_in  = (a^2+b^2+c^2 + q)/(2 sigma)
    |Theta - E| = R - rho_Dex = (a^2+b^2+c^2 - q)/(2 sigma)
  positivity: (a^2+b^2+c^2)^2 - q^2 = a^4+b^4+c^4 + (a^2b^2+b^2c^2+c^2a^2) >= 0.
- Pencil derivation: sphere through A,B,C is x^2+y^2+z^2+Dx+Ey+Fz+G=0 with
    D=-(a^2+G)/a, E=-(b^2+G)/b, F=-(c^2+G)/c; the unique simultaneous-tangency
    value is G = abc/sigma, and centre(G=abc/sigma) = Theta.
- T0=(2,3,6): Theta=(40,45,72)/22, R=85/22, rho_in=(18-3 sqrt 14)/11,
    rho_Dex=(18+3 sqrt 14)/11. (S4 values reproduced.)

This is the positive 3D Feuerbach (Grace) theorem for the whole trirectangular
family (cf. Maehara & Martini, AMM 127(10):897-910, 2020): the Grace sphere of
the (+,+,+) homothety pair is internally tangent to BOTH the insphere and the
D-exsphere, and passes through the opposite face A,B,C.

## Blockers

- None for the Grace theorem — Docker-GREEN and registered as of 2026-06-15.
- Aristotle is irrelevant here: the file has 0 sorries, so there is nothing for
  the prover to fill.

## Next Action

1. ~~Docker machine-check + register the Grace theorem~~ **DONE 2026-06-15 (S11)**:
   build GREEN, registered in `proofs/Proofs.lean`. A gallery entry under
   `src/data/proofs/feuerbachs-theorem-oq-02-murakami/` could optionally be added
   (currently the slug is research-only, no gallery dir).
2. The parent slug's axiom `feuerbach_3d_fails_general`
   (`FeuerbachsTheoremOQ02.lean:581`) can be promoted to a theorem once
   `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` (1 sorry / 2 axioms) is
   built green — a SEPARATE de-axiomatization, still open. The witness file's own
   sorry/axioms need discharge first.

Do NOT re-transcribe the Grace theorem (done + registered).

## Attempt Counts

- Total Lean builds: 3 (2026-06-15 S11) — first RED (bare `linear_combination`
  failed `ring`), then GREEN after the `field_simp; linear_combination 2 * ht`
  fix, plus a confirming rebuild.
- Approaches tried: analytic derivation + sympy certification + Lean
  transcription + Docker machine-check — all complete and GREEN.
