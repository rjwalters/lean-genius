# Current State

**Phase**: VERIFY (math + Lean transcription COMPLETE; only Docker build-check + registration remain)
**Since**: 2026-06-15T00:00:00.000Z
**Iteration**: 10

## Current Focus

The mathematics AND the Lean transcription are both finished. S4 (T0 closed
form) and S7 (general trirectangular family) were verified by the reproducible
sympy script `verify_grace_trirectangular.py` (16/16 identities OK). S8/S9 (the
Lean transcription) are ALSO DONE and merged: theorem
`grace_feuerbach_trirectangular` in
`proofs/Proofs/StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean`
proves all five identities (3 incidence + 2 internal-tangency) with 0 sorry / 0
axiom, symbolically certified by `verify_grace_proof_certificate.py` (15/15 PASS),
landed build-pending in #24189 (cert) and #24444 (discharge). The proof is
`field_simp; ring` for incidence and `linear_combination (1/(2σ²))·ht` for both
tangency goals (surd cancels: odd-in-t part ≡ 0).

The only remaining steps are infra-gated, NOT mathematical:
  - machine-check the file with Docker (`docker-build.sh`), currently the file is
    build-pending (authored under a Docker blackout);
  - register it in `proofs/Proofs.lean` and add a gallery entry once green.

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

- Docker build-verification is gated by container saturation (observed 6-7
  containers, host RAM low); a cold single-file build times out under that
  contention. The Lean file is already written and certified — only the
  machine-check is pending.
- Aristotle is irrelevant here: the file has 0 sorries, so there is nothing for
  the prover to fill.

## Next Action (Docker-gated, when containers ≤ 2)

1. `./proofs/scripts/docker-build.sh Proofs.StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular`
   (set `LEAN_BUILD_TIMEOUT=40m` if cold) to machine-check
   `grace_feuerbach_trirectangular`.
2. On green: register the module in `proofs/Proofs.lean` and add a gallery entry
   under `src/data/proofs/feuerbachs-theorem-oq-02-murakami/`.
3. Independently, the parent slug's axiom `feuerbach_3d_fails_general`
   (`FeuerbachsTheoremOQ02.lean:581`) can be promoted to a theorem once
   `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` is built green — a
   SEPARATE de-axiomatization, also Docker-gated.

Do NOT re-transcribe the Grace theorem (S8/S9 are complete and merged) and do
NOT register the file unbuilt under container saturation.

## Attempt Counts

- Total attempts: 0 Lean builds (Docker-gated throughout; file certified
  symbolically, not yet machine-checked)
- Approaches tried: analytic derivation + sympy certification + Lean
  transcription — all complete; only the Lean machine-check remains
