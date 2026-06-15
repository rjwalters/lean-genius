# Current State

**Phase**: DECOMPOSE (math COMPLETE; only Docker-gated Lean transcription remains)
**Since**: 2026-06-14T21:00:00.000Z
**Iteration**: 8

## Current Focus

The mathematics is finished. S4 (T0 closed form) and S7 (general trirectangular
family) are DONE and have now been INDEPENDENTLY re-verified this session
(S8-prep) by a committed, reproducible sympy script
`verify_grace_trirectangular.py` (16/16 identities OK, symbolic + numeric; the
insphere/exsphere radii are re-derived from first principles, not just checked).
The only remaining step is S8: transcribe the closed form into Lean, which is
Docker-gated (verification blackout, `docker ps` hangs).

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

- S8 (Lean transcription) is Docker-gated; cannot `lake build` during the
  verification blackout. All upstream math is build-free and now reproducibly
  verified.

## Next Action (S8, Docker-gated)

Transcribe into a NEW sibling `proofs/Proofs/FeuerbachsTheoremOQ02Murakami.lean`
reusing the parent file's `Point3 = R x R x R` / `dist3_sq` framework. State the
result over R with the surd carried as a hypothesis `q >= 0`, `q^2 = a^2*b^2 +
b^2*c^2 + c^2*a^2`; all tangency identities reduce to `field_simp; ring` /
`nlinarith` once cleared of denominators. The exact target identities are the
ones listed above (and machine-checked by `verify_grace_trirectangular.py`), so
the transcription is mechanical when Docker returns.

## Attempt Counts

- Total attempts: 0 (no Lean built yet -- Docker-gated throughout)
- Current approach attempts: 0
- Approaches tried: 0 (analytic derivation complete and verified)
