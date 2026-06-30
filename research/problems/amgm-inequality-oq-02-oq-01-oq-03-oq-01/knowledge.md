# Knowledge Base: amgm-inequality-oq-02-oq-01-oq-03-oq-01

Newton–Girard k=4 reduced closed form  p₄ = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄.

---

## Problem Understanding

The explicit next rung after the k=3 closed form. Express the fourth power sum purely in
the elementary symmetric polynomials e₁..e₄, both universally (MvPolynomial) and concretely
over a Finset of values in an arbitrary CommRing (char 2 included).

---

## Insights

- **k=4 recurrence is mechanical.** `psum_eq_mul_esymm_sub_sum` at n=4 has antidiagonal
  filter {(1,3),(2,2),(3,1)} and lead term (−1)⁵·4·e₄ = −4e₄, giving
  p₄ = e₁p₃ − e₂p₂ + e₃p₁ − 4e₄. Same recipe as k=2/k=3 (ext + omega, sum_insert/sum_singleton,
  ring).
- **The closed form is one `ring` step from the recurrence** once p₃, p₂, p₁ closed forms
  are substituted. The 2·e₂² cross term is the first genuinely quartic feature (absent k≤3).
- **The k=3 aeval bridge is degree-general.** `aeval_psum_subtype` / `aeval_esymm_subtype`
  are stated for arbitrary n, so the concrete k=4 form needs only
  `e4_bridge := aeval_esymm_subtype s f 4` and `p4_bridge := aeval_psum_subtype s f 4`.
  This answers, by example, the k=3 entry's own open question about degree-generalizing the
  bridge.
- **No char-2 obstruction at k=4.** The closed form is read off the universal statement via
  aeval transport (coefficient level, before evaluation), so no factor of 2 is cancelled —
  unlike the direct k=3 ordered-triple partition (which only reached 2·p₃ = 2·closed).

## Built Items

- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03OQ01.lean` — 6 thm / 2 def / 0 sorry / 0 axiom,
  Docker-verified GREEN (v4.26.0). #print axioms: [propext, Classical.choice, Quot.sound].
- Registered in `proofs/Proofs.lean`.
- Gallery entry `src/data/proofs/amgm-inequality-oq-02-oq-01-oq-03-oq-01/meta.json`.
- `lean/verify_newton_girard_k4.py` — durable cert (residual 0, n=2..6 + substitution chain
  + explicit instance).

## Mathlib Gaps

- Mathlib has only the general Newton recurrence; reduced per-degree closed forms (k≥3) and
  their concrete Finset incarnations are absent.
- No packaged degree-uniform transport lemma; per-degree bridge wrappers are instantiated.

## Next Steps

1. Package a degree-uniform transport to eliminate per-degree wrappers.
2. Continue to k=5: p₅ = e₁⁵ − 5e₁³e₂ + 5e₁e₂² + 5e₁²e₃ − 5e₂e₃ − 5e₁e₄ + 5e₅.
3. Consider upstreaming the reduced closed forms / degree-general transport to Mathlib.

---

## Session 2026-06-20 (Session 1) — ACT (SOLVED)

**Mode**: FRESH (follow-up after parent k=3 found already solved+merged) · **Outcome**: completed

### What I Did
- Confirmed the parent k=3 OQ (amgm-inequality-oq-02-oq-01-oq-03) is solved + merged
  (PR #27174), then generated and proved the k=4 closed form as the natural next rung.
- Shipped `AmgmInequalityOQ02OQ01OQ03OQ01.lean`: universal recurrence + closed form,
  concrete general-Finset form via the reused (degree-general) aeval bridge, explicit
  4-variable instance. 0 sorries / 0 axioms, Docker-verified GREEN.
- Wrote durable Python cert and gallery entry; registered in Proofs.lean.

### Key Findings
- The k=3 aeval bridge is degree-general — concrete k=4 costs two one-line bridge instances.
- No char-2 obstruction at k=4 (aeval transport bypasses any doubled factor).
