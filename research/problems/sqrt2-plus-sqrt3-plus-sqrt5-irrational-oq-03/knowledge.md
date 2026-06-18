# Knowledge Base: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-06-18 (Session 1) — Degree-8 annihilator proven (build-gated)

**Mode**: FRESH
**Outcome**: progress (goals (i)+(ii) complete & sympy-verified; (iii) open; Lean uncompiled — infra outage)

### What I Did
- Derived & symbolically verified (sympy/Gröbner) the radical-elimination identity for
  m(X)=X⁸-40X⁶+352X⁴-960X²+576: a 4-step polynomial tower over s²=2,t²=3,u²=5.
- Wrote `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03.lean`:
  `key` (abstract identity, staged `linear_combination` chain), `theta_root`,
  `aeval_theta`, `m`, `m_natDegree`, `m_monic`, `theta_isIntegral`, `theta_finrank_le`.
- Every `ring`/`linear_combination` cofactor confirmed exact in sympy (h1=[1,1,1],
  h2=[t²+u²,u²+2,5], h3=[t²u²,2u²,6], hA/hB/hC/final OK).

### Key Findings
- m(a) = ((a²-10)²-124)² - 1920a² as a ring identity (a=θ); coefficients come from
  ((b-10)²-124)² = b⁴-40b³+352b²+960b+576 minus 1920b (b=a²).
- Annihilator ⇒ [ℚ(θ):ℚ] ≤ 8 (minpoly.min + adjoin.finrank). Equality needs irreducibility.

### Files Modified
- proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03.lean (new, NOT registered, NOT built)
- src/data/research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-03.json (knowledge)

### Blocker
- Fleet-wide Docker outage (containerd content-store blob I/O error) + Aristotle 404 ⇒
  cannot compile/verify. Sister degree-4 file `Sqrt2PlusSqrt3IrrationalOQ03` is the template;
  used `compute_degree!`/`monicity!` and verified all Mathlib lemma names against the cache.

### Next Steps
- Build-verify when infra recovers; then prove irreducibility (field-tower route preferred),
  register in Proofs.lean, add gallery meta.json.
