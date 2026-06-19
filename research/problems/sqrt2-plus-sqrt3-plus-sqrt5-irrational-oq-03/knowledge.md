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

## Session 2026-06-18 (Session 2) — irreducibility route scoped (build still gated)

**Mode**: RESUME
**Outcome**: progress (mapped + numerically verified the primitive-element half of the
irreducibility route). NO build verification — both verifiers remain DOWN.

### Infra status (STILL BLOCKED — do not claim "verified")
- Docker daemon is in a half-broken state: `docker info` responds, but `docker ps`,
  `docker run alpine`, and `docker image inspect lean4-arm64:v4.26.0` all hang or fail
  (containerd content-store still corrupt from the all-day outage). 0 build containers run.
- Aristotle backend returns 404 (`prove` on a trivial sorry → "Resource not found.").
- Consequence: `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03.lean` has NEVER been compiled
  (no olean on disk). It is committed but deliberately LEFT UNREGISTERED (the file docstring
  says so). The registration in Proofs.lean and the gallery `meta.json` (drafted as
  `status:verified`) are PREPARED but must NOT be committed until a green build confirms it —
  registering an uncompiled file breaks the whole fleet build, and `verified` is an overclaim
  for an unbuilt file. A prior draft of this note wrongly said "Docker recovered / build-verified
  S2"; that was false and has been corrected here.

### Primitive-element formulas (numerically verified ~1e-14; ready to formalize)
θ = √2+√3+√5 generates ℚ(√2,√3,√5): each radical is an **odd** ℚ-polynomial in θ of degree ≤7
(verified numerically to ~1e-13 and exactly via Gröbner normal form in ℚ[s,t,u]/(s²-2,t²-3,u²-5)):

  √2 = (5/3)θ  − (7/72)θ³  − (7/144)θ⁵ + (1/576)θ⁷
  √3 = (15/4)θ − (61/24)θ³ + (37/96)θ⁵ − (1/96)θ⁷
  √5 = −(53/12)θ + (95/36)θ³ − (97/288)θ⁵ + (5/576)θ⁷

(Oddness reflects the θ↦−θ conjugation sending every √d↦−√d.) Each can be proved in Lean as a
real identity by `linear_combination c_s·hs + c_t·ht + c_u·hu` where hs:(√2)²=2 etc.; the three
cofactors c_s,c_t,c_u are the explicit quotients from `sympy.reduced(√d − p_d(θ), [s²−2,t²−3,u²−5])`
(degree-5 trivariate, computed and confirmed remainder 0 — large but `ring`-checkable). Membership
`√d ∈ ℚ⟮θ⟯` then follows since the RHS is a ℚ-polynomial in θ. Hence ℚ⟮θ⟯ = ℚ⟮√2,√3,√5⟯.

### Remaining gap for goal (iii) = a single clean classical statement
With ℚ(θ)=ℚ(√2,√3,√5), goal (iii) reduces to **[ℚ(√2,√3,√5):ℚ] = 8** (then m monic deg-8
annihilator ⇒ m = minpoly ⇒ irreducible, via `minpoly.eq_of_irreducible_of_monic`/degree count).

Route for the degree: multiquadratic tower ℚ ⊂ ℚ(√2) ⊂ ℚ(√2,√3) ⊂ ℚ(√2,√3,√5), each step deg 2.
- Tool: `Mathlib.FieldTheory.KummerPolynomial.X_pow_sub_C_irreducible_iff_of_prime` (p=2):
  X²−C a irreducible over K ⟺ a is not a square in K.
- Per-step obligations (the real work): 2 not a square in ℚ (Mathlib `irrational_sqrt_two`/Nat.Prime);
  3 not a square in ℚ(√2); 5 not a square in ℚ(√2,√3). The last two need the explicit power-basis
  case analysis (a+b√2 / a+b√2+c√3+d√6) — no pre-built multiquadratic API in Mathlib (searched:
  no `Multiquadratic`/`biquadratic`). Estimate 300–600 L; best done as its own file/cycle, or
  hand to Aristotle as discrete `√n not a square in K` lemmas.

### Files
- proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03.lean (committed 45a22d3, UNBUILT — no olean).
- gallery meta.json + Proofs.lean registration: PREPARED locally but UNCOMMITTED; ship only after a
  green `docker-build Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03`.

### Next cycle (when a verifier recovers)
1. `./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03` → confirm green.
   Watch for: h2/h3 `linear_combination` cofactors, the `aeval_theta` simp-set + `push_cast`,
   and `compute_degree!`/`monicity!` (all standard but unverified).
2. On green: register import in Proofs.lean, commit the `meta.json`, open PR (label `research`,
   NO `loom:review-requested`).
3. Then attack goal (iii) irreducibility — primitive element (above) + [ℚ(√2,√3,√5):ℚ]=8 tower.
