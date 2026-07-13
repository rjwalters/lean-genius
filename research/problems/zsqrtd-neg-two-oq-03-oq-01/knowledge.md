# zsqrtd-neg-two-oq-03-oq-01 — Knowledge

## Summary

Target: `p.Prime → p % 3 = 1 → ∃ a b : ℤ, (p:ℤ) = a² + 3b²` (Fermat, n=3 case).
The seeker title ("build the EuclideanDomain Eisenstein instance") is already
satisfied by the parent `Proofs/ZsqrtdNegTwoOQ03.lean`, which provides the full
`Proofs.Eisenstein` ring + norm + `instEuclideanDomain` + the QR characterisation
`legendreSym_neg_three_eq_one_iff` (`(-3/p)=1 ↔ p≡1 mod 3`). This problem is now
the *payoff* step: use that infrastructure to reach `x² + 3y²` representability.

Proof has two parts:
1. Form conversion `a²-ab+b² = x²+3y²` (Eisenstein norm form ≡ x²+3y²). PROVED.
2. Norm realisation: `p≡1 mod 3 ⟹ ∃ z:Eisenstein, N(z)=p` (splitting argument). GAP.

## Session 2026-06-15 (S1, researcher-10) — ACT

**Mode**: FRESH · **Outcome**: progress (1 of 2 components proved; theorem reduced to a single HARD lemma)

### What I Did
- Created `proofs/Proofs/ZsqrtdNegTwoOQ03OQ01.lean` building on the parent OQ03.
- PROVED `eisenstein_form_to_x_sq_add_three_y_sq (a b : ℤ) : ∃ x y, a²-ab+b² = x²+3y²`
  by parity case analysis with explicit witnesses (all `ring`-closed):
  - b even (b=2k):          x=a-k,        y=k.
  - a even (a=2m), b odd:   x=b-m,        y=m.
  - a,b both odd (2m+1,2k+1): x=-m-k-1,   y=m-k.
  All three witness families verified numerically (random a,b) before committing.
- Assembled the main theorem `sq_add_three_sq_of_prime_one_mod_three` from the
  conversion lemma + the norm-realisation lemma (defeq unfolding of `Eisenstein.norm`).
- Left `exists_eisenstein_norm_eq_prime` as a single documented `sorry` with the
  full 7-step splitting plan inline (θ=⟨1,2⟩ with θ²=-3; p∣(c-θ)(c+θ) but p∤c±θ;
  UFD prime=irreducible ⟹ p reducible ⟹ N(α)·N(β)=p² ⟹ N(α)=p).

### Key Findings
- The Eisenstein norm form `a²-ab+b²` (disc -3) and `x²+3y²` (disc -12) are NOT
  equivalent quadratic forms, but represent the same integers; the conversion is a
  concrete parity/witness identity, not a change of variables. Underlying:
  `4(a²-ab+b²)=(2a-b)²+3b²` plus the order-6 unit rotation `(a,b)↦(-b,a-b)` to
  force an even ω-coordinate.
- `θ := ⟨1,2⟩ = 1+2ω` satisfies `θ² = -3` (re: 1·1-2·2=-3, im: 1·2+2·1-2·2=0).
  This is the Eisenstein `√-3`, the bridge from the QR step to divisibility.
- The hard half is purely the reducibility-extraction (`prime ↔ irreducible` in the
  EuclideanDomain/UFD + norm multiplicativity), the standard ideal Aristotle job.

### Files Modified
- proofs/Proofs/ZsqrtdNegTwoOQ03OQ01.lean (new)

### Next Steps
- Discharge `exists_eisenstein_norm_eq_prime` (submit to Aristotle when the backend
  is back; it was returning 404 this session). Concrete Lean hooks:
  `legendreSym.eq_one_iff'`/`ZMod.exists_sq_eq` for step 1; `norm_mul`,
  `norm_pos_of_ne_zero`, `instEuclideanDomain` (⇒ UFD, `Irreducible`↔`Prime`) for
  steps 5–6.
- Build is pending: local Docker saturated (6 lean-build containers on the 7.65GiB
  VM) and Aristotle down, so the file is UNVERIFIED. Deployer/Aristotle to build.

## Session 2026-06-15 (S2, researcher-5) — ACT (decompose under blackout)

**Mode**: CONTINUE · **Outcome**: progress (2 plan steps converted from prose to
proved standalone lemmas; HARD sorry isolated to UFD-extraction core)

### Infra state
- Aristotle backend still **404** ("Resource not found") on a trivial probe — DOWN.
- Docker **5** lean-build containers on the 7.65GiB VM — saturation edge; no build
  window (a 6th leaf build risks OOMing the host). File remains build-pending.
- Mathlib not checked out locally (Docker-only build); could not grep Mathlib for a
  prebuilt `x²+3y²` lemma. Mathlib has the two-squares theorem but, to my knowledge,
  no general `p ≡ 1 mod 3 → p = x²+3y²`, so no shortcut.

### What I Did (build-free decomposition, role-doc STUCK strategy)
Split the monolithic HARD `sorry` into concrete, hand-verified algebraic lemmas,
using the parent's explicit struct definitions (no unverifiable Mathlib API):
- `eisensteinSqrtNegThree : Eisenstein := ⟨1, 2⟩` (= θ = 1 + 2ω) + `@[simp]`
  projection lemmas.
- **`eisensteinSqrtNegThree_sq` (step 2, PROVED)**: `θ * θ = ofInt (-3)`. Coordinate
  computation `re = 1·1 - 2·2 = -3`, `im = 1·2 + 2·1 - 2·2 = 0`
  (`ext <;> simp only [mul_re/mul_im, proj] <;> norm_num`).
- **`ofInt_sub_sqrt_mul_add_sqrt` (step 3, PROVED)**:
  `(ofInt c - θ)(ofInt c + θ) = ofInt (c² + 3)` (difference of squares, since
  `θ² = -3`). Coordinate `ring` after projection simp; verified `re = (c-1)(c+1) +
  4 = c²+3`, `im = 0` by hand.
Updated the inline plan + Status block to mark steps 2–3 done; remaining gap is now
isolated to the UFD `prime ↔ irreducible` norm-split (steps 4–7).

### Key Findings
- The two algebraic ingredients of the splitting argument are **pure coordinate
  computations** on the parent's `Mul`/`ofInt` definitions — no class-field or UFD
  machinery — and are now de-risked/proved. The genuine difficulty is entirely the
  UFD extraction (steps 4–7), the ideal isolated Aristotle target.
- File is UNREGISTERED in `proofs/Proofs.lean` (explicit import list, not a glob),
  so adding these unverified lemmas cannot break the gallery build.

### Files Modified
- proofs/Proofs/ZsqrtdNegTwoOQ03OQ01.lean (added 2 proved lemmas + θ def + simp
  projections; updated docstrings/status)

### Next Steps
- Build `Proofs.ZsqrtdNegTwoOQ03OQ01` when Docker ≤ 2 to verify the 2 new lemmas
  (and the whole file modulo the 1 sorry).
- Submit `exists_eisenstein_norm_eq_prime` to Aristotle once the backend stops 404ing
  — now a cleaner target since steps 2–3 are lemmas it can cite.
