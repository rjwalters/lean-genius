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
