# bezout-identity-oq-02-oq-01-oq-03 — Constructive Bézout coefficients via extGcd uniqueness

## Session 2026-06-28 (researcher-2): §VI general (non-coprime) classification

The file was already VERIFIED (0-axiom) for the COPRIME case: existence (bezout_identity),
homogeneous solutions (coprime_homogeneous), uniqueness (coprime_bezout_unique),
parametrization (coprime_bezout_param), extGcd specialization (gcdA_gcdB_unique). But the
file docstring claims the FULL classification — the solution set of a·x+b·y=c is one coset
of ℤ·(b/g,−a/g) — which was only proved at g=1. This session completes it.

### New §VI (verified, 0-axiom; docker-build clean, foundational axioms only)
Parametrize by the reduced pair: a=g·a', b=g·b' with a',b' coprime (a'=a/g, b'=b/g), g≠0.
Each general theorem reduces to its coprime counterpart by cancelling the nonzero g.
- **general_homogeneous**: every solution of a·u+b·v=0 is k·(b/g,−a/g). Proof:
  g·(a'·u+b'·v)=0 ⇒ (g≠0) a'·u+b'·v=0 ⇒ coprime_homogeneous.
- **general_bezout_unique**: two solutions of a·x+b·y=c differ by one lattice step k·(b/g,−a/g).
- **general_bezout_param**: converse (every lattice step is a solution; pure ring).
- **general_solvable**: g∣c ⇒ a·x+b·y=c solvable, witness (c'·s,c'·t) from a coprime Bézout
  pair a'·s+b'·t=1 (obtained by destructuring IsCoprime a' b'). linear_combination (g·c')·hst.
  Together with general_bezout_unique: solvable iff g∣c, solution set = one coset of
  ℤ·(b/g,−a/g). (Needs neither g≠0 nor b'≠0.)
- Worked non-coprime instance ex69_*: 6x+9y=3, g=3, lattice (3,−2).

GOTCHA: this problem JSON's leanFiles entries use keys `path`/`sorries`/`theoremCount`/
`definitionCount` (NOT filename/sorryCount). The reduced-pair formulation (abstract g with
a=g·a', b=g·b') avoids integer division entirely, keeping everything in ℤ and ring-friendly.

STATUS: COMPLETE. Depth-3 slug (oq-02-oq-01-oq-03) ⇒ no follow-up OQ children generated
(OQ-depth guard). The general classification fully realises the file's stated goal.
