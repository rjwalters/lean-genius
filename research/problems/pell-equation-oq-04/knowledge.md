# pell-equation-oq-04 — General norm form x² − Dy² = N

## Summary
Parent open question: implications of generalizing Pell to x² − Dy² = N for arbitrary N.
Shipped a fully verified (0-axiom, no native_decide) structural skeleton.

## Session 2026-06-23 (Session 1) — FRESH — Outcome: completed

### What I Did
- Defined normForm D x y = x² − Dy² and composition comp (multiplication in ℤ[√D]).
- Proved normForm_mul: the Brahmagupta–Fibonacci identity (norm form multiplicative) — pure `ring`.
- sol_comp: composition of an M-solution and an N-solution gives an MN-solution.
- Built a CommGroup instance on PellUnit D = {p // normForm D p.1 p.2 = 1} (the Pell group):
  identity (1,0), inverse the conjugate (x,−y), assoc/comm by ring.
- unit_smul_sol: the Pell group acts on the N-solutions (N·1 = N).
- infinite_solutions: one positive seed + one nontrivial unit ⟹ {solutions}.Infinite, via
  orbit (seed·unitᵏ): orbit_sol (norm preserved), orbit_pos, orbit_fst_strictMono (u≥2 ⇒ first
  coord at least doubles ⇒ StrictMono ⇒ injective), Set.infinite_of_injective_forall_mem.
- sol_neg_one_comp: two x²−Dy²=−1 solutions compose to x²−Dy²=1 (negative-Pell bridge).
- Worked instance: x²−2y²=7 has infinitely many solutions (seed (3,1), unit (3,2), (3,1)·(3,2)=(13,9)).

### Key Findings
- The whole theory reduces to one polynomial identity (cross terms 2Dxyuv cancel).
- A nontrivial unit forces u ≥ 2 since u² = 1 + Dv² ≥ 2 — the growth driver for infinitude.
- Clean dichotomy: x²−Dy²=N has no solutions or infinitely many (whenever a unit exists).

### Files
- proofs/Proofs/PellEquationOQ04.lean (251 lines, 17 thm, 4 def, 1 CommGroup instance, 0 sorry/axiom)
- src/data/proofs/pell-equation-oq-04/{meta.json,annotations.json}

### Next Steps (follow-ups, not done)
- Orbit classification / class number for given N (genus theory of binary quadratic forms).
- Effective bound on the smallest solution of x²−Dy²=N and a solvability decision procedure.

### Build note
Docker down, no oleans in worktree. Compiled single-file against a sibling worktree's Mathlib
oleans (eulerian-frobenius) with the exact elan toolchain lean v4.26.0 (homebrew lean header
mismatch). #print axioms: only propext/Quot.sound/Classical.choice — genuinely 0-axiom.
