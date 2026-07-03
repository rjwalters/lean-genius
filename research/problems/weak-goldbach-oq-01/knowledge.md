# Knowledge Base: weak-goldbach-oq-01

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

## Session 2026-07-03 (researcher-4) — Axiom audit (SURVEY): all 5 axioms irreducible

**Mode**: SURVEY (axiom-elimination assessment) · **Outcome**: no quick win; opportunity flagged

`proofs/Proofs/WeakGoldbach.lean` is a **mature, legitimately-axiomatized** file
(30 theorems, 14 defs, 0 sorry, 5 axioms). Per the axiom-elimination priority I
classified each axiom against current Mathlib (v4.26.0):

| Axiom | Nature | Provable from Mathlib now? |
|-------|--------|-----------------------------|
| `helfgott_weak_goldbach` | Ternary Goldbach (Helfgott 2013) | No — analytic proof far beyond formalization |
| `circle_method_asymptotic` | Hardy–Littlewood r₃(n) asymptotic | No — deep analytic number theory |
| `schnirelmann_basis_theorem` | σ(A)>0 ⟹ A an additive basis | **No — explicit Mathlib TODO** (`Mathlib/Combinatorics/Schnirelmann.lean` line ~40: "Prove Schnirelmann's theorem and Mann's theorem") |
| `chen_theorem` | n = p + P₂ for large even n | No — heavy sieve estimates |
| `binary_goldbach_verified` | binary Goldbach for n ≤ 4·10¹⁸ | No — range is uncomputable in Lean's kernel; a `decide`-verified `n ≤ 30` companion already exists |

**Conclusion.** None of the 5 axioms is a routine Mathlib lemma; the binary
Goldbach conjecture itself is open and must stay axiomatized. Adding further
theorems on top of these axioms would be scaffolding, not real progress, so I made
no code change this session.

**The one tractable-in-principle target: `schnirelmann_basis_theorem`.** Schnirelmann's
theorem is *elementary* (no analysis): σ(A)>0 ⟹ A⊕A has density ≥ min(1, 2σ(A)−σ(A)²),
iterate to reach density 1, then a full-density set is an additive basis of bounded
order. Mathlib has the density definition and basic API (`schnirelmannDensity`,
`schnirelmannDensity_setOf_prime = 0`, etc.) but **not** the theorem itself. Formalizing
it (~300–500 lines: the sumset density inequality + the iteration) would discharge one
axiom here *and* fill a flagged Mathlib gap — a worthwhile dedicated future session, too
large to start with the budget remaining this session.

Aristotle MCP down all session (`Resource not found`/404).
