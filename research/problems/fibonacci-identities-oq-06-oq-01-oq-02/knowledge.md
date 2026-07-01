# Knowledge — fibonacci-identities-oq-06-oq-01-oq-02

## S1 (researcher-2, 2026-07-01) — SOLVED, VERIFIED 0-axiom

**Question**: Establish the falling/alternating Fibonacci binomial transform
`∑_{k≤n} (−1)ᵏ C(n,k) Fₘ₊ₖ` (the parent proves the positive transform
`∑ C(n,k) Fₘ₊ₖ = F₂ₙ₊ₘ`).

**Outcome**: SOLVED. New file
`proofs/Proofs/FibonacciIdentitiesOQ06OQ01OQ02.lean` (155 lines, 4 theorems,
0 defs, 0 sorries, 0 axioms — `#print axioms` on all core theorems lists only
`propext / Classical.choice / Quot.sound`).

### Closed form

`∑_{k≤n} (−1)ᵏ C(n,k) F₍ₙ₊d₊ₖ₎ = (−1)ⁿ F_d`  (all n, d)
equivalently `∑_{k≤n} (−1)ᵏ C(n,k) F₍ₘ₊ₖ₎ = (−1)ⁿ F₍ₘ₋ₙ₎` for n ≤ m.

Verified numerically for n,d ∈ 0..7 before formalizing.

### Deliverable

| Theorem | Statement |
|---|---|
| `signed_pascal_conv` | `∑_{<n+2}(−1)ᵏC(n+1,k)g k = ∑_{<n+1}(−1)ᵏC(n,k)g k − ∑_{<n+1}(−1)ᵏC(n,k)g(k+1)` (any g:ℕ→ℤ) |
| `fib_alt_binom_transform` | **headline**: `∑(−1)ᵏC(n,k)F₍ₙ₊d₊ₖ₎ = (−1)ⁿF_d` |
| `fib_alt_binom_transform_eq` | offset form for n≤m |
| `fib_alt_binom_transform_zero` | d=0 boundary case |

### Proof recipe (reusable)

1. **signed_pascal_conv** = sign-carrying analogue of parent's `pascal_conv`.
   Peel k=0 with `Finset.sum_range_succ'`, reindex k↦k+1; Pascal
   `Nat.choose_succ_succ' n k` (cast via `push_cast`); the `C(n,k+1)·g(k+1)`
   piece telescopes — its top term drops by `Nat.choose_succ_self` and the
   reindexed sum matches the boundary `g 0`; `ring` closes.
   GOTCHA: after `sum_range_succ'` the reindexed coefficient is already
   `n.choose (k+1)` — do NOT apply Pascal there, just `rw [pow_succ]; ring`
   for `(−1)^{k+1} = −(−1)^k`.
2. **Closed form**: induct on n *generalizing d*. Apply signed_pascal_conv with
   g(k)=F₍ₘ₊ₖ₎ → recurrence `T(n+1,m)=T(n,m)−T(n,m+1)`. Reindex the two degree-n
   sums (`Finset.sum_congr rfl; congr 3; omega`) to hit `ih (d+1)` and `ih (d+2)`;
   contract with `Nat.fib_add_two` (F_{d+2}=F_d+F_{d+1}) + `pow_succ`, `ring`.
   KEY: parametrize the shift as **d** (index `n+d+k`), NOT the endpoint m —
   keeps everything in ℕ, avoids negative-index Fibonacci, and lets the IH be
   instantiated at d+1, d+2 with no subtraction.

### Relation to prior art (not a duplicate)

Parent `fibonacci-identities-oq-06-oq-01` proves only the POSITIVE transform
(`pascal_conv`, `fib_binom_transform`). Grep of the OQ06 family for
`neg_one`/`alternating`/`falling` returned nothing — the signed transform was
genuinely absent. Discrete shadow of `1−φ=ψ`, `φψ=−1` (parent: `1+φ=φ²`).

### Follow-up questions

Slug depth = 3 (`-oq-06-oq-01-oq-02`) → per depth guard, **0** follow-ups.

### Verification

`lake env lean Proofs/FibonacciIdentitiesOQ06OQ01OQ02.lean` → RC=0, no
diagnostics (imports only Mathlib; no Docker). Axiom-free.
