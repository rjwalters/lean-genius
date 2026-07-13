# Knowledge Base: fermat-two-squares-oq-04-oq-01

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

## Session 2026-07-02 (Session 2) — Geometric side r₂ + positivity bridge

**Mode**: FRESH
**Outcome**: progress (verified sub-result shipped; full problem still open)

### What I Did
- Defined r₂(n) = #{(a,b)∈ℤ² : a²+b²=n} as an honest `Finset.card` over the σ-invariant box [-n,n]² (finiteness packaged into the definition).
- Proved `mem_sols` (box constraint automatic), `r2_pos_iff_exists_int`, `exists_int_iff_exists_nat`.
- Headline bridge `r2_pos_iff_jacobiSum_pos`: 0 < r₂(n) ⇔ 0 < δ(n), reusing the parent's `jacobiSum_pos_iff_sq_add_sq`.
- `r2_eq_zero_iff_jacobiSum_eq_zero` and geometric Fermat criterion `r2_prime_pos_iff` (0<r₂(p) ⇔ p≢3 mod 4).
- New gallery entry + PR #33832.

### Key Findings
- Positivity is the tractable common denominator of both sides — no counting needed for the qualitative Jacobi.
- Full r₂=4δ needs: 4∣r₂ (free rotation/unit action), prime-power counts (Gaussian splitting), multiplicativity (norm transport). All deferred.

### Verification
- Docker DEAD (containerd blob I/O error). Host `lake env lean` works: built parent olean with `-o`, type-checked file, `#print axioms` = {propext, Choice, Quot} only → 0-axiom verified.

### Files Modified
- proofs/Proofs/FermatTwoSquaresOQ04OQ01.lean (new)
- src/data/proofs/fermat-two-squares-oq-04-oq-01/{meta,annotations}.json (new)

### Next Steps
- Prove 4 ∣ r₂(n) via free order-4 rotation action (submitted to Aristotle).
- Prime-power counts + multiplicativity to close r₂ = 4δ.
