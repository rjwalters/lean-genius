# Knowledge Base: centered-hexagonal-sum-oq-01-oq-01

Uniform closed form for centered-polygonal partial sums.

---

## Problem Understanding

Parent `centered-hexagonal-sum-oq-01` (`Proofs/CenteredHexagonalSum.lean`, verified)
proves `∑_{i=1}^{n} C_{6,i} = n³` for centered hexagonal numbers `C_{6,n}=3n(n−1)+1`.
Its OQ: do analogous centered k-gonal partial sums have equally clean closed forms, and
which reindexing keeps each inside ℕ?

---

## Session 2026-06-27 (researcher-9) — SOLVED the OQ [VERIFIED, 0-axiom]

**Outcome**: BUILD + new gallery entry. A single uniform closed form answers the OQ for
all k at once.

### The mathematics
Centered k-gonal number `C_{k,n} = k·n(n−1)/2 + 1`. Partial sum
`∑_{i=1}^{n} C_{k,i} = k·n(n²−1)/6 + n`. Cleared of division and ℕ-subtraction:

  **6·∑_{i=1}^{n} C_{k,i} = k·n³ + (6−k)·n.**

k=6 ⇒ coefficient (6−k)=0 ⇒ 6·∑ = 6n³ ⇒ ∑ = n³ (recovers parent). Hexagonal is the
UNIQUE centered-polygonal family whose partial sums are a pure power.

### Built `Proofs/CenteredHexagonalSumOQ01OQ01.lean` (96 LOC, 1 def + 4 theorems)
- `cgon k n := k*(n*(n-1))/2 + 1`.
- `cgon_six (n) : cgon 6 n = 3*(n*(n-1))+1` (= parent's centeredHex). Proof: `unfold; omega`
  (omega clears `6*Y/2` for atom Y=n*(n-1)).
- `six_mul_cgon_succ (k n) : 6 * cgon k (n+1) = 3*(k*(n*(n+1))) + 6`. The /2-elimination:
  `hdvd : 2 ∣ k*(n*(n+1))` from `(even_iff_two_dvd.mp (Nat.even_mul_succ_self n)).mul_left k`,
  then `rw [hcgon]; omega` (omega uses hdvd to discharge the division by literal 2).
- `six_mul_sum_cgon (k n) : 6 * (∑ i ∈ range n, (cgon k (i+1):ℤ)) = k*n³ + (6−k)*n`.
  Over ℤ so the single coeff (6−k) carries all families. Induction: `rw [sum_range_succ,
  mul_add, ih]; rw [hC]; push_cast; ring` where `hC := exact_mod_cast six_mul_cgon_succ`.
- `sum_centeredHex_cube (n) : ∑ i ∈ range n, cgon 6 (i+1) = n^3`. k=6 corollary: from
  six_mul_sum_cgon, `(6−6)=0`, `6*∑ℤ = 6*n³`, `linarith` ⇒ ∑ℤ=n³, `exact_mod_cast`.

### Verification
`lake env lean` (worktree proofs dir): EXIT 0, no warnings. `#print axioms` on all four
theorems = `[propext, Classical.choice, Quot.sound]` (cgon_six: only propext, Quot.sound) —
0 counting-axioms. Gallery `meta.json` + `annotations.json` created (verified, original,
axiomCount 0), JSON validated.

### GOTCHAs
- Build in the **worktree** proofs dir, NOT main (concurrent agents clobber).
- `omega` clears division by a literal (`X/2`) when a `2 ∣ X` fact is in context and the
  numerator is treated as a single atom — used to kill the centered-polygonal `/2` without
  manual `Nat.div_mul_cancel` plumbing.
- Keep the closed form division-free by stating it scaled (`6·∑ = …`) and ADDING `(6−k)·n`
  rather than subtracting — answers the OQ's "stay inside ℕ" directly.

### Files
- `proofs/Proofs/CenteredHexagonalSumOQ01OQ01.lean` (new, verified 0-axiom)
- `src/data/proofs/centered-hexagonal-sum-oq-01-oq-01/{meta.json,annotations.json}` (new)

### Next Steps
- Power sums `∑ C_{k,i}²` uniform in k.
- Partial sums of ordinary (non-centered) k-gonal numbers and their pure-power value of k.
