# combinations-formula-oq-03-oq-03 — Rogers–Ramanujan via q-Gaussian binomials

**Status:** completed (verified / 0-axiom / original)
**PR:** (this session)
**Lean file:** `proofs/Proofs/CombinationsFormulaOQ03OQ03.lean` (222 lines, 7 theorems, 1 def)

## Open question (from parent combinations-formula-oq-03)
"Can the Rogers–Ramanujan identities ∑ q^{n²}/(q;q)_n = ∏ 1/((1-q^{5n+1})(1-q^{5n+4}))
be formalized in Lean 4 using this q-binomial library as a foundation?"

## What was done
The full *analytic* identity (formal power series / infinite products over ℤ[[q]]) is
out of scope for one session. Instead formalized its **finite polynomial core**, which is
the standard rigorous entry point (Schur 1917):

- **Definition** `schurSum q n = ∑_{j∈range(n+1)} q^{j²} · qBinom q (n-j) j` over any CommRing.
- **Main theorem** `schurSum_recurrence`: `S_{n+2} = S_{n+1} + q^{n+1}·S_n` (Schur's recurrence).
- **Corollary** `schurSum_at_one_eq_fib`: `S_n(1) = Nat.fib (n+1)`.
- **Corollary** `sum_choose_eq_fib`: `∑_j C(n-j,j) = fib(n+1)` (diagonal of Pascal = Fibonacci).
- Helper `qBinom_pascal'_all`: hypothesis-free second q-Pascal identity.

`#print axioms` → only propext / Classical.choice / Quot.sound. No sorryAx, no ofReduceBool.

## Proof mechanism (for any follow-up)
Everything reduces to the parent's **second q-Pascal identity**
`[n+1 choose k+1]_q = q^{n-k}·[n choose k]_q + [n choose k+1]_q`:
1. Upgrade it to the unconditional `qBinom_pascal'_all` (both sides vanish when a<k) so it
   can be applied termwise inside a `Finset` sum without a side condition.
2. Expand `S_{n+2}` over `range (n+3)`, peel j=0 (=1) via `sum_range_succ'` and j=n+2 (=0,
   since `[0 choose n+2]_q=0`) via `sum_range_succ`.
3. Apply the Pascal split to each term; `Finset.sum_add_distrib` separates two sums.
4. One sum = `S_{n+1}` (via `schurSum_succ_peel`). The other = `q^{n+1}·S_n` via the exponent
   identity `(i+1)² + (n-i) - i = i² + (n+1)`, which holds when `2i ≤ n`; in the complement
   `[n-i choose i]_q = 0` so the term drops (case split `le_or_gt i (n-i)`).

## Lean gotchas hit
- Truncated ℕ subtraction: the exponent identity only holds in the active range; rely on the
  q-binomial being 0 elsewhere rather than fighting `omega` over `(n-i)-i`.
- `omega` can't prove `(i+1)²+...` directly (nonlinear); supply `have hsq : (i+1)^2 = i^2+2*i+1 := by ring`
  first, then `omega` treats the squares as linked atoms.
- `Nat.fib_add_two` rewrite is occurrence-ambiguous; instead state the exact equation with the
  desired (defeq) argument form: `have h : fib (n+2+1) = fib (n+1) + fib (n+1+1) := Nat.fib_add_two (n := n+1)`.
- `lake env lean -o .lake/build/lib/lean/Proofs/<File>.olean <File>.lean` is the working build
  route when Docker is down (parent olean must be built to `lib/lean/Proofs/` first, NOT `lib/Proofs/`).

## Natural follow-ups (not done)
- Companion Schur sum `∑_j q^{j²+j} · [n-j choose j]_q` (second Rogers–Ramanujan polynomial),
  same recurrence, base values shifted → second identity.
- Formal ℤ[[q]] limit connecting `S_n` to the series side `∑ q^{j²}/(q;q)_j`.
