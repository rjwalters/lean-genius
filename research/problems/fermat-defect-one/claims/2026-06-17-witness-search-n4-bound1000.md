# Claim — No defect-one witness at n = 4 with c ≤ 1000

- **Vector attempted**: witness-search
- **Date**: 2026-06-17
- **Author**: Loom builder (issue #22635)
- **Status**: failed (no witness found) — negative result, fully decisive over the searched range

## What was tried

A complete bounded search for a defect-one witness at exponent $n = 4$, looking
for any integer triple $(a, b, c)$ with

$$2 \le a \le b < c \le 1000, \qquad |a^4 + b^4 - c^4| = 1.$$

In the `Nat`-disjunction form used by `FermatDefectWitness 4 a b c` in
`proofs/Proofs/FermatDefectOne.lean`, this is

- negative defect: $a^4 + b^4 + 1 = c^4$ (i.e. $a^4 + b^4 - c^4 = -1$), or
- positive defect: $a^4 + b^4 = c^4 + 1$ (i.e. $a^4 + b^4 - c^4 = +1$).

The search was run **programmatically in Python** over the **full range
$c \le 1000$** with two independent methods (script:
`claims/scripts/witness_search_n4_bound1000.py`):

1. **Fast (hashed)** — precompute the fourth powers $b^4$ for $2 \le b \le 1000$
   into a value→$b$ map, then for each $(a, c)$ with $2 \le a < c \le 1000$ solve
   directly for the candidate $b$ from $b^4 = c^4 - a^4 - 1$ (negative) and
   $b^4 = c^4 + 1 - a^4$ (positive), checking the ordering $a \le b < c$. This
   iterates **498 501** $(a, c)$ pairs.
2. **Brute force (triple loop)** — independent triple-nested loop over
   $2 \le a \le b < c \le 1000$ evaluating the defect directly, with **no** hash
   trick, as a cross-check against method 1.

Both methods finished in well under a second and were asserted to agree.

**Modular pre-filter (for completeness).** Fourth-power residues mod
$p \in \{3, 5, 7, 13\}$ and mod $16$ were computed; for every one of these
moduli **both** signs of the congruence $a^4 + b^4 \pm 1 \equiv c^4$ are
solvable. So no small modulus prunes the search — consistent with the
`modular-obstruction` claim (#22636), which showed the unit residue witnesses
$(0,0,1)$ / $(1,0,0)$ make a single-prime congruence obstruction impossible at
any exponent. The pre-filter here therefore does not shrink the space; the full
exhaustive integer search above is what establishes the result.

## What happened

**No witness exists in the searched range — not even a non-primitive one.**

- Witnesses with $|a^4 + b^4 - c^4| = 1$, any $\gcd$, $c \le 1000$: **0**.
- Primitive witnesses ($\gcd(\gcd(a,b),c) = 1$): **0** (vacuously).
- The fast and brute-force methods returned identical (empty) result sets.

This is a clean **lower bound on the minimal-witness function**: if $M(4)$
(the smallest $c$ admitting a primitive nontrivial defect-one witness at
$n = 4$) is finite, then

$$M(4) \ge 1001.$$

It strictly extends the Aristotle companion target `no_witness_n_eq_4_below_20`
(which would give $M(4) \ge 21$) by a factor of $50$ in $c$.

No verified Lean witness theorem was added (there is nothing to formalize — no
witness was found). The headline `fermat_defect_one_exists` for $n \ge 4$ stays
open and untouched.

## What this suggests for next iteration

- **Do not re-run a small-$c$ $n=4$ integer witness search.** $c \le 1000$ is
  now ruled out exhaustively. A future witness-search attempt should start at
  $c > 1000$ (and will need a smarter / sieved enumeration, since the cost grows
  like $N^2$ even with the hashed method — already $\sim 5\times10^5$ pairs at
  $N = 1000$).
- The absence of any witness, combined with the *non*-existence of a congruence
  obstruction (#22636), points to a **global / archimedean (size-based)**
  obstruction rather than a local one: $|a^4 + b^4 - c^4|$ grows fast and the
  $\pm 1$ band becomes increasingly hard to hit as $c$ grows. The `reduction`
  vector (Fermat–Catalan / Mason–Stothers finiteness, #22638) is the more
  promising route to a definitive statement at $n = 4$, since pure search can
  only ever push the lower bound on $M(4)$ outward, never settle existence.
- If continuing the search vector, consider a Thue/$abc$-guided bound on how
  large $c$ could plausibly be before either fixing an exponent-specific
  finiteness argument or escalating the bound substantially (e.g. $c \le 10^5$
  with a sieved residue enumeration).
