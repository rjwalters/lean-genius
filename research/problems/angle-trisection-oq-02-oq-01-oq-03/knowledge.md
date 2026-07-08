# Knowledge: angle-trisection-oq-02-oq-01-oq-03 — p-group Galois ⟹ degree = p^k

## Session 2026-07-08 (researcher-1): two-prime-factor obstruction (depth-3, no new OQ)

File was already complete (10 thm, 0 axiom, 0 sorry). Depth 3 ⟹ no OQ children.
Added a theory-level strengthening on the same file:

- `no_pgroup_of_two_prime_factors`: two distinct prime divisors q₁≠q₂ of natDegree ⟹
  Gal is not a p-group for ANY prime p. Proof: case on q₁ = p; whichever branch,
  a prime ≠ p divides the degree ⟹ master criterion `not_pgroup_of_prime_dvd_degree_ne`.
- `degree_six_no_pgroup`: degree 6 = 2·3 ⟹ no p-group Galois for any prime (concrete).

This is qualitatively stronger than the prior single-prime obstructions (which each
rule out one fixed p): a p-group forces degree = p^k (a single prime factor), so a
degree with ≥2 distinct prime factors is ruled out for *every* prime simultaneously.

Docker VERIFIED (needed `--repair-cache` — persistent line-less exit-135 SIGBUS on the
target survived two plain retries; cache force-refresh cleared it, real build = 6.3s).
12 thm, 0 axiom, 0 sorry. #print axioms unchanged (propext/Classical.choice/Quot.sound).

Remaining OPEN (unchanged): converse gap (degree = p^k does NOT force a p-group,
e.g. S₄ quartic deg 4=2² |Gal|=24) needs a concrete Galois-group computation;
blocked infra for the concrete cos 20° corollary (v4.26 AlgHom drift in a ~740-line dep).
