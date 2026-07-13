# Problem: Sharp gcd Bound for General Lucas Sequences — gcd(Uₙ, Vₙ) ∣ 2

**Slug**: lucas-sequence-degree2-identities-oq-02-oq-01
**Status**: Active
**Source**: proof-suggestion (open question from `lucas-sequence-degree2-identities-oq-02`)

## Problem Statement

### Formal Statement

For a general Lucas sequence pair with parameters $P, Q$ satisfying $\gcd(P, Q) = 1$, where
$U_n$ is the fundamental sequence ($U_0 = 0,\ U_1 = 1,\ U_{n+1} = P\,U_n - Q\,U_{n-1}$) and
$V_n$ the companion sequence ($V_0 = 2,\ V_1 = P,\ V_{n+1} = P\,V_n - Q\,V_{n-1}$), sharpen the
divisibility relation to the tight bound

$$
\gcd(U_n, V_n) \mid 2.
$$

Use that consecutive fundamental terms $U_n, U_{n+1}$ are coprime (from the identity `U_quad` /
$U_{n+1}^2 - P U_n U_{n+1} + Q U_n^2 = \pm 1$-type relation) together with the companion relation

$$
V_n = 2\,U_{n+1} - P\,U_n.
$$

### Plain Language

The parent entry established degree-2 identities for general Lucas sequences. This asks to prove the
*sharp* gcd bound: under $\gcd(P,Q)=1$, the fundamental and companion terms at the same index share
at most a factor of 2 — mirroring the classical $\gcd(F_n, L_n) \in \{1, 2\}$ for Fibonacci/Lucas.

### Why This Matters

The tight $\gcd \mid 2$ bound is the general-Lucas-sequence analogue of the well-known Fibonacci–Lucas
gcd fact, and is the key structural coprimality input for divisibility theory of Lucas sequences.

## Known Results

### What's Already Proven

- Degree-2 identities and $V_n = 2U_{n+1} - P U_n$ — parent `lucas-sequence-degree2-identities-oq-02`.
- Consecutive-term coprimality `gcd(U_n, U_{n+1}) = 1` (from the quadratic invariant `U_quad`).

### Our Goal

Prove $\gcd(U_n, V_n) \mid 2$ under $\gcd(P,Q) = 1$, 0 axioms, 0 sorries, reusing the parent's
identities as lemmas.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lucas-sequence-degree2-identities-oq-02 | Parent: degree-2 identities, $V_n=2U_{n+1}-PU_n$ | recurrence, addition law |
| fibonacci-divisibility-* | Fibonacci/Lucas gcd facts | `Nat.gcd`, divisibility |

## Initial Thoughts

### Potential Approaches

1. **Substitute the companion relation.** From $V_n = 2U_{n+1} - P U_n$, any common divisor $d$ of
   $U_n, V_n$ divides $2 U_{n+1}$. Since $\gcd(U_n, U_{n+1}) = 1$, $d \mid 2$. Formalize with
   `Nat.dvd_gcd` / `Int.gcd` divisibility lemmas.
2. **Direct dvd chase** using the quadratic invariant to control the common factor.

### Key Difficulties

- Choosing the right base ring ($\mathbb{Z}$ vs $\mathbb{N}$) for the gcd and sign handling.
- Cleanly transferring the parent's consecutive-coprimality lemma.
