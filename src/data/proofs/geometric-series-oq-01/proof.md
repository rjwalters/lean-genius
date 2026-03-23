# Geometric Series at the Boundary: |r| = 1

## The Question

For $|r| < 1$, the geometric series $\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}$ converges beautifully. But what happens at the critical boundary $|r| = 1$?

## The Answer

The boundary $|r| = 1$ is a **phase transition** where classical convergence fails, but more subtle summability methods can still extract meaningful values.

### Case 1: $r = 1$ — Divergence

The partial sums $S_n = \sum_{k=0}^{n-1} 1^k = n$ grow without bound. This is the simplest divergent series.

### Case 2: $r = -1$ — Grandi's Series

The partial sums oscillate:
$$S_1 = 1, \quad S_2 = 0, \quad S_3 = 1, \quad S_4 = 0, \quad \ldots$$

More precisely, $S_{2m} = 0$ and $S_{2m+1} = 1$. The series $1 - 1 + 1 - 1 + \cdots$ does not converge.

### Case 3: Cesàro Summability to $\frac{1}{2}$

While Grandi's series doesn't converge, its **Cesàro mean** — the average of partial sums — does:

$$\sigma_n = \frac{S_1 + S_2 + \cdots + S_n}{n} = \frac{\lceil n/2 \rceil}{n} \to \frac{1}{2}$$

This is proved via the bound $|\sigma_n - 1/2| \leq 1/(2n)$ and the squeeze theorem.

### General: $|r| \geq 1$ Implies Not Summable

For any $r$ with $|r| \geq 1$, the terms $|r^n| = |r|^n \geq 1$ don't tend to zero, so the series cannot be summable.

## Key Proof Techniques

- **Parity case analysis**: The geometric sum formula $2 \cdot S_n = 1 - (-1)^n$ splits cleanly into even ($S_n = 0$) and odd ($S_n = 1$) cases.
- **Squeeze theorem**: The Cesàro mean is bounded by $|\sigma_n - 1/2| \leq 1/(2n)$ using the integer arithmetic fact that $n \leq 2\lceil n/2 \rceil \leq n+1$.
- **Subsequence extraction**: Non-summability is proved by showing the even subsequence $(-1)^{2m} = 1$ doesn't tend to zero.

## Historical Significance

Grandi's series (1703) was one of the first examples to challenge the notion of "sum." Euler famously assigned it the value $1/2$, which Cesàro later justified rigorously (1890) through his theory of summability. This opened the door to modern summability theory and regularization methods used throughout mathematics and physics.
