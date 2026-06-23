# Distribution of Ruin Times (Martingale Stopping)

## Source
Gallery proof: `fair-games-theorem` (open question #1)

## Problem Statement
What is the distribution of ruin times in the gambler's ruin problem? Formalize the stopping time distribution using martingale theory.

## Mathematical Context
In the gambler's ruin problem, a player starts with fortune k and plays a fair game until reaching 0 (ruin) or N (target). The fair games theorem establishes that the expected fortune is constant (martingale property). The natural follow-up: what is the **distribution** of the ruin time T?

Key results:
- E[T] = k(N-k) for fair games
- The distribution involves the eigenvalues of the transition matrix
- Generating function: E[z^T] can be computed via the gambler's ruin Markov chain
- Connection to the arc-sine law for returns to the origin

## Key Components
1. **Stopping times**: T = inf{n : Sₙ = 0 or Sₙ = N}
2. **Optional stopping theorem**: E[S_T] = E[S_0] (already related to fair games)
3. **Wald's identity**: For computing E[T]
4. **Moment generating function**: Full distributional characterization
5. **Arc-sine law connection**: Distribution of last visit to 0

## Suggested Approach
1. Define the gambler's ruin stopping time formally
2. Prove E[T] = k(N-k) using the martingale Sₙ² - n
3. Formalize the Wald identity for bounded stopping times
4. Compute the MGF or characteristic function of T
5. Connect to the existing fair games theorem formalization

## Tractability
Challenging but well-scoped — Mathlib has filtrations and stopping times. The computations are classical and well-documented.

## Category
Extension of fair games theorem
