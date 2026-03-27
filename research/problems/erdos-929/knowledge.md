# Erdős #929 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set of $n$ where\[n+1,n+2,\ldots,n+k\]are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?



It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$. The best bound on large gaps between primes due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18} (see [4]) implies\[S(k) \ll k \frac{\log\log\log k}{\log\log k\log\log\log\log k}.\]




References


[FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence, Long gaps between primes. J. Amer. Math. Soc. (2018), 65-105.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #4
- Problem #928
- Problem #930
- Problem #39
- Problem #1

## References

- Er76d
- FGKMT18

## Sessions

### Session 2026-03-25 (Session 1) — Eliminate smoothBlockSet_pos_density sorry

**Mode**: REVISIT
**Outcome**: completed (sorry eliminated)

#### What I Did
- Proved `smoothBlockSet_pos_density`: the set smoothBlockSet k (k+1) has positive upper density
- Proof strategy: the AP {M*i+1 : i ∈ ℕ} (M = (k+1)!) is contained in the smooth block set (via `arithProg_subset_smoothBlockSet`). At index n=M*t, the AP contributes ≥ t members to {0,...,n}. So densityRatio ≥ t/(M*t+1) ≥ 1/(M+1) > 0 frequently.
- Used `Filter.le_limsup_of_frequently_le` + `densityRatio_isBoundedUnder` for the limsup bound
- Used `Finset.card_image_of_injOn` + `Finset.card_le_card` for the cardinality injection
- Overcame DecidablePred instance mismatch: `change` to `densityRatio S (M*t)` then `unfold densityRatio` to match exact Classical.decPred instance from Set.upperDensity definition

#### Key Findings
- DecidablePred instance from `haveI` does NOT match the one embedded in Set.upperDensity definition — must use `@Finset.filter` with explicit `Classical.decPred (· ∈ S)` to match
- `div_le_div_iff` is deprecated; use `div_le_div_iff₀` in current Mathlib
- `omega` cannot handle nonlinear multiplication (M*a = M*b); use `linarith` + `mul_left_cancel₀`

#### Files Modified
- `proofs/Proofs/Erdos929Problem.lean` — eliminated sorry in smoothBlockSet_pos_density

#### Next Steps
- smooth_threshold_2 (S(2)=3) may be provable: show x≤2 gives zero density, x=3 works via n≡2 mod 6
- rosser_lower and fgkmt_upper are deep analytic NT — keep as axioms

---

*Generated from erdosproblems.com on 2026-01-15*
