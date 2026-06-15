# Knowledge: erdos-1179-oq-02

## Question (defined from the parent 0-knowledge stub)

Erdős #1179 (PROVED, main asymptotic): for `0<ε<1`, `g_ε(N)` = least `k` such that
a uniformly random `k`-subset `A` of an abelian group `G`, `|G|=N`, has w.h.p. an
ε-uniform subset-sum representation function
`F_A(g)=#{S⊆A : Σ_{x∈S} x = g}`, i.e. `|F_A(g) − 2^k/N| ≤ ε·2^k/N` for all `g`.

**oq-02 (OPEN):** can the Erdős–Hall `(1+o(1))` *multiplicative* factor be sharpened
to a bounded *additive* error?  `g_ε(N) ≤ log₂N + O_ε(1)`.

## Bound hierarchy

| Result | Bound on g_ε(N) |
|--------|-----------------|
| Trivial lower bound | `≥ log₂N` (need `2^k ≥ N`) |
| Erdős–Rényi (1965) | `≤ (2+o(1))log₂N + O_ε(1)` |
| Erdős–Hall (1976) | `≤ (1 + O_ε(log log log N / log log N))·log₂N` |
| **oq-02 (open)** | **`≤ log₂N + O_ε(1)`** ? |

## Status

ORIENT/DEFINE only (2026-06-14). The OQ is asymptotic/analytic — finite computation
cannot decide it. `verify_uniform_subset_sums.py` (build-free, stdlib) confirms the
parent identity `Σ_g F_A(g)=2^|A|`, the lower bound (no ε-uniform `k<log₂N`), and
tabulates the exact empirical additive gap on `ℤ/N` (stays ~1–3.5 for the
probabilistic proxy, `N=2..12`). Honest caveat: tiny `N`, single group — consistent
with but not evidence for a bounded gap. Both backends (Docker + Aristotle) down.

See `src/data/research/problems/erdos-1179-oq-02.json` for the full record.
