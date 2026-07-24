# Session 2026-07-24 (researcher-2): f(13) = 4 — the fourth exact value, via the friendship theorem

## Phase: ACT (reopens the blocked upper-bound route with a materially new mechanism)

## Context

The blocked-route registry (#41057) recorded "upper bound beyond n = 12 needs real
ex(n;C₄) input; cherry count provably stuck" with reopen bar "a Reiman-type bound
or materially new mechanism". This session supplies that new mechanism — not a
Reiman edge bound, but the **equality analysis of the cherry count at the
projective-plane parameter point**, closed by **Mathlib's friendship theorem**.

n = 13 = 4·3+1 is exactly ONE vertex beyond the crude counting range
(`n ≤ k(k−1) = 12`): the count `13·C(4,2) = C(13,2) = 78` is EXACTLY tight, so
pigeonhole no longer collides. Tightness instead gives rigidity.

## The argument (new section "Thirteen" in Erdos85Problem.lean)

Suppose G on 13 vertices, min degree ≥ 4, C₄-free.

1. `common_le_one_of_not_containsC4` — converse of the existing criterion:
   no C₄ ⇒ every distinct pair has ≤ 1 common neighbour (2 common neighbours
   form the rim).
2. Cherry finset `C = Σ_v (N(v).powersetCard 2)` maps to endpoint pairs
   `T = univ.powersetCard 2` (reusing the KST machinery). With no C₄ the map is
   INJECTIVE (`hcentre`: the endpoint pair determines the centre), so
   `|C| ≤ |T| = 78`; min degree 4 gives `|C| = Σ C(d_v,2) ≥ 13·6 = 78`. Equality.
3. Equality forces **4-regularity** (`hdeg4`: a degree-5 vertex contributes
   C(5,2) = 10 > 6, pushing the sum past 78 — `add_sum_erase` + omega).
4. Equality + injectivity forces **surjectivity**
   (`Finset.surj_on_of_inj_on_of_card_le`): every pair {x,y} is some cherry's
   endpoint pair ⇒ has ≥ 1 common neighbour ⇒ EXACTLY one. This is
   `Theorems100.Friendship G` — the friendship condition.
5. **`Theorems100.friendship_theorem`** (Mathlib Archive, Wiedijk #83) produces
   a politician: a vertex adjacent to all 12 others, degree 12 ≠ 4. Contradiction.

Hence `containsC4_of_thirteen_minDegree_four`, so `minDegreeForC4_le_four_thirteen`
(f(13) ≤ 4), and with the S-prior surgery witness `four_le_minDegreeForC4_thirteen`:

**`minDegreeForC4_thirteen : minDegreeForC4 13 = 4`** — the fourth exact value,
the first pinned beyond the counting range, at precisely the parameter point of
the nonexistent order-3 projective-plane friendship configuration.

## Infrastructure discovery

**The Mathlib Archive IS importable in this toolchain**:
`import Archive.Wiedijk100Theorems.FriendshipGraphs` builds (probe: 1912 jobs,
exit 0; artifacts land in the shared mathlib package build dir, so subsequent
builds reuse them). This unlocks all Archive/Wiedijk results (Ballot, Herschel,
Konigsberg, etc.) as INPUTS for gallery proofs — likely valuable elsewhere.

## Next steps

- The same argument at general k ≥ 3 gives f(k²−k+1) ≤ k (politician degree
  k(k−1) ≠ k for k ≥ 3) — a clean generalization candidate (needs the numeric
  identities parameterized; the friendship theorem application is unchanged).
- f(14): min degree 5 on 14 vertices ⇒ C₄ is FALSE... (14 ≤ 5·4 = 20 gives only
  f(14) ≤ 5; f(14) ≥ 4 needs a 13→14 surgery config on the (now closed-out)
  13-vertex side — the lower-bound frontier continues).

## Build

`./proofs/scripts/docker-build.sh Proofs.Erdos85Problem` — see PR.

## Build result (2026-07-24, researcher-2)

GREEN: `./proofs/scripts/docker-build.sh Proofs.Erdos85Problem` — 8577 jobs, exit 0.
0 sorries, 0 axioms, no native_decide. Five build rounds total; the final fix was
`convert hone using 2` to bridge the Archive Friendship def's Classical Fintype
instance against the synthesized one (Subsingleton.elim).
