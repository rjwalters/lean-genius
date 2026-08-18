# Branch-matching no-closure law vs saver/miss calculus (h=1, d=7, 49-lab)

Mandate: msg 1225 priority 1, plan from msg 1164. Derive the branch version of
`minimumLayer_externalBlock_no_closed_fourStep` against the msg-537/538/540
saver/miss calculus; decide whether it yields encoder clauses beyond the raw C4
quadruples; A/B on a hard BBBB orbit if so.

## Setup (all previously established in-room)

Root v (deg 8), mids s_1..s_8 (deg 7) in 4 paired pairs, outer 40 lows (deg 7)
in branches B_a = N(s_a)∖({v}∪N(v)), |B_a| = 5. No edges between paired
branches; cross-branch edge sets between unpaired branches are partial
matchings sigma_ab; in-branch adjacency is a matching with in_a edges.
Matched low covers exactly 5 of its 6 unpaired foreign branches (miss beta(y));
unmatched low covers all 6. m_ab = #misses B_a->B_b, symmetric, row sum
Sigma_b m_ab = 2 in_a. BBBB profile: in_a = 2 for all a (4 matched + 1
unmatched per block), row sums 4, total misses 32.

## Part 1: the literal branch no-closure law

Four branches (a,b,c,d), consecutive pairs unpaired: a closed 4-step
x∈B_a ~ y∈B_b ~ z∈B_c ~ w∈B_d ~ x is a C4 (x≠z, y≠w automatic across distinct
blocks). So the composed partial holonomy sigma_da∘sigma_cd∘sigma_bc∘sigma_ab
is fixed-point-free — the law HOLDS, uniformly, with partiality.
3-branch and 2-branch outer C4s are structurally impossible (a middle vertex
has ≤1 neighbor per foreign branch), and the partner-transport C4
(partners -> partners) reduces in profile-pinned instances to binary clauses
the preprocessor already extracts from the raw quadruple clauses.

**Verdict (a): as a clause family the branch no-closure law IS the raw C4
quadruple clause set restricted to cross-branch quadruples — already present,
zero new pruning.**

## Part 2: what the fan/no-closure calculus DOES give — the exact defect ledger

C4-freeness = every vertex pair has ≤1 common neighbor. Count 2-walks per pair
class and subtract. Defect pair := zero common neighbors.

Global: Sigma_v C(deg,2) = 48·21 + 28 = 1036 walks, C(49,2) = 1176 pairs,
so exactly **140 defect pairs**, always.

Per class (BBBB numbers in brackets):

| pair class                     | 2-walk count                        | defect count |
|--------------------------------|-------------------------------------|--------------|
| (v, mid), (v, outer), (mid,mid)| ≥1 forced                           | 0            |
| (mid s_c, outer y), c unpaired | [y covers c]                        | = #misses [32] |
| (mid s_c, y ∈ B_c)             | matched: partner; unmatched: none   | = #unmatched [8] |
| same-block pairs               | parent (+partner edge)              | 0            |
| paired product B_i × B_j       | 30 − 2in_i − 2in_j                  | 2(in_i+in_j) − 5 each [3 each, 12 total] |
| unpaired product B_a × B_b     | 20 + m_{a,pair(b)} + m_{b,pair(a)}  | 5 − m_{a,pair(b)} − m_{b,pair(a)} [total 88] |

Ledger check (BBBB): 32 + 8 + 12 + 88 = 140. EXACT — consistent, so no free
analytic kill (matches the msg-533 LP-feasibility finding), and the saver law
re-derives inside it: the 4 misses into pair(c) land 1-per-misser in B_c
(incidence law), needy absorbs ≥1 (saver), leaving exactly 3 defect pairs in
the paired product — the two calculi agree.

Derivation notes:
- Paired product: only middle-block apexes exist (partner routes vanish since
  paired blocks have no cross edges); middles(i,j) = the 6 blocks unpaired
  with i = unpaired with j; total = Sigma_c (5 − m_ci − m_cj) = 30 − 2in_i − 2in_j.
- Unpaired product: apex routes = partner-in-B_a (4 − m_ab), partner-in-B_b
  (4 − m_ab), and the 4 blocks unpaired with both: Sigma (5 − m_ca − m_cb);
  the m_ab terms cancel: total = 20 + m_{a,pair(b)} + m_{b,pair(a)}.
  (≥0 slack re-derives the msg-540 capacity m_{a,pair(b)} + m_{b,pair(a)} ≤ 5.)

**Verdict (b): the new encoder content is the system of product-level counting
EQUALITIES — "exactly 3 defect pairs per paired product" and "exactly
5 − m − m' per unpaired product" — plus the miss-defect bijections. These are
implied by the axioms but require cardinality reasoning CDCL cannot perform;
exactly the h=9 partition-law shape.**

## Part 3: payload refined against remote_worker.py (the deployed encoder)

**(F1) FREE TIGHTENING — asymmetric miss pinning.** The encoder pins block c's
misses into j only for c<j; the reverse direction m_{j->c} is semantically
forced (m-symmetry theorem, msg 535: |E(B_c,B_j)| = 5−m_{c->j} = 5−m_{j->c})
but NOT propagationally present. Pin both directions with the same constant.

**(F2) Per-vertex paired-direction fan equality (the saver calculus, exact).**
For x ∈ B_c with paired block B_c′: ALL of x's far neighbors live in the 6
middle blocks of (c,c′); each far neighbor w covering c′ launches a 2-walk
x–w–(w's c′-neighbor); landings pairwise distinct (two apexes to one z = C4,
already forbidden). Hence in every model:
   Sigma_{z∈B_c′} C_{xz} + Sigma_{w matched middle} s_{x,w} = deg_far(x)
where C_{xz} ↔ ∨_w [e(x,w)∧e(w,z)] (common indicator) and
s_{x,w} = e(x,w)∧missvar(w,c′) (x's saver-edges). Implied, sound, and pure
counting — 40 CardEnc.equals circuits over ~29 literals.

**(F3) Product-level totals are CONSTANTS.** With the m-table pinned, every
product's defect count is a number, not a formula: paired products carry
exactly 22 commons (25−3); unpaired products {a,b} carry exactly
20 + m_{a,pair(b)} + m_{b,pair(a)} commons. 4 + 24 cardinality circuits over
the C vars.

Arms: v1 = F1+F2+paired-F3 (556k clauses vs 520k base); v2 adds unpaired-F3
(613k). A/B on orbit 3151303b651a1de5 (hardest solved, 5130s historical),
all arms same box same contention. Implementation: `sat49/ab_worker.py`;
cube-and-conquer budget variant: `sat49/sweep_worker.py` (900s budget, then
25 cubes on the two unmatched-vertex fan edges u(B0)->B2 × u(B1)->B3 —
exactly-one on both axes makes the cubes a partition).

## Deferred/future

- Sign/parity holonomy obstruction (S5-voltage): undefined for partial
  matchings without per-defect bookkeeping; revisit only if the ledger A/B
  underperforms.
- General-profile ledger (AAAB etc.): same equalities with 2(in_i+in_j)−5 and
  row sums 2in_a; nothing BBBB-specific in the derivation.
