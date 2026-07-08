# Erdős #1204 - Knowledge Base

## Problem Statement

We call a sequence of integers $0\leq a_1<\cdots <a_k$ admissible if it is missing at least one congruence class modulo every prime $p$. Let $A(k)=\min a_k$. Estimate $A(k)$ - in particular, is it true that\[A(k)\sim k\log k?\]Estimate\[B(k)=\min \frac{a_1+\cdots+a_k}{k}.\]

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #60
- Problem #2
- Problem #855
- Problem #1203
- Problem #1205
- Problem #39
- Problem #1

## References

- Er80
- HeRi73
- Po14c
- El65

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-04-16*

## Session 2026-06-25 (researcher-1) — structural properties + well-definedness of A(k)

Added 4 verified theorems (now 10 thm/1 def, 0 axioms, 0 sorries):
- `Admissible.subset` — downward closure (subset of admissible is admissible).
- `admissible_image_add` — translation invariance (a ↦ a+t preserves admissibility);
  `card_image_add` — translation preserves cardinality.
- `exists_admissible_card` — **an admissible k-set exists for every k** (multiples
  0,N,2N,…,(k-1)N of the primorial N=∏_{p≤k}p), so **A(k) is well-defined**, with the
  explicit weak upper bound A(k) ≤ (k-1)·∏_{p≤k}p.

Insight: admissibility is a property of the *pattern*, not the position. The headline
A(k)∼k log k and B(k) estimate remain OPEN (need sieve theory).

Gotcha: `(N:ZMod p)=0` from `p∣N` via `CharP.cast_eq_zero_iff (ZMod p) p N` (no NeZero needed,
unlike `ZMod.natCast_zmod_eq_zero_iff_dvd`); `push_cast` then `rw [hp0, mul_zero]; exact zero_ne_one`.

## Session 2026-06-25 (researcher-8) — defined A(k) + trivial regime exact values

Added 8 verified theorems + 1 def (now 18 thm / 2 def, 0 axioms, 0 sorries):
- `A (k : ℕ) : ℕ := sInf {a.sup id | a admissible, a.card = k}` — **the central object A(k)
  is now actually defined in Lean** (previously only `Admissible` + existence existed). This
  makes the headline question "A(k) ∼ k log k?" expressible. Uses `a.sup id` (max, ∅↦0) for totality.
- `A_set_nonempty`, `A_mem` — the family is nonempty (via `exists_admissible_card`), so the
  infimum is **attained**: ∃ admissible k-set with max exactly A(k).
- `A_le` — A(k) is a genuine lower bound on the max of any admissible k-set (`Nat.sInf_le`).
- `card_le_sup_succ` (a.card ≤ a.sup id + 1) ⇒ `sub_one_le_A`: **A(k) ≥ k-1** (packing bound).
- `A_zero = 0`, `A_one = 0`, `A_two = 2` exact. **A(2)=2 > 1=k-1** is the first place
  admissibility is *binding*: the densest 2-set {0,1} is inadmissible, forcing the max above
  the packing bound. (Lower bound: a 2-set with max 1 must be {0,1} = not admissible.)

Still OPEN: the asymptotics A(k)∼k log k and B(k) (need sieve theory). The new content brackets
A(k) between k-1 and (k-1)·primorial and nails the trivial small-k regime.

Gotchas: `A_le` k is implicit — `(by decide)` for `card {0,2} = k` fails with "Expected type must
not contain metavariables"; pass `(k := 2)` explicitly. `a.sup id ≥ k-1` via `a ⊆ range (sup+1)`
+ `Finset.le_sup (f := id)`. `Nat.sInf_mem`/`Nat.sInf_le` give attainment + lower bound directly.

## Session 2026-06-25 (researcher-5) — exact value A(3)=6

Added 5 verified theorems (now 23 thm / 2 def, 0 axioms, 0 sorries; #print axioms A_three =
propext/Classical.choice/Quot.sound only — no native_decide, no sorryAx):
- `A_three : A 3 = 6` — **the next exact value after A(2)=2**, and the first appreciable gap
  over the packing bound (6 vs k-1=2). 6 = Hardy–Littlewood minimal diameter H(3).
- `admissible_zero_two_six : Admissible {0,2,6}` — the witness giving A(3) ≤ 6 (all even ⇒
  miss odd class mod 2; residues {0,2,0} mod 3 ⇒ miss class 1).
- `admissible_three_sup_ge : a.card=3 → Admissible a → 6 ≤ a.sup id` — the lower bound core.
- `not_admissible_zero_two_four`, `not_admissible_one_three_five` — both 3-sets cover ALL
  classes mod 3, so are inadmissible.

**Lower-bound argument (A(3) ≥ 6).** Any admissible 3-set with max ≤ 5 lies in {0,..,5}.
Missing a class mod 2 forces all three elements to share a parity ⇒ the set is exactly
{0,2,4} or {1,3,5} (the only single-parity triples in {0,..,5}). Both cover every residue
class mod 3 ({0,2,1} and {1,0,2} resp.), so neither is admissible — contradiction.

**Key realization.** A(k) = the Hardy–Littlewood minimal diameter H(k) (translation invariance
makes min a_k = min diameter). So the exact-value frontier is just computing successive H(k):
H(3)=6, H(4)=8, H(5)=12, …. Next: A(4)=8 (witness {0,2,6,8}).

Gotchas: parity extracted via `ZMod.natCast_eq_zero_iff x 2` ((x:ZMod 2)=0 ↔ 2∣x) — note
`ZMod.natCast_zmod_eq_zero_iff_dvd` is now DEPRECATED. `∀ y:ZMod 2, y=0∨y=1` by `decide`
splits the ≠1 case to get evenness. `omega` closes membership in {0,2,4}/{1,3,5} from
`x ≤ 5` + a divisibility fact. Pin the 3-set with `Finset.eq_of_subset_of_card_le`.

## Session 2026-06-25 (researcher-5b) — parity sharpens A(k) ≥ 2(k−1) for ALL k

Added 4 verified theorems (now 27 thm / 2 def total, 0 axioms, 0 sorries), STRENGTHENING the
existing trivial bound `sub_one_le_A : k−1 ≤ A k` to `two_mul_sub_one_le_A : 2(k−1) ≤ A k`:
- `admissible_same_parity` — the prime p=2 forces ALL elements of an admissible set to share
  parity: ZMod 2 has only two classes, one is missed, so every element lies in the other
  (`∀ s z w : ZMod 2, z ≠ s → w ≠ s → z = w` by `decide`).
- `admissible_diam_ge` — any nonempty admissible set has `max' − min' ≥ 2(card − 1)`. Same
  parity ⇒ `2 ∣ x − min'`; the map `x ↦ (x − min')/2` injects `a` into `range((max'−min')/2+1)`,
  so `card ≤ (max'−min')/2 + 1`.
- `admissible_two_mul_card_sub_one_le_sup` — for admissible `a`, `2(card−1) ≤ a.sup id`
  (diameter bound + `min' ≥ 0` + `max' ≤ sup id`).
- `two_mul_sub_one_le_A` — **A(k) ≥ 2(k−1)**, twice the packing bound, sharp at k=2 (A 2 = 2 ✓).

Insight: this is the leading prime-2 term of the sieve heuristic predicting A(k) ∼ k log k.
Each further prime p contributes a factor p/(p−1) (elements occupy ≤ p−1 of p classes); the
log k comes from summing/CRT over small primes — that combination needs analytic sieve
machinery and stays OPEN.

Gotchas: `Finset.card_le_card_of_injOn` wants `Set.MapsTo f ↑s ↑t`, not `∀ x ∈ s, f x ∈ t` —
pass `(t := …)` explicitly so the target Finset is inferred. `2 ∣ x − min` from
`(min : ZMod 2) = (x : ZMod 2)` via `ZMod.natCast_eq_natCast_iff` then `Nat.modEq_iff_dvd'`
(needs `min ≤ x`). `omega` discharges all the /2 division reasoning (injectivity, range bound,
diameter→sup chain). This bound is the general-k counterpart of the per-value A(3)=6 lower
bound above (which used the same parity-pins-the-set idea for k=3). NOTE: always rebase onto
current `origin/main` before editing — the A(k) section grew from 201→289→404→480 lines across
concurrent sessions; a stale worktree branch can hold an old copy.

## Session 2026-07-02 (researcher-1) — exact value A(4) = 8

Added the next exact value after A(2)=2, A(3)=6, as a **companion file**
`proofs/Proofs/Erdos1204A4.lean` (120 L, 5 thm, **0 axioms / 0 sorries**,
`#print axioms A_four` = propext/Classical.choice/Quot.sound only — kernel `decide`,
NO native_decide). Kept it a separate file (not edited into the 480-line
`Erdos1204Problem.lean`) to avoid the concurrent-session race on that file.

- `A_four : A 4 = 8` — matches Hardy–Littlewood minimal diameter H(4)=8.
- `admissible_zero_two_six_eight : Admissible {0,2,6,8}` — witness for A(4) ≤ 8
  (even ⇒ miss odd mod 2; residues 0,2,0,2 mod 3 ⇒ miss class 1).
- `admissible_four_sup_ge : a.card=4 → Admissible a → 8 ≤ a.sup id` — lower bound.
- `not_admissible_evens_four` / `not_admissible_odds_four` — the two single-parity
  4-sets in {0..7} ({0,2,4,6}, {1,3,5,7}) both cover all classes mod 3.

**Lower-bound argument (A(4) ≥ 8).** Any admissible 4-set with max ≤ 7 lies in
{0,…,7}; missing a class mod 2 forces one parity, and the only 4-element
single-parity subsets of {0,…,7} are {0,2,4,6} and {1,3,5,7}, both mod-3-complete
⇒ inadmissible. This mirrors the A(3)=6 argument verbatim (parity pins the set,
then mod 3 kills it) — the general template for the next H(k). Note A(4)=8 > 6 =
2(k−1), so at k=4 the mod-3 constraint (beyond parity) is already binding, unlike
k=2,3 where 2(k−1) was tight/near-tight.

Reused base helpers: `admissible_iff_card` (reduce to primes p ≤ card),
`A_le`, `A_mem`, `A`. Same `ZMod.natCast_eq_zero_iff` parity extraction and
`Finset.eq_of_subset_of_card_le` set-pinning as A(3). Frontier continues: next
A(5)=12 (witness {0,2,6,8,12}? — H(5)=12; needs ruling out max ≤ 11, more single-
parity 5-subsets to eliminate mod 3, likely mod-5 too). Build survived the
concurrent-Mathlib-rebuild storm via olean-existence retry loop (base built on
attempt 4, my file clean on attempt 1).

## Session 2026-07-08 (researcher-1) — exact value A(6) = 16 (first prime-5-binding lower bound)

Added the next exact value after A(2)=2, A(3)=6, A(4)=8, A(5)=12, as companion file
`proofs/Proofs/Erdos1204A6.lean` (203 L, 5 thm, **0 axioms / 0 sorries**, kernel
`decide` only — NO native_decide, so `#print axioms A_six` is the propext/Choice/Quot
trio). Kept separate from the 480-line Problem file to avoid the concurrent-session race.

- `A_six : A 6 = 16` — matches Hardy–Littlewood minimal diameter H(6)=16.
- `admissible_witness_six : Admissible {0,4,6,10,12,16}` — witness for A(6) ≤ 16
  (even ⇒ miss odd mod 2; residues 0,1,0,1,0,1 mod 3 ⇒ miss class 2; residues
  0,4,1,0,2,1 mod 5 ⇒ miss class 3; p≥7 automatic since |a|=6<p).
- `admissible_six_sup_ge` — lower bound A(6) ≥ 16.
- `no_admissible_six_evens` / `no_admissible_six_odds` — the lower-bound cores.

**Why A(6) is the interesting frontier point.** For k≤5 the lower bound closed with
parity + mod 3 (each mod-3 class in the six single-parity elements ≤ {0..11} held
exactly two elements, so missing one left ≤4 slots < 5). At k=6 the single-parity
window is the EIGHT evens/odds in {0..15}, where mod-3 classes have sizes 3,2,3.
Missing the size-2 class (1 mod 3 for evens, 2 mod 3 for odds) leaves a FULL 6-set:
{0,2,6,8,12,14} resp. {1,3,7,9,13,15}. Neither dies to mod 3 — but BOTH cover all
five residue classes mod 5, so they fail admissibility at p=5. **This is the first
exact value whose lower bound genuinely needs the third prime 5** — the finite
analogue of the sieve heuristic (each prime p removes a p/(p−1) factor) behind the
conjectured A(k) ∼ k log k.

Recipe (reused from A5): `Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)`
to pin the forced 6-set, then `rw [heq] at ha; obtain ⟨r5,hr5⟩ := ha 5 (by decide);
fin_cases r5` and discharge each class with `exact absurd (by decide) (hr5 <elem> (by decide))`
picking the concrete element realizing that class. mod-3 subset narrowing uses the A5
idiom `fin_cases hxE <;> first | decide | exact absurd (by decide) hxne`.

Still OPEN: asymptotics A(k)∼k log k and B(k) (need analytic sieve). Next exact value:
A(7)=20 (H(7)), witness e.g. {0,4,6,10,16,18,22}? — verify; the lower bound will need
primes 2,3,5,7 combined and the case analysis grows.

## Session 2026-07-08 (researcher-1, iteration 6) — exact value A(7) = 20 (prime 7 NOT yet binding)

Added the next exact value after A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16 as companion
file `proofs/Proofs/Erdos1204A7.lean` (5 thm, **0 axioms / 0 sorries**, kernel `decide`
only — NO native_decide). Kept separate from the Problem file to avoid the concurrent-
session race, matching A4/A5/A6.

- `A_seven : A 7 = 20` — matches Hardy–Littlewood minimal diameter H(7)=20.
- `admissible_witness_seven : Admissible {0,2,6,8,12,18,20}` — witness for A(7) ≤ 20
  (even ⇒ miss odd mod 2; residues 0,2,0,2,0,0,2 mod 3 ⇒ miss class 1; residues
  0,2,1,3,2,3,0 mod 5 ⇒ miss class 4; residues 0,2,6,1,5,4,6 mod 7 ⇒ miss class 3;
  p≥11 automatic since |a|=7<p).
- `no_admissible_seven_evens` / `no_admissible_seven_odds` — the lower-bound cores.
- `admissible_seven_sup_ge` — A(7) ≥ 20.

**CORRECTION to the A(6) note's prediction.** The A(6) session guessed A(7)=20 "will need
primes 2,3,5,7 combined". It does NOT. In each 10-element single-parity window
{0,2,…,18} / {1,3,…,19} the mod-3 classes have sizes 4,3,3 (not 3,2,3 as in the smaller
8-element A(6) windows). Missing the size-4 class leaves 6 elements (< 7 ⇒ contradiction),
and missing EITHER size-3 class leaves a forced 7-set — so there are TWO forced 7-sets per
parity (vs exactly one at A(6)):
- evens: {0,2,6,8,12,14,18} (drop 1 mod 3) and {0,4,6,10,12,16,18} (drop 2 mod 3);
- odds: {1,5,7,11,13,17,19} (drop 0 mod 3) and {1,3,7,9,13,15,19} (drop 2 mod 3).
All four are mod-5-COMPLETE (cover every residue class mod 5), so p=5 alone kills them.
Hence A(7)=20 closes with 2,3,5 and the prime 7 is not yet binding. The A(7) witness DOES
miss a class mod 7, but that is only needed for the *upper*-bound admissibility of the
witness, not the lower bound.

**Recipe (reused verbatim from A6).** For each forced 7-set use
`Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)` to pin it, then
`rw [heq] at ha; obtain ⟨r5,hr5⟩ := ha 5 (by decide); fin_cases r5` and discharge each
class with `exact absurd (by decide) (hr5 <elem> (by decide))` picking the concrete
element realizing that mod-5 class. Subset-narrowing under a missed mod-3 class uses
`fin_cases hxE <;> first | decide | exact absurd (by decide) hxne`. Card contradictions
(the size-4-class branches) use `have hle := Finset.card_le_card hs; rw [hcard] at hle;
revert hle; decide`. The main split is `obtain ⟨r2,hr2⟩ := ha 2 (by decide); fin_cases r2`
with `omega` closing single-parity window membership from `x ≤ 19` + `2 ∣ x` / `¬2∣x`.

**INFRA (important for next session).** The shared docker Mathlib-cache volume developed a
filesystem-level SIGBUS corruption: EVERY `import Mathlib` build died at exit 135 in ~1s
while compiling the Erdos1204Problem dependency (line-less, at [7743/7744]). Reproduced 5×
across the sparse `.loom` worktree AND a fresh durable worktree. `--repair-cache`
(`lake exe cache get!` force-overwrite) reported "Cache force-refresh succeeded" but the
next build still hit the identical 135 — so `cache get!` does NOT fix filesystem-level
volume damage; only a full `--nuke` reset would, and that needs a zero-container window
(2 fleet containers were active, so nuke was unsafe/impolite). A(7) was VERIFIED instead
via the host-lake bypass: `LAKE_UNSAFE=1 ./bin/lake exe cache get` then
`./bin/lake env lean Proofs/Erdos1204A7.lean` on the host, outside docker (fresh host
.lake, unaffected by the corrupt docker volume). Also note: `--repair-cache` run from a
RESET/sparse `.loom` worktree fails on attempt 2 with "no configuration file ...
lakefile.toml" — it must be run from a NON-SPARSE worktree that actually has proofs/.

Still OPEN: asymptotics A(k)∼k log k and B(k) (need analytic sieve). Next: A(8)=26 (H(8)
jumps by 6). Consider factoring a generic "single-parity window minus one mod-p class"
helper before the case analysis grows further.
