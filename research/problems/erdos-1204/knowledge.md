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
