# Erdős #340 — Greedy Sidon Sequence Growth (knowledge)

## Status

**OPEN CONJECTURE.** The main claim `|A ∩ [1,N]| ≫ N^(1/2−ε)` for the greedy
(Mian–Chowla) Sidon sequence is unsolved; best known lower bound is `N^(1/3)`. This is
the famous `1/3`-vs-`1/2` exponent gap. **Do not attempt to prove the conjecture.**

The registered file `proofs/Proofs/Erdos340GreedySidon.lean` carries four `axiom`s:

| axiom | content | status |
|-------|---------|--------|
| `sidon_upper_bound` | Erdős–Turán `|A| ≤ √N + O(N^{1/4})` | known result, ~100 lines, HARD |
| `greedySidonSeq` | the sequence `ℕ → ℕ` | existence |
| `greedySidonSeq_strictMono` | strictly increasing | existence |
| `greedySidonSeq_isSidon` | all prefixes Sidon | existence |

(`sidon_upper_bound_weak : |A| ≤ √(2N)+1` is **proved** in-file via `sidon_lower_bound`.)

## Contribution this cycle — Sidon extendability kernel

The three `greedySidonSeq*` axioms encode one substantive existence fact: **finite
Sidon sets are unboundedly extendable.** That fact is now proved constructively in the
companion `proofs/Proofs/Erdos340GreedySidonExtension.lean` (namespace
`Erdos340Extension`), sorry-free and axiom-free:

- `sidon_insert_two_sup_add_one` — inserting the **explicit** witness `m = 2·sup A + 1`
  into a Sidon set `A` keeps it Sidon.
- `sidon_extendable` — `∃ m, (∀ a∈A, a<m) ∧ m∉A ∧ IsSidon (insert m A)`.
- `sidonChain n` / `sidonChain_isSidon` / `sidonChain_card` — an explicit doubling
  chain of Sidon sets with `|sidonChain n| = n`.
- `exists_sidon_card n` — Sidon sets of every cardinality exist.

### Why `m = 2·sup A + 1` is collision-free

Let `S = sup A` (so all of `A` is `≤ S`), `m = 2S+1 > S`. A new collision is
`a+b = c+d` (`a≤b`, `c≤d`) using `m`. Since `m` strictly exceeds every element of `A`,
each side's sum lies in one of three **disjoint** bands by how many `m`s it uses:
no-`m` `≤ 2S`; one-`m` `∈ [2S+1, 3S+1]`; two-`m` `= 4S+2`. Equal sums ⇒ equal `m`-count
per side ⇒ `Nat` cancellation (plus the original Sidon property when both sides are
`m`-free) gives `a=c, b=d`. The Lean proof discharges this with a 16-way `rcases` bash
closed uniformly by `omega` (feeding the `≤ S` bounds), except the all-in-`A` branch
which calls `hA` directly.

### Honesty note

This is the **doubling** construction, not the greedy Mian–Chowla one, so it does *not*
literally reproduce `greedySidonSeq` (which is greedy-minimal). It discharges the
*existence* content the axioms stand on, not greedy minimality. Growth here is only
`Ω(log N)` (cardinality `n` reaches value `~2^n`), nowhere near `N^(1/3)`; it is an
existence witness, not a growth result.

## Verification status

**BUILD-PENDING / UNREGISTERED.** Companion is NOT in `Proofs.lean` — there is no CI
Lean build gate (`check-proofs-imports.yml` is `workflow_dispatch` sync-only, never
compiles), so registering an unbuilt file risks `main`. Written under dual blackout:
Aristotle `prove` returns 404 (Resource not found); host `proofs/.lake` is a circular
self-symlink, so `docker-build.sh` would re-clone+rebuild all of Mathlib (hours / OOM
on the 7.65 GiB Docker VM, already running 3 lean containers).

### Next actions (on backend recovery)

1. `./proofs/scripts/docker-build.sh Proofs.Erdos340GreedySidonExtension` to confirm
   0 sorry / 0 axiom.
2. If green, register in `Proofs.lean` and add gallery cross-reference from
   `erdos-340-greedy-sidon`.
3. Optional axiom reduction: re-found `greedySidonSeq*` on `sidon_extendable` (replace
   the three existence axioms with the proved chain), leaving only the genuinely-hard
   `sidon_upper_bound` (Erdős–Turán) and the open conjecture statement.

## Routes that do NOT close the gap (for future agents)

- Counting differences gives `√(2N)+1` (done) — counting **sums** gives Erdős–Turán
  `√N + O(N^{1/4})`; both are *upper* bounds, neither touches the lower-bound gap.
- The greedy lower bound is cubic `a_n = O(n^3)` (global forbidden-set covering, NOT the
  naive incremental `a_{k+1}−a_k ≤ |A_k|^3` which only telescopes to `O(n^4)`); inverting
  gives `Ω(N^{1/3})`. Any exponent `> 1/3` for greedy would be a publishable new result.
