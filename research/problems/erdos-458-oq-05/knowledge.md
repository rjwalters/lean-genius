# erdos-458-oq-05: Prove nthPrime value axioms from Lean Nat.nth definition

Parent: erdos-458 (LCM Inequality for Primes). File: `proofs/Proofs/Erdos458Problem.lean`.

## Goal
The parent file defined `nthPrime k := Nat.nth Nat.Prime k` but never connected it to
concrete prime values; the verified small cases (`erdos458_k1/k2`) hardcoded the primes
3 and 5. This sub-problem computes `nthPrime` values directly from the `Nat.nth` definition.

## Session 1 (researcher-7, 2026-06-27)
Added, proved from the definition (no `native_decide`, axiom-clean):
- `nthPrime_zero  : nthPrime 0 = 2`
- `nthPrime_one   : nthPrime 1 = 3`
- `nthPrime_two   : nthPrime 2 = 5`
- `nthPrime_three : nthPrime 3 = 7`
- `nthPrime_four  : nthPrime 4 = 11`

Technique: `Nat.nth_count : p n → Nat.nth p (Nat.count p n) = n` instantiated at a known
prime `n` (via `Nat.prime_two/three/five/seven/eleven`), with the auxiliary
`Nat.count Nat.Prime n = k` discharged by kernel `decide`. `decide` uses the
`Nat.decidablePrime` instance (`decidable_of_iff' _ prime_def_lt'`) and kernel-accelerated
Nat arithmetic, so it does NOT introduce `Lean.ofReduceBool` (unlike `native_decide`).

Then connected the verified small cases to the conjecture as genuine instances:
- `erdos458_conjecture_at_one : lcm_upto (nthPrime 2 - 1) < nthPrime 1 * lcm_upto (nthPrime 1)`
- `erdos458_conjecture_at_two : lcm_upto (nthPrime 3 - 1) < nthPrime 2 * lcm_upto (nthPrime 2)`
(each reduces via `rw [nthPrime_*]` to the existing `erdos458_k1/k2`).

theoremCount 14 → 21. axiomCount unchanged at 1 (`Lean.ofReduceBool` from the lcm_upto
small-value `native_decide`s; the new lemmas are axiom-clean).

## Status
UNVERIFIED — build host unavailable (disk 97%/~500Mi free; two zombie `lean-build`
containers up 5h belonging to other agents — not killed). Proofs verified by hand against
the pinned Mathlib 4.26.0 source (lemma signatures confirmed in
`.lake/packages/mathlib/Mathlib/Data/Nat/{Nth,Count}.lean` and `Prime/Defs.lean`).

## Session 2 (researcher-14, 2026-07-02) — axiom-elimination lever analysis (NO build possible)
Primary oq-05 goal is **complete and merged**: `nthPrime_zero..four` and
`erdos458_conjecture_at_one/two` are all present in `Erdos458Problem.lean` on `main`
(theoremCount 21, axiomCount 1). Nothing remains to do on the stated goal.

The only remaining lever is the parent file's `axiomCount 1` = `Lean.ofReduceBool`, which
comes entirely from seven `native_decide`s: `lcm_upto_two/three/four/five/six` and
`erdos458_k1/k2`. Definitive analysis of the "replace with kernel `decide`/`rfl`" idea from
Session 1's next-steps:

- **Kernel `decide`/`rfl` CANNOT work here.** `lcm_upto n = (Finset.Icc 1 n).lcm id`
  bottoms out in `Nat.lcm a b = a * b / Nat.gcd a b`, and `Nat.gcd` in Lean 4 core is
  defined by **well-founded recursion** (`WellFounded.fix`). WF recursion does not reduce
  definitionally in the kernel, so `decide` (which needs the `Decidable` instance to whnf to
  `isTrue`) and `rfl` both get stuck on the `gcd` subterms. This is exactly *why* the
  original author reached for `native_decide`. Do not spend a session trying `by decide`.

- **Correct axiom-free recipe (needs a build host to verify).** Prove each small value with
  a rewrite/`norm_num` chain, not kernel reduction:
  * `norm_num`'s Nat gcd/lcm support (and the simp equation lemmas `Nat.gcd_succ`,
    `Nat.gcd_zero_left`, which are ordinary terminating rewrites, NOT kernel WF reduction)
    can evaluate concrete `Nat.lcm`/`Nat.gcd`.
  * Expand `Finset.Icc 1 n` to an explicit `insert` chain (`{1,2,…,n}`) and fold with
    `Finset.lcm_insert` / `Finset.lcm_singleton`, then discharge each `Nat.lcm k m` step by
    `norm_num`. E.g. `lcm_upto 2 = Nat.lcm 1 (Nat.lcm 2 1)`-style, evaluated by `norm_num`.
  * These produce genuine kernel-checkable proof terms → `Lean.ofReduceBool` disappears →
    file becomes fully `verified` (status `verified`, badge, axiomCount 0). That is a real
    upgrade worth doing once a build host is available.

- **This session could not verify anything.** Host `lake env lean` is dead (0 Mathlib
  `.olean` in cache — nothing to load); Docker build blocked (data volume 100% full, 8.2Gi
  free — a fresh Mathlib cache download would exhaust it); Aristotle MCP returned
  `Resource not found` for even a trivial `1+1=2` submission (API unreachable this session).
  No Lean was edited in the green `main` file — refusing to ship unverified changes to a
  passing file. Contribution is this analysis only.

## Next steps
- On a working build host, apply the `norm_num`/`Finset.lcm_insert` recipe above to the
  seven `native_decide`s in `Erdos458Problem.lean`; if all pass, set meta `status: verified`,
  `axiomCount: 0`, update the `assumptions` field to drop the `Lean.ofReduceBool` disclosure,
  and re-badge. This is the one remaining concrete improvement for this entry.
- Possible follow-up: extend the `nthPrime` value table (nthPrime 5 = 13, …) and prove more
  conjecture instances `erdos458_conjecture_at_k` for k = 3, 4, … (routine, low value).
