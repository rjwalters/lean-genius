# euler-totient-oq-02-oq-02-oq-01 — Carmichael λ(n) as the true universal exponent of (ℤ/nℤ)ˣ

## Summary

Parent `euler-totient-oq-02-oq-02` proved `φ(n)` is *a* universal exponent of the
unit group (order of every unit divides φ(n)). This leaf answers the parent's
**first stated open question**: formalize the Carmichael function
`λ(n) := Monoid.exponent (ZMod n)ˣ` as *the* (least) universal exponent and prove
the sharper arithmetic `a^λ(n) ≡ 1 (mod n)`.

## Session 2026-07-01 (Session 1, researcher-5) — FRESH — outcome: progress (UNVERIFIED, build-blocked)

### What I did
- Wrote a complete 184-line draft `proofs/Proofs/EulerTotientOQ02OQ02OQ01.lean`
  (11 theorems, 1 def, 0 sorries by construction).
- Structure:
  - `def carmichael n := Monoid.exponent (ZMod n)ˣ`
  - `carmichael_pow_eq_one` — universality (`Monoid.pow_exponent_eq_one`)
  - `orderOf_dvd_carmichael` — `Monoid.order_dvd_exponent`
  - `carmichael_dvd_of_forall_pow_eq_one` — minimality (`Monoid.exponent_dvd_of_forall_pow_eq_one`)
  - `carmichael_dvd_totient` — λ(n) ∣ φ(n) via `pow_card_eq_one` + `ZMod.card_units_eq_totient`
  - `carmichael_pos`, `euler_from_carmichael` (recovers parent's Euler)
  - `carmichael_isLeast` — packaged as `IsLeast {e | 0<e ∧ ∀a, a^e=1}`
  - `carmichael_modEq` — arithmetic Carmichael a^λ ≡ 1 [MOD n] via `ZMod.unitOfCoprime`
  - `carmichael_eight` (λ(8)=2 via `decide` + `Nat.dvd_prime`), `carmichael_lt_totient_eight` (2<4)

### Key findings / insights
- The honest formalization of the Carmichael function IS `Monoid.exponent (ZMod n)ˣ`
  — Mathlib has no named `Nat.carmichael`, but the group-exponent API gives
  universality + minimality for free.
- Strictness over Euler is witnessed at n=8: `(ZMod 8)ˣ ≅ ℤ/2×ℤ/2` has exponent 2,
  provable by kernel `decide` (0-axiom, NOT native_decide) since the unit group is
  a 4-element Fintype with DecidableEq. Keeps entry `Lean.ofReduceBool`-free.
- Positivity trick: λ(n) ∣ φ(n) with φ(n)>0 forces λ(n)≠0 (0∣m ↔ m=0), avoiding
  reliance on a `Monoid.exponent_pos` lemma whose name I was unsure of.

### BLOCKER (infrastructure, not math)
- Host disk at 99% (16 Gi free). `docker-build.sh` → `lake exe cache get` cannot
  unpack Mathlib oleans (~6–10 GB), failing with `unknown module prefix 'Mathlib'`.
- Heavy docker build reaped the git worktree TWICE mid-session (destroyed `.git`
  linkage). Real disk hogs: /private/tmp `vibesql_*_checkpoints` (24G+15G, NOT ours).
- Proof is therefore **UNVERIFIED**. Preserved on origin branch
  `research/carmichael-oq020201` (commit e4eb7bbde98, via git plumbing — no PR).

### Next steps (future session, once disk freed)
1. `git fetch origin research/carmichael-oq020201`, check out, run
   `./proofs/scripts/docker-build.sh Proofs.EulerTotientOQ02OQ02OQ01`.
2. Fix any Mathlib name mismatches. Highest-risk names to verify:
   - `Monoid.order_dvd_exponent` (maybe `Monoid.orderOf_dvd_exponent`)
   - `Monoid.pow_exponent_eq_one` (confirm it's unconditional)
   - `Monoid.exponent_dvd_of_forall_pow_eq_one`
   - `Units.val_pow_eq_pow_val`, `ZMod.coe_unitOfCoprime`, `pow_card_eq_one`
   - `Nat.totient_pos` (iff form), `Nat.dvd_prime`
3. Confirm `decide` over `(ZMod 8)ˣ` and `φ 8 = 4` by decide reduce in reasonable time.
4. `#print axioms` on all decls → confirm only propext/Classical.choice/Quot.sound.
5. Create gallery entry `src/data/proofs/euler-totient-oq-02-oq-02-oq-01/` (mirror
   parent meta.json), open the real research PR, set pool status → completed.

## Session 2026-07-01 (Session 2, researcher-6) — REVISIT — outcome: progress (STILL UNVERIFIED, build-blocked)

### What I did
- **Confirmed EVERY "highest-risk" Mathlib API name** the prior session flagged as
  uncertain (all exist in Mathlib 4.26.0, verified by grepping the vendored source):
  - `Monoid.pow_exponent_eq_one` (unconditional, `GroupTheory/Exponent.lean:148`)
  - `Monoid.order_dvd_exponent` (`:195`) — name is correct as written
  - `Monoid.exponent_dvd_iff_forall_pow_eq_one` (`:203`) + alias
    `exponent_dvd_of_forall_pow_eq_one` (`:221`)
  - `Group.exponent_dvd_card [Fintype G]` (`:516`) — **cleaner than the prior
    `pow_card_eq_one` route** for λ(n) ∣ φ(n)
  - `Monoid.exists_orderOf_eq_exponent (ExponentExists G)` (`:429`, `[CommMonoid]`)
    — the attainment / primitive-λ-root theorem (a genuinely nice addition)
  - `Monoid.pow_eq_mod_exponent` (`:156`) — sharp exponent reduction
  - `ExponentExists.exponent_pos` (`:118`), `ExponentExists.of_finite`
  - `ZMod.isUnit_iff_coprime`, `ZMod.unitOfCoprime`, `ZMod.coe_unitOfCoprime`,
    `Units.val_pow_eq_pow_val`, `ZMod.card_units_eq_totient`, `ZMod.natCast_eq_natCast_iff` — all present
- **KEY DISCOVERY: Mathlib already ships the Carmichael function** as
  `ArithmeticFunction.Carmichael` (`Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean`,
  Snir Broshi, 2025) with `carmichael_eq_exponent`, `pow_carmichael`,
  `carmichael_dvd_totient`, `carmichael_mul`/`_lcm`, prime-power values, and
  `IsCyclic`/cyclic-units lemmas (`ZMod.isCyclic_units_prime`,
  `ZMod.not_isCyclic_units_eight`, `IsCyclic.iff_exponent_eq_card`). The prior
  session's "Mathlib has no named `Nat.carmichael`" is technically right (it's
  `ArithmeticFunction.Carmichael`, not `Nat.`) but the function EXISTS — so the
  entry's value is NOT re-deriving λ=exponent/λ∣φ but the *characterisation* layer.
- **Wrote a richer 229-line alternative** at `proofs/Proofs/EulerTotientOQ02OQ02OQ01.lean`
  (main checkout, untracked; backup `/tmp/r6-carmichael-improved.lean`). Built on
  Mathlib's `ArithmeticFunction.Carmichael` (no redundant local def). Adds beyond the
  184-line branch version:
  - `carmichael_dvd_iff` — full **iff** characterisation (universal exponents = multiples of λ)
  - `carmichael_isLeast_universal` — `IsLeast` packaging
  - `carmichael_eq_totient_iff_isCyclic` — **the boundary theorem** λ(n)=φ(n) ⟺ (ℤ/nℤ)ˣ cyclic
  - `carmichael_lt_totient_of_not_isCyclic` — strictness off the cyclic locus
  - `carmichael_prime` (=φ(p)) proved via cyclic-units, and `carmichael_eight` via
    Mathlib's `carmichael_two_pow_of_ne_two` (no `decide` needed for the value)
  - `modEq_one_iff_cast_pow` ModEq⇄ZMod bridge; `pow_mod_carmichael_modEq`

### BLOCKER (evolved: cache corruption + concurrent-agent races, not just disk)
- Fixed one real issue: docker `lake build` got `permission denied (code 13)` writing
  `*.olean.private.hash` into the host mathlib build dir. **Root cause: `@` extended
  attributes / ACLs** on those files (from the corrupted cache extraction). Fix that
  WORKS: `chmod -RN proofs/.lake/packages/mathlib/.lake/build/lib && xattr -rc <same>`.
  After this the build compiled **all 7743 deps and reached our file**.
- Then two fatal environmental failures, NOT proof errors:
  1. Our file crashed with `Lean exited with code 135` (SIGBUS) after a full 265 s
     elaboration — mmap under cgroup memory pressure (3 *other* `lean-build` docker
     containers running concurrently, 96 GB host contended, disk 98%).
  2. Retry failed with `failed to open .../aesop/.lake/build/lib/lean/Aesop/Tree/Data.olean`
     — a shared dep olean **went missing mid-run**: concurrent agents' `lake build`s
     race on the same host `.lake` (delegated mount), deleting/rebuilding each other's oleans.
- Did NOT force a full Mathlib rebuild (would risk 100% disk → host corruption per
  CLAUDE.md). Proof remains **UNVERIFIED**.

### Recommendation for next session
- Build when **no other `lean-build` containers are running** (`docker ps | grep lean-build`)
  and disk has headroom. Apply the `chmod -RN` + `xattr -rc` fix first if hash-write
  perms recur. The 229-line version is the better starting point (richer, uses Mathlib's
  Carmichael); the 184-line branch commit is the fallback. All API names are pre-verified,
  so a clean build should be close to first-try.
- The draft gallery `meta.json` in worktree `/Users/rwalters/lg-wt-carmichael` claims
  `status: "verified"` — **that claim is false until a build succeeds**; do not push it.
