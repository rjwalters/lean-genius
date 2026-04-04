# partition-theorem-oq-04
## Glaisher Bijection Formalization — IN PROGRESS (sorries: dedup_bind + bijectivity)

**Status: IN PROGRESS** — Both round-trips proved. 2 sorries remain: dedup_bind identity + bijective packaging.

---

## Summary

`PartitionTheoremOQ04.lean` (~640 lines) formalizes the Glaisher bijection as a computable function:
- `glaisherFwdPart k`: k = 2^a × b (b odd) → 2^a copies of b
- `glaisherBwdStep b m`: binary expansion of count m → distinct parts
- **Both round-trip directions proved** (modulo standard multiset identity)

**Proved theorems (0 sorries)**:
- `glaisherFwdPart_sum`, `glaisherFwd_sum`: forward map preserves weight
- `glaisherBwdStep_sum`, `glaisherBwdStep_pow_two`: backward step properties
- `glaisherFwdPart_parts_odd`, `glaisherFwd_parts_odd`: forward produces odd parts
- `glaisherBwd_glaisherFwdPart`: backward(forward(k)) = {k}
- `glaisherBwdStep_add_pow_two`, `glaisherBwd_add_replicate`: additivity lemmas
- **`glaisherFwd_count_bit_zero`**: bit a of count b is 0 when 2^a*b ∉ t (KEY LEMMA)
- **`glaisherBwd_glaisherFwd`**: round-trip on distinct multisets (DIRECTION 1)
- `padicValNat_not_even`, `padicValNat_pow_mul`, `glaisherFwdPart_pow_mul`: helpers
- **`glaisherFwd_glaisherBwdStep_gen`**: strong induction key lemma (DIRECTION 2 core)
- **`glaisherFwd_glaisherBwd`**: round-trip on odd-part multisets (DIRECTION 2)

**Remaining sorries (2)**:
- `dedup_bind_replicate_count_eq`: `s.toFinset.val.bind (fun b => replicate (count b) b) = s`
- `glaisher_bijection_exists`: packaging as Function.Bijective (deferred)

**PR**: #9097

---

## Session Log

### Session 2026-04-03 (Session 1)
**Mode**: FRESH
**Outcome**: progress

**What Was Done**:
1. Created `PartitionTheoremOQ04.lean` (~255 lines) from scratch
2. Defined `glaisherFwdPart` and `glaisherFwd` using `padicValNat 2 k`
3. Defined `glaisherBwdStep b m` using well-founded recursion on `m/2`
4. Proved `glaisherFwdPart_sum`, `glaisherFwd_sum`, `glaisherBwdStep_sum`
5. Proved `oddPart_odd` via `padicValNat` multiplicativity chain
6. Proved `glaisherFwdPart_parts_odd`, `glaisherFwd_parts_odd`
7. Proved `glaisherBwdStep_pow_two` by induction on `a`
8. Added concrete examples via `native_decide`
9. Build succeeded: 0 errors, 3 sorry warnings (bijectivity)

**Key Lean Fixes**:
1. `termination_by m` (not `termination_by _ m => m`) for two-arg `(b m : ℕ)` form
2. Well-founded recursion opacity: `simp [glaisherBwdStep]` works via `cases m with | succ n => simp [...]`
3. `padicValNat.prime_pow_self` unknown; proved `padicValNat_two_pow` by induction using `padicValNat.mul`
4. `decide` fails for `padicValNat 2 2 = 1`; use `native_decide`
5. After `set a := padicValNat 2 k`, need explicit type annotation `have hdec : 2^a * m = k := padic_factorization`
6. `Multiset.map_congr rfl` returns `s.map f = s.map (fun k => k)`, not `= s`; need `simp`
7. `Nat.strong_induction_on` (not `Nat.strong_rec_on`)
8. `Even x` destructs to `x = c + c`; need `⟨c, by linarith⟩` to supply `2 ∣ x`

**Files Created**:
- `proofs/Proofs/PartitionTheoremOQ04.lean` (255 lines)

**Next Steps**:
1. Prove `glaisherBwd_glaisherFwdPart`:
   - `glaisherFwdPart k = replicate (2^a) b`
   - Need: `toFinset (replicate n b) = {b}` for n ≥ 1
   - Need: `count b (replicate n b) = n`
   - Then `glaisherBwdStep b (2^a) = {2^a * b} = {k}` via `glaisherBwdStep_pow_two`
2. Prove `glaisherBwd_glaisherFwd`: induction on s (Nodup), using single-part case

---

### Session 2026-04-03 (Session 2)
**Mode**: FRESH (continuation)
**Outcome**: progress — `glaisherBwd_glaisherFwd` proved

**What Was Done**:
1. Proved `glaisherBwdStep_add_pow_two`: glaisherBwdStep b (2^a + m) = {2^a * b} + glaisherBwdStep b m when bit a of m is 0
2. Proved `glaisherBwd_add_replicate`: additivity of backward map over replicate parts
3. Designed `glaisherFwd_count_bit_zero_aux`: induction on multiset, universally quantified over a and b
4. Proved `add_two_pow_lt_of_bit_zero`: arithmetic helper (adding 2^v is carry-free when bit v = 0)
5. Proved `glaisherFwd_count_bit_zero`: bit a of count b is 0 when 2^a*b ∉ t
6. Proved `glaisherBwd_glaisherFwd`: full round-trip — main theorem completed
7. Build succeeded: 0 errors, 1 sorry warning (glaisher_bijection_exists only)

**Key Lean Fixes**:
1. `Nat.pos_pow_of_pos` doesn't exist — use `(by positivity)` for `0 < 2^n`
2. After `set k := r / 2^v`, `linarith` can't unify `k` and `r/2^v`; fix: use `show` to unfold before `linarith`
3. `Nat.mod_nonneg` doesn't exist — for Nat, use `Nat.zero_le` explicitly in linarith
4. omega can't prove `k + 2 ≤ 2^(a-v)` from parity alone; needs `2^(a-v) % 2 = 0` added explicitly (`dvd_pow_self`)
5. `simp [glaisherFwdPart, ...]` with `set v` unfolds back to `padicValNat 2 j`; use explicit `rw [show ... from rfl]` instead
6. `padic_factorization ▸ h` invalid in term mode; convert to `rw [this] at h; exact h`
7. In `Multiset.count_replicate`, when `if_neg hjb` fails with `set v`, move `by_cases` before `set`

**Files Modified**:
- `proofs/Proofs/PartitionTheoremOQ04.lean` (255 → ~500 lines)

**Next Steps**:
1. (Optional) Prove `glaisher_bijection_exists` using the round-trip result + cardinality argument
2. Look for follow-up open questions (converses, variants, sharp bounds)

---

### Session 2026-04-03 (Session 3)
**Mode**: REVISIT (continuation of Session 2)
**Outcome**: progress — `glaisherFwd_glaisherBwd` proved (reverse round-trip)

**What Was Done**:
1. Proved `padicValNat_not_even`: odd b ≠ 0 → padicValNat 2 b = 0 (via `pow_dvd_pow` + `pow_padicValNat_dvd`)
2. Proved `padicValNat_pow_mul`: padicValNat 2 (2^j * b) = j for odd b (via `padicValNat.mul` + `padicValNat_two_pow`)
3. Proved `glaisherFwdPart_pow_mul`: glaisherFwdPart (2^j * b) = replicate (2^j) b
4. Proved `glaisherFwd_glaisherBwdStep_gen`: strong induction on m, generalized over j, showing
   `glaisherFwd (glaisherBwdStep (2^j*b) m) = replicate (2^j*m) b` for odd b ≠ 0
5. Proved `glaisherFwd_glaisherBwd`: forward undoes backward on odd-part multisets
   (depends on `dedup_bind_replicate_count_eq`, left as sorry)
6. Build succeeded: 0 errors, 2 sorry warnings

**Key Lean Fixes**:
1. `Multiset.cons_bind` doesn't match `{x} : Multiset ℕ`; use `Multiset.singleton_bind` instead
2. `Multiset.bind_bind` doesn't exist; prove associativity `(m.bind f).bind g = m.bind (fun a => ...)` by `Multiset.induction`
3. `padicValNat.eq_zero_iff` has three-way disjunction; easier to use `by_contra` + `pow_dvd_pow` + `pow_padicValNat_dvd`
4. Strong induction generalizing j: `induction m using Nat.strong_induction_on generalizing j`
5. Arithmetic: `2^j + 2^(j+1) * ((m+1)/2) = 2^j * (m+1)` proved by `ring` + `omega` for the `2*((m+1)/2) = m+1` step

**Files Modified**:
- `proofs/Proofs/PartitionTheoremOQ04.lean` (~500 → ~640 lines)

**Next Steps**:
1. Prove `dedup_bind_replicate_count_eq`: `s.toFinset.val.bind (fun b => replicate (count b) b) = s`
   - Approach: `ext a; simp [Multiset.count_bind, Multiset.count_replicate]`; then nodup-sum argument
   - Alternative: search Mathlib for `Multiset.toFinset_sum` or `Finsupp`-based reconstruction
2. Prove `glaisher_bijection_exists` once dedup_bind is done
3. Submit to Aristotle for automated proof search on remaining sorries

---

## Key Mathematical Insights

1. **Well-founded recursion opacity in Lean 4**: Functions recursing on `m/2` are not definitionally transparent. `simp [f]` on `f 0` works but on `f (n+1)` requires `cases` to expose the equation lemma.

2. **padicValNat multiplicativity** (`padicValNat.mul`): Key for `oddPart_odd`. Chain: `padicValNat 2 k = padicValNat 2 (2^a * m) = a + padicValNat 2 m`. Since this equals `a`, we get `padicValNat 2 m = 0`, i.e., m is odd.

3. **Backward step inverse**: `glaisherBwdStep b (2^a) = {2^a * b}` by induction on `a`:
   - Base: `glaisherBwdStep b 1 = {b}` (1 is odd)
   - Step: `2^(a+1)` is even; skip; recurse `glaisherBwdStep (2b) (2^a) = {2^a*(2b)} = {2^(a+1)*b}`

4. **`native_decide` required for padicValNat**: Kernel can't evaluate `padicValNat` (uses `Nat.find`).
