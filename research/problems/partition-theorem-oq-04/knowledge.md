# partition-theorem-oq-04
## Glaisher Bijection Formalization — IN PROGRESS (sorries: bijectivity)

**Status: IN PROGRESS** — Core theorems proved. Bijectivity round-trip left as structured sorries.

---

## Summary

`PartitionTheoremOQ04.lean` (~500 lines) formalizes the Glaisher bijection as a computable function:
- `glaisherFwdPart k`: k = 2^a × b (b odd) → 2^a copies of b
- `glaisherBwdStep b m`: binary expansion of count m → distinct parts
- Core round-trip direction **`glaisherBwd_glaisherFwd`** proved (no sorry)

**Proved theorems (0 sorries)**:
- `glaisherFwdPart_sum`, `glaisherFwd_sum`: forward map preserves weight
- `glaisherBwdStep_sum`, `glaisherBwdStep_pow_two`: backward step properties
- `glaisherFwdPart_parts_odd`, `glaisherFwd_parts_odd`: forward produces odd parts
- `glaisherBwd_glaisherFwdPart`: backward(forward(k)) = {k}
- `glaisherBwdStep_add_pow_two`, `glaisherBwd_add_replicate`: additivity lemmas
- **`glaisherFwd_count_bit_zero`**: bit a of count b is 0 when 2^a*b ∉ t (KEY LEMMA)
- **`glaisherBwd_glaisherFwd`**: full round-trip on distinct multisets (MAIN RESULT)

**Remaining sorry**:
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

## Key Mathematical Insights

1. **Well-founded recursion opacity in Lean 4**: Functions recursing on `m/2` are not definitionally transparent. `simp [f]` on `f 0` works but on `f (n+1)` requires `cases` to expose the equation lemma.

2. **padicValNat multiplicativity** (`padicValNat.mul`): Key for `oddPart_odd`. Chain: `padicValNat 2 k = padicValNat 2 (2^a * m) = a + padicValNat 2 m`. Since this equals `a`, we get `padicValNat 2 m = 0`, i.e., m is odd.

3. **Backward step inverse**: `glaisherBwdStep b (2^a) = {2^a * b}` by induction on `a`:
   - Base: `glaisherBwdStep b 1 = {b}` (1 is odd)
   - Step: `2^(a+1)` is even; skip; recurse `glaisherBwdStep (2b) (2^a) = {2^a*(2b)} = {2^(a+1)*b}`

4. **`native_decide` required for padicValNat**: Kernel can't evaluate `padicValNat` (uses `Nat.find`).
