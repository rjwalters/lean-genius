/-
DRAFT — UNVERIFIED (researcher-6, 2026-07-01). NOT built this session: the shared
docker `.lake/build` cache volume was contended by 5–7 concurrent `lean-build`
containers all session (SIGBUS risk), so this could not be compiled. Do NOT copy into
`proofs/Proofs/` or change gallery meta to `verified` until this compiles cleanly via
`./proofs/scripts/docker-build.sh Proofs.BurnsideCounting` with an EMPTY build queue.

Goal: replace the two `native_decide` calls in `proofs/Proofs/BurnsideCounting.lean`
(`fixed_point_sum_binary_4`, `binary_necklaces_4`) with kernel-checked proofs, removing
the `Lean.ofReduceBool` assumption and upgrading the entry from `axiomatized` to `verified`.

Two routes are sketched. Route A (quick) is preferred IF kernel `decide` handles the
16-element `Fin 4 → Fin 2` enumeration; Route B (bijection) is the fallback that reuses
the file's already-proved count lemmas and does not depend on `decide` performance.

Names/lemmas confirmed present in vendored Mathlib (see ../knowledge.md).
-/

-- ===========================================================================
-- ROUTE A (quick): try kernel `decide` for the finite counts, additive Burnside
-- for the necklace count.  Drop-in replacements for the two theorems.
-- ===========================================================================

-- theorem fixed_point_sum_binary_4 :
--     Fintype.card { c : Coloring 4 2 // IsFixedByRotation 0 c } +
--     Fintype.card { c : Coloring 4 2 // IsFixedByRotation 1 c } +
--     Fintype.card { c : Coloring 4 2 // IsFixedByRotation 2 c } +
--     Fintype.card { c : Coloring 4 2 // IsFixedByRotation 3 c } = 24 := by
--   decide   -- replaces `native_decide`; only valid if the kernel enumeration is feasible

-- theorem binary_necklaces_4 :
--     @Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2) = 6 := by
--   -- additive Burnside: ∑ a, card (fixedBy X a) = card (orbitRel.Quotient) * card G
--   have hb := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (ZMod 4) (Coloring 4 2)
--   -- Each `AddAction.fixedBy (Coloring 4 2) r` is the subtype `{c // IsFixedByRotation r c}`
--   -- because `AddAction.mem_fixedBy` is `Iff.rfl` and `IsFixedByRotation r c := r +ᵥ c = c`.
--   -- Rewrite the sum over `ZMod 4 ≡ Fin 4` with `Fin.sum_univ_four`, use `fixed_point_sum_binary_4`
--   -- to get LHS = 24, and `ZMod.card 4` to get `card (ZMod 4) = 4`; then `omega`.
--   -- (Fintype-instance mismatch on the quotient is closed by `Subsingleton.elim`/`Fintype.card_eq`.)
--   sorry

-- ===========================================================================
-- ROUTE B (fallback, decide-independent): characterize each fixed-point set and
-- reuse the file's proved bijection lemmas, then additive Burnside as in Route A.
-- Insert AFTER `period2_count` and BEFORE `fixed_point_sum_binary_4`.
-- ===========================================================================

-- /-- Per-index evaluation of a rotation on `Coloring 4 2`. -/
-- lemma rotate_eval (r : ZMod 4) (c : Coloring 4 2) (i : Fin 4) :
--     (r +ᵥ c) i = c ⟨(i.val + 4 - r.val) % 4, Nat.mod_lt _ (by norm_num)⟩ := by
--   show rotateColoring 4 2 r c i = _
--   unfold rotateColoring
--   simp only [Nat.mod_eq_of_lt (ZMod.val_lt r)]

-- /-- Rotation by 1 fixes exactly the constant colorings. -/
-- theorem isFixedByRotation_one_iff (c : Coloring 4 2) :
--     IsFixedByRotation (1 : ZMod 4) c ↔ IsConstant c := by
--   have hv : (1 : ZMod 4).val = 1 := by decide
--   unfold IsFixedByRotation
--   rw [funext_iff]
--   constructor
--   · intro h i j
--     have e0 := h 0; have e1 := h 1; have e2 := h 2; have e3 := h 3
--     rw [rotate_eval, hv] at e0 e1 e2 e3
--     -- e1 : c 0 = c 1, e2 : c 1 = c 2, e3 : c 2 = c 3 (indices reduce definitionally)
--     have h01 : c 0 = c 1 := e1
--     have h12 : c 1 = c 2 := e2
--     have h23 : c 2 = c 3 := e3
--     have key : ∀ k : Fin 4, c k = c 0 := by
--       intro k; fin_cases k
--       · rfl
--       · exact h01.symm
--       · exact (h12.symm.trans h01.symm)
--       · exact (h23.symm.trans (h12.symm.trans h01.symm))
--     rw [key i, key j]
--   · intro h i
--     rw [rotate_eval, hv]; exact h _ i

-- /-- Rotation by 3 also fixes exactly the constant colorings (same as rotation by 1). -/
-- theorem isFixedByRotation_three_iff (c : Coloring 4 2) :
--     IsFixedByRotation (3 : ZMod 4) c ↔ IsConstant c := by
--   -- analogous to `isFixedByRotation_one_iff` with `(3 : ZMod 4).val = 3`;
--   -- adjacency chain c3=c(3+3 mod4)=c2, etc.
--   sorry

-- /-- Rotation by 2 fixes exactly the period-2 colorings. -/
-- theorem isFixedByRotation_two_iff (c : Coloring 4 2) :
--     IsFixedByRotation (2 : ZMod 4) c ↔ HasPeriod2 c := by
--   -- `(2 : ZMod 4).val = 2`; c(i) = c(i+2 mod 4) ⟺ c0=c2 ∧ c1=c3 = HasPeriod2.
--   sorry

-- Then, with the four characterizations, each count reuses an existing lemma via
-- `Fintype.card_congr (Equiv.subtypeEquivRight ·)`:
--   card {c // IsFixedByRotation 0 c} = 16  (Equiv.subtypeUnivEquiv; 0 +ᵥ c = c by zero_vadd)
--   card {c // IsFixedByRotation 1 c} = 2   (subtypeEquivRight isFixedByRotation_one_iff; constant_4_2)
--   card {c // IsFixedByRotation 2 c} = 4   (subtypeEquivRight isFixedByRotation_two_iff; period2_count)
--   card {c // IsFixedByRotation 3 c} = 2   (subtypeEquivRight isFixedByRotation_three_iff; constant_4_2)
-- giving `fixed_point_sum_binary_4 = 24` with no `native_decide`, and `binary_necklaces_4`
-- via the additive-Burnside chain of Route A.
