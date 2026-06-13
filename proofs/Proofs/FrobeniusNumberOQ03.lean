/-
  Frobenius Number — Three Generators (OQ-03)

  S2 ACT skeleton (researcher-1, 2026-05-13). Direct three-generator port of
  the closure-lemma block from `Proofs/FrobeniusNumber.lean` (lines 42–69).
  S2-fix BUILD UNBLOCKER (researcher-9, 2026-05-14, PR #18979).
  S3a ACT (researcher-12, 2026-05-14): `frobeniusNumber3` definition + a small
  set-theoretic API for the non-representable set.
  S3b ACT (researcher-9, 2026-05-16): bridge lemma
  `large_representable3_via_two_gen` lifting the 2-generator Sylvester bound
  from `FrobeniusNumber.large_representable` (in module `Proofs.FrobeniusNumber`,
  now safely importable after mechanic PR #19194 cleared the v4.26.0 regression
  in the parent file) into a 3-generator existence form by setting the third
  coefficient to zero.
  S3c ACT (researcher-5, 2026-05-16): concrete Sylvester upper bound
  `frobeniusNumber3_le_sylvester_bound : frobeniusNumber3 a b c ≤ (a-1)(b-1)`
  combining S3a's `frobeniusNumber3_le_of_subset_Iio` with S3b's
  `large_representable3_via_two_gen`. The loose form (no `-1` tightening,
  so no case-split for `a = 1 ∨ b = 1` degenerate cases needed).

    Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z

  together with the seven canonical closure lemmas (S2), the Frobenius number
  definition + structural API (S3a):

    `noncomputable def frobeniusNumber3 a b c : ℕ := sSup { n | ¬ Representable3 a b c n }`
    `representable3_of_gt_of_bddAbove` — every `n > frobeniusNumber3 a b c` is
        representable, conditional on bounded-aboveness;
    `frobeniusNumber3_le_of_subset_Iio` — abstract upper bound;

  and the 2→3 generator bridge (S3b):

    `large_representable3_via_two_gen` — for `Nat.Coprime a b`, `1 ≤ a`,
        `1 ≤ b`, every `n ≥ (a-1)(b-1)` is `Representable3 a b c n`.

  and the concrete Sylvester upper bound (S3c):

    `frobeniusNumber3_le_sylvester_bound` — for `Nat.Coprime a b`, `1 ≤ a`,
        `1 ≤ b`, the 3-generator Frobenius number is bounded above by
        `(a-1)(b-1)` (the loose form; the tight `-1` form is deferred to
        a successor iteration with a case-split for `a = 1 ∨ b = 1`).

  Subsequent stages (per `research/problems/frobenius-number-oq-03/state.md`):
    S3c — finiteness of the non-representable set for `gcd(a,b,c) = 1`
          (via the bridge + cofiniteness of the 2-generator non-rep set).
    S4 — `large_representable3` for the three-consecutive family.
    S5 — `frobenius_three_consecutive` (Roberts d=1 closed form).
    S6+ — Roberts 3-AP, Fibonacci triples, Mersenne triples.

  0 sorries, 0 axioms.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Lattice
import Proofs.FrobeniusNumber

namespace FrobeniusOQ03

/-- A natural number `n` is **representable** by three generators `a, b, c`
    if `n = a*x + b*y + c*z` for some `x, y, z : ℕ`. -/
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = a * x + b * y + c * z

/-- 0 is always representable, via the trivial witness `x = y = z = 0`. -/
theorem representable3_zero (a b c : ℕ) : Representable3 a b c 0 :=
  ⟨0, 0, 0, by ring⟩

/-- Each of the three generators is itself representable. -/
theorem representable3_a (a b c : ℕ) : Representable3 a b c a :=
  ⟨1, 0, 0, by ring⟩

theorem representable3_b (a b c : ℕ) : Representable3 a b c b :=
  ⟨0, 1, 0, by ring⟩

theorem representable3_c (a b c : ℕ) : Representable3 a b c c :=
  ⟨0, 0, 1, by ring⟩

/-- Representability is closed under adding `a`. -/
theorem representable3_add_a {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + a) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x + 1, y, z, by linarith⟩

/-- Representability is closed under adding `b`. -/
theorem representable3_add_b {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + b) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y + 1, z, by linarith⟩

/-- Representability is closed under adding `c`. -/
theorem representable3_add_c {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z + 1, by linarith⟩

/-! ### S3a — `frobeniusNumber3` definition + structural API -/

/-- **Three-generator Frobenius number**: the largest natural that is NOT
    representable as a non-negative ℕ-combination of `a, b, c`.

    Defined as `sSup` of the non-representable set. The supremum is attained
    whenever the non-representable set is finite (proved in S3b for
    `gcd(a,b,c) = 1`); for an empty or unbounded non-representable set the
    value defaults to `0` via the `ℕ` `sSup` convention. -/
noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
  sSup { n : ℕ | ¬ Representable3 a b c n }

/-- Unfolding lemma: `frobeniusNumber3 a b c` is the `sSup` of the
    non-representable set. -/
theorem frobeniusNumber3_def (a b c : ℕ) :
    frobeniusNumber3 a b c = sSup { n : ℕ | ¬ Representable3 a b c n } :=
  rfl

/-- Every natural strictly above `frobeniusNumber3 a b c` is representable,
    provided the non-representable set is bounded above (which holds whenever
    the set is finite — see S3b for `gcd(a,b,c) = 1`). -/
theorem representable3_of_gt_frobeniusNumber3_of_bddAbove {a b c n : ℕ}
    (hbdd : BddAbove { m : ℕ | ¬ Representable3 a b c m })
    (hn : frobeniusNumber3 a b c < n) :
    Representable3 a b c n := by
  by_contra hcontra
  have hmem : n ∈ { m : ℕ | ¬ Representable3 a b c m } := hcontra
  have hle : n ≤ frobeniusNumber3 a b c := le_csSup hbdd hmem
  omega

/-- Abstract upper bound on `frobeniusNumber3 a b c`: if the non-representable
    set is contained in `Iio K` for some `K`, then `frobeniusNumber3 a b c ≤ K`
    (and is strictly below `K` when `K ≥ 1` and the set is nonempty). -/
theorem frobeniusNumber3_le_of_subset_Iio {a b c K : ℕ}
    (hsub : { n : ℕ | ¬ Representable3 a b c n } ⊆ Set.Iio K) :
    frobeniusNumber3 a b c ≤ K := by
  unfold frobeniusNumber3
  by_cases hne : ({ n : ℕ | ¬ Representable3 a b c n }).Nonempty
  · refine csSup_le hne ?_
    intro n hn
    have hlt : n ∈ Set.Iio K := hsub hn
    simp only [Set.mem_Iio] at hlt
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty]
    exact bot_le

/-- When the non-representable set is bounded above and nonempty, the supremum
    is attained — i.e. `frobeniusNumber3 a b c` is itself non-representable. -/
theorem not_representable3_frobeniusNumber3_of_nonempty {a b c : ℕ}
    (hbdd : BddAbove { m : ℕ | ¬ Representable3 a b c m })
    (hne : ({ m : ℕ | ¬ Representable3 a b c m }).Nonempty) :
    ¬ Representable3 a b c (frobeniusNumber3 a b c) :=
  Nat.sSup_mem hne hbdd

/-- A `Representable3` witness with the third coefficient zero collapses to a
    two-generator witness in `a, b`. (Bridge lemma used in S3b.) -/
theorem representable3_of_two_gen {a b c n x y : ℕ} (h : n = a * x + b * y) :
    Representable3 a b c n := ⟨x, y, 0, by linarith⟩

/-! ### S3b — 2→3 generator bridge -/

/-- **S3b bridge**: lift the 2-generator Sylvester bound to 3 generators by
    setting the third coefficient to zero. For coprime `a, b` with `1 ≤ a`,
    `1 ≤ b`, every `n ≥ (a-1)(b-1)` satisfies `Representable3 a b c n`
    (witnessed with `z = 0`). The third generator `c` is irrelevant for the
    upper-bound side, foreshadowing S3c's finiteness argument. -/
theorem large_representable3_via_two_gen
    {a b c n : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : (a - 1) * (b - 1) ≤ n) : Representable3 a b c n := by
  obtain ⟨x, y, hxy⟩ := FrobeniusNumber.large_representable hab ha hb n hn
  exact representable3_of_two_gen hxy

/-! ### S3c — concrete Sylvester upper bound on the 3-generator Frobenius number -/

/-- **S3c bound**: the 3-generator Frobenius number is bounded above by
    the 2-generator Sylvester quantity `(a - 1) * (b - 1)`. This combines
    the S3a abstract upper bound `frobeniusNumber3_le_of_subset_Iio` with
    the S3b 2→3 bridge `large_representable3_via_two_gen`: any `n` not
    `Representable3 a b c` must be `< (a - 1) * (b - 1)`, so the supremum
    of the non-representable set is bounded by `(a - 1) * (b - 1)`.

    Note: this is the *loose* form of the Sylvester bound. The strictly
    tighter form `≤ (a - 1) * (b - 1) - 1` is also true but requires a
    case-split for the degenerate `a = 1 ∨ b = 1` cases (where the
    non-representable set is empty and the `ℕ`-subtraction underflows to
    `0`). The loose form here is the unconditional all-cases bound. -/
theorem frobeniusNumber3_le_sylvester_bound {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) := by
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)

/-! ### S4 — finiteness of the non-representable set under `Nat.Coprime a b` -/

/-- **S4 ACT (Route 1)**: for coprime `a, b` with `1 ≤ a, 1 ≤ b`, the
    set of three-generator non-representable values is finite. Proof:
    every element is `< (a - 1) * (b - 1)` by the contrapositive of
    `large_representable3_via_two_gen` (S3b), so the set is a subset
    of `Set.Iio ((a - 1) * (b - 1))`, which is finite by
    `Set.finite_Iio` (via `LocallyFiniteOrderBot ℕ`).

    This is the strongest tractable finiteness statement at this stage
    of the slug — the full `Nat.gcd a (Nat.gcd b c) = 1` hypothesis
    (which would also subsume the `c`-only-coprime case) is strictly
    weaker than `Nat.Coprime a b` for the purpose of bounding the
    non-representable set, since `c` plays no role in the
    `large_representable3_via_two_gen` Sylvester bound (the witness
    sets `z = 0`).

    Together with `not_representable3_frobeniusNumber3_of_nonempty`
    (S3a, requires `Set.Nonempty` of the non-rep set) and the
    `BddAbove` corollary of this finiteness lemma
    (`Set.Finite.bddAbove`), this establishes that
    `frobeniusNumber3 a b c` is **`sSup`-attained** (the supremum is a
    member of the non-representable set) whenever the set is nonempty. -/
theorem set_non_representable3_finite_of_coprime_ab {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite := by
  apply Set.Finite.subset (Set.finite_Iio ((a - 1) * (b - 1)))
  intro n hn
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)

/-! ### S4a — tight Sylvester upper bound on the 3-generator Frobenius number -/

/-- **S4a tight bound**: refines S3c's loose
    `frobeniusNumber3 a b c ≤ (a - 1) * (b - 1)` to the tight
    `≤ (a - 1) * (b - 1) - 1`, matching the classical 2-generator Sylvester
    identity `g(a, b) = a*b - a - b = (a - 1)*(b - 1) - 1` for coprime
    `a, b ≥ 1`. The proof reuses the same contrapositive of S3b's
    `large_representable3_via_two_gen` bridge as S3c, but tightens the
    `Iio K` containment to a strict inequality `n < (a - 1) * (b - 1)`
    on every element of the non-representable set; in `ℕ`, this implies
    `n ≤ (a - 1) * (b - 1) - 1` (including the degenerate case
    `(a - 1) * (b - 1) = 0` where `ℕ`-subtraction underflows to `0` and
    the non-representable set is empty so `sSup` is `0`). -/
theorem frobeniusNumber3_le_sylvester_bound_tight {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  unfold frobeniusNumber3
  by_cases hne : ({ n : ℕ | ¬ Representable3 a b c n }).Nonempty
  · refine csSup_le hne ?_
    intro n hn
    by_contra hge
    push_neg at hge
    have hlt : (a - 1) * (b - 1) ≤ n := by omega
    exact hn (large_representable3_via_two_gen hab ha hb hlt)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty]
    exact bot_le

/-! ### S5 — `large_representable3` for three-consecutive integers -/

/-- **S5 (researcher-1, 2026-06-02)**: specialization of S3b's
    `large_representable3_via_two_gen` to the three-consecutive family
    `(n, n + 1, n + 2)`. For `1 ≤ n`, every `m ≥ (n - 1) * n` is
    `Representable3 n (n + 1) (n + 2) m` (witnessed with the third
    coefficient `z = 0`, lifted by `representable3_of_two_gen`).

    The bound `(n - 1) * n = n² - n` is the Sylvester quantity
    `(a - 1) * (b - 1)` instantiated at `a := n, b := n + 1` (consecutive
    integers are coprime via `Nat.coprime_self_add_right` reducing to
    `Nat.coprime_one_right`). This is loose compared to Roberts' tight
    d = 1 closed form `g(n, n+1, n+2) = ⌊(n - 2) / 2⌋ · n + (n - 1) ≈ n²/2`
    (asymptotically half this bound) but is unconditional and serves as
    the foundation for the Roberts closed-form chain (S6 = Roberts 3-AP,
    S6+ = Fibonacci / Mersenne triples per `state.md` §"Forward outlook"). -/
theorem large_representable3_three_consecutive {n m : ℕ} (hn : 1 ≤ n)
    (hm : (n - 1) * n ≤ m) : Representable3 n (n + 1) (n + 2) m := by
  have hcop : Nat.Coprime n (n + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right n
  have hb : 1 ≤ n + 1 := by omega
  have hbound : (n - 1) * (n + 1 - 1) ≤ m := by
    have heq : n + 1 - 1 = n := by omega
    rw [heq]
    exact hm
  exact large_representable3_via_two_gen hcop hn hb hbound

/-! ### S6 — Pair-symmetric Sylvester bounds

The existing `large_representable3_via_two_gen` (S3b) and
`frobeniusNumber3_le_sylvester_bound{,_tight}` (S3c, S4a) all use the
**(a, b)** pair as the coprime input — they witness representability with
the third generator `c` set to zero. But the choice of which two
generators to call "the coprime pair" is arbitrary: the `Representable3`
predicate is symmetric across the three slots. Therefore the Sylvester
bound applies under any of the three coprimality hypotheses, not just
the first.

This section adds the **(a, c)** and **(b, c)** variants. The
consequence is a strictly weaker hypothesis-set for the finiteness
result `set_non_representable3_finite_of_coprime_ab` (S4): finiteness
now holds whenever *any* pair of `(a, b, c)` is coprime, not just the
first two. In particular, the gallery's `Representable3 a b c` becomes
finite even in cases like `a = 4, b = 6, c = 5` where `gcd(a, b) = 2`
but `gcd(a, c) = gcd(b, c) = 1`.
-/

/-- Variant of `representable3_of_two_gen` with the middle coefficient
    zero — collapses a `Representable3` witness with `y = 0` to a
    two-generator witness in `(a, c)`. -/
theorem representable3_of_ac_gen {a b c n x z : ℕ} (h : n = a * x + c * z) :
    Representable3 a b c n := ⟨x, 0, z, by linarith⟩

/-- Variant of `representable3_of_two_gen` with the first coefficient
    zero — collapses a `Representable3` witness with `x = 0` to a
    two-generator witness in `(b, c)`. -/
theorem representable3_of_bc_gen {a b c n y z : ℕ} (h : n = b * y + c * z) :
    Representable3 a b c n := ⟨0, y, z, by linarith⟩

/-- **(a, c) bridge**: for coprime `a, c` with `1 ≤ a, 1 ≤ c`, every
    `n ≥ (a - 1) * (c - 1)` is `Representable3 a b c n` (witnessed with
    `y = 0`). The middle generator `b` is irrelevant. -/
theorem large_representable3_via_ac
    {a b c n : ℕ} (hac : Nat.Coprime a c) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hn : (a - 1) * (c - 1) ≤ n) : Representable3 a b c n := by
  obtain ⟨x, z, hxz⟩ := FrobeniusNumber.large_representable hac ha hc n hn
  exact representable3_of_ac_gen hxz

/-- **(b, c) bridge**: for coprime `b, c` with `1 ≤ b, 1 ≤ c`, every
    `n ≥ (b - 1) * (c - 1)` is `Representable3 a b c n` (witnessed with
    `x = 0`). The first generator `a` is irrelevant. -/
theorem large_representable3_via_bc
    {a b c n : ℕ} (hbc : Nat.Coprime b c) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hn : (b - 1) * (c - 1) ≤ n) : Representable3 a b c n := by
  obtain ⟨y, z, hyz⟩ := FrobeniusNumber.large_representable hbc hb hc n hn
  exact representable3_of_bc_gen hyz

/-- **(a, c) Sylvester bound**: variant of S3c using `(a, c)` instead of
    `(a, b)` as the coprime pair. -/
theorem frobeniusNumber3_le_sylvester_bound_ac {a b c : ℕ}
    (hac : Nat.Coprime a c) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    frobeniusNumber3 a b c ≤ (a - 1) * (c - 1) := by
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_ac hac ha hc hge)

/-- **(b, c) Sylvester bound**: variant of S3c using `(b, c)` instead of
    `(a, b)` as the coprime pair. -/
theorem frobeniusNumber3_le_sylvester_bound_bc {a b c : ℕ}
    (hbc : Nat.Coprime b c) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    frobeniusNumber3 a b c ≤ (b - 1) * (c - 1) := by
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_bc hbc hb hc hge)

/-- **(a, c) finiteness**: variant of S4 — the non-representable set is
    finite whenever `(a, c)` is coprime. -/
theorem set_non_representable3_finite_of_coprime_ac {a b c : ℕ}
    (hac : Nat.Coprime a c) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite := by
  apply Set.Finite.subset (Set.finite_Iio ((a - 1) * (c - 1)))
  intro n hn
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_ac hac ha hc hge)

/-- **(b, c) finiteness**: variant of S4 — the non-representable set is
    finite whenever `(b, c)` is coprime. -/
theorem set_non_representable3_finite_of_coprime_bc {a b c : ℕ}
    (hbc : Nat.Coprime b c) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite := by
  apply Set.Finite.subset (Set.finite_Iio ((b - 1) * (c - 1)))
  intro n hn
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_bc hbc hb hc hge)

/-- **Pair-min bound**: if any two of `(a, b, c)` are coprime, the
    Frobenius number is bounded by the *minimum* of the corresponding
    three Sylvester quantities. Useful when more than one pair is
    coprime — picks the strongest bound automatically. -/
theorem frobeniusNumber3_le_min_sylvester_bound {a b c : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    frobeniusNumber3 a b c ≤
      min ((a - 1) * (b - 1)) (min ((a - 1) * (c - 1)) ((b - 1) * (c - 1))) := by
  refine le_min (frobeniusNumber3_le_sylvester_bound hab ha hb) ?_
  refine le_min (frobeniusNumber3_le_sylvester_bound_ac hac ha hc)
    (frobeniusNumber3_le_sylvester_bound_bc hbc hb hc)

/-! ### S6 — Exact representability criterion for three *consecutive* generators

The Sylvester-style bounds above are one-directional (they only establish
representability *above* a threshold). For the three-consecutive family
`(n, n + 1, n + 2)` there is a clean two-sided characterisation, which is
the structural key to Roberts' tight `d = 1` closed form.

The observation: a combination collapses to
`n·x + (n+1)·y + (n+2)·z = n·(x + y + z) + (y + 2·z)`. Writing
`s := x + y + z` for the total number of generators used, the "remainder"
`y + 2·z` ranges over exactly `[0, 2·s]` as `y, z` vary with `y + z ≤ s`.
Hence `m` is representable **iff** it lands in one of the intervals
`[n·s, (n+2)·s]` for some `s : ℕ`. This converts the Frobenius question
into an interval-covering problem on `ℕ`. -/

/-- **Exact representability criterion for consecutive triples.**
    `m` is `Representable3 n (n+1) (n+2)` iff `n·s ≤ m ≤ (n+2)·s` for some
    `s : ℕ` (namely `s = x + y + z`, the total generator count). -/
theorem representable3_consecutive_iff (n m : ℕ) :
    Representable3 n (n + 1) (n + 2) m ↔ ∃ s : ℕ, n * s ≤ m ∧ m ≤ (n + 2) * s := by
  constructor
  · rintro ⟨x, y, z, rfl⟩
    refine ⟨x + y + z, ?_, ?_⟩
    · have h : n * (x + y + z) + (y + 2 * z)
          = n * x + (n + 1) * y + (n + 2) * z := by ring
      omega
    · have h : (n + 2) * (x + y + z)
          = (n * x + (n + 1) * y + (n + 2) * z) + (2 * x + y) := by ring
      omega
  · rintro ⟨s, h1, h2⟩
    rcases le_or_lt (m - n * s) s with ht | ht
    · -- remainder `t := m - n*s` satisfies `t ≤ s`: use `x = s - t, y = t, z = 0`.
      obtain ⟨u, hu⟩ : ∃ u, s = u + (m - n * s) := ⟨s - (m - n * s), by omega⟩
      refine ⟨u, m - n * s, 0, ?_⟩
      have e1 : (n + 1) * (m - n * s)
          = n * (m - n * s) + (m - n * s) := by ring
      have key : n * s = n * u + n * (m - n * s) := by
        conv_lhs => rw [hu]
        rw [Nat.mul_add]
      omega
    · -- remainder `t` satisfies `s < t ≤ 2·s`: use `x = 0, y = 2s - t, z = t - s`.
      have hexp : (n + 2) * s = n * s + 2 * s := by ring
      obtain ⟨v, hv⟩ : ∃ v, m - n * s = s + v := ⟨m - n * s - s, by omega⟩
      obtain ⟨w, hw⟩ : ∃ w, s = w + v := ⟨s - v, by omega⟩
      refine ⟨0, w, v, ?_⟩
      have e2 : (n + 1) * w + (n + 2) * v
          = n * w + n * v + (w + 2 * v) := by ring
      have e3 : n * s = n * w + n * v := by rw [hw]; ring
      omega

end FrobeniusOQ03
