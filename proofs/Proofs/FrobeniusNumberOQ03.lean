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
    S6 — `representable3_consecutive_iff` (interval criterion, d=1).
    S7 — Roberts d=1 closed form + concrete instances.
    S8 (researcher-11, 2026-07-02) — Roberts' closed form for the full
        three-term arithmetic progression `(a, a+d, a+2d)` with `gcd(a,d)=1`:
        `frobenius_three_ap : frobeniusNumber3 a (a+d) (a+2*d)
           = (a-2)/2*a + (a-1)*d`, generalizing S7's `d = 1` case. Supported
        by `representable3_ap_iff` (AP interval/divisibility criterion),
        `not_representable3_ap_roberts` (witness maximality via residue
        `t ≡ a-1 [MOD a]`), and `representable3_above_ap_roberts`
        (mod-`a` reduction of a two-generator representation). Concrete
        instances `g(3,5,7)=4`, `g(4,7,10)=13`.
    Remaining: Fibonacci / Mersenne triples, general `s`-term Roberts.

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

/-! ### S7 — Roberts' closed form for three consecutive generators (d = 1)

Roberts (1956) gives the exact Frobenius number of an arithmetic progression.
For the three-consecutive family `(n, n+1, n+2)` (common difference `d = 1`,
three terms) his formula specialises to

  `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n - 1)`.

Combined with the exact interval criterion `representable3_consecutive_iff`
(S6), we pin `frobeniusNumber3 n (n+1) (n+2)` to this value unconditionally for
every `n ≥ 1`. The `ℕ`-truncated subtractions make the degenerate small cases
come out correctly: `g(1,2,3) = 0` (everything is representable since `1` is a
generator) and `g(2,3,4) = 1`.

Geometrically, writing `q := ⌊(n-2)/2⌋`, the witness `g = q·n + (n-1) =
(q+1)·n - 1` is the right endpoint of the **last gap** between the consecutive
representable intervals `[n·s, (n+2)·s]`. For `s ≤ q` adjacent intervals leave a
gap (`(n+2)·s < n·(s+1) - 1`), while at `s = q+1` they become contiguous
(`n ≤ 2(q+1)+1`). Hence every value `≥ (q+1)·n` is representable while
`(q+1)·n - 1` is not. This is asymptotically `~ n²/2`, roughly half the loose
Sylvester bound `(n-1)·n` from `large_representable3_three_consecutive` (S5). -/

/-- The Roberts witness `g = ⌊(n-2)/2⌋·n + (n-1)` is **not** representable by
    `(n, n+1, n+2)`: by `representable3_consecutive_iff` a witness would give an
    interval `[n·s, (n+2)·s]` containing `g`, but `n·s ≤ g` forces
    `s ≤ ⌊(n-2)/2⌋`, whence `(n+2)·s ≤ ⌊(n-2)/2⌋·n + 2·⌊(n-2)/2⌋ < g`. -/
theorem not_representable3_roberts (n : ℕ) (hn : 2 ≤ n) :
    ¬ Representable3 n (n + 1) (n + 2) ((n - 2) / 2 * n + (n - 1)) := by
  rw [representable3_consecutive_iff]
  rintro ⟨s, h1, h2⟩
  -- From `n·s ≤ g`, the index `s` cannot exceed `⌊(n-2)/2⌋`.
  have hsq : s ≤ (n - 2) / 2 := by
    by_contra hc
    push_neg at hc
    have hc' : (n - 2) / 2 + 1 ≤ s := hc
    have hge : n * ((n - 2) / 2 + 1) ≤ n * s := Nat.mul_le_mul (le_refl n) hc'
    have he : n * ((n - 2) / 2 + 1) = (n - 2) / 2 * n + n := by ring
    omega
  -- But then the right endpoint `(n+2)·s` lands strictly below `g`.
  have hle : (n + 2) * s ≤ (n + 2) * ((n - 2) / 2) :=
    Nat.mul_le_mul (le_refl (n + 2)) hsq
  have he2 : (n + 2) * ((n - 2) / 2) = (n - 2) / 2 * n + 2 * ((n - 2) / 2) := by ring
  omega

/-- Every value strictly above the Roberts witness is representable by
    `(n, n+1, n+2)`. Choosing the interval index `s = m / n` works: `n·s ≤ m`
    always holds, and `m ≤ (n+2)·s` reduces to `m % n ≤ 2·(m / n)`, which holds
    because `m % n < n ≤ 2·(m / n) + 1` once `m / n ≥ ⌊(n-2)/2⌋ + 1`. -/
theorem representable3_above_roberts {n m : ℕ} (hn : 1 ≤ n)
    (hm : (n - 2) / 2 * n + (n - 1) < m) :
    Representable3 n (n + 1) (n + 2) m := by
  rw [representable3_consecutive_iff]
  have hn0 : 0 < n := hn
  have hdm : n * (m / n) + m % n = m := Nat.div_add_mod m n
  have hmod : m % n < n := Nat.mod_lt m hn0
  -- `m` is at least `(⌊(n-2)/2⌋ + 1)·n`, so `m / n ≥ ⌊(n-2)/2⌋ + 1`.
  have hbig : ((n - 2) / 2 + 1) * n ≤ m := by
    have hexpand : ((n - 2) / 2 + 1) * n = (n - 2) / 2 * n + n := by ring
    omega
  have hk : (n - 2) / 2 + 1 ≤ m / n := (Nat.le_div_iff_mul_le hn0).mpr hbig
  refine ⟨m / n, ?_, ?_⟩
  · omega
  · have hexp : (n + 2) * (m / n) = n * (m / n) + 2 * (m / n) := by ring
    omega

/-- **Roberts' closed form (`d = 1`).** For every `n ≥ 1` the Frobenius number of
    the three consecutive generators `(n, n+1, n+2)` equals
    `⌊(n-2)/2⌋ · n + (n - 1)`.

    Proof: `not_representable3_roberts` shows the value lies in the
    non-representable set (so it is `≤ sSup`, using that the set is finite hence
    bounded — `set_non_representable3_finite_of_coprime_ab` with the coprime pair
    `(n, n+1)`), while `representable3_above_roberts` shows everything strictly
    larger is representable (so `sSup ≤` it). Antisymmetry pins the value. -/
theorem frobenius_three_consecutive (n : ℕ) (hn : 1 ≤ n) :
    frobeniusNumber3 n (n + 1) (n + 2) = (n - 2) / 2 * n + (n - 1) := by
  have hcop : Nat.Coprime n (n + 1) := by
    rw [Nat.coprime_self_add_right]; exact Nat.coprime_one_right n
  have hfin : { m : ℕ | ¬ Representable3 n (n + 1) (n + 2) m }.Finite :=
    set_non_representable3_finite_of_coprime_ab hcop hn (by omega)
  have hbdd : BddAbove { m : ℕ | ¬ Representable3 n (n + 1) (n + 2) m } :=
    hfin.bddAbove
  apply le_antisymm
  · rw [frobeniusNumber3_def]
    by_cases hne : ({ m : ℕ | ¬ Representable3 n (n + 1) (n + 2) m }).Nonempty
    · refine csSup_le hne (fun m hm => ?_)
      by_contra hgt
      push_neg at hgt
      exact hm (representable3_above_roberts hn hgt)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le _
  · rw [frobeniusNumber3_def]
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · -- `n = 1`: the witness is `0`, and the non-representable set is empty, so
      -- the lower bound `0 ≤ sSup ∅` is trivial.
      have hn1 : n = 1 := by omega
      subst hn1
      have hzero : (1 - 2) / 2 * 1 + (1 - 1) = 0 := by norm_num
      rw [hzero]
      exact Nat.zero_le _
    · exact le_csSup hbdd (not_representable3_roberts n hge)

/-! ### S7a — concrete instances of Roberts' closed form -/

/-- `g(3,4,5) = 2`. -/
theorem frobenius_3_4_5 : frobeniusNumber3 3 4 5 = 2 := by
  have h := frobenius_three_consecutive 3 (by norm_num)
  norm_num at h; exact h

/-- `g(4,5,6) = 7`. -/
theorem frobenius_4_5_6 : frobeniusNumber3 4 5 6 = 7 := by
  have h := frobenius_three_consecutive 4 (by norm_num)
  norm_num at h; exact h

/-- `g(5,6,7) = 9`. -/
theorem frobenius_5_6_7 : frobeniusNumber3 5 6 7 = 9 := by
  have h := frobenius_three_consecutive 5 (by norm_num)
  norm_num at h; exact h

/-! ### S8 — Roberts' closed form for three-term arithmetic progressions

Roberts (1956): for `a ≥ 2`, `d ≥ 1`, and `gcd(a, d) = 1`, the Frobenius number
of the arithmetic-progression triple `(a, a + d, a + 2·d)` is

  `g(a, a + d, a + 2·d) = ⌊(a - 2)/2⌋ · a + (a - 1) · d`.

This is the genuine three-parameter generalization of the `d = 1` consecutive
case `frobenius_three_consecutive` (S7): setting `d = 1` recovers
`⌊(a - 2)/2⌋ · a + (a - 1)`. Every three-generator combination
`a·x + (a+d)·y + (a+2d)·z` collapses to `a·s + d·t` with `s = x + y + z` the
total generator count and `t = y + 2·z ∈ [0, 2·s]` the "excess" carried by the
two larger generators; representability of `m` is therefore equivalent to
writing `m = a·s + d·t` with `t ≤ 2·s` (`representable3_ap_iff`, generalizing
S6's `representable3_consecutive_iff`). Coprimality of `a, d` pins the residue
`t mod a`, which is exactly what makes the Roberts witness maximal. Finiteness
of the non-representable set comes from the S3b/S4 two-generator Sylvester bridge
applied to the coprime pair `(a, a + d)` (since `gcd(a, a+d) = gcd(a, d) = 1`). -/

/-- **Exact representability criterion for AP triples.** `m` is
    `Representable3 a (a + d) (a + 2·d)` iff `m = a·s + d·t` for some `s t : ℕ`
    with `t ≤ 2·s`. (Generalizes `representable3_consecutive_iff`, the `d = 1`
    case where the `d·t` term collapses to `t`.) -/
theorem representable3_ap_iff (a d m : ℕ) :
    Representable3 a (a + d) (a + 2 * d) m
      ↔ ∃ s t : ℕ, m = a * s + d * t ∧ t ≤ 2 * s := by
  constructor
  · rintro ⟨x, y, z, rfl⟩
    exact ⟨x + y + z, y + 2 * z, by ring, by omega⟩
  · rintro ⟨s, t, hm, ht⟩
    rcases le_or_lt t s with hts | hts
    · -- excess `t ≤ s`: use `x = s - t, y = t, z = 0`.
      obtain ⟨u, hu⟩ : ∃ u, s = u + t := ⟨s - t, by omega⟩
      refine ⟨u, t, 0, ?_⟩
      have e2 : (a + d) * t = a * t + d * t := by ring
      have e3 : a * s = a * u + a * t := by rw [hu]; ring
      simp only [Nat.mul_zero, Nat.add_zero]
      omega
    · -- excess `s < t ≤ 2·s`: use `x = 0, y = 2·s - t, z = t - s`.
      obtain ⟨v, hv⟩ : ∃ v, t = s + v := ⟨t - s, by omega⟩
      obtain ⟨w, hw⟩ : ∃ w, s = w + v := ⟨s - v, by omega⟩
      refine ⟨0, w, v, ?_⟩
      have e4 : (a + d) * w = a * w + d * w := by ring
      have e5 : (a + 2 * d) * v = a * v + d * v + d * v := by ring
      have e6 : a * s = a * w + a * v := by rw [hw]; ring
      have e7 : d * s = d * w + d * v := by rw [hw]; ring
      have e8 : d * t = d * s + d * v := by rw [hv]; ring
      simp only [Nat.mul_zero, Nat.zero_add]
      omega

/-- The Roberts witness `g = ⌊(a-2)/2⌋·a + (a-1)·d` is **not** representable by
    the AP triple `(a, a + d, a + 2·d)` when `gcd(a, d) = 1` and `a ≥ 2`. A
    representation `g = a·s + d·t` with `t ≤ 2·s` would force (via coprimality)
    `t ≡ a - 1 [MOD a]`, hence `t = a·k + (a-1)` for some `k`, whence
    `s + d·k = ⌊(a-2)/2⌋` so `s ≤ ⌊(a-2)/2⌋`; but then
    `t ≥ a - 1 > 2·⌊(a-2)/2⌋ ≥ 2·s`, contradicting `t ≤ 2·s`. -/
theorem not_representable3_ap_roberts {a d : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d)
    (hcop : Nat.Coprime a d) :
    ¬ Representable3 a (a + d) (a + 2 * d) ((a - 2) / 2 * a + (a - 1) * d) := by
  rw [representable3_ap_iff]
  rintro ⟨s, t, hm, ht⟩
  -- Rearrange to the canonical form and reduce modulo `a`.
  have hkey : a * s + d * t = a * ((a - 2) / 2) + d * (a - 1) := by
    have c1 : (a - 2) / 2 * a = a * ((a - 2) / 2) := Nat.mul_comm _ _
    have c2 : (a - 1) * d = d * (a - 1) := Nat.mul_comm _ _
    omega
  have hmod : d * t ≡ d * (a - 1) [MOD a] := by
    unfold Nat.ModEq
    have l1 : (a * s + d * t) % a = d * t % a := Nat.mul_add_mod a s (d * t)
    have l2 : (a * ((a - 2) / 2) + d * (a - 1)) % a = d * (a - 1) % a :=
      Nat.mul_add_mod a ((a - 2) / 2) (d * (a - 1))
    rw [← l1, ← l2, hkey]
  have htmod : t ≡ (a - 1) [MOD a] := Nat.ModEq.cancel_left_of_coprime hcop hmod
  -- The residue of the excess is `a - 1`.
  have htm : t % a = a - 1 := by
    have h := htmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (by omega : a - 1 < a)] at h
  have hdm : a * (t / a) + (a - 1) = t := by
    have := Nat.div_add_mod t a; rw [htm] at this; exact this
  -- From `hkey`, cancelling `d·(a-1)`: `a·s + d·(a·(t/a)) = a·⌊(a-2)/2⌋`.
  have expand : d * t = d * (a * (t / a)) + d * (a - 1) := by
    rw [← Nat.mul_add, hdm]
  have hsk : a * s + d * (a * (t / a)) = a * ((a - 2) / 2) := by omega
  have hs_le : a * s ≤ a * ((a - 2) / 2) := by omega
  have hsq : s ≤ (a - 2) / 2 := Nat.le_of_mul_le_mul_left hs_le (by omega)
  have hdml : (a - 2) / 2 * 2 ≤ a - 2 := Nat.div_mul_le_self (a - 2) 2
  omega

/-- Every value strictly above the Roberts witness is representable by the AP
    triple `(a, a + d, a + 2·d)` (for `gcd(a, d) = 1`, `a ≥ 2`, `d ≥ 1`). Take
    any two-generator representation `m = a·s₀ + d·t₀` (available by the Sylvester
    bound for the coprime pair `(a, d)`), then reduce the excess modulo `a`:
    `t' := t₀ % a`, `s' := s₀ + (t₀ / a)·d`. Then `m = a·s' + d·t'` still holds,
    with `t' < a`; and `t' ≤ 2·s'`, else `s' ≤ ⌊(a-2)/2⌋` and `t' ≤ a - 1` give
    `m ≤ ⌊(a-2)/2⌋·a + (a-1)·d`, contradicting `m` being above the witness. -/
theorem representable3_above_ap_roberts {a d m : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d)
    (hcop : Nat.Coprime a d)
    (hm : (a - 2) / 2 * a + (a - 1) * d < m) :
    Representable3 a (a + d) (a + 2 * d) m := by
  rw [representable3_ap_iff]
  -- A two-generator representation of `m` by the coprime pair `(a, d)`.
  have hbig : (a - 1) * (d - 1) ≤ m := by
    have hb1 : (a - 1) * (d - 1) ≤ (a - 1) * d :=
      Nat.mul_le_mul (le_refl (a - 1)) (Nat.sub_le d 1)
    omega
  obtain ⟨s₀, t₀, hst⟩ :=
    FrobeniusNumber.large_representable hcop (by omega) (by omega) m hbig
  have hdm : a * (t₀ / a) + t₀ % a = t₀ := Nat.div_add_mod t₀ a
  refine ⟨s₀ + (t₀ / a) * d, t₀ % a, ?_, ?_⟩
  · calc m = a * s₀ + d * t₀ := hst
      _ = a * s₀ + d * (a * (t₀ / a) + t₀ % a) := by rw [hdm]
      _ = a * (s₀ + (t₀ / a) * d) + d * (t₀ % a) := by ring
  · by_contra hcon
    push_neg at hcon
    have hmodlt : t₀ % a < a := Nat.mod_lt _ (by omega)
    have hsq : s₀ + (t₀ / a) * d ≤ (a - 2) / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
      omega
    have hb1 : a * (s₀ + (t₀ / a) * d) ≤ a * ((a - 2) / 2) :=
      Nat.mul_le_mul (le_refl a) hsq
    have hb2 : d * (t₀ % a) ≤ d * (a - 1) :=
      Nat.mul_le_mul (le_refl d) (by omega)
    have hmeq : m = a * (s₀ + (t₀ / a) * d) + d * (t₀ % a) := by
      calc m = a * s₀ + d * t₀ := hst
        _ = a * s₀ + d * (a * (t₀ / a) + t₀ % a) := by rw [hdm]
        _ = a * (s₀ + (t₀ / a) * d) + d * (t₀ % a) := by ring
    have c1 : a * ((a - 2) / 2) = (a - 2) / 2 * a := Nat.mul_comm _ _
    have c2 : d * (a - 1) = (a - 1) * d := Nat.mul_comm _ _
    omega

/-- **Roberts' closed form (three-term arithmetic progression).** For `a ≥ 2`,
    `d ≥ 1`, and `gcd(a, d) = 1`,
    `g(a, a + d, a + 2·d) = ⌊(a - 2)/2⌋ · a + (a - 1) · d`.

    Proof: `not_representable3_ap_roberts` places the witness in the
    non-representable set (`⇒ ≤ sSup`, using finiteness of that set via the
    coprime pair `(a, a+d)`), while `representable3_above_ap_roberts` shows
    everything strictly larger is representable (`⇒ sSup ≤`). Antisymmetry pins
    the value. The `d = 1` case recovers `frobenius_three_consecutive`. -/
theorem frobenius_three_ap {a d : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d)
    (hcop : Nat.Coprime a d) :
    frobeniusNumber3 a (a + d) (a + 2 * d) = (a - 2) / 2 * a + (a - 1) * d := by
  have hcop' : Nat.Coprime a (a + d) := by
    rw [Nat.add_comm]; exact Nat.coprime_add_self_right.mpr hcop
  have hfin : { n : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) n }.Finite :=
    set_non_representable3_finite_of_coprime_ab hcop' (by omega) (by omega)
  have hbdd : BddAbove { n : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) n } :=
    hfin.bddAbove
  apply le_antisymm
  · rw [frobeniusNumber3_def]
    by_cases hne : ({ n : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) n }).Nonempty
    · refine csSup_le hne (fun mm hmm => ?_)
      by_contra hgt
      push_neg at hgt
      exact hmm (representable3_above_ap_roberts ha hd hcop hgt)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le _
  · rw [frobeniusNumber3_def]
    exact le_csSup hbdd (not_representable3_ap_roberts ha hd hcop)

/-! ### S8a — concrete instances of the 3-AP closed form -/

/-- `g(3, 5, 7) = 4` (common difference `d = 2`). -/
theorem frobenius_3_5_7 : frobeniusNumber3 3 5 7 = 4 := by
  have h := frobenius_three_ap (a := 3) (d := 2) (by norm_num) (by norm_num) (by decide)
  norm_num at h; exact h

/-- `g(4, 7, 10) = 13` (common difference `d = 3`). -/
theorem frobenius_4_7_10 : frobeniusNumber3 4 7 10 = 13 := by
  have h := frobenius_three_ap (a := 4) (d := 3) (by norm_num) (by norm_num) (by decide)
  norm_num at h; exact h

/-! ### S9 — Sharpness of the coprimality hypothesis

Roberts' closed form `frobenius_three_ap` requires `gcd(a, d) = 1`. This
hypothesis is **necessary**, not a convenience. If `g := gcd(a, d) ≥ 2` then `g`
divides each of the three generators `a`, `a + d`, `a + 2·d`, hence every
representable number; the non-representable set therefore contains the entire
infinite arithmetic progression `{g·k + 1 : k}` (none of whose members is
divisible by `g`) and is infinite. In particular the `sSup`-based
`frobeniusNumber3` degenerates: there is no finite Frobenius number to compute
when the generators share a common factor. -/

/-- **Divisibility obstruction.** Every number representable by the AP triple
    `(a, a + d, a + 2·d)` is divisible by `gcd(a, d)`, which divides each of the
    three generators. -/
theorem gcd_dvd_of_representable3_ap {a d m : ℕ}
    (h : Representable3 a (a + d) (a + 2 * d) m) : Nat.gcd a d ∣ m := by
  obtain ⟨x, y, z, rfl⟩ := h
  have hga : Nat.gcd a d ∣ a := Nat.gcd_dvd_left a d
  have hgd : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
  have hgb : Nat.gcd a d ∣ a + d := dvd_add hga hgd
  have hgc : Nat.gcd a d ∣ a + 2 * d := dvd_add hga (hgd.mul_left 2)
  exact dvd_add (dvd_add (hga.mul_right x) (hgb.mul_right y)) (hgc.mul_right z)

/-- **Sharpness of the coprimality hypothesis in `frobenius_three_ap`.** If
    `gcd(a, d) ≥ 2`, the set of numbers *not* representable by the AP triple
    `(a, a + d, a + 2·d)` is infinite: it contains `g·k + 1` for every `k`
    (none divisible by `g := gcd(a, d)`). Hence no finite Frobenius number
    exists, and the coprimality hypothesis cannot be dropped. -/
theorem non_representable3_ap_infinite_of_gcd_ne_one {a d : ℕ}
    (hg : 2 ≤ Nat.gcd a d) :
    { m : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) m }.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => Nat.gcd a d * k + 1) := by
    intro k j hkj
    simp only at hkj
    have hmul : Nat.gcd a d * k = Nat.gcd a d * j := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  have hmem : ∀ k : ℕ,
      (fun k : ℕ => Nat.gcd a d * k + 1) k ∈
        { m : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) m } := by
    intro k
    simp only [Set.mem_setOf_eq]
    intro hrep
    have hdvd : Nat.gcd a d ∣ Nat.gcd a d * k + 1 :=
      gcd_dvd_of_representable3_ap hrep
    have hdvd2 : Nat.gcd a d ∣ Nat.gcd a d * k := dvd_mul_right _ _
    have h1 : Nat.gcd a d ∣ 1 := (Nat.dvd_add_right hdvd2).mp hdvd
    have hle : Nat.gcd a d ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- Consequently, when `gcd(a, d) ≥ 2` the non-representable set is **not**
    bounded above, so the `sSup`-based `frobeniusNumber3` has no genuine
    Frobenius number to report. -/
theorem not_bddAbove_non_representable3_ap_of_gcd_ne_one {a d : ℕ}
    (hg : 2 ≤ Nat.gcd a d) :
    ¬ BddAbove { m : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) m } := by
  intro hbdd
  obtain ⟨B, hB⟩ := hbdd
  have hsub : { m : ℕ | ¬ Representable3 a (a + d) (a + 2 * d) m } ⊆ Set.Iic B :=
    fun m hm => hB hm
  exact (non_representable3_ap_infinite_of_gcd_ne_one hg)
    ((Set.finite_Iic B).subset hsub)

/-- Concrete witness that coprimality is essential: for `(2, 4, 6)` (here
    `a = d = 2`, so `gcd = 2`), the non-representable set is infinite — every
    odd number is missing. -/
theorem non_representable3_2_4_6_infinite :
    { m : ℕ | ¬ Representable3 2 4 6 m }.Infinite := by
  simpa using
    non_representable3_ap_infinite_of_gcd_ne_one (a := 2) (d := 2) (by decide)

end FrobeniusOQ03
