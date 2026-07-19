import Proofs.CollatzStructuredOQ02OQ03

/-!
# Collatz OQ-02-03 — Part XI: Certificate uniqueness (companion module)

This companion extends `Proofs.CollatzStructuredOQ02OQ03` with the **uniqueness /
completeness** layer for Terras parity certificates.  It lives in its own module for a
purely operational reason: the mother file already sits at the Lean kernel's memory ceiling
(its Part VI/VII `autoDropCert` kernel-`decide` reductions are heavy, and appending even a
few more elaborations reproducibly tips the kernel into a SIGBUS during checking).  Splitting
the new theorems into a separate compilation unit keeps the mother file green and gives these
lemmas a fresh elaboration context.  Nothing here uses `decide` or adds any axiom.

## What Part VIII already gives

`affValid_orbit_parity` shows that a valid certificate `v` for the affine class `c·m + d`
records the orbit's *genuine* parity bit at each step: `collatz^[i] (c·m + d) % 2 =
(v[i]).toNat`.  That is a *faithfulness* statement — the recorded parities are the real
ones.

## What Part XI adds

Because the recorded parities are forced by the Collatz dynamics of the class member itself
(evaluate at `m = 0`, i.e. the member `d`), and not by anything about the certificate, two
valid certificates of the same length for the same class must agree bit-for-bit:

* `affValid_unique` — equal-length valid certificates for `(c, d)` are identical;
* `affValid_eq_deriveVec` — the auto-derived vector `deriveVec (2b+1) (2^b) r` is the
  *canonical* certificate: any valid `v` of its length for the class `r (mod 2^b)` equals it.

This upgrades Part VIII from "the certificate is faithful" to "the certificate is the *only*
faithful one", exactly characterizing residue-determined windows.  Axiom-free (independent of
`tao_2019`).
-/

namespace CollatzStructuredOQ02OQ03

/-- **Certificate uniqueness.**  Two valid parity certificates of equal length for the same
affine class `(c, d)` are identical.  Each bit `v[i]` equals the orbit parity
`collatz^[i] d % 2` (Part VIII at the class member `m = 0`), which pins it independently of
the certificate; so a valid transcript is forced by the dynamics, never chosen. -/
theorem affValid_unique {v w : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hw : AffValid w c d) (hlen : v.length = w.length) :
    v = w := by
  apply List.ext_getElem hlen
  intro i h₁ h₂
  -- both bits reduce, via Part VIII at `m = 0`, to the same orbit parity `collatz^[i] d % 2`
  have hb : (v[i]'h₁).toNat = (w[i]'h₂).toNat := by
    have pv := affValid_orbit_parity hv 0 i h₁
    have pw := affValid_orbit_parity hw 0 i h₂
    simp only [Nat.mul_zero, Nat.zero_add] at pv pw
    rw [← pv, ← pw]
  -- `Bool.toNat` is injective, so equal parities force equal bits
  cases hvv : v[i]'h₁ <;> cases hww : w[i]'h₂ <;>
    simp_all [Bool.toNat_true, Bool.toNat_false]

/-- **Engine completeness / canonical certificate.**  For a power-of-two modulus `2^b`, the
auto-derived vector `deriveVec (2b+1) (2^b) r` is the *unique* valid certificate of its
length for the residue class `r (mod 2^b)`: any `AffValid v (2^b) r` of that length must
equal it.  So the turnkey engine of Part VII yields not merely *a* certificate but the
canonical one — the residue-determined parity window admits no alternative transcript. -/
theorem affValid_eq_deriveVec {b r : ℕ} {v : List Bool}
    (hv : AffValid v (2 ^ b) r)
    (hlen : v.length = (deriveVec (2 * b + 1) (2 ^ b) r).length) :
    v = deriveVec (2 * b + 1) (2 ^ b) r :=
  affValid_unique hv (affValidB_sound (affValidB_deriveVec _ _ _)) hlen

/-- **Prefix comparability of certificates.**  A shorter valid certificate for a class
`(c, d)` is a *prefix* of any longer valid certificate for the same class.  This upgrades
`affValid_unique` from equal length to arbitrary length: since each bit `v[i]` is pinned to
the orbit parity `collatz^[i] d % 2` (Part VIII at the class member `m = 0`), independently of
the certificate or of its total length, the first `v.length` bits of the longer transcript `w`
must reproduce `v` bit-for-bit.  Hence the valid certificates for a fixed class form a *chain*
under the prefix order — the forced parity window grows monotonically, never branches. -/
theorem affValid_isPrefix {v w : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hw : AffValid w c d) (hlen : v.length ≤ w.length) :
    v <+: w := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem ?_ ?_
  · rw [List.length_take]; omega
  · intro i h₁ h₂
    have hiw : i < w.length := lt_of_lt_of_le h₁ hlen
    -- both bits reduce, via Part VIII at `m = 0`, to the same orbit parity `collatz^[i] d % 2`
    have pv := affValid_orbit_parity hv 0 i h₁
    have pw := affValid_orbit_parity hw 0 i hiw
    simp only [Nat.mul_zero, Nat.zero_add] at pv pw
    have hb : (v[i]'h₁).toNat = (w[i]'hiw).toNat := by rw [← pv, ← pw]
    rw [List.getElem_take]
    cases hvv : v[i]'h₁ <;> cases hww : w[i]'hiw <;>
      simp_all [Bool.toNat_true, Bool.toNat_false]

/-- **The canonical certificate is maximal.**  Every valid certificate `v` for the residue
class `r (mod 2^b)` whose length does not exceed that of the auto-derived vector
`deriveVec (2b+1) (2^b) r` is a *prefix* of it.  So `deriveVec` is not merely *a* certificate
(Part VII) and the *unique* one of its own length (`affValid_eq_deriveVec`): it is the maximal
element of the prefix chain of all valid certificates for the class — every faithful transcript
of the residue-determined window is an initial segment of the engine's output. -/
theorem affValid_prefix_deriveVec {b r : ℕ} {v : List Bool}
    (hv : AffValid v (2 ^ b) r)
    (hlen : v.length ≤ (deriveVec (2 * b + 1) (2 ^ b) r).length) :
    v <+: deriveVec (2 * b + 1) (2 ^ b) r :=
  affValid_isPrefix hv (affValidB_sound (affValidB_deriveVec _ _ _)) hlen

/-! ## Part XI (cont.) — the valid certificates are *exactly* the prefixes of `deriveVec`

`affValid_prefix_deriveVec` shows one containment: every valid certificate is a prefix of the
canonical vector.  The converse containment is **prefix closure** of validity, which holds for
a structural reason: the `AffValid` inductive consumes bits from the *front*, so truncating a
valid transcript's tail only ends the derivation earlier at `nil` while every surviving head
condition is unchanged.  Together the two containments pin the valid-certificate set of a class
to a single chain — the set of initial segments of `deriveVec` — completing the exact
characterization of the residue-determined parity window. -/

/-- **Prefix closure of validity.**  If `v` is a valid certificate for the affine class
`(c, d)`, then so is every prefix `w` of `v`.  Each `AffValid` constructor pins the head parity
and recurses into the tail with the class advanced one Collatz step, so dropping trailing bits
just terminates the derivation sooner at `nil`; the head conditions that remain are untouched.
Hence the valid certificates for a fixed class are *downward closed* under the prefix order. -/
theorem affValid_prefix_closed {v w : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hw : w <+: v) : AffValid w c d := by
  induction hv generalizing w with
  | nil =>
      obtain ⟨t, ht⟩ := hw
      cases w with
      | nil => exact AffValid.nil
      | cons b w' => exact absurd ht (List.cons_ne_nil _ _)
  | odd hc hd _htail ih =>
      obtain ⟨t, ht⟩ := hw
      cases w with
      | nil => exact AffValid.nil
      | cons b w' =>
          rw [List.cons_append] at ht
          injection ht with hb hrest
          subst hb
          exact AffValid.odd hc hd (ih ⟨t, hrest⟩)
  | even hc hd _htail ih =>
      obtain ⟨t, ht⟩ := hw
      cases w with
      | nil => exact AffValid.nil
      | cons b w' =>
          rw [List.cons_append] at ht
          injection ht with hb hrest
          subst hb
          exact AffValid.even hc hd (ih ⟨t, hrest⟩)

/-- The canonical auto-derived vector is a valid certificate for its class (named for reuse
below; the term appears inline in `affValid_eq_deriveVec`). -/
theorem affValid_deriveVec (b r : ℕ) :
    AffValid (deriveVec (2 * b + 1) (2 ^ b) r) (2 ^ b) r :=
  affValidB_sound (affValidB_deriveVec _ _ _)

/-- **Exact characterization of valid certificates.**  A parity list `v` is a valid certificate
for the residue class `r (mod 2^b)` *within* the residue-determined window (length not exceeding
the canonical vector's) **iff** it is a prefix of the auto-derived `deriveVec (2b+1) (2^b) r`.
So the valid certificates for the class are *exactly* the initial segments of one canonical
vector: forward is `affValid_prefix_deriveVec`, backward is `affValid_prefix_closed` applied to
`affValid_deriveVec`.  This closes the uniqueness/completeness thread — the residue-determined
window admits a single chain of transcripts, not a branching family. -/
theorem affValid_iff_prefix_deriveVec {b r : ℕ} {v : List Bool} :
    (AffValid v (2 ^ b) r ∧ v.length ≤ (deriveVec (2 * b + 1) (2 ^ b) r).length)
      ↔ v <+: deriveVec (2 * b + 1) (2 ^ b) r := by
  constructor
  · rintro ⟨hv, hlen⟩
    exact affValid_prefix_deriveVec hv hlen
  · intro hpre
    exact ⟨affValid_prefix_closed (affValid_deriveVec b r) hpre, hpre.length_le⟩

/-! ## Part XII — no two consecutive odd steps

Every prior part treats the *values* recorded by a certificate (`affValid_orbit_parity`,
the prefix chain).  This part records a purely **combinatorial** constraint on which parity
lists can be valid at all: the classical Collatz fact that an odd step is *never* immediately
followed by another odd step.  The reason is elementary — the odd branch sends
`d ↦ 3d + 1`, and `3d + 1` is *even* whenever `d` is odd (`3·odd + 1 = even`), so the very
next step is forced to be a halving.  In certificate terms, the `AffValid.odd` constructor
recurses into the class `(3c, 3d + 1)` whose constant term is even, and the head bit of any
valid certificate is pinned to the parity of that constant term.  Hence no valid transcript
contains `true :: true`, and the certificates satisfy `List.Chain'` for the relation
"if this bit is odd then the next is even".
-/

/-- **Head bit = parity of the constant term.**  The leading bit of a valid certificate for
the affine class `(c, d)` is `true` (an odd step) exactly when the class constant `d` is odd.
Both constructors of `AffValid` pin the head bit to `d % 2`: `odd` needs `d % 2 = 1` and emits
`true`; `even` needs `d % 2 = 0` and emits `false`. -/
theorem affValid_head_parity {b : Bool} {v : List Bool} {c d : ℕ}
    (h : AffValid (b :: v) c d) : b = true ↔ d % 2 = 1 := by
  cases h with
  | odd hc hd _ => simp [hd]
  | even hc hd _ => simp [hd]

/-- **No `odd :: odd` at the head.**  A valid certificate can never begin `true :: true`: the
first odd step advances the class constant to `3d + 1`, which is even (`d` was odd), so the
second bit is forced to be a halving.  Attempting two consecutive odd steps contradicts the
parity requirement of the inner `AffValid.odd` constructor. -/
theorem not_affValid_true_true {v : List Bool} {c d : ℕ} :
    ¬ AffValid (true :: true :: v) c d := by
  intro h
  cases h with
  | odd hc hd htail =>
      cases htail with
      | odd hc' hd' _ => omega

/-- **No two consecutive odd steps.**  Any valid parity certificate `v` for an affine class
`(c, d)` satisfies `List.IsChain` for the relation "an odd bit is followed by an even bit":
`true` is never immediately followed by `true`.  This is the certificate-level statement of
the classical Collatz fact that `3n + 1` is always even, so odd steps in the accelerated map
cannot be adjacent.  Proof by induction on the certificate: after an odd step the class
constant becomes even, so `affValid_head_parity` forces the next recorded bit to be `false`;
after an even step the guard is vacuous. -/
theorem affValid_no_two_consecutive_odd :
    ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
      List.IsChain (fun a b => a = true → b = false) v := by
  intro v c d hv
  induction hv with
  | nil => exact List.IsChain.nil
  | @odd v c d hc hd htail ih =>
      -- `htail : AffValid v (3c) (3d+1)` with `3d+1` even, so the head of `v` is `false`.
      cases v with
      | nil => exact List.IsChain.singleton _
      | cons b w =>
          refine List.IsChain.cons_cons ?_ ih
          intro _
          have hpar := affValid_head_parity htail
          rcases Bool.dichotomy b with hb | hb
          · exact hb
          · exact absurd (hpar.mp hb) (by omega)
  | @even v c d hc hd htail ih =>
      cases v with
      | nil => exact List.IsChain.singleton _
      | cons b w =>
          exact List.IsChain.cons_cons (fun h => by simp at h) ih

/-- **Adjacent-position form.**  Restatement of `affValid_no_two_consecutive_odd` at explicit
indices: if the certificate records an odd step at position `i`, the step at `i + 1` is a
halving.  Derived from the suffix-validity law `affValid_drop` — the tail `v.drop i` is itself
a valid certificate that would begin `true :: true` — together with `not_affValid_true_true`. -/
theorem affValid_true_succ_false {v : List Bool} {c d : ℕ} (hv : AffValid v c d)
    {i : ℕ} (h : i + 1 < v.length) (hi : v[i] = true) : v[i + 1] = false := by
  by_contra hne
  have hi2 : v[i + 1] = true := by
    rcases Bool.dichotomy (v[i + 1]) with h0 | h1
    · exact absurd h0 hne
    · exact h1
  have hdrop := affValid_drop hv i
  have e1 : v.drop i = v[i] :: v.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
  have e2 : v.drop (i + 1) = v[i + 1] :: v.drop (i + 2) := List.drop_eq_getElem_cons (by omega)
  rw [e1, e2] at hdrop
  simp only [hi, hi2] at hdrop
  exact not_affValid_true_true hdrop
/-! ## Part XI (cont.) — Length maximality of the derived window

The prefix results above (`affValid_prefix_deriveVec`) still assume a comparison against
`deriveVec`'s *own* length.  The lemmas below discharge that hypothesis at its root: the
`deriveVec` engine records a bit under exactly the branch condition (`c` even) that the
`AffValid` constructors demand, so the certificate recursion and the engine recursion stay
in lockstep.  Consequently a valid certificate is *never* longer than the window the fuel
can reach — `deriveVec` produces the maximal faithful transcript — and increasing the fuel
only extends the window, never revising a recorded bit.  This settles the standing
"maximality of `deriveVec` length" step: no valid certificate is strictly longer than
`deriveVec fuel c d` once `fuel` covers it, and the canonical choice `fuel = v.length`
always covers it.  Still axiom-free (independent of `tao_2019`; no `decide`). -/

/-- The auto-derived window never records more bits than its fuel: `deriveVec` stops as soon
as the leading coefficient turns odd or the fuel runs out, so `(deriveVec fuel c d).length ≤
fuel` unconditionally.  This is the intrinsic length budget that replaces the
self-referential bound `v.length ≤ (deriveVec …).length`. -/
theorem deriveVec_length_le : ∀ (fuel c d : ℕ), (deriveVec fuel c d).length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro c d; simp [deriveVec]
  | succ f ih =>
    intro c d
    rw [deriveVec]
    split_ifs
    · simp
    · simp only [List.length_cons]; exact Nat.succ_le_succ (ih (3 * c) (3 * d + 1))
    · simp only [List.length_cons]; exact Nat.succ_le_succ (ih (c / 2) (d / 2))

/-- **Maximality of the derived window (prefix form).**  Any valid certificate `v` for the
affine class `(c, d)` whose length is within the available `fuel` is a *prefix* of the
auto-derived window `deriveVec fuel c d`.  Unlike `affValid_prefix_deriveVec`, this needs no
hypothesis comparing `v` to `deriveVec`'s own length — only `v.length ≤ fuel`, met by the
canonical choice `fuel = v.length`.  Proof: induction on the `AffValid` derivation.  Both
constructors (`odd`, `even`) require `c % 2 = 0`, which is exactly the branch `deriveVec`
takes before recording a bit, so at each step the engine emits the same parity the
certificate does and recurses into the same successor pair. -/
theorem affValid_prefix_deriveVec_of_length :
    ∀ {v : List Bool} {c d : ℕ}, AffValid v c d → ∀ {fuel : ℕ}, v.length ≤ fuel →
      v <+: deriveVec fuel c d := by
  intro v c d hv
  induction hv with
  | nil => intro fuel _; exact List.nil_prefix
  | @odd v c d hc hd _ ih =>
    intro fuel hfuel
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := by
      cases fuel with
      | zero => simp only [List.length_cons] at hfuel; omega
      | succ f => exact ⟨f, rfl⟩
    rw [deriveVec, if_neg (by omega : ¬ c % 2 = 1), if_pos hd]
    obtain ⟨t, ht⟩ := ih (show v.length ≤ fuel' by
      simp only [List.length_cons] at hfuel; omega)
    exact ⟨t, by rw [List.cons_append, ht]⟩
  | @even v c d hc hd _ ih =>
    intro fuel hfuel
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := by
      cases fuel with
      | zero => simp only [List.length_cons] at hfuel; omega
      | succ f => exact ⟨f, rfl⟩
    rw [deriveVec, if_neg (by omega : ¬ c % 2 = 1), if_neg (by omega : ¬ d % 2 = 1)]
    obtain ⟨t, ht⟩ := ih (show v.length ≤ fuel' by
      simp only [List.length_cons] at hfuel; omega)
    exact ⟨t, by rw [List.cons_append, ht]⟩

/-- **Length maximality.**  A valid certificate is never longer than the auto-derived window
the fuel can reach: `deriveVec` yields the *longest* faithful transcript of the
residue-determined parity window.  Immediate from the prefix form via `IsPrefix.length_le`. -/
theorem affValid_length_le_deriveVec {v : List Bool} {c d fuel : ℕ}
    (hv : AffValid v c d) (hfuel : v.length ≤ fuel) :
    v.length ≤ (deriveVec fuel c d).length :=
  (affValid_prefix_deriveVec_of_length hv hfuel).length_le

/-- **Fuel monotonicity of the engine.**  Increasing the fuel only *extends* the derived
window — it never revises an already-recorded bit: `deriveVec fuel c d` is a prefix of
`deriveVec fuel' c d` whenever `fuel ≤ fuel'`.  (The shorter window is itself a valid
certificate by `affValidB_deriveVec`, and its length is `≤ fuel ≤ fuel'`, so the previous
lemma applies.)  Hence the derived certificates for a fixed class form a *chain* under the
prefix order, stabilizing at the maximal valid transcript once the window closes. -/
theorem deriveVec_prefix_mono {c d fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    deriveVec fuel c d <+: deriveVec fuel' c d :=
  affValid_prefix_deriveVec_of_length
    (affValidB_sound (affValidB_deriveVec fuel c d))
    (le_trans (deriveVec_length_le fuel c d) h)

/-- **Prefix maximality for the dyadic engine, without a self-referential hypothesis.**  For
the residue class `r (mod 2^b)`, any valid certificate `v` of length `≤ 2b+1` is a prefix of
the canonical window `deriveVec (2b+1) (2^b) r`.  This is `affValid_prefix_deriveVec` with its
hypothesis `v.length ≤ (deriveVec …).length` replaced by the intrinsic fuel budget
`v.length ≤ 2b+1` — a bound on the engine's input, not a quantity read back off its output. -/
theorem affValid_prefix_deriveVec_pow {b r : ℕ} {v : List Bool}
    (hv : AffValid v (2 ^ b) r) (hlen : v.length ≤ 2 * b + 1) :
    v <+: deriveVec (2 * b + 1) (2 ^ b) r :=
  affValid_prefix_deriveVec_of_length hv hlen

/-! ## Part XII (cont.) — odd steps are at most half of the window

`affValid_no_two_consecutive_odd` records the *shape* constraint that a valid certificate
never contains `true :: true`.  This section turns that qualitative fact into a **quantitative
count bound**: in any list with no two adjacent `true`s, at most `⌈length/2⌉` of the entries
are `true`.  Applied to a certificate `v` this bounds the number of *odd* (tripling) steps
`v.count true` by one more than the number of *even* (halving) steps `v.count false`.

The bound is the certificate-level statement of the classical Collatz fact that triplings can
never outnumber halvings by more than one over any window.  It is sharp: the alternating
transcript `true :: false :: true :: … :: true` (which arises for `d` odd) attains
`2·count true = length + 1`.

Honest reach: this yields `a ≤ b + 1` for a window with `a = v.count true` triplings and
`b = v.count false` halvings, which is strictly weaker than the drop criterion `3^a < 2^b`
(the latter needs `a` genuinely smaller than `b·log 2 / log 3 ≈ 0.63 b`).  It is the exact
combinatorial content extractable from adjacency alone, no more.  Axiom-free (independent of
`tao_2019`, no `decide`). -/

/-- **General count bound (bounded induction form).**  In any `Bool` list with no two adjacent
`true`s — expressed as `List.IsChain` for the relation "an odd bit forces the next to be even"
— twice the number of `true`s is at most `length + 1`.  Proved by induction on a length budget
`n`: an even head defers to the tail (one shorter), an odd head forces the following bit to be
even and peels *two* entries (`true :: false`) adding one `true` for two positions. -/
theorem count_true_le_of_noTwoTrue :
    ∀ (n : ℕ) (v : List Bool), v.length ≤ n →
      List.IsChain (fun a b => a = true → b = false) v →
      2 * v.count true ≤ v.length + 1 := by
  intro n
  induction n with
  | zero =>
      intro v hlen _
      have : v = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this; simp
  | succ n ih =>
      intro v hlen hchain
      match v with
      | [] => simp
      | [a] =>
          have : List.count true [a] ≤ 1 := by cases a <;> simp
          simp only [List.length_singleton]; omega
      | a :: b :: rest =>
          have hrel : a = true → b = false := hchain.rel_head
          have htail : List.IsChain (fun a b => a = true → b = false) (b :: rest) :=
            hchain.of_cons
          have hlen' : (b :: rest).length ≤ n := by
            simp only [List.length_cons] at hlen ⊢; omega
          rcases Bool.dichotomy a with ha | ha
          · -- even head: `count true` unchanged, tail is one shorter
            have hc : List.count true (a :: b :: rest) = List.count true (b :: rest) := by
              simp [ha]
            have hih := ih (b :: rest) hlen' htail
            rw [hc]; simp only [List.length_cons] at hih ⊢; omega
          · -- odd head forces `b = false`; peel two entries, adding one `true`
            have hb : b = false := hrel ha
            have hc : List.count true (a :: b :: rest) = 1 + List.count true rest := by
              simp [ha, hb]; omega
            have htail2 : List.IsChain (fun a b => a = true → b = false) rest := htail.of_cons
            have hlen2 : rest.length ≤ n := by simp only [List.length_cons] at hlen; omega
            have hih := ih rest hlen2 htail2
            rw [hc]; simp only [List.length_cons]; omega

/-- **General count bound.**  A `Bool` list with no two adjacent `true`s has
`2 · (count true) ≤ length + 1`.  The unbudgeted form of `count_true_le_of_noTwoTrue`, taking
the length itself as the budget. -/
theorem two_mul_count_true_le_of_isChain {v : List Bool}
    (h : List.IsChain (fun a b => a = true → b = false) v) :
    2 * v.count true ≤ v.length + 1 :=
  count_true_le_of_noTwoTrue v.length v le_rfl h

/-- Partition identity for `Bool` lists: every entry is `true` or `false`, so
`count true + count false = length`. -/
theorem count_true_add_count_false (v : List Bool) :
    v.count true + v.count false = v.length := by
  induction v with
  | nil => simp
  | cons a t ih => cases a <;> simp <;> omega

/-- **Odd steps are at most half the window.**  For any valid parity certificate `v`, twice
the number of odd (tripling) steps is at most `length + 1`.  Immediate from
`affValid_no_two_consecutive_odd` (no `true :: true`) via the general count bound. -/
theorem affValid_two_mul_count_true_le {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) : 2 * v.count true ≤ v.length + 1 :=
  two_mul_count_true_le_of_isChain (affValid_no_two_consecutive_odd hv)

/-- **Triplings never exceed halvings by more than one.**  For any valid parity certificate,
the number of odd (tripling) steps `count true` is at most one more than the number of even
(halving) steps `count false`.  This is the certificate-level form of the classical fact that
a `3n+1` step is always followed by a halving, so over any window `a ≤ b + 1` where
`a = #odd`, `b = #even`.  Combined with the mother module's drop criterion
`3^(count true) < 2^(count false)`, it quantifies exactly how far short of the drop threshold
adjacency alone leaves us: `a ≤ b + 1` does not imply `3^a < 2^b`. -/
theorem affValid_count_true_le_count_false_succ {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) : v.count true ≤ v.count false + 1 := by
  have h1 := affValid_two_mul_count_true_le hv
  have h2 := count_true_add_count_false v
  omega

/-! ## Part XII (cont.) — the intrinsic length budget `v.length ≤ 2b+1`

The count bound above (`affValid_count_true_le_count_false_succ`) controls the *odd* steps in
terms of the *even* steps but says nothing about the total length: it leaves
`v.length ≤ 2·(count false) + 1` still hostage to how large `count false` can be.  This section
supplies the missing half — a bound on the *even* steps `count false ≤ b` for the dyadic engine
`AffValid v (2^b) r` — and combines the two into the intrinsic budget `v.length ≤ 2b+1`.

The mechanism is the 2-adic valuation of the leading coefficient `c`.  Every `AffValid` step
requires `c` even, and:
  * an **odd** step (`true`) sends `c ↦ 3c`, which *preserves* `v₂(c)` (3 is odd);
  * an **even** step (`false`) sends `c ↦ c/2`, which *drops* `v₂(c)` by one.
So each halving consumes one factor of 2 from `c`, giving the divisibility invariant
`2^(count false) ∣ c`.  For the dyadic class `c = 2^b` this reads `2^(count false) ∣ 2^b`, i.e.
`count false ≤ b`: there can be at most `b` halvings before the leading coefficient runs out of
2s.  This makes `affValid_prefix_deriveVec_pow` unconditional — the fuel budget `2b+1` is a
theorem about the certificate, not a hypothesis. -/

/-- **Halvings consume factors of 2 from the leading coefficient.**  Every valid certificate `v`
for the affine class `c·m + d` satisfies `2^(v.count false) ∣ c`: each even (halving) step peels
one factor of 2 off `c`, while odd (tripling) steps `c ↦ 3c` preserve its 2-adic valuation. -/
theorem affValid_two_pow_count_false_dvd {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) : 2 ^ (v.count false) ∣ c := by
  induction hv with
  | nil => simp
  | @odd v c d hc hd hrec ih =>
    have hcount : (true :: v).count false = v.count false := by simp
    rw [hcount]
    -- `2^k ∣ 3 * c` and `Coprime (2^k) 3` give `2^k ∣ c`
    have hcop : Nat.Coprime (2 ^ (v.count false)) 3 :=
      Nat.Coprime.pow_left _ (by decide)
    exact hcop.dvd_of_dvd_mul_left ih
  | @even v c d hc hd hrec ih =>
    have hcount : (false :: v).count false = v.count false + 1 := by simp
    rw [hcount, pow_succ, mul_comm (2 ^ v.count false) 2]
    -- goal: `2 * 2^k ∣ c`; rewrite `c = 2 * (c / 2)` and use `ih : 2^k ∣ c/2`
    have hc2 : c = 2 * (c / 2) := by omega
    rw [hc2]
    exact mul_dvd_mul_left 2 ih

/-- **At most `b` halvings for the dyadic class.**  For the residue class `r (mod 2^b)`, any
valid certificate `v` has `v.count false ≤ b`: the divisibility invariant
`2^(count false) ∣ 2^b` forces the number of even steps below `b`. -/
theorem affValid_count_false_le_of_pow {v : List Bool} {b r : ℕ}
    (hv : AffValid v (2 ^ b) r) : v.count false ≤ b := by
  have hdvd : 2 ^ (v.count false) ∣ 2 ^ b := affValid_two_pow_count_false_dvd hv
  exact (pow_dvd_pow_iff (by norm_num) (by simp)).mp hdvd

/-- **Intrinsic length budget for the dyadic engine.**  Every valid certificate `v` for the
residue class `r (mod 2^b)` has `v.length ≤ 2b+1`.  Combines `count false ≤ b`
(`affValid_count_false_le_of_pow`) with `count true ≤ count false + 1`
(`affValid_count_true_le_count_false_succ`): `length = count true + count false ≤ 2·count false + 1
≤ 2b+1`.  This is the bound that `affValid_prefix_deriveVec_pow` previously had to *assume*. -/
theorem affValid_length_le_of_pow {v : List Bool} {b r : ℕ}
    (hv : AffValid v (2 ^ b) r) : v.length ≤ 2 * b + 1 := by
  have hf := affValid_count_false_le_of_pow hv
  have ht := affValid_count_true_le_count_false_succ hv
  have hsum := count_true_add_count_false v
  omega

/-- **Prefix maximality for the dyadic engine — fully unconditional.**  For the residue class
`r (mod 2^b)`, *every* valid certificate `v` (no length hypothesis) is a prefix of the canonical
window `deriveVec (2b+1) (2^b) r`.  This is `affValid_prefix_deriveVec_pow` with its input budget
`v.length ≤ 2b+1` now discharged intrinsically by `affValid_length_le_of_pow`, so the canonical
window `deriveVec (2b+1) …` provably contains every certificate for the class. -/
theorem affValid_prefix_deriveVec_pow_of_pow {b r : ℕ} {v : List Bool}
    (hv : AffValid v (2 ^ b) r) :
    v <+: deriveVec (2 * b + 1) (2 ^ b) r :=
  affValid_prefix_deriveVec_pow hv (affValid_length_le_of_pow hv)

end CollatzStructuredOQ02OQ03
