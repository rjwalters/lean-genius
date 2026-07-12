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

end CollatzStructuredOQ02OQ03
