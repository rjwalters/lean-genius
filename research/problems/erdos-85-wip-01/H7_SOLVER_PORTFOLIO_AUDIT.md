# H7 bounded solver-configuration portfolio audit

Date: 2026-08-26.  Scope: one completed control (`cube_F7_t7`) and one hard
missing parent (`cube_F6_t2`) from the exact compact canonical H7 encoding.
This was a bounded signal test, not a certificate campaign.

## Inputs

- `cube_F7_t7`: 17,633 variables / 720,825 clauses, SHA-256
  `fdbd3dad77d033125b1b3a1ad8294de8728110faadacb6286e92caff1d19280b`.
- `cube_F6_t2`: 17,633 variables / 720,825 clauses, SHA-256
  `7ab482258ca35bb3d6ba57637a31caddee1826980d7822c59b694621e084fc82`.
- Installed solvers: Kissat 4.0.4 and CaDiCaL 3.0.1.

## Bounded result

Kissat `--plain` solved the completed F7/t7 control UNSAT in 18.15 seconds
(918,403 conflicts).  This is a real constant-factor improvement over the
historical default census verdict at 38 seconds, and confirms that solver
configuration materially changes easy-parent performance.

The decisive hard-parent test ran Kissat `--default`, `--unsat`, and `--plain`
in parallel with equal 60-second wall limits on F6/t2.  All three returned
`UNKNOWN` at the limit.  Thus the control speedup did not transfer to a
qualitative hard-parent result.

## Verdict

CUT as a standalone mechanism.  There is no basis for a configuration-grid
campaign: the hard root remains unknown under every predefined Kissat regime.
The exact proof boundary remains unchanged—only UNSAT followed by checked
LRAT/DRAT replay may enter the 43-parent evidence manifest.  Configuration
choice can still be used opportunistically inside a future mechanism that
already produces a structural reduction.
