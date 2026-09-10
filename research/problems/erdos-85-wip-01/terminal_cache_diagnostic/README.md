# Concrete-table terminal diagnostic

One direct Lean evaluation on full compact U parameters `(6,6,15)`, secondary
representative14 and the explicit cross used in the separate terminal_canary
kernel certificate. The cached separated joint search returned `false` in393ms;
the entire Lean process completed in4.55s under a30s deadline. Clock reads bracket
the forced/printed Boolean result, so this interval includes result printing.

Run from `proofs`:

```
lake env lean --run ../research/problems/erdos-85-wip-01/terminal_cache_diagnostic/Benchmark.lean
```

This is one local runtime observation, not a bound for other completions or a
proof of rejection. Exact Boolean equality and soundness are proved in
Erdos85ThreeHighCachedSupportClosure.lean; the separate terminal_canary artifact
proves the same completion has no joint witness using ordinary kernel checks.
No cross enumeration is performed here.

The implementation carries concrete Vector-valued tables through recursion.
Inspection of generated C confirmed each new table is constructed before lookup
closures are made, and recursive calls carry the table itself. Earlier private
function-returning cache experiments rebuilt arrays during lookup; those versions
were replaced before banking.
