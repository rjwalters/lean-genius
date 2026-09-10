# Phase B verdict reducer evidence

The five implementation and test files live in `../sat49/`. From that directory run `python3 -m unittest -v test_summarize_phase_b_verdicts test_reviewed_historical_snapshot test_overlay_integration` (26 tests). The latter two suites read pinned historical fixtures from the integration worktree; their local research path is explicit in the test source.

`REVIEW2015_README.md` and `REVIEW2015_PINS.json` preserve the original private review layout and its scope. `BANK_PINS.json` binds the installed layout. `REVIEW2013.json` records independent approval of the crash correction. The unchanged independent `publication_matrix.py` needs the sat49 directory on PYTHONPATH; run it in a fresh scratch working directory because it writes `publication-matrix.json`. The retained matrix contains 12 passing synthetic cases across both solvers and six publication stages.

Historical evidence is accepted only from the exact reviewed 95-row snapshot. It remains distinct from fresh verdicts. Raw SAT alarms, incomplete runs and conflicting input identities prevent false closure. This package launches no solvers, replays no proofs and establishes no new mathematical exclusion. The full details and limitations are preserved in the review README.
