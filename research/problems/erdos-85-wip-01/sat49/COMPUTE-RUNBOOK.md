# Restarting the computational sweep

Written 2026-08-15, as the first sweep wound down in favour of the algebraic
route. Read this before spending money again.

The single most important line: **build the write-through to object storage
before dispatching a single job.** Most of what follows is downstream of not
having done that. Infrastructure detail is in `AWS-RUNBOOK.md` beside this
file; this one is about the sweep.

---

## Where the first sweep got to

| | |
|---|---|
| inventory | 13,541 orbit representatives |
| solver-decided at wind-down | 2,077 |
| replayed in Lean | ~270 |
| profiles touched | BBBB only; four profiles never attempted |
| undecided | 11,465 |

Every verdict ever returned, in any mode, on any machine, was UNSAT. There is
no counterexample anywhere in the archive.

## What it would cost to finish by exhaustion

At the measured rate of about 16 decided orbits an hour across nine instances,
11,465 undecided representatives is roughly **717 hours, thirty days, and
$4,700** of fleet time for the solving alone. Certification runs behind that
rather than beside it, because an undecided orbit cannot be certified.

**Treat thirty days as an upper bound, not a forecast**, and understand which
way the error runs. That rate was measured on the BBBB tail, which is the
hardest slice: the remaining orbits there were measured at roughly thirty-two
times more spread than the ones already decided. But the four untouched
profiles are structurally *lighter* — strictly lower total edge weight, more
degree-2 vertices — so they should be faster to solve and easier to kill
structurally.

Estimating from the hardest available sample and projecting it across the whole
population was the single most repeated error of this campaign. It also
produced a 36 TB storage projection whose median-based figure was 3.1 TB.

## Structure worth exploiting before brute force

A survey of all 13,541 rows found strata that look amenable to a single
argument each, rather than to per-orbit search:

| stratum | count | why it might fall at once |
|---|---:|---|
| disconnected tables | 1,179 (8.7%) | if the CNF factors over components, one factorization theorem plus a small component library kills all of them |
| carrying a weight-4 edge | 555 | a doubled-pair argument, in the style of the divisibility kills that closed other branches |
| all-weight-1 simple graphs | 122 | literally degree-constrained simple graphs on eight vertices; plausibly a hand-checkable classification |

Every table is a loopless weighted graph on 8 vertices with weights 1..4, whose
degree sequence is exactly the profile's row vector. Total edge weight is
invariant per profile. No duplicate tables exist anywhere, and none is shared
across profiles, so the group quotient is exact.

The reduction from 737,300 representatives down to 13,541 is itself a cover
theorem. The 13,541 is not the problem; it is the residue after algebra has run
once. Before restarting the grind, ask whether the covers can be pushed
further, because a theorem that halves the residue is worth about fifteen days
and two thousand dollars, and one that collapses a profile is worth more than
the whole fleet.

## Instrumentation

None of these cost money. All of them produced a wrong answer given to the
operator, which is worse.

- **A check that cannot fail is worthless.** Several scans returned a clean
  zero while reading no files at all: one passed thirty-two filenames as a
  single argument and died with "File name too long" behind a suppressed
  stderr; another was grepping an empty file because the tool it invoked had
  been uninstalled. Assert that a control string *is* present before trusting
  any absence.
- **`grep -c` counts lines, not occurrences.** In minified output everything is
  one line. A duplicated entry survived four verifications because of this.
- **Bracket-trick greps still self-match** when another alternative in the same
  pattern contains a literal match for it.
- **Compare timestamps parsed, not as strings.** ISO timestamps
  (`2026-08-14T23:35:31.678Z`) against a space-separated cutoff make `'T' > ' '`
  true, silently matching everything from that day. Daily totals were reported
  as three-hour ones.
- **Point the instrument at every place the data lives.** The decided count sat
  at exactly 2,048 for hours because it counted only the durable volume, while
  the collector had been writing to local scratch since that volume wedged.
- **Detect work by what is running, not by one script name.** An idle-instance
  detector that counted only the queue runner reported a machine as empty while
  it drove a solver directly, and nearly got it released mid-proof. Count every
  solver and checker binary, and err toward under-reporting idleness.

## Order of work if restarting

1. Write-through to object storage in the worker. Nothing else until this is
   done; it removes an entire class of loss.
2. Work fetch in user-data, or a fleet type that does not auto-replace.
3. A two-minute interruption handler that stops accepting work and flushes.
   With (1) there is nothing large left to flush, which is the point.
4. Start the progress sampler at the same time as the first dispatch, so the
   rate is measured from the first hour rather than reconstructed later from
   whatever happens to be on disk.
