#!/usr/bin/env python3
"""
Erdős #1107, r=3 case (OQ erdos-1107-oq-02-oq-01).

Background (gallery entry erdos-1107-oq-02): every integer n >= 120 is a sum of at
most THREE squareful (2-powerful) numbers; the exceptional set below 120 is exactly
{7, 15, 23, 87, 111, 119}. Heath-Brown (1988) gives the asymptotic; the threshold 120
is the effective constant.

Open question: the r=3 (cubeful / 3-powerful) analogue. The parent problem's stated
form is "every sufficiently large integer is a sum of at most r+1 r-powerful numbers",
i.e. at most FOUR cubeful numbers for r=3. The Erdős-as-quoted form in the overview is
"at most THREE r-powerful numbers" for every r. These differ for r=3, so we settle the
question empirically: compute the exceptional set and threshold for BOTH the <=3 and
<=4 cubeful conjectures.

A number n is r-powerful iff every prime p | n satisfies p^r | n. By convention 1 is
r-powerful (vacuously, no prime factors). We include 1 as a summand, matching the
squareful base case (7 is an exception precisely because 7 = 4+1+1 needs 3 summands and
4+4 = 8: with summands from {1,4} no 2-term or 3-term sum hits 7).
"""

from sympy import factorint


def powerful_set(limit, r):
    """All r-powerful numbers in [1, limit]."""
    out = []
    for n in range(1, limit + 1):
        if n == 1 or all(e >= r for e in factorint(n).values()):
            out.append(n)
    return out


def reps_up_to(N, basis, k):
    """
    representable[n] = True iff n is a sum of AT MOST k elements of `basis`
    (elements drawn from basis, with repetition, 1 <= count <= k), for n in [0, N].
    n = 0 corresponds to the empty sum (count 0); we report on n >= 1.
    Uses bounded coin-change DP: dp[j][n] = reachable using at most j summands.
    """
    basis = [b for b in basis if b <= N]
    # dp[n] = minimum number of summands to reach n (inf if unreachable), capped at k
    INF = k + 1
    dp = [INF] * (N + 1)
    dp[0] = 0
    # unbounded knapsack but tracking summand count; do k passes
    # reach[c] = set reachable with exactly <= c summands
    reach = [False] * (N + 1)
    reach[0] = True
    cur = [False] * (N + 1)
    cur[0] = True
    reachable_atmost = [False] * (N + 1)
    reachable_atmost[0] = True
    frontier = {0}
    for _ in range(k):
        new_frontier = set()
        for n in list(frontier):
            for b in basis:
                m = n + b
                if m <= N and not reachable_atmost[m]:
                    reachable_atmost[m] = True
                    new_frontier.add(m)
        frontier |= new_frontier
        if not new_frontier:
            break
    return reachable_atmost


def exceptions(N, basis, k):
    reach = reps_up_to(N, basis, k)
    return [n for n in range(1, N + 1) if not reach[n]]


def report(label, r, k, N):
    basis = powerful_set(N, r)
    exc = exceptions(N, basis, k)
    print(f"\n=== {label}: r={r}-powerful, at most {k} summands, range [1,{N}] ===")
    print(f"basis (first 20 of {len(basis)}): {basis[:20]}")
    print(f"# exceptions in [1,{N}]: {len(exc)}")
    print(f"exceptions: {exc}")
    if exc:
        print(f"largest exception: {max(exc)}  =>  empirical threshold N = {max(exc)+1}")
    else:
        print("no exceptions: every n in range is representable")
    return exc


if __name__ == "__main__":
    # --- Validation: reproduce the KNOWN squareful (r=2) base case ---
    sq_exc = report("VALIDATION squareful base case", r=2, k=3, N=1000)
    expected = [7, 15, 23, 87, 111, 119]
    assert sq_exc == expected, f"VALIDATION FAILED: got {sq_exc}, expected {expected}"
    print("VALIDATION PASSED: squareful <=3 reproduces threshold 120, exceptions match.\n")

    # --- The open question: cubeful (r=3) ---
    N = 20000
    report("cubeful <=3 summands", r=3, k=3, N=N)
    report("cubeful <=4 summands", r=3, k=4, N=N)
