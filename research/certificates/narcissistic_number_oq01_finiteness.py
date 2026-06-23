# Certificate for narcissistic-number-oq-01 (finiteness of narcissistic numbers).
#
# An n-digit number m (10^(n-1) <= m <= 10^n - 1) is narcissistic iff
#   m = sum over digits d of m of d^n.
# The digit-power-sum of any n-digit number is <= n * 9^n.
# If 10^(n-1) > n * 9^n, then for every n-digit m we have
#   m >= 10^(n-1) > n*9^n >= (digit-power-sum) , so m is NOT narcissistic.
# Therefore every narcissistic number has fewer than D digits, where D is the
# least n with 10^(n-1) > n*9^n.  A bounded set of naturals is FINITE.  QED.

D = next(n for n in range(1, 500) if 10**(n-1) > n * 9**n)
print(f"crossover D = {D}: for all n >= {D}, no n-digit number is narcissistic")
for n in range(D-2, D+2):
    lhs, rhs = 10**(n-1), n*9**n
    print(f"  n={n}: 10^(n-1) {'>' if lhs>rhs else '<='} n*9^n   ({lhs} vs {rhs})")

# Bounded enumeration for examples (digit-lengths 1..7 only, for illustration).
def narc_of_length(n):
    out=[]
    lo = 1 if n==1 else 10**(n-1)
    for m in range(lo, 10**n):
        if sum(int(c)**n for c in str(m)) == m:
            out.append(m)
    return out
ex=[]
for n in range(1,8):
    ex += narc_of_length(n)
print("narcissistic numbers with <= 7 digits:", ex)
# Known full list has 88 entries, largest = 115132219018763992565095597973971522401 (39 digits)
print("known full count (base 10) = 88; largest = 115132219018763992565095597973971522401 (39 digits, < 10^%d)" % D)
print("FINITE: proven by the digit-count bound D=%d" % D)
