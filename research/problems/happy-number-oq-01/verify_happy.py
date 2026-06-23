def S(n):
    return sum(int(c)**2 for c in str(n))

T = {1,4,16,37,58,89,145,42,20}

# 1) cycle facts
cyc = [4,16,37,58,89,145,42,20]
print("S(1)=", S(1))
for c in cyc:
    print(f"S({c})={S(c)}")
# verify it's the 8-cycle 4->16->37->58->89->145->42->20->4
seq=[4]
x=4
for _ in range(8):
    x=S(x); seq.append(x)
print("cycle from 4:", seq, "closes:", seq[-1]==4)

# 2) T closed under S
print("T closed under S:", all(S(t) in T for t in T))

# 3) steps from each cycle elt to reach 4
for c in cyc:
    j=0; x=c
    while x!=4:
        x=S(x); j+=1
    print(f"steps {c}->4 = {j}")

# 4) base case: every n in [1,999] reaches T within K steps; find max K
maxk=0; worst=None
for n in range(1,1000):
    x=n; k=0
    while x not in T:
        x=S(x); k+=1
        if k>200: break
    if x not in T:
        print("FAIL reach T:", n); 
    if k>maxk: maxk=k; worst=n
print("max steps to reach T over [1,999] =", maxk, "at n=", worst)

# 5) descent bound: S(n) < n for all n >= 1000? check up to large, plus the formula 81*L < 10^(L-1) for L>=4
bad=[n for n in range(1000,200000) if S(n)>=n]
print("counterexamples S(n)>=n for 1000<=n<200000:", bad[:10], "count", len(bad))
for L in range(4,12):
    print(f"L={L}: 81*L={81*L} 10^(L-1)={10**(L-1)} ok={81*L<10**(L-1)}")

# 6) also confirm S(n)<n already holds from 100? (not used, just curiosity)
bad100=[n for n in range(100,1000) if S(n)>=n]
print("S(n)>=n for 100<=n<1000:", bad100)
