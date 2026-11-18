import numpy as np, time, sys

# Test : scission des arcs descendants
#   Delta-arc : n = m - (b-a)/2  (enfant "difference", porte la paire (m-b, m+a))
#   Sigma-arc : n = m - (a+b)/2  (enfant "somme",      porte la paire (m-b, m-a))
# M_D[m] = max r(n) sur enfants Delta descendants ; M_S idem Sigma.
# a_D(k) = #{m in V_k : M_D[m] < k} ; a_S(k) idem.
# Verifie aussi : mu_min(k) > M(k)/2 sur tous les niveaux mesures.

t0 = time.time()
r = np.load('rtable_1M.npy')
NF = len(r) - 1
print('table r: m <=', NF, ' max r =', int(r.max()), flush=True)

P = np.ones(2*NF + 2, bool); P[0] = P[1] = False
for i in range(2, int((2*NF+2)**.5) + 1):
    if P[i]:
        P[i*i::i] = False

KMAX = int(r.max()) + 1
M_D = np.zeros(NF + 1, np.int64)
M_S = np.zeros(NF + 1, np.int64)

for m in range(4, NF + 1):
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1   # rayons t : m-t, m+t premiers
    rr = len(T)
    if rr < 2:
        continue
    md = 0; ms = 0
    for i in range(rr - 1):
        a = T[i]; b = T[i+1:]
        nD = m - (b - a) // 2          # < m, >= m/2+2 >= 4 : tous valides
        vD = r[nD]
        mv = int(vD.max())
        if mv > md: md = mv
        nS = m - (a + b) // 2          # < m ; peut etre < 4 -> masque
        ok = nS >= 4
        if ok.any():
            mv2 = int(r[nS[ok]].max())
            if mv2 > ms: ms = mv2
    M_D[m] = md; M_S[m] = ms
    if m % 200000 == 0:
        print('m=%d  %.0fs' % (m, time.time()-t0), flush=True)

np.save('M_delta.npy', M_D); np.save('M_sigma.npy', M_S)

# comptages par niveau via range-add
diffD = np.zeros(KMAX + 2, np.int64); diffS = np.zeros(KMAX + 2, np.int64)
diffA = np.zeros(KMAX + 2, np.int64)
for m in range(4, NF + 1):
    rm = int(r[m])
    if rm < 2: continue
    if M_D[m] < rm:      # puits Delta aux niveaux M_D+1..rm
        diffD[M_D[m]+1] += 1; diffD[rm+1] -= 1
    if M_S[m] < rm:
        diffS[M_S[m]+1] += 1; diffS[rm+1] -= 1
    ma = max(M_D[m], M_S[m])
    if ma < rm:
        diffA[ma+1] += 1; diffA[rm+1] -= 1
aD = np.cumsum(diffD); aS = np.cumsum(diffS); aA = np.cumsum(diffA)

print('k : a_Delta | a_Sigma | a_tous (niveaux ou >0)', flush=True)
for k in range(2, KMAX + 1):
    if aD[k] or aS[k] or aA[k]:
        print('%d : %d | %d | %d' % (k, aD[k], aS[k], aA[k]), flush=True)

# verification mu_min(k) > M(k)/2
mu = np.full((3, KMAX + 1), -1, np.int64)
Rprev = np.zeros(3, np.int64)
for m in range(4, NF + 1):
    c = m % 3; rm = int(r[m])
    if rm > Rprev[c]:
        mu[c, Rprev[c]+1:rm+1] = m
        Rprev[c] = rm
bad = []
for k in range(2, KMAX + 1):
    if mu[1,k] < 0 or mu[2,k] < 0: break
    M = max(mu[1,k], mu[2,k]); mn = min(mu[1,k], mu[2,k])
    if mn <= M // 2:
        bad.append(k)
print('niveaux k>=2 avec mu_min <= M/2 :', bad[:50], ' total=%d' % len(bad), flush=True)
print('FINI %.0fs' % (time.time()-t0), flush=True)
