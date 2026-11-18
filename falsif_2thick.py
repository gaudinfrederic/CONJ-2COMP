import numpy as np, time

# 2THICK (complement de falsif_delta_sigma) :
# multiplicite w(m,n) = #paires de rayons (a<b) de m produisant l'enfant
# descendant n (Delta : n=m-(b-a)/2 ; Sigma : n=m-(a+b)/2 ; paires de
# meme parite seulement). M2[m] = max r(n) sur enfants epais (w>=2).
# a2(k) = #{m in V_k : M2[m] < k} = #puits du digraphe epais.
# Attendu : stabilisation a a2(k)=3, zero rechute a 2 au-dela de k2 petit.

t0 = time.time()
r = np.load('rtable_1M.npy')
NF = len(r) - 1
print('table r: m <=', NF, ' max r =', int(r.max()), flush=True)

P = np.ones(2*NF + 2, bool); P[0] = P[1] = False
for i in range(2, int((2*NF+2)**.5) + 1):
    if P[i]:
        P[i*i::i] = False

KMAX = int(r.max()) + 1
M2 = np.zeros(NF + 1, np.int64)
cD = np.zeros(NF + 1, np.int32)
cS = np.zeros(NF + 1, np.int32)
seen = np.zeros(NF + 1, np.int64)
stamp = 0

for m in range(4, NF + 1):
    stamp = m
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
    rr = len(T)
    if rr < 2:
        continue
    md = 0
    for i in range(rr - 1):
        a = T[i]
        b = T[i + 1:]
        par = ((b - a) % 2) == 0          # enfants definis seulement si meme parite
        if not par.any():
            continue
        bb = b[par]
        nD = m - (bb - a) // 2            # < m, >= 4 pour m >= 4
        nS = m - (bb + a) // 2            # < m ; filtrer >= 4
        nS = nS[nS >= 4]
        for n_arr, c in ((nD, cD), (nS, cS)):
            if len(n_arr) == 0:
                continue
            new = seen[n_arr] != stamp
            c[n_arr[new]] = 0
            seen[n_arr[new]] = stamp
            np.add.at(c, n_arr, 1)
    touch = np.flatnonzero(seen == stamp)
    if len(touch):
        thick = touch[cD[touch] + cS[touch] >= 2]
        if len(thick):
            md = int(r[thick].max())
    M2[m] = md
    if m % 200000 == 0:
        print('m=%d  %.0fs' % (m, time.time() - t0), flush=True)

np.save('M_2thick.npy', M2)

diff = np.zeros(KMAX + 2, np.int64)
for m in range(4, NF + 1):
    rm = int(r[m])
    if rm < 2:
        continue
    if M2[m] < rm:
        diff[M2[m] + 1] += 1
        diff[rm + 1] -= 1
a2 = np.cumsum(diff)

print('k : a2(k)   (niveaux ou >0)', flush=True)
nb3 = nb2 = nbo = 0
for k in range(2, KMAX + 1):
    if a2[k]:
        if a2[k] == 3:
            nb3 += 1
        elif a2[k] == 2:
            nb2 += 1
        else:
            nbo += 1
        print('%d : %d' % (k, a2[k]), flush=True)
print('niveaux a2=2 : %d | a2=3 : %d | autres : %d' % (nb2, nb3, nbo),
      flush=True)
# rechutes : niveaux a2(k)=2 au-dela du premier k ou a2=3 atteint
first3 = next((k for k in range(2, KMAX + 1) if a2[k] == 3), None)
rel = [k for k in range(first3 or KMAX, KMAX + 1) if a2[k] == 2]
print('rechutes a 2 apres premier 3 :', rel[:30], ' total=%d' % len(rel),
      flush=True)
print('FINI %.0fs' % (time.time() - t0), flush=True)
