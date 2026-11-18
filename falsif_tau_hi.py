import numpy as np, time

# Test discriminant : has_valid_child(m, tau(m))
# pour tout m <= 1e6 avec tau(m) >= 7227  ->  ferme les rangs j>=3
# a l'interieur de la table 1e6, pour k in [7227, 14089].
RT = 'rtable_1M.npy'
r = np.load(RT)
NF = len(r) - 1  # borne incluse
print('table r: m <=', NF, ' max r =', int(r.max()), flush=True)

P = np.ones(2*NF + 2, bool); P[0] = P[1] = False
for i in range(2, int((2*NF+2)**.5) + 1):
    if P[i]:
        P[i*i::i] = False

def has_valid_child(m, kthr):
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
    rr = len(T)
    if rr < 2:
        return False, rr
    for d in range(1, rr):
        a = T[:rr-d]; b = T[d:]
        n = m - (b - a)//2
        ok = (n >= 4) & (n < m)
        if ok.any() and (r[n[ok]] >= kthr).any():
            return True, rr
        n2 = m - (a + b)//2
        ok2 = (n2 >= 4) & (n2 < m)
        if ok2.any() and (r[n2[ok2]] >= kthr).any():
            return True, rr
    return False, rr

Rprev = np.zeros(3, np.int64)
trouves = []
testes = 0
t0 = time.time()
LOG = open('falsif_tau_hi.log', 'w')
for m in range(6, NF+1):
    c = m % 3
    tau = min(int(r[m]), int(Rprev[c]))
    if tau >= 7227:
        ok, rr = has_valid_child(m, tau)
        testes += 1
        if not ok:
            T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
            Mm = 0
            for i in range(len(T)):
                for j in range(i+1, len(T)):
                    for v in ((T[j]-T[i])//2, (T[i]+T[j])//2):
                        n = m - v
                        if 4 <= n < m and r[n] > Mm:
                            Mm = int(r[n])
            line = 'PARASITE m=%d classe=%d r=%d tau=%d M=%d' % (m, c, r[m], tau, Mm)
            print(line, flush=True); LOG.write(line+'\n'); LOG.flush()
            trouves.append(m)
    if int(r[m]) > Rprev[c]:
        Rprev[c] = int(r[m])

print('FINI. vitaux tau>=7227 testes=%d parasites=%s (%.0fs)' % (testes, trouves, time.time()-t0), flush=True)
LOG.write('FINI testes=%d parasites=%s\n' % (testes, trouves)); LOG.close()
np.savez('falsif_tau_hi_res.npz', parasites=np.array(trouves), testes=testes)
