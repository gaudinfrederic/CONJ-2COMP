import numpy as np, time, sys

RT = 'rtable_1M.npy'
OUT = 'falsif_tau'

r = np.load(RT)
NF = len(r)
N = NF - 1   # la table couvre m dans [0, N]

# --- L_k = dernier u avec r(u) < k ; M_cut(k) ; KCUT dynamique
#     (meme protocole que producteur.py / verificateur.py :
#      KCUT = max{k : M_cut(k) <= N}, B_max = max M_cut + 2)
G = np.zeros(int(r.max()) + 1, np.int64)   # G[v] = dernier m avec r(m) = v
maxR = np.zeros(3, np.int64)
for m in range(4, N + 1):
    v = int(r[m])
    if m > G[v]:
        G[v] = m
    c = m % 3
    if v > maxR[c]:
        maxR[c] = v
Kvalid = int(maxR.min())
Lk = np.zeros(Kvalid + 1, np.int64)
run = 0
for v in range(0, Kvalid):
    if G[v] > run:
        run = G[v]
    Lk[v + 1] = run
Mc = np.zeros(Kvalid + 1, np.int64)
for k in range(2, Kvalid + 1):
    L = int(Lk[k])
    Mc[k] = L + 1 + (L - 4) // (2 * k - 3) if L >= 4 else L + 1
KCUT = max(k for k in range(2, Kvalid + 1) if Mc[k] <= N)
Bmax = int(Mc[2:KCUT + 1].max()) + 2
kmax_at = int(Mc[2:KCUT + 1].argmax()) + 2
print('KCUT=%d ; B_max = %d (max M_cut=%d atteint a k=%d)'
      % (KCUT, Bmax, Mc[kmax_at], kmax_at), flush=True)

# --- crible jusqu'a 2*Bmax (rayons t : m-t et m+t premiers, t>=1)
NP2 = 2*Bmax + 2
P = np.ones(NP2, bool); P[0] = P[1] = False
for i in range(2, int(NP2**.5)+1):
    if P[i]:
        P[i*i::i] = False

def has_valid_child(m, kthr):
    """True si m a un enfant n<m, n>=4, r(n)>=kthr.
    Itere les ecarts croissants : d=1 donne les plus grands n en premier."""
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1  # rayons croissants
    rr = len(T)
    if rr < 2:
        return False, 0
    for d in range(1, rr):
        a = T[:rr-d]; b = T[d:]
        # enfant n1 = m - (b-a)/2  (grands n d'abord)
        v = (b - a) // 2
        n = m - v
        ok = (n >= 4) & (n < m)
        if ok.any() and (r[n[ok]] >= kthr).any():
            return True, rr
        # enfant n2 = m - (a+b)/2
        v2 = (a + b) // 2
        n2 = m - v2
        ok2 = (n2 >= 4) & (n2 < m)
        if ok2.any() and (r[n2[ok2]] >= kthr).any():
            return True, rr
    return False, rr

# --- passe unique : tau(m) = min(r(m), R_prev[classe])
Rprev = np.zeros(3, np.int64)
trouves = []
testes = 0
t0 = time.time()
LOG = open(OUT + '.log', 'w')
for m in range(6, Bmax+1):
    c = m % 3
    tau = min(int(r[m]), int(Rprev[c]))
    if tau >= 2:
        ok, rr = has_valid_child(m, tau)
        testes += 1
        if not ok:
            # contre-exemple : m puits interieur pour k in (M(m), tau]
            # calcul exact de M(m) = max r sur les enfants
            T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
            Mm = 0
            for i in range(len(T)):
                for j in range(i+1, len(T)):
                    for v in ((T[j]-T[i])//2, (T[i]+T[j])//2):
                        n = m - v
                        if 4 <= n < m and r[n] > Mm:
                            Mm = int(r[n])
            line = 'PARASITE m=%d classe=%d r=%d tau=%d M=%d -> puits pour k in (%d..%d]' % (m, c, r[m], tau, Mm, Mm, tau)
            print(line, flush=True); LOG.write(line + '\n'); LOG.flush()
            trouves.append(m)
    if int(r[m]) > Rprev[c]:
        Rprev[c] = int(r[m])
    if m % 20000 == 0:
        print('m=%d testes=%d parasites=%d t=%.0fs' % (m, testes, len(trouves), time.time()-t0), flush=True)

print('FINI. vitaux testes=%d  parasites=%s' % (testes, trouves), flush=True)
LOG.write('FINI testes=%d parasites=%s\n' % (testes, trouves)); LOG.close()
np.savez(OUT + '_res.npz', parasites=np.array(trouves), testes=testes, Bmax=Bmax, Mc=Mc)
