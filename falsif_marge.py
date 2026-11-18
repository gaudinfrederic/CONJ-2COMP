import numpy as np, time

RT = 'rtable_1M.npy'
r = np.load(RT); NF = len(r)
BMAX = 100000

P = np.ones(2*BMAX+2, bool); P[0] = P[1] = False
for i in range(2, int((2*BMAX)**.5)+1):
    if P[i]:
        P[i*i::i] = False

def marge(m):
    """M(m) = max r(n) sur les enfants ; retourne M(m), tau handled outside."""
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
    rr = len(T); M = 0
    for i in range(rr):
        a = T[i]; b = T[i+1:]
        v = (b - a)//2; n = m - v
        ok = (n >= 4) & (n < m)
        if ok.any():
            M = max(M, int(r[n[ok]].max()))
        v2 = (a + b)//2; n2 = m - v2
        ok2 = (n2 >= 4) & (n2 < m)
        if ok2.any():
            M = max(M, int(r[n2[ok2]].max()))
    return M

# delta(m) = M(m) - tau(m) pour les vitaux "precoces" (r(m) <= 400 pour cout)
LOG = open('falsif_marge.log', 'w')
def log(s):
    print(s, flush=True); LOG.write(s+'\n'); LOG.flush()

Rprev = np.zeros(3, np.int64)
res = []  # (m, classe, r(m), tau, M, delta)
t0 = time.time(); faits = 0
for m in range(6, BMAX+1):
    c = m % 3
    tau = min(int(r[m]), int(Rprev[c]))
    if tau >= 2 and int(r[m]) <= 400:
        M = marge(m)
        res.append((m, c, int(r[m]), tau, M, M - tau))
        faits += 1
    if int(r[m]) > Rprev[c]:
        Rprev[c] = int(r[m])
    if m % 20000 == 0:
        log('m=%d faits=%d t=%.0fs' % (m, faits, time.time()-t0))

res = np.array(res)
log('FINI n=%d' % len(res))
if len(res):
    # delta_min par octave de k (tau)
    for lo, hi in [(2,8),(8,16),(16,32),(32,64),(64,128),(128,256),(256,512),(512,1024)]:
        sel = res[(res[:,3] >= lo) & (res[:,3] < hi)]
        if len(sel):
            log('tau in [%d,%d) : n=%d delta_min=%d delta_med=%.0f' % (lo, hi, len(sel), sel[:,5].min(), np.median(sel[:,5])))
np.savez('falsif_marge_res.npz', res=res)
LOG.close()
