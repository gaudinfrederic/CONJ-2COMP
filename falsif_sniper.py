import numpy as np, time

RT = 'rtable_1M.npy'
r = np.load(RT); NF = len(r)

# crible jusqu'a 2*NF (rayons de m : m-t, m+t premiers)
P = np.ones(2*NF, bool); P[0] = P[1] = False
for i in range(2, int((2*NF)**.5)+1):
    if P[i]:
        P[i*i::i] = False

def est_enfant(m, n):
    """True si n est enfant de m : existe rayons a<b de m avec
    v=(b-a)/2=m-n ou v=(a+b)/2=m-n.  O(r)."""
    v = m - n
    T = np.flatnonzero(P[m-1:1:-1] & P[m+1:2*m-1]) + 1
    S = set(T.tolist())
    for a in T:
        if a + 2*v in S and a + 2*v != a:      # v=(b-a)/2 -> b=a+2v
            return True
        if 2*v - a in S and 2*v - a > a:        # v=(a+b)/2 -> b=2v-a
            return True
    return False

# scan : classes chargees c in {1,2} ; leader R1 (m1) et second R2 par classe
LOG = open('falsif_sniper.log', 'w')
def log(s):
    print(s, flush=True); LOG.write(s+'\n'); LOG.flush()

R1 = np.zeros(3, np.int64); M1 = np.zeros(3, np.int64)   # max r et son m
R2 = np.zeros(3, np.int64)
trig = 0; echappe = 0; cex = []
t0 = time.time()
for m in range(6, NF):
    c = m % 3
    if c in (1, 2):
        thr = min(int(r[m]), int(R1[c]))
        if int(R2[c]) < thr and R1[c] > 0:
            # m = 2e vital de sa classe au niveau k=thr ; u1 = leader
            u1 = int(M1[c]); k = thr
            if not P[2*m - 3]:            # pont tue : enfants confines en classe c
                trig += 1
                v = m - u1
                if v >= 1 and est_enfant(m, u1):
                    echappe += 1
                else:
                    cex.append((m, u1, k, int(r[m])))
                    log('PARASITE? m=%d u1=%d k=%d r=%d (u1 pas enfant, 2m-3 compose)' % (m, u1, k, r[m]))
        # mise a jour top-2
        if int(r[m]) > R1[c]:
            R2[c] = R1[c]; R1[c] = r[m]; M1[c] = m
        elif int(r[m]) > R2[c]:
            R2[c] = r[m]
    if m % 100000 == 0:
        log('m=%d triggers=%d echappes=%d cex=%d t=%.0fs' % (m, trig, echappe, len(cex), time.time()-t0))

log('FINI triggers=%d echappes=%d parasites=%s' % (trig, echappe, cex))
np.savez('falsif_sniper_res.npz', cex=np.array(cex), trig=trig, echappe=echappe)
LOG.close()
