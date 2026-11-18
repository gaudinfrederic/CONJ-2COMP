import numpy as np, time, collections, json

t0 = time.time()
def log(s):
    print('[%5.0fs] %s' % (time.time()-t0, s), flush=True)

RT = 'rtable_1M.npy'
r = np.load(RT); NF = len(r)
log('rtable len=%d dtype=%s max=%d' % (len(r), r.dtype, r.max()))

# crible 0..2NF-1 (toutes les valeurs testees < 2*u2 <= 2*10^6)
P = np.ones(2*NF, bool); P[0] = P[1] = False
for i in range(2, int((2*NF)**.5)+1):
    if P[i]:
        P[i*i::i] = False
log('crible ok')

def Ncount(u1, u2):
    """N(u1,u2) vectorise : #{p in [3,u1-1] : p,2u1-p,p+2v,2u2-p premiers, p!=2u1-u2}."""
    v = u2 - u1
    ps = np.arange(3, u1, dtype=np.int64)
    mask = P[ps] & P[2*u1 - ps] & P[ps + 2*v] & P[2*u2 - ps]
    n = int(mask.sum())
    ex = 2*u1 - u2
    if 3 <= ex < u1 and P[ex] and P[2*u1-ex] and P[ex+2*v] and P[2*u2-ex]:
        n -= 1
    return n

# ---------- PASS 1 : extraction verbatim falsif_lambda + top-10 par classe ----------
R1 = np.zeros(3, np.int64); M1 = np.zeros(3, np.int64); R2 = np.zeros(3, np.int64)
goulots = []                      # (u1,u2,k,ru2,ru1,c,pont_mort)
K = 10
topv = [[], [], []]; topm = [[], [], []]
large = []                        # (m, c, rm, j_above, targets tuple)
jhist = collections.Counter(); cnt_deep = 0
for m in range(6, NF):
    c = m % 3
    # --- verbatim falsif_lambda (j=2) ---
    thr = min(int(r[m]), int(R1[c]))
    if int(R2[c]) < thr and R1[c] > 0:
        goulots.append((int(M1[c]), m, int(thr), int(r[m]), int(R1[c]), c, bool(not P[2*m-3])))
    if int(r[m]) > R1[c]:
        R2[c] = R1[c]; R1[c] = r[m]; M1[c] = m
    elif int(r[m]) > R2[c]:
        R2[c] = r[m]
    # --- top-10 par classe pour j>=3 ---
    rm = int(r[m]); tv = topv[c]; tm = topm[c]
    if len(tv) < K or rm > tv[-1]:
        j = 0
        while j < len(tv) and tv[j] >= rm:
            j += 1                     # vitaux strictement au-dessus OU egaux arrives avant
        if j >= 2:                     # 2+ vitaux au-dessus a son niveau r(m)
            large.append((m, c, rm, j, tuple(tm[:j])))
            jhist[j] += 1
        tv.insert(j, rm); tm.insert(j, m)
        if len(tv) > K:
            del tv[K:]; del tm[K:]
    elif len(tv) == K:
        cnt_deep += 1                  # rang > 10 : non elargi
log('pass1: goulots j=2 = %d ; larges j>=3 (band top10) = %d ; pool rang>10 = %d' % (len(goulots), len(large), cnt_deep))
log('final top3 per class: ' + str({c: list(zip(topm[c][:3], topv[c][:3])) for c in range(3)}))

# ---------- PASS 2 : couverture vs falsif_lambda_res.npz + N recalcule ----------
d = np.load('falsif_lambda_res.npz', allow_pickle=True)
res = d['res']
stored = {(int(a), int(b)): (int(nn), float(ll)) for a, b, nn, ll in zip(res[:,0], res[:,1], res[:,7], res[:,8])}
mine = {(u1, u2) for (u1, u2, *_ ) in goulots}
miss_mine = [k for k in stored if k not in mine]
miss_stored = [k for k in mine if k not in stored]
log('couverture: stored=%d mine=%d manquants_dans_mien=%d nouveaux=%d' % (len(stored), len(mine), len(miss_mine), len(miss_stored)))
if miss_mine: log('  absents du mien: %s' % str(miss_mine[:20]))
if miss_stored: log('  nouveaux non stockes: %s' % str(miss_stored[:20]))

pm = [g for g in goulots if g[6]]
log('goulots pont-mort extraits: %d' % len(pm))

rows = []
Nmis = 0
for (u1, u2, k, ru2, ru1, c, pont) in goulots:
    n = Ncount(u1, u2)
    sn, slam = stored.get((u1, u2), (None, None))
    if sn is not None and sn != n:
        Nmis += 1
        log('  MISMATCH N (%d,%d): stocke=%d recalcule=%d' % (u1, u2, sn, n))
    rows.append((u1, u2, k, ru2, ru1, c, pont, n, slam))
log('N recalcules: %d goulots, mismatches vs stocke: %d' % (len(rows), Nmis))

pmrows = [x for x in rows if x[6]]
Narr = np.array([x[7] for x in pmrows])
log('pont-mort: N min=%d ; N==0: %d ; N==1: %d ; N==2: %d ; N==3: %d' % (Narr.min(), (Narr==0).sum(), (Narr==1).sum(), (Narr==2).sum(), (Narr==3).sum()))

# distribution
buckets = [(1,1),(2,2),(3,3),(4,5),(6,10),(11,20),(21,50),(51,100),(101,300),(301,1000),(1001,10**9)]
dist = [('%d-%d' % (a,b) if b < 10**9 else '>1000', int(((Narr>=a)&(Narr<=b)).sum())) for a,b in buckets]
log('distribution N pont-mort: ' + str(dist))

# ---------- PASS 3 : larges j>=3 ----------
# N leader pour tous les larges ; N sur toutes cibles pour echantillon
leadN = np.zeros(len(large), np.int64)
for i, (m, c, rm, j, tg) in enumerate(large):
    leadN[i] = Ncount(tg[0], m)
log('larges: N(leader) min=%d, N_leader==0: %d' % (leadN.min(), int((leadN==0).sum())))

# echantillon ~200 : tous N_leader<=3 + pas fixe sur le reste
idx_small = [i for i in range(len(large)) if leadN[i] <= 3]
rest = [i for i in range(len(large)) if leadN[i] > 3]
step = max(1, len(rest) // max(1, 200 - len(idx_small)))
sample = idx_small + rest[::step]
sample = sorted(set(sample))[:260]
log('larges echantillon: %d (dont N_leader<=3: %d)' % (len(sample), len(idx_small)))

samp_rows = []
for i in sample:
    m, c, rm, j, tg = large[i]
    Ns = [Ncount(t, m) for t in tg[:5]]
    samp_rows.append((tg[0], m, c, rm, j, bool(not P[2*m-3]), Ns))
allzero = [x for x in samp_rows if all(n == 0 for n in x[6])]
log('larges echantillon: min Ns=%d ; tous-targets-N==0 : %d' % (min(min(x[6]) for x in samp_rows), len(allzero)))
if allzero:
    for x in allzero[:20]: log('  PARASITE-LARGE? %s' % str(x))
minlead = [x for x in samp_rows if x[6][0] == 0]
log('  N_leader==0 dans echantillon: %d' % len(minlead))
for x in minlead[:30]:
    log('  N_leader=0: u1=%d u2=%d c=%d r=%d j=%d pm=%s Ns=%s' % (x[0],x[1],x[2],x[3],x[4],x[5],x[6]))

# ---------- PASS 4 : bord ----------
edge9 = [x for x in pmrows if x[1] > 900000]
edge5 = [x for x in pmrows if x[1] > 500000]
log('bord: u2>9e5 = %d ; u2>5e5 = %d' % (len(edge9), len(edge5)))

np.savez('falsif_goulots_danger_res.npz',
         rows=np.array(rows, dtype=object),
         large=np.array(large, dtype=object),
         leadN=leadN,
         samp=np.array(samp_rows, dtype=object),
         edge9=np.array(edge9, dtype=object))

# dump json pour le rapport
out = {
 'total_goulots': len(goulots), 'pontmort': len(pm),
 'couverture': {'stored': len(stored), 'mine': len(mine), 'missing_in_mine': miss_mine[:50], 'extra_in_mine': miss_stored[:50], 'N_mismatch': Nmis},
 'Ndist': dist,
 'N_counts': {int(v): int((Narr==v).sum()) for v in sorted(set(Narr.tolist())) if v <= 10},
 'larges_band': len(large), 'larges_deep': cnt_deep, 'jhist': dict(jhist),
 'larges_Nleader0': int((leadN==0).sum()), 'larges_sample': len(sample),
 'larges_allzero': len(allzero),
}
json.dump(out, open('falsif_goulots_danger_summary.json','w'), indent=1)
log('FINI')
