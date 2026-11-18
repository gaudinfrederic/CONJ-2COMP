# verificateur.py -- VERIFICATEUR INDEPENDANT des certificats CONJ-2COMP
# (digraphe de re-pairage : table r, puits par niveau, goulots, passe tau).
# Necessite numpy uniquement (FFT pour la table r ; la table est aussi
# re-verifiee par echantillonnage direct). Aucun code partage avec
# producteur.py : les formats sont relus depuis SPECS_CERTS.md.
#
# Le verificateur recalcule TOUT :
#   - crible propre + table r propre (FFT numpy, puis re-enumeree
#     integralement dans le C jumeau / spot-checks directs ici) ;
#   - minima de classe mu_c(k) et masques de puits par niveau ;
#   - goulots (u1,u2) re-extraits + N(u1,u2) recompte ;
#   - L_k, M_cut, passe tau interieure ;
#   - b-files a(k) et m1(k) rederives et compares.
#
# Usage : python verificateur.py <N> <dossier_certs>
import sys, os, struct, time
import numpy as np

N = int(sys.argv[1])
OUT = sys.argv[2]
T0 = time.time()


def log(s):
    print("[%6.1fs] %s" % (time.time() - T0, s), flush=True)


def invalid(msg):
    print("!!! CERTIFICAT INVALIDE : %s" % msg, flush=True)
    sys.exit(3)


# ---------- crible propre ----------
P = np.ones(2 * N + 2, bool)
P[0] = P[1] = False
for i in range(2, int((2 * N + 1) ** 0.5) + 1):
    if P[i]:
        P[i * i::i] = False
log("crible 2N=%d ok" % (2 * N))
anchors = {1000000: 148933, 100000: 17984}
if N in anchors:
    pi = int(P.sum())
    if pi != anchors[N]:
        invalid("ancre crible pi(2N)=%d attendu %d" % (pi, anchors[N]))

# ---------- table r propre (FFT independante) ----------
nfft = 1 << int(np.ceil(np.log2(4 * N + 4)))
F = np.fft.rfft(P.astype(np.float64), nfft)
conv = np.rint(np.fft.irfft(F * F, nfft)).astype(np.int64)
idx = 2 * np.arange(N + 1)
r = (conv[idx] - P[:N + 1].astype(np.int64)) // 2
r[:4] = 0
log("rtable FFT ok : max=%d" % int(r.max()))

# spot-checks d'enumeration directe (methode differente : t-scan)
for m, exp in ((12, 3), (45, 9), (17, 3), (23, 3), (37, 4)):
    if m <= N:
        cnt = int(sum(1 for t in range(1 + (m & 1), m, 2)
                      if P[m - t] and P[m + t]))
        if cnt != int(r[m]) or cnt != exp:
            invalid("r(%d) FFT=%d enum=%d attendu %d" % (m, r[m], cnt, exp))
log("spot-checks r(m) enum vs FFT : OK")

primes = np.flatnonzero(P).astype(np.int64)


def rays(m):
    lo = np.searchsorted(primes, m, side="right")
    hi = np.searchsorted(primes, 2 * m, side="left")
    ps = primes[lo:hi]
    return (ps - m)[P[2 * m - ps]]


def load(fn, magic, hdr, recsize):
    path = os.path.join(OUT, fn)
    data = open(path, "rb").read()
    if len(data) < hdr.size:
        invalid("%s : %d o < en-tete" % (fn, len(data)))
    h = hdr.unpack_from(data, 0)
    if h[0] != magic or h[1] != 1:
        invalid("%s : magic/version" % fn)
    if h[2] != N:
        invalid("%s : N=%d incoherent avec %d" % (fn, h[2], N))
    exp = hdr.size + h[-1] * recsize
    if len(data) != exp:
        invalid("%s : taille %d != %d attendue" % (fn, len(data), exp))
    return data, h


HDR = struct.Struct("<4sIQQ")
HDRP = struct.Struct("<4sIQQQ")

# ---------- 1. certs_rtable.bin ----------
data, h = load("certs_rtable.bin", b"RT2C", HDR, 2)
rt = np.frombuffer(data, dtype="<u2", count=N + 1, offset=HDR.size)
nbad = int((rt != r[:N + 1]).sum())
if nbad:
    bad = np.flatnonzero(rt != r[:N + 1])[:10]
    for m in bad:
        print("  r mismatch m=%d cert=%d recalc=%d" % (m, rt[m], r[m]))
    invalid("rtable : %d valeurs divergentes" % nbad)
print("RTABLE : %d valeurs comparees, 0 divergence" % (N + 1))

# ---------- minima de classe ----------
KALL = int(r.max())
mu = np.zeros((3, KALL + 1), np.int64)
maxR = np.zeros(3, np.int64)
for m in range(4, N + 1):
    c = m % 3
    rm = int(r[m])
    if rm > maxR[c]:
        mu[c, maxR[c] + 1:rm + 1] = m
        maxR[c] = rm
Kvalid = int(maxR.min())

cache_bridge = {}
cache_full = {}


def bridge_max(m):
    if m in cache_bridge:
        return cache_bridge[m]
    if not P[2 * m - 3]:
        cache_bridge[m] = -1
        return -1
    T = rays(m)
    a = T[T != m - 3]
    ns = np.concatenate([m - (m - 3 - a) // 2, m - (a + m - 3) // 2])
    ns = ns[(ns >= 4) & (ns < m)]
    bm = int(r[ns].max()) if len(ns) else 0
    cache_bridge[m] = bm
    return bm


def full_max(m):
    if m in cache_full:
        return cache_full[m]
    T = rays(m)
    M = 0
    for i in range(len(T) - 1):
        a = T[i]
        b = T[i + 1:]
        for ns in (m - (b - a) // 2, m - (a + b) // 2):
            ns = ns[(ns >= 4) & (ns < m)]
            if len(ns):
                M = max(M, int(r[ns].max()))
    cache_full[m] = M
    return M


# ---------- 2. certs_puits.bin ----------
REC_PU = struct.Struct("<IIII BB H")
data, h = load("certs_puits.bin", b"PU2C", HDRP, REC_PU.size)
kf, count = h[3], h[4]
if kf != Kvalid:
    invalid("Kvalid cert=%d recalc=%d" % (kf, Kvalid))
if count != Kvalid - 1:
    invalid("puits count=%d != Kvalid-1" % count)
masks = np.zeros(Kvalid + 1, np.int64)
nbad = 0
npuits_tot = 0
for k in range(2, Kvalid + 1):
    off = HDRP.size + REC_PU.size * (k - 2)
    rk, m0, m1, m2, mask, cnt, _ = REC_PU.unpack_from(data, off)
    if rk != k or m0 != mu[0, k] or m1 != mu[1, k] or m2 != mu[2, k]:
        print("  puits k=%d : minima divergents" % k)
        nbad += 1
        continue
    own = 0
    if m0 == min(m0, m1, m2) or full_max(m0) < k:
        own |= 1
    if bridge_max(m1) < k:
        own |= 2
    if bridge_max(m2) < k:
        own |= 4
    if own != mask or cnt != bin(own).count("1"):
        print("  puits k=%d : mask cert=%d recalc=%d" % (k, mask, own))
        nbad += 1
        continue
    masks[k] = mask
    npuits_tot += cnt
print("PUITS : %d niveaux verifies ; total puits=%d ; mismatches=%d"
      % (Kvalid - 1, npuits_tot, nbad))
if nbad:
    sys.exit(3)

# ---------- puits niveau 1 ----------
ones = sorted(m for m in range(4, N + 1) if int(r[m]) == 1)
got = sorted(int(s) for s in
             open(os.path.join(OUT, "puits_k1.txt")).read().split())
if got != ones:
    print("  k1 : cert=%s recalc=%s" % (got, ones))
    sys.exit(3)
print("PUITS_K1 : %s verifies" % ones)

# ---------- 3. ak_bfile.txt ----------
lines = [s for s in open(os.path.join(OUT, "ak_bfile.txt"))
         .read().split("\n") if s.strip()]
nbad = 0
for i, s in enumerate(lines):
    k, v = map(int, s.split())
    exp = len(ones) if i == 0 else bin(int(masks[i + 1])).count("1")
    if k != i + 1 or v != exp:
        print("  a(%d) cert=%d recalc=%d" % (i + 1, v, exp))
        nbad += 1
if len(lines) != Kvalid:
    print("  ak bfile : %d lignes != Kvalid %d" % (len(lines), Kvalid))
    nbad += 1
print("AK_BFILE : %d lignes, %d mismatches" % (len(lines), nbad))
if nbad:
    sys.exit(3)

# ---------- 4. certs_goulots.bin ----------
REC_GO = struct.Struct("<IIIII BB H")
data, h = load("certs_goulots.bin", b"GO2C", HDR, REC_GO.size)
count = h[3]
R1 = np.zeros(3, np.int64)
R2 = np.zeros(3, np.int64)
M1 = np.zeros(3, np.int64)
gi = 0
nbad = 0
npm = 0
minN = None
for m in range(6, N + 1):
    c = m % 3
    thr = min(int(r[m]), int(R1[c]))
    if int(R2[c]) < thr and R1[c] > 0:
        u1, u2 = int(M1[c]), m
        v = u2 - u1
        pmort = not P[2 * u2 - 3]
        if gi >= count:
            print("  goulot recalcule en trop (%d,%d)" % (u1, u2))
            nbad += 1
        else:
            off = HDR.size + REC_GO.size * gi
            cu1, cu2, ck, cru1, cru2, cc, cpm, cN = REC_GO.unpack_from(data, off)
            ps = np.arange(3, u1, dtype=np.int64)
            Nw = int((P[ps] & P[2 * u1 - ps] & P[ps + 2 * v]
                      & P[2 * u2 - ps]).sum())
            ex = 2 * u1 - u2
            if 3 <= ex < u1 and P[ex] and P[2 * u1 - ex] \
                    and P[ex + 2 * v] and P[2 * u2 - ex]:
                Nw -= 1
            if (cu1, cu2, ck, cru1, cru2, cc, cpm, cN) != \
                    (u1, u2, thr, int(R1[c]), int(r[u2]), c, int(pmort), Nw):
                print("  goulot #%d mismatch : cert=%s recalc=(%d,%d,%d,%d,%d,%d,%d,%d)"
                      % (gi, (cu1, cu2, ck, cru1, cru2, cc, cpm, cN),
                         u1, u2, thr, int(R1[c]), int(r[u2]), c, int(pmort), Nw))
                nbad += 1
            if pmort:
                npm += 1
                minN = Nw if minN is None else min(minN, Nw)
            gi += 1
    if int(r[m]) > R1[c]:
        R2[c] = R1[c]
        R1[c] = r[m]
        M1[c] = m
    elif int(r[m]) > R2[c]:
        R2[c] = r[m]
if gi != count:
    print("  goulots recalcules %d != count %d" % (gi, count))
    nbad += 1
print("GOULOTS : %d verifies ; pont-mort=%d ; minN_pm=%s ; mismatches=%d"
      % (gi, npm, minN, nbad))
if nbad:
    sys.exit(3)
if minN == 0:
    print("!!! N=0 SUR GOULOT PONT-MORT - CONTRE-EXEMPLE")
    sys.exit(2)

# ---------- 5. m1_bfile.txt ----------
lines = [s for s in open(os.path.join(OUT, "m1_bfile.txt"))
         .read().split("\n") if s.strip()]
nbad = 0
for i, s in enumerate(lines):
    k, v = map(int, s.split())
    own = min(int(mu[c, i + 1]) for c in range(3))
    if k != i + 1 or v != own:
        print("  m1(%d) cert=%d recalc=%d" % (i + 1, v, own))
        nbad += 1
if len(lines) != Kvalid:
    print("  m1 bfile : %d lignes != Kvalid %d" % (len(lines), Kvalid))
    nbad += 1
print("M1_BFILE : %d lignes, %d mismatches" % (len(lines), nbad))
if nbad:
    sys.exit(3)

# ---------- 6. passe tau interieure ----------
G = np.zeros(KALL + 2, np.int64)
for m in range(4, N + 1):
    v = int(r[m])
    if m > G[v]:
        G[v] = m
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


def has_valid_child(m, kthr):
    T = rays(m)
    rr = len(T)
    if rr < 2:
        return False
    for d in range(1, rr):
        a = T[:rr - d]
        b = T[d:]
        n1 = m - (b - a) // 2
        if len(n1) and int(r[n1].max()) >= kthr:
            return True
        n2 = m - (a + b) // 2
        if len(n2) and int(r[n2].max()) >= kthr:
            return True
    return False


Rprev = np.zeros(3, np.int64)
testes = 0
parasites = []
for m in range(6, Bmax + 1):
    c = m % 3
    tau = min(int(r[m]), int(Rprev[c]))
    if tau >= 2:
        testes += 1
        if not has_valid_child(m, tau):
            parasites.append(m)
    if int(r[m]) > Rprev[c]:
        Rprev[c] = int(r[m])
print("TAU : KCUT=%d B_max=%d vitaux_testes=%d parasites=%s"
      % (KCUT, Bmax, testes, parasites))
if parasites:
    print("!!! PUITS INTERIEUR DETECTE - CONTRE-EXEMPLE : %s" % parasites)
    sys.exit(2)

# ---------- passe 2 : vitaux tau >= 7227 sur [6,N] ----------
Rprev2 = np.zeros(3, np.int64)
testes2 = 0
parasites2 = []
for m in range(6, N + 1):
    c = m % 3
    tau2 = min(int(r[m]), int(Rprev2[c]))
    if tau2 >= 7227:
        testes2 += 1
        if not has_valid_child(m, tau2):
            parasites2.append(m)
    if int(r[m]) > Rprev2[c]:
        Rprev2[c] = int(r[m])
print("TAU_HI : seuil=7227 vitaux_testes=%d parasites=%s"
      % (testes2, parasites2))
if parasites2:
    print("!!! PUITS INTERIEUR HAUT DETECTE - CONTRE-EXEMPLE : %s" % parasites2)
    sys.exit(2)

print("=" * 50)
print("VERDICT PY (independant) N=%d %.1fs" % (N, time.time() - T0))
print("  chaine : r-table + puits + goulots + tau verifies")
