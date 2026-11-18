# producteur.py -- PRODUCTEUR des certificats CONJ-2COMP (digraphe de
# re-pairage : puits par niveau, goulots, table r(m)).
#
# Produit, pour une borne N donnee :
#   <out>/certs_rtable.bin  - table r(m) pour m in [0,N]  (u16 LE)
#   <out>/certs_puits.bin   - par niveau k in [2,Kvalid] : minima de classe
#                             (mu0,mu1,mu2) + masque des puits
#   <out>/certs_goulots.bin - goulots (u1,u2) + champs + N(u1,u2) mesure
#   <out>/puits_k1.txt      - puits du niveau 1 ({m >= 4 : r(m)=1})
#   <out>/ak_bfile.txt      - b-file a(k) = #puits du niveau k (k=1..Kvalid)
#   <out>/m1_bfile.txt      - b-file m1(k) = min V_k        (k=1..Kvalid)
#   <out>/stats.txt         - comptes, timings, sha256 des certs
#   <out>/producteur_log.txt
#
# Formats binaires little-endian (voir SPECS_CERTS.md).
#
# Methode : crible numpy -> table r par UNE convolution FFT (exacte, u16)
# -> minima de classe / goulots / passe-tau interieure. Toutes les
# emissions sont deterministes : tri par k (puits), par m (goulots).
#
# Usage : python producteur.py <N> <dossier_sortie>
import sys, os, struct, time, json, hashlib
import numpy as np

N = int(sys.argv[1])
OUT = sys.argv[2]
os.makedirs(OUT, exist_ok=True)
T0 = time.time()
LOG = open(os.path.join(OUT, "producteur_log.txt"), "w", encoding="utf-8")


def log(s):
    print("[%6.1fs] %s" % (time.time() - T0, s), flush=True)
    LOG.write(s + "\n")
    LOG.flush()


# ---------- crible jusqu'a 2N ----------
P = np.ones(2 * N + 2, bool)
P[0] = P[1] = False
for i in range(2, int((2 * N + 1) ** 0.5) + 1):
    if P[i]:
        P[i * i::i] = False
log("crible 2N=%d ok" % (2 * N))

# ---------- table r par convolution FFT ----------
nfft = 1 << int(np.ceil(np.log2(4 * N + 4)))
F = np.fft.rfft(P.astype(np.float64), nfft)
conv = np.rint(np.fft.irfft(F * F, nfft)).astype(np.int64)
idx = 2 * np.arange(N + 1)
r = (conv[idx] - P[:N + 1].astype(np.int64)) // 2
r[:4] = 0
KALL = int(r.max())
assert KALL < 65536, "r(m) depasse u16"
log("rtable FFT ok : max r=%d" % KALL)

# ---------- certs_rtable.bin ----------
hdr = struct.Struct("<4sIQQ")
rt = r.astype("<u2")
data_rt = hdr.pack(b"RT2C", 1, N, N + 1) + rt.tobytes()
with open(os.path.join(OUT, "certs_rtable.bin"), "wb") as f:
    f.write(data_rt)
log("certs_rtable.bin : %d octets (N+1=%d valeurs u16)"
    % (len(data_rt), N + 1))

# ---------- rayons via liste de premiers (enumeration) ----------
primes = np.flatnonzero(P).astype(np.int64)


def rays(m):
    """S(m) = {t>=1 : m-t,m+t premiers}, tries croissant.
    Via les premiers p in (m,2m) : t = p-m, garde si P[2m-p]."""
    lo = np.searchsorted(primes, m, side="right")
    hi = np.searchsorted(primes, 2 * m, side="left")
    ps = primes[lo:hi]
    return (ps - m)[P[2 * m - ps]]


# ---------- minima de classe mu_c(k) ----------
maxR = np.zeros(3, np.int64)
mu = np.zeros((3, KALL + 1), np.int64)
for m in range(4, N + 1):
    c = m % 3
    rm = int(r[m])
    if rm > maxR[c]:
        mu[c, maxR[c] + 1:rm + 1] = m
        maxR[c] = rm
Kvalid = int(maxR.min())          # tout k <= Kvalid a ses 3 minima
log("maxR par classe = %s ; Kvalid = %d" % (maxR.tolist(), Kvalid))

# ---------- puits par niveau (k >= 2) ----------
# mu_c charge : puits ssi bridge_max(mc) < k (pont 2mc-3 mort -> -1)
# mu0        : puits ssi min global OU M(mu0) < k (enumeration complete)
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
    n1 = m - (m - 3 - a) // 2
    n2 = m - (a + m - 3) // 2
    ns = np.concatenate([n1, n2])
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
                mx = int(r[ns].max())
                if mx > M:
                    M = mx
    cache_full[m] = M
    return M


REC_PU = struct.Struct("<IIII BB H")   # k,mu0,mu1,mu2,mask,count,pad = 20 o
recs_puits = []
ak = {1: 0}
for k in range(2, Kvalid + 1):
    m0, m1, m2 = (int(mu[c, k]) for c in range(3))
    mask = 0
    if m0 == min(m0, m1, m2) or full_max(m0) < k:
        mask |= 1
    if bridge_max(m1) < k:
        mask |= 2
    if bridge_max(m2) < k:
        mask |= 4
    cnt = bin(mask).count("1")
    ak[k] = cnt
    recs_puits.append(REC_PU.pack(k, m0, m1, m2, mask, cnt, 0))
log("puits par niveau calcules (k=2..%d)" % Kvalid)

# ---------- puits niveau 1 ----------
ones = [m for m in range(4, N + 1) if int(r[m]) == 1]
ak[1] = len(ones)
with open(os.path.join(OUT, "puits_k1.txt"), "w", encoding="utf-8") as f:
    for m in ones:
        f.write("%d\n" % m)
log("puits k=1 : %s" % ones)

# ---------- certs_puits.bin ----------
hdrp = struct.Struct("<4sIQQQ")
data_pu = hdrp.pack(b"PU2C", 1, N, Kvalid, len(recs_puits)) + b"".join(recs_puits)
with open(os.path.join(OUT, "certs_puits.bin"), "wb") as f:
    f.write(data_pu)
log("certs_puits.bin : %d octets (%d niveaux x %d o)"
    % (len(data_pu), len(recs_puits), REC_PU.size))

# ---------- b-files ----------
with open(os.path.join(OUT, "ak_bfile.txt"), "w", encoding="utf-8") as f:
    for k in range(1, Kvalid + 1):
        f.write("%d %d\n" % (k, ak[k]))
with open(os.path.join(OUT, "m1_bfile.txt"), "w", encoding="utf-8") as f:
    for k in range(1, Kvalid + 1):
        f.write("%d %d\n" % (k, min(int(mu[c, k]) for c in range(3))))
n2 = sum(1 for k in range(3, Kvalid + 1) if ak[k] == 2)
n3 = sum(1 for k in range(3, Kvalid + 1) if ak[k] == 3)
nbig = sum(1 for k in range(3, Kvalid + 1) if ak[k] >= 4)
log("a(k) : a(1)=%d a(2)=%d ; k>=3 : a=2:%d niveaux, a=3:%d, a>=4:%d"
    % (ak[1], ak[2], n2, n3, nbig))

# ---------- goulots (verbatim falsif_lambda, 3 classes) ----------
R1 = np.zeros(3, np.int64)
M1 = np.zeros(3, np.int64)
R2 = np.zeros(3, np.int64)
goulots = []
for m in range(6, N + 1):
    c = m % 3
    thr = min(int(r[m]), int(R1[c]))
    if int(R2[c]) < thr and R1[c] > 0:
        goulots.append((int(M1[c]), m, int(thr), int(r[m]),
                        int(R1[c]), c, bool(not P[2 * m - 3])))
    if int(r[m]) > R1[c]:
        R2[c] = R1[c]
        R1[c] = r[m]
        M1[c] = m
    elif int(r[m]) > R2[c]:
        R2[c] = r[m]
log("goulots extraits : %d (pont-mort : %d)"
    % (len(goulots), sum(1 for g in goulots if g[6])))


def Ncount(u1, u2):
    v = u2 - u1
    ps = np.arange(3, u1, dtype=np.int64)
    mask = P[ps] & P[2 * u1 - ps] & P[ps + 2 * v] & P[2 * u2 - ps]
    n = int(mask.sum())
    ex = 2 * u1 - u2
    if 3 <= ex < u1 and P[ex] and P[2 * u1 - ex] and P[ex + 2 * v] \
            and P[2 * u2 - ex]:
        n -= 1
    return n


REC_GO = struct.Struct("<IIIII BB H")  # u1,u2,k,ru1,ru2,classe,pm,N = 24 o
recs_go = []
Nmin_pm = None
for (u1, u2, k, ru2, ru1, c, pm) in goulots:
    nn = Ncount(u1, u2)
    if pm and (Nmin_pm is None or nn < Nmin_pm):
        Nmin_pm = nn
    recs_go.append(REC_GO.pack(u1, u2, k, ru1, ru2, c, int(pm), nn))
data_go = hdr.pack(b"GO2C", 1, N, len(recs_go)) + b"".join(recs_go)
with open(os.path.join(OUT, "certs_goulots.bin"), "wb") as f:
    f.write(data_go)
log("certs_goulots.bin : %d octets ; min N pont-mort = %s"
    % (len(data_go), Nmin_pm))

# ---------- passe tau interieure ----------
# L_k = max{m : r(m) < k} (mesure dans la table) ; G[v] = max m avec r=v
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
log("KCUT=%d ; B_max=%d (Mcut max a k=2..%d)" % (KCUT, Bmax, KCUT))

Rprev = np.zeros(3, np.int64)
testes = 0
parasites = []


def has_valid_child(m, kthr):
    T = rays(m)
    rr = len(T)
    if rr < 2:
        return False
    for d in range(1, rr):
        a = T[:rr - d]
        b = T[d:]
        n = m - (b - a) // 2
        if len(n) and int(r[n].max()) >= kthr:
            return True
        n2 = m - (a + b) // 2
        if len(n2) and int(r[n2].max()) >= kthr:
            return True
    return False


for m in range(6, Bmax + 1):
    c = m % 3
    tau = min(int(r[m]), int(Rprev[c]))
    if tau >= 2:
        testes += 1
        if not has_valid_child(m, tau):
            parasites.append(m)
    if int(r[m]) > Rprev[c]:
        Rprev[c] = int(r[m])
log("passe tau : %d vitaux testes, parasites=%s" % (testes, parasites))

# ---------- stats + sha ----------
def sha16(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


files = ["certs_rtable.bin", "certs_puits.bin", "certs_goulots.bin",
         "puits_k1.txt", "ak_bfile.txt", "m1_bfile.txt"]
shas = {fn: sha16(os.path.join(OUT, fn)) for fn in files}
with open(os.path.join(OUT, "stats.txt"), "w", encoding="utf-8") as f:
    f.write("N=%d\n" % N)
    f.write("KALL(max r)=%d ; maxR per classe=%s ; Kvalid=%d\n"
            % (KALL, maxR.tolist(), Kvalid))
    f.write("rtable_records=%d\n" % (N + 1))
    f.write("puits_niveaux=%d (k=2..%d) ; puits_k1=%s\n"
            % (len(recs_puits), Kvalid, ones))
    f.write("a(k): a1=%d a2=%d ; k>=3 : a=2:%d a=3:%d a>=4:%d\n"
            % (ak[1], ak[2], n2, n3, nbig))
    f.write("goulots=%d ; pont_mort=%d ; minN_pm=%s\n"
            % (len(goulots), sum(1 for g in goulots if g[6]), Nmin_pm))
    f.write("KCUT=%d ; B_max=%d ; tau_testes=%d ; parasites=%d\n"
            % (KCUT, Bmax, testes, len(parasites)))
    f.write("temps_total=%.1fs\n" % (time.time() - T0))
    for fn in files:
        f.write("sha256 %s = %s\n" % (fn, shas[fn]))
log("stats.txt ecrit ; total %.1fs" % (time.time() - T0))
LOG.close()
