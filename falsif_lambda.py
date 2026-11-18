import numpy as np, time, math

RT = 'rtable_1M.npy'
r = np.load(RT); NF = len(r)
C4 = 4.15118086
P = np.ones(2*NF, bool); P[0] = P[1] = False
for i in range(2, int((2*NF)**.5)+1):
    if P[i]:
        P[i*i::i] = False

# ---------- 1. retrouver les goulots (u1, u2) ----------
R1 = np.zeros(3, np.int64); M1 = np.zeros(3, np.int64)
R2 = np.zeros(3, np.int64)
goulots = []  # (u1, u2, k, r_u2, classe, pont_mort)
for m in range(6, NF):
    c = m % 3
    thr = min(int(r[m]), int(R1[c]))
    if int(R2[c]) < thr and R1[c] > 0:
        goulots.append((int(M1[c]), m, int(thr), int(r[m]), int(c), bool(not P[2*m-3])))
    if int(r[m]) > R1[c]:
        R2[c] = R1[c]; R1[c] = r[m]; M1[c] = m
    elif int(r[m]) > R2[c]:
        R2[c] = r[m]
print('goulots total=%d (pont mort: %d)' % (len(goulots), sum(g[5] for g in goulots)), flush=True)

# ---------- 2. N(u1,u2) et lambda_int ----------
def facteurs_impairs(n):
    """Facteurs premiers >=5 de n (division complete)."""
    out = []
    while n % 2 == 0:
        n //= 2
    while n % 3 == 0:
        n //= 3
    d = 5
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 2
    if n >= 5:
        out.append(n)
    return out

def S4(u1, u2):
    base = C4 if u1 % 3 != 0 else 2 * C4   # nu_3=2 vs nu_3=1
    div = set()
    for x in (u1, u2, u2 - u1, 2 * u2 - u1):
        for l in facteurs_impairs(x):
            div.add(l)
    s = base
    for l in div:
        nu = len({0 % l, u1 % l, u2 % l, (u1 - u2) % l})
        s *= (l - nu) / (l - 4)
    return s

def lambda_int(u1, u2):
    v = u2 - u1
    xs = np.arange(3.0, u1 - 2.0, 0.25)          # quadrature fine
    f = 1.0 / (np.log(xs) * np.log(2*u1 - xs) * np.log(xs + 2*v) * np.log(2*u2 - xs))
    I = np.trapezoid(f, xs)
    return S4(u1, u2) * I

# calibrage (98,110)
print('calibrage (98,110): S4=%.3f lambda_int=%.3f (attendus ~21.7, ~5.31)' % (S4(98,110), lambda_int(98,110)), flush=True)

res = []
for (u1, u2, k, ru2, c, pont) in goulots:
    v = u2 - u1
    N = sum(1 for p in range(3, u1) if P[p] and P[2*u1-p] and P[p+2*v] and P[2*u2-p] and p != 2*u1 - u2)
    lam = lambda_int(u1, u2)
    res.append((u1, u2, k, ru2, int(r[u1]), c, pont, N, lam))
res = np.array(res, dtype=object)
N = res[:, 7].astype(float); L = res[:, 8].astype(float)
ratio = N / L
print('---- RESULTATS ----')
imin = int(np.argmin(N))
print('min N = %d atteint en (u1,u2)=%s' % (N.min(), res[imin, :2]))
print('N/lambda : moy=%.3f med=%.3f' % (ratio.mean(), np.median(ratio)))
print('dispersion normalisee std((N-lam)/sqrt(lam)) = %.3f (Poisson attend ~1)' % np.std((N - L)/np.sqrt(L)))
x = res[:, 4].astype(float) / np.log(2 * res[:, 1].astype(float)) ** 2
slope = np.polyfit(x, N, 1)
print('pente N ~ r(u1)/ln^2(2u2) : %.3f (borne kappa >= 3.144)' % slope[0])
np.savez('falsif_lambda_res.npz', res=res)
