import numpy as np, time, os

# CONJ-M : delta(m) = M(m) - tau(m) >= 0 pour tout m (marge de puits).
# tau(m) = min(rch(m), R(m)), R(m) = record de richesse sur la meme
# classe mod 3 (max r(w), 4 <= w < m, w ≡ m mod 3 ; R = 0 pour les
# starters {4,5,6}).
# M(m) = max(M_delta[m], M_sigma[m]) = richesse max d'un enfant.
# delta < 0 <=> puits interieur au sens de CONJ-M (enfants sous tau).
# ATTENTION : M - r(m) < 0 mesure autre chose - un puits a son propre
# niveau r(m), ce n'est PAS la marge de CONJ-M.
# Ce script attend la fin de falsif_delta_sigma puis analyse la marge.

t0 = time.time()
while not (os.path.exists('M_delta.npy') and os.path.exists('M_sigma.npy')):
    time.sleep(60)

r = np.load('rtable_1M.npy')
MD = np.load('M_delta.npy'); MS = np.load('M_sigma.npy')
M = np.maximum(MD, MS)
NF = len(r) - 1

# R(m) : maximum courant de r sur chaque classe mod 3 (w < m).
R = np.zeros(NF + 1, dtype=r.dtype)
for c in (0, 1, 2):
    idx = np.arange(4, NF + 1)
    idx = idx[idx % 3 == c]
    R[idx] = np.maximum.accumulate(r[idx - 3])
R[4:7] = 0                      # starters : ensemble vide -> R = 0

tau = np.minimum(r, R)

ok = r >= 2                     # sommets emettant potentiellement des arcs
m_idx = np.flatnonzero(ok)
delta = M[m_idx] - tau[m_idx]

neg = m_idx[delta < 0]
print('sommets r>=2 :', len(m_idx))
print('delta < 0 (PUITS INTERIEURS, CONJ-M) :', len(neg))
if len(neg):
    print('contre-exemples :', neg[:50])
np.save('delta_margin.npy', delta)

# diagnostic separe : M - r (puits a leur propre niveau r(m), pas CONJ-M)
selfwell = m_idx[M[m_idx] - r[m_idx] < 0]
print('M - r < 0 (puits propres, hors CONJ-M) :', len(selfwell))

vals, cnts = np.unique(delta, return_counts=True)
print('distribution delta :')
for v, c in zip(vals[:15], cnts[:15]):
    print('  delta=%d : %d' % (v, c))
print('  ...')
print('delta=0 (marge nulle) :', int(cnts[vals == 0][0]) if (vals == 0).any() else 0)
z = m_idx[delta == 0]
print('premiers sommets a marge nulle :', z[:30])
print('FINI %.0fs' % (time.time() - t0))
