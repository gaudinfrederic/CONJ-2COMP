# SPECS_CERTS - formats des certificats CONJ-2COMP

Certificats du digraphe de re-pairage : table `r(m)`, puits par
niveau, goulots, passe tau interieure. Un dossier par run
(`run_petit/` = N=1e5, `run_1e6/` = N=1e6, `run_corrupt_*/` =
mutations qui DOIVENT etre rejetees). Little-endian partout.

Rappels des definitions (toutes recomptees par les verificateurs) :

- `S(m) = {t >= 1 : m-t et m+t premiers}`, `r(m) = |S(m)|`
  (convention A061357 : `t >= 1`, representations a premiers
  distincts ; pour `m` premier `t=0` est exclu)
- classes `c = m mod 3` ; `mu_c(k)` = plus petit `m = c (mod 3)`
  avec `r(m) >= k`
- enfants de `m` depuis une paire de rayons `a < b` :
  `n1 = m - (b-a)/2`, `n2 = m - (a+b)/2`, retenu si `n < m`
  et `r(n) >= k` ; `M(m)` = max des `r(n)` sur tous les enfants ;
  pont = extremal `t* = m-3` (n'existe que si `2m-3` premier) ;
  `M_pont(m)` = max des `r(n)` restreint aux paires `(a, m-3)`
- puits de niveau `k` : `m` avec `r(m) >= k` et `M(m) < k`
- goulot `(u1, u2)` : `u1` vital de classe `c`, `u2` vital
  suivant de meme classe, `min(r(u1), r(u2))` strictement
  superieur a tout record intermediaire ; `pont-mort` ssi
  `2*u2-3` composite ; `N(u1,u2)` = nombre de `p` dans `[3, u1)`
  tels que `p`, `2*u1-p`, `p+2v`, `2*u2-p` sont tous premiers
  (`v = u2-u1`), moins l'exclus `p = 2*u1-u2` si temoin
- `L_k` = dernier `m <= N` avec `r(m) < k` (seuil de queue) ;
  `M_cut(k, L) = L + 1 + floor((L-4)/(2k-3))`
- `Kvalid = min_c maxR_c` : profondeur a laquelle les trois
  classes ont des minima definis dans la table

## 1. certs_rtable.bin - table r complete

En-tete (24 octets) :

```
struct.pack("<4sIQQ", b"RT2C", 1, N, N+1)
```

| offset | taille | champ   | valeur              |
|--------|--------|---------|---------------------|
| 0      | 4      | magic   | `RT2C` (ASCII)      |
| 4      | 4      | version | u32 = 1             |
| 8      | 8      | N       | u64, borne du run   |
| 16     | 8      | count   | u64 = N+1           |

Records : `N+1` valeurs `u16` consecutives, `r(m)` pour
`m = 0..N` (`r(m) < 65536` partout dans les runs fournis).
Taille exacte : `24 + 2*(N+1)` octets.

Verification : le verificateur recalcule sa propre table
(crible + re-enumeration `t` par `t` en C ; crible +
convolution FFT re-verifiee par enumeration directe en
Python) et compare les `N+1` valeurs une a une.

## 2. certs_puits.bin - puits par niveau

En-tete (32 octets) :

```
struct.pack("<4sIQQQ", b"PU2C", 1, N, Kvalid, Kvalid-1)
```

| offset | taille | champ   | valeur                  |
|--------|--------|---------|-------------------------|
| 0      | 4      | magic   | `PU2C`                  |
| 4      | 4      | version | u32 = 1                 |
| 8      | 8      | N       | u64                     |
| 16     | 8      | Kvalid  | u64                     |
| 24     | 8      | count   | u64 = Kvalid-1          |

Un record de 20 octets par niveau `k = 2..Kvalid`, ordre
croissant de `k` :

```
struct.pack("<IIII BB H", k, mu0, mu1, mu2, mask, cnt, pad)
```

| offset | taille | champ | sens                                     |
|--------|--------|-------|------------------------------------------|
| 0      | 4      | k     | u32, niveau (doit etre l'index attendu)  |
| 4      | 4      | mu0   | u32 = mu_0(k)                            |
| 8      | 4      | mu1   | u32 = mu_1(k)                            |
| 12     | 4      | mu2   | u32 = mu_2(k)                            |
| 16     | 1      | mask  | u8 : bit0 = mu0 puits, bit1 = mu1,       |
|        |        |       |      bit2 = mu2                          |
| 17     | 1      | cnt   | u8 = popcount(mask) = a(k)               |
| 18     | 2      | pad   | u16 = 0                                  |

Semantique du masque (re-derivee par le verificateur, pas crue) :

- `mu0` est puits ssi `mu0 = min(mu0,mu1,mu2)` (minimum global,
  le test `M(mu0) < k` complet est fait en secours) ou
  `M(mu0) < k`
- `mu1` est puits ssi `M_pont(mu1) < k` (a `k` fixe, le pont
  extremal est le seul candidat enfant retenu pour `mu1`
  minimum de sa classe : tout enfant par paire non extremale
  est strictement inferieur au minimum de sa classe, donc
  `r(n) < k` et non retenu - voir papier, Theoremes 3.10-3.11 ;
  le verificateur recalcule `M_pont`
  par enumeration complete des paires `(a, m-3)`)
- `mu2` idem.

Niveau 1 : `puits_k1.txt`, un entier par ligne, liste exacte
des `m` avec `r(m) = 1` = `{4, 5, 6, 7, 19}` dans tous les
runs fournis.

`ak_bfile.txt` : `k a(k)` par ligne, `k = 1..Kvalid`,
`a(1) = |{m : r(m)=1}|`, `a(k) = cnt` des records ci-dessus.

## 3. certs_goulots.bin - goulots et verdicts N

En-tete (24 octets) :

```
struct.pack("<4sIQQ", b"GO2C", 1, N, count)
```

Un record de 24 octets par goulot `(u1, u2)`, ordre croissant
d'emission (le verificateur re-extrait la meme sequence et
compare champ par champ) :

```
struct.pack("<IIIII BB H", u1, u2, k, r_u1, r_u2, classe,
            pont_mort, N)
```

| offset | taille | champ     | sens                            |
|--------|--------|-----------|---------------------------------|
| 0      | 4      | u1        | u32                             |
| 4      | 4      | u2        | u32                             |
| 8      | 4      | k         | u32 = min(r(u1), r(u2))         |
| 12     | 4      | r_u1      | u32                             |
| 16     | 4      | r_u2      | u32                             |
| 20     | 1      | classe    | u8 = u1 mod 3 = u2 mod 3        |
| 21     | 1      | pont_mort | u8 = 1 ssi `2*u2-3` composite   |
| 22     | 2      | N         | u16 = N(u1,u2) recompte         |

Extraction : par classe `c`, `R1`/`R2` = deux derniers records
de richesse et `M1` = l'argument de `R1` ; un goulot est emis a
chaque `m` avec `R2 < min(r(m), R1)` et `R1 > 0` (i.e. la
richesse remonte strictement au-dessus du second record : le
precedent record `u1` est un "goulot" franchi par `u2 = m`).

`N(u1,u2)` est recompte integralement : nombre de `p` dans
`[3, u1)` avec les 4 primalites, moins l'exclus eventuel
`p = 2*u1 - u2`. Un `N = 0` sur un goulot pont-mort serait un
CONTRE-EXEMPLE a la conjecture de goulot (exit 2, flagrant).

## 4. Fichiers texte annexes

- `puits_k1.txt` : les `m` avec `r(m) = 1`, un par ligne
- `ak_bfile.txt` : `k a(k)`, `k = 1..Kvalid`
- `m1_bfile.txt` : `k min_c mu_c(k)`, `k = 1..Kvalid`
- `stats.txt` : metriques du run + sha256 des fichiers du run
- `producteur_log.txt` : journal horodate du producteur

## 5. Passe tau interieure (re-jouee, pas un fichier)

Pas de certificat dedie : le resultat (aucun puits interieur
mesure) est une ABSENCE - le verificateur re-joue la passe
complete a partir de sa propre table `r` :

- `L_k`, `M_cut(k, L_k)`, `KCUT = max{k : M_cut <= N}`
- `B_max = max M_cut(k) + 2` sur `k = 2..KCUT`
- pour chaque `m <= B_max` vital (`tau = min(r(m), R_prev[c])
  >= 2`) : recherche exhaustive d'un enfant retenu par
  enumeration des paires de rayons `a < b` (court-circuit).
- tout `m` vital sans enfant retenu = puits interieur =
  contre-exemple (exit 2).
- seconde passe (ligne `TAU_HI`) : sur `[6,N]`, tout `m`
  avec `tau >= 7227` (=KCUT+1) est re-teste a son seuil
  `tau` - 290 177 vitaux, 0 parasite ; clot la queue
  `[999959,10^6]` pour `k in [7227,14089]` (les minima de
  classe portant l'enum des puits).

## Table de reconciliation (endpoint)

| run      | N     | Kvalid | puits k=1        | goulots | pont-mort | min N pm |
|----------|-------|--------|------------------|---------|-----------|----------|
| run_petit| 1e5   | 1902   | {4,5,6,7,19}     | 553     | 375       | 1        |
| run_1e6  | 1e6   | 14089  | {4,5,6,7,19}     | 951     | 674       | 1        |

| run      | a(1) | a(2) | a=2 (k>=3) | a=3 (k>=3) | a>=4 (k>=3) | vitaux tau | puits int. |
|----------|------|------|------------|------------|-------------|------------|------------|
| run_petit| 5    | 1    | 379        | 1521       | 0           | 99 963     | 0          |
| run_1e6  | 5    | 1    | 1826       | 12261      | 0           | 999 947    | 0          |

Pour `k >= 3`, `a(k) in {2, 3}` dans les deux runs (aucun
niveau n'a 4 puits ou plus dans les tables fournies) ;
`a(1) = 5` et `a(2) = 1` sont les deux niveaux d'exception.

| run      | KCUT | B_max   | fichiers certs (octets)                    |
|----------|------|---------|--------------------------------------------|
| run_petit| 1035 | 99 974  | rtable 200 026 ; puits 38 052 ; gou 13 296 |
| run_1e6  | 7226 | 999 958 | rtable 2 000 026 ; puits 281 792 ; gou 22 848 |
