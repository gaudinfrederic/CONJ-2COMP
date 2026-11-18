# RAPPORT - verification certifiee CONJ-2COMP

Date : 2026-11-14. Objet : digraphe de re-pairage sur les
partitions de Goldbach symetriques `2m = p + q`, `p < q`
(`S(m) = {t >= 1 : m-t et m+t premiers}`, `r(m) = |S(m)|`,
convention A061357 - PAS A045917 qui inclut `t = 0`).

Protocole : un producteur (`producteur.py`, numpy FFT +
enumeration) ecrit des certificats binaires + texte ; DEUX
verificateurs independants (`verificateur.c` C99,
`verificateur.py` numpy) recomptent TOUT depuis les entiers
- crible propre, table `r` propre (C : re-enumeration
integrale `t` par `t` ; Python : FFT + enumerations
directes de controle), minima de classe, masques de puits,
extraction des goulots, temoins `N`, `L_k`/`M_cut`, passe
tau interieure. Aucune valeur du producteur n'est crue.
Formats : `SPECS_CERTS.md`.

## Verdicts (run principal `run_1e6`, N = 1 000 000)

| etape                 | volume        | verificateur C | verificateur Py |
|-----------------------|---------------|----------------|-----------------|
| crible `2N`           | pi = 148 933  | OK (ancre)     | OK (ancre)      |
| table `r(m)`          | 1 000 001 val.| 0 divergence   | 0 divergence    |
| puits `k = 2..14089`  | 40 436 puits  | 0 mismatch     | 0 mismatch      |
| puits `k = 1`         | {4,5,6,7,19}  | OK             | OK              |
| `ak_bfile.txt`        | 14 089 lignes | 0 mismatch     | 0 mismatch      |
| `m1_bfile.txt`        | 14 089 lignes | 0 mismatch     | 0 mismatch      |
| goulots               | 951 records   | 0 mismatch     | 0 mismatch      |
| - dont pont-mort      | 674           | min N = 1      | min N = 1       |
| passe tau interieure  | 999 947 vitaux| 0 parasite     | 0 parasite      |

Timings (machine de reference, x86_64 Windows) :
producteur 204.1 s ; verificateur C 112.6 s ; verificateur
Python 258.3 s (meme chaine, plus lent sur les enumerations
de paires de rayons par niveau ; timings incluant la passe
TAU_HI ajoutee ulterieurement).

Petit run (`run_petit`, N = 1e5) : memes verdicts en ~3 s
(producteur), ~1 s (C), ~3 s (Python) - echantillon de
regression.

## Mesures principales (borne 1e6)

- `a(1) = 5` : puits `{4, 5, 6, 7, 19}` ; `a(2) = 1` : `{8}`
- `a(k) in {2, 3}` pour `3 <= k <= 14089` : 1 826 niveaux
  a 2 puits, 12 261 a 3 (52 fenetres de 2 puits, derniere
  `[14021, 14089]` ; la poursuite projetee vers ~14324 est
  NON certifiee - hors table)
- 951 goulots `(u1, u2)`, 674 a pont mort (`2*u2-3`
  composite) : `N(u1,u2) >= 1` sur 674/674, `min N = 1`
  en `(6, 9)` (temoin `p = 5` ; quadruplet 5,7,11,13)
- passe tau : `KCUT = 7226`, `B_max = 999 958`,
  999 947 vitaux testes, 0 puits interieur
- `Kvalid = 14089` (maxR par classe `[27988, 14608, 14089]`)

## Statuts logiques (rappel - voir FALSIFICATION.md)

- Statut de puits de chaque `mu_c(k)` dans la table :
  theoreme local inconditionnel (segment fini).
- `a(k) in {2,3}`, `k <= 14089` : MESURE exhaustive dans
  la table `m <= 1e6`.
- `#puits(V_k) <= 3` sur N entier : CONDITIONNEL a l'absence
  de puits interieur au-dela de la table (CONJ-M) ; `L_k` fini
  (dernier `m` avec `r(m) < k` borne) ne ferme que la queue et
  implique, des `k = 1`, le probleme binaire classique -
  jamais borne finie.
- `N(u1,u2) >= 1` : mesure sur les goulots a portee ;
  conjecture ouverte en general. Somme de modele ~1e-75 =
  heuristique Hardy-Littlewood convergente, jamais borne
  d'impossibilite (caveat Maier 1985).

## Suite anti-corruption (4 fixtures, regeneration
## `python make_corrupt.py run_petit`)

| fixture                | mutation                     | C   | Py  |
|------------------------|------------------------------|-----|-----|
| `run_corrupt_rtable/`  | `r(5000)` +1                 | 3   | 3   |
| `run_corrupt_skip/`    | record niveau k=10 supprime  | 3   | 3   |
| `run_corrupt_goulot/`  | `N` mise a 0 sur pont-mort   | 3   | 3   |
| `run_corrupt_trunc/`   | `certs_puits.bin` coupe      | 3   | 3   |

Les 4 mutations sont rejetees par les deux verificateurs
(exit != 0). `NOTE.txt` dans chaque dossier decrit la
mutation exacte.

## Reproduction

```
python producteur.py 100000 run_petit     # ~3 s
python producteur.py 1000000 run_1e6      # ~3.5 min
cc -O2 -o verificateur.exe verificateur.c
./verificateur.exe 100000 run_petit       # ~1 s
./verificateur.exe 1000000 run_1e6        # ~1.2 min
python verificateur.py 100000 run_petit   # ~3 s
python verificateur.py 1000000 run_1e6    # ~5 min
```

Environment : Python 3.14.2, numpy 2.5.2, gcc 15 (win32)
(C99, -O2), Windows x86_64.

## SHA-256 des certificats (run_1e6 ; complet : SHA256SUMS.txt)

```
92cff4ec6dd3a364...  certs_rtable.bin   (2 000 026 o)
dfc739f644d1d269...  certs_puits.bin    (  281 792 o)
fb6cd7b359fabe8a...  certs_goulots.bin  (   22 848 o)
2e00ee2fc7c5f952...  ak_bfile.txt
31a198c92cf369e2...  m1_bfile.txt
03007323e8d77ea9...  puits_k1.txt
```

## Errata / limites connues

- L'ancien intervalle de fenetre `14090-14608` etait un
  artefact `mu2 = 0` ; la zone valide est `k <= 14089`.
- Compte a 3 puits corrige : 12 261 niveaux dans
  `[3, 14089]` (plus `a(2) = 1` a part), pas 12 262.
- `a(k) >= 4` : absent des tables (k >= 3) - mesure, pas
  borne prouvee.
