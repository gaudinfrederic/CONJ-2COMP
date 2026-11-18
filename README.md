# CONJ-2COMP - verification certifiee du digraphe de re-pairage

DOI Zenodo : `10.5281/zenodo.24350578`

Certificats computationnels et code de verification pour la
structure de niveaux du digraphe de re-pairage sur les
partitions de Goldbach symetriques `2m = p + q`, `p < q`
(centre `m` ; `S(m) = {t >= 1 :
m-t et m+t premiers}`, `r(m) = |S(m)|`, convention A061357) :

- `V_k = {m : r(m) >= k}` ; puits de niveau `k` = sommet de
  `V_k` sans enfant retenu (`n = m - (b-a)/2` ou
  `n = m - (a+b)/2`, `a < b` rayons, `n < m`, `r(n) >= k`)
- `a(k)` = nombre de puits de niveau `k`
- goulots `(u1, u2)` et temoins `N(u1, u2)` (quadruplets de
  premiers `p, 2u1-p, p+2v, 2u2-p`)

## Scope et limitations (a lire)

- Ceci est une **verification exhaustive bornee a `m <= 1e6`** -
  *bounded verification, not a proof* - pas une preuve des
  enonces generaux, et encore moins une preuve du probleme
  binaire classique sous-jacent.
- `a(k) in {2,3}` pour `3 <= k <= 14089` est une **mesure**
  dans la table `r <= 1e6` (minima de classe `mu_c(k)`
  determines dans `m <= 1e6`) - PAS un theoreme global.
  L'enonce `#puits(V_k) <= 3` sur N entier est CONDITIONNEL :
  il se deduit de l'absence de puits interieur au-dela de la
  table (CONJ-M : `M(m) >= tau(m)` pour tout `m` avec
  `tau(m) >= 2`) ; la clause
  « `L_k < infini` pour tout `k` » (dernier `m` avec `r(m) < k`
  borne) ne ferme que la queue via `M_cut` - et des `k = 1`
  elle est le probleme binaire classique lui-meme.
- `N(u1,u2) >= 1` sur les 674 goulots a pont mort mesures est
  une mesure finie, pas une preuve de la conjecture de goulot.
- Le modele asymptotique (Hardy-Littlewood, somme ~1e-75) est
  heuristique : une somme convergente de modele, jamais une
  borne d'impossibilite ; les modeles de Poisson peuvent etre
  mis en defaut loin (caveat Maier 1985).
- Les petits runs sont des echantillons de regression, pas
  la preuve.

## Resultat (run_1e6, N = 1 000 000)

| objet                | records    | verdict                                    |
|----------------------|------------|--------------------------------------------|
| table `r(m)`         | 1 000 001  | recomparee valeur par valeur, 0 divergence |
| puits par niveau     | 14 088 niv.| `a(1)=5`, `a(2)=1`, `a(k) in {2,3}` k>=3   |
| `ak_bfile.txt`       | 14 089     | `a=2`:1826, `a=3`:12261, `a>=4`:0 (k>=3)   |
| goulots              | 951        | re-extraits + `N` recompte, 0 mismatch     |
| goulots pont-mort    | 674        | `N >= 1` partout, `min N = 1` en (6,9)     |
| passe tau interieure | 999 947    | 0 puits interieur (k <= 7226 via `M_cut`)  |

Detail des conventions, formats binaires et comptes :
`SPECS_CERTS.md`. Statuts exacts (theoreme local vs mesure
vs conditionnel) : `FALSIFICATION.md`.

Deux verificateurs independants, recomptage complet :

- C99 : `verificateur.c`, propre crible + re-enumeration
  integrale de `r(m)` (`t` par `t`), propre passe tau
- Python/numpy : `verificateur.py`, propre crible + table
  `r` par convolution FFT re-verifiee par enumeration
  directe sur echantillons, propre passe tau

Les deux verificateurs recalculent TOUT depuis les entiers
(minima de classe, masques de puits, extraction des goulots,
`N(u1,u2)`, `L_k`, `M_cut`, passe tau) : rien n'est cru du
producteur.

SHA-256 des certificats (voir `SHA256SUMS.txt` pour tous les
fichiers) : rtable `92cff4ec6dd3a364…`, puits
`dfc739f644d1d269…`, goulots `fb6cd7b359fabe8a…`.

## Quickstart

```
# verification C sur le petit run (quelques secondes)
cc -O2 -o verificateur.exe verificateur.c
./verificateur.exe 100000 run_petit

# verification Python/numpy (numpy uniquement)
python verificateur.py 100000 run_petit

# verification complete du run principal (~4-5 min)
./verificateur.exe 1000000 run_1e6
python verificateur.py 1000000 run_1e6

# regeneration des certificats (numpy seul, ~3.5 min a 1e6)
python producteur.py 100000 run_petit
python producteur.py 1000000 run_1e6
```

`run_corrupt_*/` forme la suite anti-corruption (4 mutations,
regenerees par `make_corrupt.py` depuis `run_petit`) : le
verificateur DOIT rejeter chacune (exit != 0) -

| dossier                | mutation                                        |
|------------------------|-------------------------------------------------|
| `run_corrupt_rtable/`  | `r(5000)` incrementee dans `certs_rtable.bin`   |
| `run_corrupt_skip/`    | record du niveau `k=10` supprime (niveau saute) |
| `run_corrupt_goulot/`  | `N(u1,u2)` mis a 0 sur un goulot pont-mort      |
| `run_corrupt_trunc/`   | `certs_puits.bin` coupe a mi-record             |

Detail de chaque mutation : `NOTE.txt` dans le dossier.

## Structure

```
FALSIFICATION.md     etat des mesures + statuts honnetes
PERIMETRE-REDUIT.md  reduction du perimetre de mesure
METHODE-RTABLE-FFT.md methode de calcul de la table r
FALSIF-GOULOTS-DANGER.md distribution de N sur les goulots
CONJ-2COMP-paper.tex  article (source), CONJ-2COMP-paper.pdf
lean-artifact/       artefact Lean 4 (triptyque, 0 sorry)
                     [sources seules publiees ; .lake/ local]
RAPPORT.md           protocole + verdicts + timings
SPECS_CERTS.md       spec des formats + reconciliation
manifest.json        metadonnees machine-lisibles des runs
SHA256SUMS.txt       empreintes de tous les fichiers publies
producteur.py        generation des certs (numpy)
verificateur.c       verificateur independant n1 (C99)
verificateur.py      verificateur independant n2 (numpy)
make_corrupt.py      regeneration des fixtures anti-corruption
run_petit/ run_1e6/  certificats + logs
run_corrupt_*/       suite de 4 runs mutes (doivent echouer)
LICENSE-CODE         Apache-2.0 (code)
LICENSE-DATA         CC-BY-4.0 (donnees + documents)
NOTICE               mapping chemin -> licence
(autres documents internes : journaux, brouillons,
                     scripts de depot — non publies)
```

## Licences

- Code (`*.py`, `*.c`, `Makefile`) : Apache-2.0
  (`LICENSE-CODE`, identique au `LICENSE` historique)
- Donnees (`run_*/`, `run_corrupt_*/`, certificats binaires)
  et documents (`*.md`, `*.tex`, `*.pdf`) : CC-BY-4.0
  (`LICENSE-DATA`)
- Mapping complet chemin -> licence : `NOTICE`

## Signalement / errata

Decouverte d'un contre-exemple au-dela de la borne ou d'un
defaut du protocole : signaler a
frederic.gaudin@unicaen.fr ; une nouvelle version Zenodo
(DOI de version, meme DOI de concept) publiera l'errata.
Le statut revendique est borne - tout contre-exemple
documente est une contribution legitime.

## Materiel de reference

Calculs CPU (numpy FFT + enumeration) ; les verificateurs
n'exigent ni GPU ni dependances exotiques (C99 ou numpy).
