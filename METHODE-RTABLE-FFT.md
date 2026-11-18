# METHODE - table r(m) par convolution FFT (2026-11)

## Objet

`r(m)` = #{t : m-t et m+t premiers} = nombre de decompositions
de `2m` en somme de deux premiers `p < q` = partition symetrique
a premiers distincts. Reference externe : OEIS A045917 (compte
aussi la paire `p=q` ; donc `r(m) = A045917(m) - [m premier]`).

## Formule FFT

L'indicatrice premiers `P(n) in {0,1}` pour `n <= 2N`. La
convolution `conv = P * P` donne les paires ORDONNEES :
`conv[2m] = #{(p,q) : p+q = 2m}`. D'ou :

    r(m) = ( conv[2m] - [m premier] ) / 2

Une seule FFT de taille ~4N produit TOUTES les valeurs
`r(m)` pour `m <= N` en O(N log N).

Implementation : `rtable_1M.npy` (N = 10^6, calcule en
0,2 s). Code source : `verificateur.py` (section "table r
propre", meme formule) ; `make_rtable.py` regenere le .npy
depuis le certificat signe `run_1e6/certs_rtable.bin`.

## Validation

- `b045917.txt` (OEIS, 20000 valeurs) : 0 divergence sur
  `r(m) + [m premier] = A045917(m)`.
- Points de controle internes : r(45)=9, r(12)=3, r(50)=6,
  r(40)=4, r(20)=3, r(17)=3, r(15)=3, r(195195)=7094 —
  tous exacts vs enumeration directe.

## Usage dans le pipeline

- `V_k = {m : r(m) >= k}` se lit directement dans la table :
  vitaux pour n'importe quel `k` en O(N) sans enumeration.
- L'enumeration de `S(m)` (les rayons eux-memes) n'est
  toujours necessaire QUE pour les `m` vitaux — la descente
  (enfants, puits, composantes) reste le calcul inedit,
  aucune table publiee n'existe.

## Ce qui n'est PAS remplace

La dynamique de re-pairage (arcs `m -> m - (b+-a)/2`) n'a
aucune source externe — c'est la contribution originale du
projet. La FFT ne supprime que la facture d'enumeration des
niveaux, pas le graphe.
