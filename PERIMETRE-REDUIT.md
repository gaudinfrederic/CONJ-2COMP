# PERIMETRE REDUIT (apres veille bibliographique ciblee)

NOTE DE STATUT : le scan final a ete mene de facon exhaustive
sur les vitaux jusqu'a m <= 10^6 (999 947 testes, 0 parasite) -
le perimetre reduit ci-dessous reste la justification de
l'approche vitaux-seuls adoptee par la passe tau.

## Ce que la litterature couvre deja : NE PAS REFAIRE

| Brique | Couvert par | Consequence pour nous |
|---|---|---|
| Correlations r(n)r(n+h), moments de r | Granville 2007, Montgomery-Vaughan 1975, Goldston-Yang | ne pas formuler d'heuristique de correlation |
| Comptage asymptotique de tuples premiers en configuration lineaire | Green-Tao 2010 (Linear equations in primes) | toute densite asymptotique d'arcs = derivee, la citer ne pas la recalculer |
| Filtre r(n)>=k a l'infini | trivial sous HL (filtre vrai p.p.) | aucun calcul asymptotique a mener |

## Ce qui reste : la fenetre transitionnelle

Un parasite (puits interieur) ne peut exister que parmi les vitaux proches
du bord bas du niveau. Bord bas mesure (premier m avec r(m)>=k) :

| k | premier vital | zone de chasse retenue [lo, 10*lo] | vitaux dans la zone |
|---|---|---|---|
| 64 | 630 | 630 - 6300 | ~4300 |
| 128 | 1365 | 1365 - 13650 | ~8700 |
| 256 | 3465 | 3465 - 34650 | ~22600 |
| 512 | 8085 | 8085 - 80850 | ~52000 |
| 1024 | 19635 | 19635 - 196350 | ~128000 |

Total ~2.2e5 vitaux a tester avec has_valid_child court-circuite,
au lieu du scan exhaustif d'arcs jusqu'a 1e6 (strategie retenue :
la passe tau finale a teste les vitaux seuls, exhaustivement).

## Justification de la borne 10*lo

Au-dela de ~10x le premier vital, les enfants proches de m ont r(m) >> k
(la richesse monte en m/ln2 m) : tout pairage de rayons produit
massivement des enfants valides. Le regime est couvert par l'asymptotique
Green-Tao/HL. La zone [lo,10lo] contient les minima de classe mesures et
toute la region ou le filtre r(n)>=k mord encore.

## Verdict honnete

- Nouveaute residuelle : MESURE dans la bande, pas formule.
- Green-Tao couvre l'asymptotique : notre objet n'est nouveau qu'a
  echelle finie. Le papier doit le dire.
- Si un parasite apparait dans la bande : contre-exemple reel.
  Hors bande : pratiquement exclu par l'asymptotique (non prouve).

## Veille anteriorite (ciblee arXiv/OEIS/Zenodo/Preprints)

Verdict : les 4 resultats (graphe de re-appariement sur V_k, puits =
minima mod 3, oscillation {2,3} par mort/reemergence du pont 2m-3,
zero puits interieur dans la bande, suite des premiers vitaux) :
pas de trace trouvee. Revendication "inedit" possible avec precautions :

- Citer : primality radii (Kak 2014),
  graphes voisins Bozek 2019 (arXiv:1909.09900) et Das et al. 2021
  (arXiv:1611.10259), suites A061357, A001172/A258713, A109679,
  A000954. Le verrou mod 3 elementaire n'est pas revendicable.
- Reserve residuelle : MathSciNet/zbMATH paywall non couvert a 100 %.
- Suite des premiers vitaux absente de l'OEIS : soumission possible.
- r(m) = A061357(m) (t>=1, premiers distincts) ; A002375/A045917
  incluent t=0 (2m=m+m pour m premier). VERIFIE : r_table(17)=3,
  r_table(23)=3, r_table(37)=4 -> convention t>=1 confirmee dans la
  table ET la descente. L'ancienne validation "0 divergence vs
  b045917" n'etait vraie que sur m compose/pair (t=0 impossible) :
  la reference correcte est A061357, ne pas citer A045917 comme
  convention identique.
