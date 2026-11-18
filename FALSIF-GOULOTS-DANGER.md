# FALSIF-GOULOTS-DANGER - distribution de N et cas limites
# (falsification de la conjecture de goulot sur rtable_1M, 2026-11-15)

Mission : re-extraire les goulots (u1,u2) depuis rtable_1M.npy
(regeneree par make_rtable.py depuis run_1e6/ ; logique
falsif_lambda.py reprise verbatim), recalculer N(u1,u2) sur
chaque goulot pont-mort, produire la distribution et les goulots les
plus en danger (N=1,2,3), verifier la couverture 674, tester le regime
j>=3, lister le bord de table.
Artefacts : falsif_goulots_danger.py, falsif_goulots_danger_res.npz,
falsif_goulots_danger_summary.json.

================================================================
## 0. VERDICT
================================================================

- N=0 sur les goulots j=2 pont-mort : NON. 674/674 goulots ont
  N >= 1 ; minimum N=1 atteint en un seul point, (u1,u2)=(6,9) [M].
- Couverture identique au rapport precedent : OUI. Re-extraction =
  951 goulots totaux, 674 pont-mort ; les paires (u1,u2) sont
  EXACTEMENT celles de falsif_lambda_res.npz (sortie de
  falsif_lambda.py, regenerable ; 0 absent, 0 nouveau) ;
  N recalcule independamment : 0 divergence sur les 951 [M].
- Regime j>=3 : N=0 existe, mais uniquement en zone degeneree
  (u2 <= 31, r(u2) <= 2). Un seul cas "pont-mort ET toutes cibles
  N=0" : (10,19) ; u2=19 a r(19)=1 (un seul rayon, aucune paire de
  rayons, aucun enfant possible) : c'est le puits k=1 connu
  {4,5,6,7,19}, pas un parasite nouveau [M].
- Bord de table : aucun goulot extrait n'est non testable (le crible
  couvre 2*10^6 > 2*u2-3 pour tout u2 <= 10^6, et tout enfant
  n = u2-v verifie n < u2 <= 10^6 par construction). Ce qui est hors
  table : les goulots a u2 > 10^6, invisibles, et les suites des
  leaders finaux de classe [ouvert].

Detail classe par classe (pont-mort) : classe 0 = 316, classe 1 = 184,
classe 2 = 174. Rappel : la classe 0 est automatiquement pont-mort
(m = 0 mod 3 => 2m-3 = 0 mod 3, compose des que > 3) ; les classes 1+2
donnent 184+174 = 358 = le compte du sniper (falsif_sniper.py ne
scannait que les classes chargees {1,2}). Extraction faite sur les 3
classes comme falsif_lambda.py ; "classes chargees" dans la mission =
le domaine complet du scan.

================================================================
## 1. DISTRIBUTION DE N (674 goulots pont-mort) [M]
================================================================

    N            | nombre de goulots
    -------------+------------------
    1            |   1
    2            |   3
    3            |   3
    4..5         |   8
    6..10        |  18
    11..20       |  19
    21..50       |  56
    51..100      |  63
    101..300     | 132
    301..1000    | 177
    >1000        | 194

min = 1, mediane = 381, moyenne = 751.5, max = 4108.
N <= 5 : 15 goulots, tous a u1 <= 162 (petit leader = petit lambda).

Les 7 goulots en danger N <= 3 (u1, u2, v=u2-u1, lambda_int) :

    (u1,u2)   |  v | classe | N | lambda
    ----------+----+--------+---+--------
    (  6,  9) |  3 |   0    | 1 |  0.398
    (  9, 12) |  3 |   0    | 2 |  2.267
    ( 18, 21) |  3 |   0    | 2 |  2.855
    ( 12, 15) |  3 |   0    | 2 |  4.301
    ( 30, 33) |  3 |   0    | 3 |  5.034
    ( 24, 27) |  3 |   0    | 3 |  3.718
    ( 45, 57) | 12 |   0    | 3 |  3.986

Tous en classe 0, tous a u1 <= 45 : la zone de risque est le fond de
table (petits vitaux), jamais le bord haut. Le goulot le plus en
danger du monde visible est (6,9), seul temoin p=5 : quadruplet
(5,7,11,13). lambda=0.398 < 1 : c'est le seul goulot dont le modele
Poisson predisait une chance non triviale d'echec (e^-0.398 ~ 0.67)
et le temoin existe quand meme.

================================================================
## 2. TOP 30 PAR N CROISSANT (pont-mort) [M]
================================================================

    u1 | u2  | v   | k   | r(u2)| r(u1)| c | N   | lambda
    ---+-----+-----+-----+------+------+---+-----+-------
      6|    9|   3 |   1 |   2  |   1  | 0 |   1 |  0.398
      9|   12|   3 |   2 |   3  |   2  | 0 |   2 |  2.267
     12|   15|   3 |   3 |   3  |   3  | 0 |   2 |  4.301
     18|   21|   3 |   4 |   4  |   4  | 0 |   2 |  2.855
     24|   27|   3 |   5 |   5  |   5  | 0 |   3 |  3.718
     30|   33|   3 |   6 |   6  |   6  | 0 |   3 |  5.034
     45|   57|  12 |   9 |  10  |   9  | 0 |   3 |  3.986
     90|  102|  12 |  14 |  14  |  14  | 0 |   4 |  5.108
    105|  117|  12 |  15 |  15  |  19  | 0 |   4 |  7.270
    130|  145|  15 |  10 |  10  |  10  | 1 |   4 |  5.415
     39|   42|   3 |   7 |   8  |   7  | 0 |   5 |  7.658
     42|   45|   3 |   8 |   9  |   8  | 0 |   5 |  8.393
     60|   72|  12 |  11 |  11  |  12  | 0 |   5 |  4.886
     98|  110|  12 |   9 |   9  |   9  | 2 |   5 |  5.572
    150|  162|  12 |  20 |  20  |  21  | 0 |   5 |  5.047
     60|   75|  15 |  12 |  12  |  12  | 0 |   6 |  7.016
     84|   90|   6 |  13 |  14  |  13  | 0 |   6 |  8.949
    140|  182|  42 |  14 |  14  |  14  | 2 |   6 |  4.826
    175|  190|  15 |  13 |  13  |  13  | 1 |   6 |  7.716
     57|   60|   3 |  10 |  12  |  10  | 0 |   8 |  9.504
    305|  335|  30 |  20 |  21  |  20  | 2 |   8 |  5.994
    350|  425|  75 |  24 |  25  |  24  | 2 |   8 |  8.214
    105|  120|  15 |  18 |  18  |  19  | 0 |   9 | 11.232
    165|  180|  15 |  22 |  22  |  24  | 0 |   9 | 12.385
    165|  195|  30 |  24 |  27  |  24  | 0 |   9 | 12.434
    245|  260|  15 |  17 |  17  |  19  | 2 |   9 | 10.362
    255|  300|  45 |  32 |  32  |  32  | 0 |   9 | 11.317
    550|  580|  30 |  28 |  29  |  28  | 1 |   9 |  8.926
    105|  135|  30 |  19 |  19  |  19  | 0 |  10 | 11.422
    150|  165|  15 |  21 |  24  |  21  | 0 |  10 | 12.155

Lecture : le danger (N petit) est concentre sur les premiers goulots
de la table (u1 <= 600 pour tout le top 30) ; au-dela N croit avec
lambda ~ u1/ln^2(2u2).

================================================================
## 3. COUVERTURE (point 3 de la mission)
================================================================

- Re-extraction verbatim falsif_lambda.py : 951 goulots, identique au
  fichier stocke (falsif_lambda_res.npz, sortie de falsif_lambda.py :
  951 lignes, memes paires).
- Pont-mort : 674 dans les deux (674 = 316 + 184 + 174 par classe).
- N recalcule par formule vectorisee independante sur les 951 :
  0 divergence avec les N stockes.
- Difference de perimetre deja documentee : le sniper ne comptait que
  les classes {1,2} -> ses 358 declencheurs = exactement les 184+174
  goulots pont-mort des classes chargees non nulles. Aucune perte de
  couverture : les deux comptes se recomposent.
- v = u2-u1 = 0 mod 3 sur les 951 paires (6 | 2v partout : la
  condition Dubner decalee est verifiee partout) [M].

================================================================
## 4. CAS j>=3 - GOULOTS LARGES [M]
================================================================

Definition : m entre dans sa classe a un rang >= 3 = "2+ vitaux
au-dessus a son niveau" : #{vital u < m, meme classe, r(u) >= r(m)} >= 2
(les cibles de descente possibles sont ces vitaux).

Population : 2933 goulots larges dans la bande top-10 (rangs 3 a 10) ;
996060 vitaux au-dela du rang 10 (population immense, jamais en
danger : plus de 10 cibles a leur niveau - non retenu). Repartition
du nombre de cibles j dans la bande :

    j=2: 436 | j=3: 379 | j=4: 374 | j=5: 362 | j=6: 376
    j=7: 338 | j=8: 316 | j=9: 352
    par classe : 0: 1036 | 1: 939 | 2: 958 ; pont-mort : 2155/2933.

N(leader) sur les 2933 (leader = cible de rang 1) :
    N=0: 6 | N=1: 11 | N=2: 28 | N=3: 28 | 4-5: 46 | 6-10: 94
    11-50: 401 | >50: 2319.

Echantillon borne : 203 goulots (tous les N_leader<=3 + pas fixe
stratifie sur u2), test N sur TOUTES les cibles (jusqu'a 5). Min sur
cibles : 0 pour 19 goulots, 1 pour 25, >=2 pour 159.
Toutes-cibles N=0 : 3 cas seulement :

    u2 | classe | r(u2) | nb cibles | pont   | Ns par cible
    ---+--------+-------+-----------+--------+------------------
    16 |   1    |  2    |  2        | vivant | [0,0]
    19 |   1    |  1    |  4        | MORT   | [0,0,0,0]
    31 |   1    |  2    |  6        | vivant | [0,0,0,0,0,0]

Seul (10,19) est pont-mort + toutes cibles a 0. r(19)=1 : S(19)={12},
un rayon unique, aucune paire a<b, donc AUCUN enfant possible - le
"parasite large" est le puits k=1 deja connu ({4,5,6,7,19}), pas un
evenement nouveau. (10,16) et (25,31) ont le pont vivant
(2*16-3=29, 2*31-3=59 premiers) : ils sortent par le pont vers la
classe opposee, le confinement ne s'applique pas.

Les autres N_leader=0 (pont-mort mais au moins une cible non nulle) :
    (17,29) Ns=[0,0,1,2] - sort par la 3e cible
    (25,34) Ns=[0,1,0,0,0,0,0] - sort par la 2e cible
Statut : [M] sur l'echantillon et sur la totalite de la bande pour
N_leader ; le cas j>=3 confirme la lecture (le risque tombe des que
le nombre de cibles croit - le seul echec total est le puits trivial
de niveau 1 en fond de table).

================================================================
## 5. BORD DE TABLE
================================================================

Lecture litterale : les enfants de descente n = u2-v sont toujours
< u2 (v >= 1), donc AUCUN goulot extrait n'a un enfant > 10^6 ; tous
les tests (r, enfants, pont, N) restent dans les tables
(r <= 10^6, premiers <= 2*10^6). Ensemble vide par construction.

Ce qui change au bord :
- 145 goulots ont u2 > 5*10^5 (109 pont-mort) : les valeurs testees
  (pont 2u2-3, temoins p+2v, 2u2-p) depassent 10^6 mais restent
  < 2*10^6 : testables, rien de non verifie.
- 23 goulots ont u2 > 9*10^5 (16 pont-mort). Liste complete :

    u1     | u2    | k    | c | pm | N   | lambda
    -------+-------+------+---+----+-----+-------
    855855 |903210 |26246 | 0 |  M |4058 |4008.0
    890890 |905905 |12934 | 1 |  M |1879 |1899.0
    905905 |907060 |13055 | 1 |  V |1845 |1855.8
    850850 |910910 |13138 | 2 |  M |1775 |1803.0
    903210 |915915 |26597 | 0 |  M |3855 |3898.9
    905905 |920920 |13101 | 1 |  V |2138 |2135.7
    850850 |925925 |13165 | 2 |  M |1817 |1877.9
    925925 |929390 |13195 | 2 |  M |1877 |1872.4
    915915 |930930 |26755 | 0 |  M |3925 |3930.7
    920920 |935935 |13731 | 1 |  M |2364 |2338.8
    925925 |940940 |13641 | 2 |  M |1860 |1964.4
    930930 |943635 |26859 | 0 |  M |3992 |3951.4
    930930 |945945 |26924 | 0 |  M |3718 |3773.1
    940940 |949025 |13685 | 2 |  V |1911 |1978.5
    935935 |950950 |14268 | 1 |  V |2243 |2240.6
    930930 |960960 |27329 | 0 |  M |3834 |3731.6
    949025 |968660 |13708 | 2 |  M |1911 |1883.7
    968660 |970970 |13881 | 2 |  V |1962 |1997.1
    930930 |975975 |27561 | 0 |  M |4108 |3982.7
    970970 |985985 |13992 | 2 |  V |1852 |1914.4
    975975 |990990 |27802 | 0 |  M |3846 |3822.8
    985985 |994175 |14020 | 2 |  V |1939 |1921.8
    950950 |994840 |14324 | 1 |  M |2111 |2122.0

  Aucun danger au bord : N > 1700 partout (le haut de table est le
  regime lambda grand, oppose au fond ou N=1 existe).

- Non testable sur cette table [ouvert] :
  (a) les goulots (u1,u2) avec u2 > 10^6 - entierement invisibles ;
  (b) les leaders finaux de classe en fin de table, dont le goulot
      futur (comme u1' d'un u2' > 10^6) est hors portee :
      classe 0 : leader 990990 (r=27988), puis 975975, 997815 ;
      classe 1 : leader 994840 (r=14608), puis 950950, 935935 ;
      classe 2 : leader 994175 (r=14089), puis 985985, 970970.
      Les trois goulots dont u2 EST un leader final :
      (975975,990990) c0 pm N=3846 ; (985985,994175) c2 V N=1939 ;
      (950950,994840) c1 pm N=2111 - eux-memes testes, mais leur
      releve au niveau suivant est hors table.
  (c) l'ascendance de u2 : un u2 proche de 10^6 peut etre enfant
      d'un parent > 10^6 - non verifiable (enfants lisent vers le
      bas, parents vers le haut).

================================================================
## 6. CE QUI MANQUE
================================================================

- La table s'arrete a 10^6 : tout goulot u2 > 10^6 est invisible,
  et le risque concentre au fond (N=1 a (6,9)) dit que la zone
  dangereuse est deja entierement vue - mais la logique du modele
  Poisson (P(N=0) ~ e^-lambda) n'est pas une borne ; les goulots
  hors table restent [ouvert].
- j>=3 teste sur la bande rangs 3-10 + echantillon stratifie ; le
  bassin des vitaux de rang > 10 (996060) n'est pas epuise
  individuellement - il est sans danger par structure (10+ cibles)
  mais aucun test N n'y est fait.
- Le seul parasite large trouve est le puits trivial r=1 (u2=19) ;
  rien ne garantit qu'un parasite large degenere de meme type
  (r(u2) petit) ait ete exhaustif au-dela de la bande top-10.
- lambda_int est le modele calibre du rapport precedent
  (N/lambda 0.973/0.991) ; les N<=3 sont tous dans le regime ou le
  modele est le moins fiable (queue, caveat Maier deja consigne).
