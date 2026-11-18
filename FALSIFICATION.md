# FALSIFICATION - etat final (arret volontaire a 10^6)

Objet : DAG de re-pairage sur partitions de Goldbach
symetriques 2m = p + q, p < q.
S(m)={t>=1 : m-t,m+t premiers} (r(m)=A061357(m), convention t>=1
verifiee - PAS A045917 qui inclut t=0 pour m premier).
Enfants n=m-v, v=(b-a)/2 ou (a+b)/2 ; retenu si n<m et r(n)>=k.
V_k={m:r(m)>=k} ; puits = vital sans enfant retenu.

## 1. Mesures terminees (fermees)

- Passe tau interieure : 999 947 vitaux testes, 0 puits
  interieur ; fermeture inconditionnelle [M_cut,10^6] par
  tiroirs M_cut(k,L)=L+1+floor((L-4)/(2k-3)) pour k<=7226
  (B_max=999 958).
- Sniper goulots j=2 (u2 second vital classe chargee, pont mort) :
  358/358 jusqu'a 10^6 : u1 toujours enfant de u2.
- Mesure N(u1,u2) vs lambda_int sur 951 goulots :
  N/lambda moy=0.973 med=0.991 ; dispersion 0.773 (<1, binomial
  conservatif) ; pente kappa_eff~30 (plancher C4/2C2=3.144).
  Goulots pont-mort stricts : min N=1 sur 674/674
  (cas le plus serre : N=1 unique en (6,9), temoin p=5
  [quadruplet 5,7,11,13], lambda=0.398 ; danger au fond
  de table : N<=3 <=> u1<=45 [FALSIF-GOULOTS-DANGER]).
  Perimetre : falsif_lambda couvre les 3 classes mod 3
  (la classe 0 est auto-pont-mort, 2m-3 divisible par 3)
  tandis que le sniper ne couvre que {1,2} - les deux
  comptes (674/358) se recomposent exactement ; la
  conjecture de goulot ne porte que sur les charges.
- (7,10) resolu : identite arithmetique r>=5(7)=0 ; S(10)={3,7}
  donne enfant 8 ; faux goulot (pont 17 premier).
- k=1 : 5 puits {4,5,6,7,19} ; k=2 : 1 puits (m=8).

## 2. DECOUVERTE - oscillation {2,3}, pas de transition monotone

#puits(k) oscille entre 2 et 3 pour k>=3 (jamais 4+).
Mecanisme : M=max(mu1,mu2) echappe ssi 2M-3 premier ET un
enfant-pont a r>=k. Un seul enfant-pont riche cree une FENETRE
continue de 2 puits (ex : k=8103-8242 cree par n=533995 r=8242,
M=535535, 2M-3=1071067 premier - verifie).
Fenetres 2-puits mesurees (52 fenetres, k<=14089) : 3-13,
15-20, 27-28, 30-33, 35-41, 47-48, 52-58, 79-82, 86-90,
93-101, 103, 115-117, 153-158, 171-172, 208-231, 238,
354-385, 415-426, 480-482, 485-492, 526-528, 547-549,
584-604, 634-649, 656-676, 759-781, 920-944, 1097-1144,
1277-1291, 1308-1355, 1426-1427, 1688, 1835-1838,
2096-2108, 2183-2186, 2264-2278, 2616-2631, 2646-2693,
3046-3055, 3350-3501, 3713-3855, 3974-4047, 4477-4503,
4552-4708, 6747-6816, 8103-8242, 8465-8492, 9673-9745,
9832-9996, 10166-10234, 10436-10609, 14021-14089.
Compte exact k in [3,14089] : 1826 seuils a 2 puits,
12261 a 3 puits (k=2 a part : a(2) = 1, l'unite {8}).
DERNIER k a 2 puits : 14089 (fenetre
[14021,14089] : M=994175 classe 2, 2M-3=1988347 premier,
28176 enfants-pont, max r=14324 - la fenetre continue
probablement jusqu'a 14324 mais mu2(k)>14089 est hors
table : portion certifiee seulement). Zone valide
k<=14089 (maxR par classe [27988,14608,14089]) ;
l'ancien intervalle 14090-14608 etait un artefact mu2=0.
k=512 et k=1024 tombaient par hasard dans des fenetres 3.
Sous HL3 le pont 2M-3 ne meurt jamais (prob ~lnlnM/lnM amplifiee
sur primoriaux) : oscillation attendue a l'infini.

## 3. Statuts exacts (a ecrire ainsi dans le papier)

- DELTA0 (inconditionnel ZFC, local) : pour chaque k verifie,
  statut de puits des mu_c(k) = theoreme (segment [1,m] fini).
- "mu0(k)<min(mu1,mu2) => >=2 puits" : theoreme inconditionnel.
- "2*max(mu1,mu2)-3 composite => >=3 puits" : theoreme
  inconditionnel (a k fixe).
- #puits(V_k ∩ [1,10^6]) <= 3 pour 2<=k<=14089 : mesure
  exhaustive (interieur exhaustif k<=7226 par fermeture M_cut ;
  au-dela, statuts determines par les minima de classe).
- #puits(V_k)<=3 sur N ENTIER : CONDITIONNEL a l'absence de
  puits interieur au-dela de la table (CONJ-M : M(m)>=tau(m)
  pour tau(m)>=2) ; le seuil L_k<infini (type A000954, dernier m avec
  r(m)<k) ne ferme que la queue et implique, des k=1, la
  conjecture binaire classique : jamais prouvable par
  borne finie.
- Conjecture ouverte exacte : N(u1,u2)>=1 sur les goulots
  (analogue Dubner a decalage 2v=0 mod 6 ; risque residuel
  ~10^-75 sous HL4-Poisson = SOMME convergente du modele,
  jamais borne d'impossibilite ; queue j=3 ~5e-20 ; caveat
  Maier 1985 : un modele Poisson peut etre mis en defaut
  loin - le modele ne permet pas d'ecrire "presque prouve" ni
  "4 n'existe pas").
- PAS prouve : ">=3 pour tout k>=k_c" (rechutes 3->2 attendues).

## 4. Protocole de calcul (reproductible)

- rtable_1M.npy : r(m) par une FFT convolution (0.2s), N=10^6,
  convention A061357 (t>=1) ; regenerable depuis le certificat
  signe run_1e6/certs_rtable.bin via make_rtable.py.
- falsif_tau.py : passe unique tau(m)=min(r(m),R_prev[classe]),
  has_valid_child court-circuite.
- falsif_sniper.py : goulots j=2, test O(r) u1 in C(u2).
- falsif_lambda.py : N(u1,u2) vs lambda_int=S4*integrale log
  (garde-fous : produit fini sur u1*u2*(u2-u1)*(2u2-u1), facteur
  2C4 pour classe 0, integrale non asymptotique).
- test_rechute.py : compte #puits(k) par minima+pont ; a produit
  l'oscillation {2,3}.

## 5. Lean 4 - triptyque termine (0 sorry, compile)

Fichiers (lean/descente_*.lean, toolchain v4.35.0, verifie) :

- descente_mod3.lean (394 lignes, Mathlib via lean-artifact) :
  31 decl. - vanne mod3, pont 2m-3 iff premier, enfants-pont vers
  classe opposee 3-c, certificat "min de classe sans pont = puits".
- descente_bijection.lean (580 lignes, Lean core) : 28 thm -
  goulot_bijection u1 in C(u2) <=> N>=1 (deux sens), N<=min(r u1,
  r u2) inconditionnel, plafond sous u2%3!=0 et 2u2-3 compose.
- descente_tiroirs.lean (421 lignes, Lean core) : pigeonhole sur
  ecarts de rayons + descente_tiroirs + no_puits_ge_Mcut
  (sous forall u>L, r(u)>=k : aucun puits dans [M_cut,+inf)).

ERRATA consignes (corrections par rapport aux premieres versions) :
1. Borne raffinee N<=min(r>=5) inconditionnelle est FAUSSE :
   contre-exemple (u1,u2)=(4,11), p=3 temoin mais r5(4)=0.
   Elle tient exactement sous ¬Prime(2u2-3) (contexte du plafond).
   Version sure : N<=min(r u1,r u2) toujours.
2. m congru 0 mod 3 : la loi vraie est 3|t JAMAIS pour tout rayon
   (l'inverse du texte initial ; contre-ex. m=6,t=1).
3. Plafond exige u2%3!=0 ; l'hypothese "u2 record" est inutile
   (mecanisme = confinement, plus fort qu'enonce).
4. Le ~10^-75 est une SOMME convergente du
   modele Poisson, pas une borne - interdiction d'ecrire
   "4 puits n'existe nulle part". Queue j=3 au plancher :
   ~5e-20 (pas 10^-75). Caveat Maier 1985 a garder : les modeles
   Poisson peuvent etre mis en defaut loin. Couverture enfants
   ~6/ln^2(k) qui decroit : argument "le graphe se densifie" valide
   pour les GAPS de rayons, pas pour garantir l'absence de puits.

## 6. Replication independante

- verificateur.c (C99) et verificateur.py (Python/numpy),
  deux implementations independantes : re-derivation
  complete des certificats achevee sur run_1e6 (rtable
  integrale 1..10^6 ; puits pour tous les niveaux
  k<=14089 ; goulots ; passe tau interieure a B_max=999958
  plus seconde passe tau>=7227 sur [6,10^6] - 290 177
  vitaux testes, clot la queue pour k>7226 ; protocole
  detaille dans SPECS_CERTS.md).
- chk1M (implementation tierce de controle) : re-joue la
  plage k<=256 comme verification additionnelle.

## 7. Manquants honnetes

- <=3 sur N : conditionnel a CONJ-M (pas de puits interieur) ;
  L_k fini = seuil de queue, a k=1 c'est le probleme binaire
  classique, non prouve.
- N>=1 : conjecture ouverte, heuristique HL4 seulement.
- Anteriorite : veille bibliographique ciblee + OEIS = pas de
  trace trouvee ; reserve zbMATH/MathSciNet paywall.
- Interieur pour k>7226 : statuts determines par les minima de
  classe certifies (certs_puits) + fermeture M_cut en queue ;
  passe tau exhaustive bornee a B_max=999 958.
