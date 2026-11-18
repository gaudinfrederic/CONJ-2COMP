# thm:dense — preuve rigoureuse (couverture locale type Schnirelmann)

Date : 2026-11-17, rev. 4 (resynchronise v30). (Point
technique cle : S_2(2m) non borne sur les primorielles ; le
choix de m a S_2 <= Lambda se fait par Markov.)
Statut : **PROUVE inconditionnellement (ZFC)** — les inputs
crible sont decharges : H_A via Halberstam-Richert Thm 5.7,
H_B par comparaison elementaire de facteurs locaux, H_C par
l'ordre maximal de f, L1 par Tchebychev + Markov. Le pas
combinatoire est formalise noyau-pur dans
`lean-artifact/ThmDense.lean` (les bornes y restent des
parametres explicites ; H_C est decharge cote papier).

## Enonce

Theoreme (couverture Schnirelmann locale). Pour X >= X0, il
existe m in (X, 2X] tel que
|C_Delta^-(m)| >= max{ c1 m, c2 m/(ln ln m)^6 }, c1,c2 > 0
ABSOLUS (independants de m). Tout enfant n in C_Delta^-(m)
porte une paire premiere de Part(m), donc r(n) >= 1
inconditionnellement.

## Decomposition en lemmes

### L1 (elementaire) — centre riche a serie singuliere bornee

Saut dyadique direct : les milieux
(p+q)/2 de X<p<q<=2X tombent tous dans (X,2X], donc
sum_{X<m<=2X} r(m) >= C(pi(2X)-pi(X),2) >= c_T X^2/ln^2 X
(Tchebychev dyadique pi(2X)-pi(X) >> X/ln X).
Par le crible superieur (dim 2) : r(m) <= K_s S_2(2m) m/ln^2 m.
Second moment convergent : sum_{m<=Y} S_2(2m)^2 <= K_2 Y
(S_2(2m)^2 = 4C_2^2 sum_{d|m} h(d), h(p)/p = O(2/p^2), K_2~4.6).
Markov : m/ln^2 m <= 2X/ln^2 X sur (X,2X] et la somme vaut
<= 2K_2 X, donc la masse des m avec S_2(2m) > Lambda est
<= (4 K_s K_2/Lambda) X^2/ln^2 X. Fixer Lambda absolu avec
8 K_s K_2/Lambda < c_T => il existe m in (X,2X] avec

  r(m) >= c0 m/ln^2 m   ET   S_2(2m) <= Lambda   (absolus).

Indispensable : S_2(2m) ~ m/phi(m) non borne (primorielles) —
sans cette restriction, c1 ne serait pas absolu.

### L2 (noyau-pur, formalise) — identite combinatoire

C(r(m),2) = sum_d mu(d), mu(d) = #{paires a<b : b-a=2d}.
Cauchy-Schwarz support :

  |C_Delta^-(m)| >= C(r(m),2)^2 / sum_d mu(d)^2.        (D1)

[FORMALISE dans ThmDense.lean.]

### H_A (PROUVE) — borne superieure par ecart, constante 384

mu(d) = #{a : m-a, m+a, m-a-2d, m+a+2d premiers}. Selberg
superieur 1D, dimension 4 (Halberstam-Richert, Thm 5.7) :

  mu(d) <= (384 + o(1)) S_4(m,d) m/ln^4 m + O(m (ln m)^{3-2B}),

2^4 * 4! = 384 ; niveau xi = m^{1/2} (ln m)^{-B}, B >= 4 ;
uniformite en d via |E| = 64 m^2 d^2 (m^2-d^2) <= 16 m^6,
condition log E << log xi satisfaite (verifie a la source :
Ford-Konyagin arXiv:1910.08452, Lemma 4 = "essentially
Theorem 5.7 of [HR]").
Le terme additif couvre S_4 = 0 (nu_3 = 3 : une forme <= xi
peut etre premiere, au plus 4xi temoins) ; contribution a
sum mu^2 : O(m^3/ln^9 m) = o(m^3/ln^8 m).

### H_B (PROUVE) — second moment de la serie singuliere

  sum_{d<m/2} S_4(m,d)^2 <= 18 C_6 m S_2(2m)^4,
  C_6 = prod_{p>=5}(1 + ((p/(p-2))^6 - 1)/p) ~ 17.5,
  S_4 <= 6 S_2^2 f(d)f(m-d)f(m+d), f(k) = prod_{p|k,p>=5} p/(p-2),
  f(k)^6 = sum_{r|k} g(r), g(p) ~ 12/p, Holder 1/3+1/3+1/3 puis
  AM-GM : (S1 S2 S3)^{1/3} <= (S1+S2+S3)/3 (3 ensembles
  d'indices disjoints) -> 36/3 = 12 devant sum f^6 ->
  12 * (3m/2) C_6 = 18 C_6 m.
Borne inferieure (facultative) : d=0 mod 3 ->
S_4 >= c_loc S_2^2, c_loc ~ 1.19 (NB : c_loc n'est PAS le c0
de Tchebychev — ne jamais l'utiliser pour minorer mu(d) : la
parite interdit les bornes inferieures individuelles).

### H_C (PROUVE) — ordre maximal de la serie singuliere

  max_d S_4(m,d) <= C_s S_2(2m)^2 (ln ln m)^6,
via max_k f(k) << (ln ln k)^2 : ln f <= sum_{p|k} 2/(p-2)
<= 2 ln ln y + O(1) sur y ~ ln k (Mertens), serre sur les
primoriaux. Decharge cote papier (hors scope Lean).

### Assemblage — deux bornes

Au centre m de L1 (S_2 <= Lambda) :

(a) voie moment (D1) : sum mu(d)^2 <=
    (384+o(1))^2 * 18 C_6 Lambda^4 m^3/ln^8 m
  |C_D| >= (c0^4 m^4/16 ln^8) * ln^8/(384^2 * 18 C_6 Lambda^4 m^3)
        =  c0^4 m / (7.5e8 Lambda^4)  =: c1 m,
c1 ABSOLU : 16 * 384^2 * 18 * C_6 ~ 7.44e8 < 7.5e8, Lambda fixe.

(b) voie sup-norme : sum mu^2 <= (max mu) * C(r,2) (identite
    de fibre exacte, formalisee) =>
  |C_D| >= C(r,2) / max mu
        >= c0^2 m^2/(4 ln^4) * ln^4/(385 C_s Lambda^2 (ln ln m)^6 m)
        =: c2 m / (ln ln m)^6,
o(1) absorbe par la marge 384 -> 385 ; c2 = c0^2/(4*385*C_s*Lambda^2).
Cette borne domine c1 m sous un seuil double-exponentiel.

## Constante effective

Selberg sur Z + Tchebychev uniquement (ni caracteres, ni BV) :
c1 et X0 effectifs en principe. Modele local attendu de H_B :
sum S_4^2 ~ (kappa_4(m)/2) m S_2^4 avec kappa_4(m) =
4 M_2(3;m) prod_{p>=5} M_2(p;m) ~ 5-15 (jamais ~1 ; M_2(2)=4
ratio constant 2, M_2(3) = 9/8 ou 3, M_2(p) = 1+(p-1)^-3
(p|m) ou 1+(6p-16)/(p-2)^4 (p n'm)) -> c1 ~ 1e-7 c0^4 Lambda^-4.

## Verdict

PROUVE (ZFC, inconditionnel). Le facteur de crible degre 4
2^4 * 4! = 384 est la raison chiffree exacte pour laquelle la
fraction prouvee plafonne sous 100 %.
