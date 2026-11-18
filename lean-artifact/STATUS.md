# STATUS - artefact Lean de CONJ-2COMP

Date : 2026-11-14. Objet : formalisation Lean 4 du theoreme
de la vanne mod-3 du papier CONJ-2COMP (thm:valve).

## Verdict build

**BUILD OK, ZERO SORRY.** L'artefact allait au-dela du scaffold :
tous les enonces vises sont PROUVES (les clauses (a), (b), (c)
de la vanne et les corollaires) - aucun `sorry` n'a ete necessaire.

- `lake env lean Conj2comp.lean` : exit 0, aucune erreur (un warning
  style sur `import Mathlib`, cosmetique).
- `lake build` : `Built Conj2comp`, 9048 jobs, succes.
- `#print axioms` en fin de fichier :
  - `barrier_a` : [propext, Classical.choice, Quot.sound]
  - `barrier_b` : [propext, Classical.choice, Quot.sound]
  - `barrier_c` : [propext, Classical.choice, Quot.sound]
  - aucun `sorryAx` = aucune preuve incomplete.
- Pas de `native_decide` : `decide`, `norm_num`, `omega`
  uniquement + API Mathlib (Nat.Prime.eq_one_or_self_of_dvd,
  Finset.card_*, Nat.modEq_iff_dvd').

## Setup

- `lakefile.toml` : package `conj2comp`, mathlib rev v4.35.0
  (sha 56a005855ea17e0b0958f73ec801ae140b0a1679),
  lean_lib `Conj2comp`.
- `lean-toolchain` : `leanprover/lean4:v4.35.0` (elan 4.2.4, installe).
- `.lake/` initialise depuis un cache mathlib local (v4.35.0)
  + `lake-manifest.json`.
- `lake exe cache get` : 9030 oleans mathlib deja en cache local,
  decompression ~88 s, aucun download reseau necessaire.

## Enonces formalises (Conj2comp.lean, 702 lignes)

### Definitions (paper sec. 2)

| Papier | Lean | Ligne | Statut |
|---|---|---|---|
| def:rays S(m) | `S m : Finset Nat` (Icc 1 m filtre primes m-t, m+t) | 32 | def |
| def:rays r(m) | `rayCount m = (S m).card` | 36 | def |
| def:rays Part(m) | `Part m : Finset Nat` (p premier, 2m-p premier, p != m) | 39 | def |
| def:arc | `Arc m n : Prop` (m != n, existe p<q premiers, p+q=2n, {p,q} dans Part m) | 44 | def |
| def:extr | `extRay m = m - 3` | 49 | def |
| Part = {m±t} | `part_iff_ray` (iff complet) | 73 | prouve |
| t* dans S(m) iff 2m-3 premier | `mem_S_ext` | 110 | prouve |

### Forme des enfants (sec. 2 du papier)

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| (1) t <= m-3 | `ray_le_ext` | 128 | prouve |
| (1) parite opposee | `ray_parity`, `rays_same_parity` | 137, 148 | prouve |
| (1) enfants >= 4 | `child_ge_four` | 279 | prouve |
| (2) iff des 4 enfants | `children_form` | 216 | prouve (deux sens) |

### lem:ray3 (classes de rayons mod 3)

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| (1) t != -m mod 3 | `ray_mod3_ne_neg` | 157 | prouve |
| (2) t = m mod 3 -> t = m-3, 2m-3 premier | `ray_mod3_eq_ext` | 167 | prouve |
| (3) m charge : rayon = 0 ou extremal | `ray3_charged` | 180 | prouve |
| (3) m neutre : aucun rayon = 0 | `ray3_neutral` | 188 | prouve |

### Table des arcs mod 3 (thm:valve)

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| parent charge (regulier / extremal) | `table_charged` | 292 | prouve |
| parent neutre ({0,-s2} desc, {0,+s2} asc) | `table_neutral` | 327 | prouve |

### thm:valve (vanne mod 3) - THEOREME A

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| (a) pas d'arc descendant charge -> 0 | `barrier_a` | 349 | **prouve** |
| (b) arcs charge -> neutre = ascendants des paires extremales | `barrier_b` | 367 | **prouve** |
| (c) classe -m interdite (tout p) | `ray_class_neg_forbidden` | 441 | prouve |
| (c) classe +m -> representant bord t = m-p | `ray_class_boundary` | 452 | prouve |
| (c) classes interdites (def) | `forbiddenClasses` | 464 | def |
| (c) les 2 classes interdites sont distinctes (m != 0) | `forbidden_classes_ne` | 468 | prouve |
| (c) comptage : admissibles = 1 iff p = 3, sinon p-1 | `admissible_card` | 486 | prouve |
| (c) restatement singleton iff p = 3 | `admissible_singleton_iff` | 515 | prouve |
| (c) paquet (i-iv) | `barrier_c` | 531 | **prouve** |
| (c) degenerescence p = 2 : rayon bord m-2 absent | `boundary_ray_p2_absent`, `barrier_fails_p2` | 203, 561 | prouve |

Note fidelite (c) : le papier dit ">= p-2 >= 3 classes admissibles
pour p >= 5" ; le module prouve le comptage exact p-1 (classe -m
seule exclue, classe +m admissible via le representant bord non
extremal), ce qui est plus fort et coherent avec "classes 0, m et
au moins une autre admissibles". La forme "mecanisme a classe unique
iff p = 3" est `admissible_singleton_iff`.

### Permeabilite / auto-alimentation (sec. 3)

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| ascendance impermeable (arc +1/-1 => descente) | `cor_perm_asc` | 568 | prouve |
| descente permeable (paire extremale emet 2 enfants desc = -m) | `cor_perm_desc` | 585 | prouve |
| fibre neutre auto-alimentee (r(m)>=2 => enfant desc = 0) | `cor_self` | 616 | prouve |

### Temoins premiers (thm:pgates) et contre-exemple p = 2

| Clause | Lean | Ligne | Statut |
|---|---|---|---|
| S(9)={2,4}, S(11)={6,8}, S(15)={2,4,8}, S(14)={3,9} | `S9_eq` etc. | 649-652 | decide |
| arc 9 -> 8 (echec barriere p = 2) | `arc_9_8` | 655 | prouve (temoins 5+11) |
| temoin p=5 : 11 -> 10 | `wit_p5` | 660 | prouve |
| temoin p=7 : 15 -> 14 | `wit_p7` | 665 | prouve |
| temoin p=11 : 14 -> 11 | `wit_p11` | 670 | prouve |
| temoin p=13 : 15 -> 13 | `wit_p13` | 675 | prouve |
| existence d'arcs desc non-0 -> 0 pour p in {5,7,11,13} | `wit_desc_arcs` | 681 | prouve |
| arc 9 -> 8 via children_form | `arc_9_8_children` | 693 | prouve |

## Sorries restantes par ligne

**AUCUNE.** Le fichier ne contient aucun `sorry`, aucun `native_decide`,
aucune hypothese libre. `#print axioms` confirme : seuls propext,
Classical.choice, Quot.sound (axiomes standard de Mathlib).

## Ecarts de fidelite / reserves (a declarer dans le papier)

- `Arc` exige `m != n` (papier : "n != m" dans def:arc) - conforme.
- `Part m` borne p <= 2m dans le Finset ; equivalence `part_iff_ray`
  prouvee, donc pas de perte.
- vanne (b) : la forme retenue donne `2n = (m ∓ t) + (2m-3)`
  (identification exacte de la paire emettrice), equivalent a
  "emise exactement par les paires extremales" du papier.
- vanne (c) : le comptage est enonce sur `Finset.range p \
  forbiddenClasses p m` (classes a-priori admissibles aux rayons non
  extremaux), conforme au papier ; il manque
  volontairement le volet "existence pour tout p >= 5"
  (thm:pgates du papier, prouve ; hors scope de cet artefact).
- permeabilite : le papier est informel ("permeable") ; le module
  prouve les deux directions factuelles utilisees par la suite.
- Hors scope : niveaux V_k, puits, goulots, propositions et
  conjectures (sauf les petits temoins ci-dessus).

## Regles projet

- Nommage du package : "conj2comp" / "re-pairing digraph"
  (nommage du package ; la publication releve d'une
  decision de l'utilisateur).
- Aucun calcul python utilise (hors perimetre de l'artefact) ;
  seuls lake/lean/elan.

## ThmDense.lean (2026-11-15) - KERNEL-PUR ATTEINT

Formalisation de thm:dense (rev.8, couverture Schnirelmann
locale par Delta-arcs). Compile : `lake env lean ThmDense.lean`
exit 0, ZERO SORRY. `#print axioms Conj2comp.dense_coverage` :
[propext, Classical.choice, Quot.sound] uniquement.

Decomposition certifiee :
- NOYAU-PUR prouve : deltaChild_lt (n < m),
  deltaChildren_subset_range, card_rayPairs_eq_sum_wDelta
  (fibres), card_rayPairs_bound (r^2 <= 2P + 3r via swap/offDiag),
  dense_combinatorial (Cauchy-Schwarz support : P^2 <= C*W).
- HYPOTHESES EXPLICITES (non-axiomes, parametres) :
  SieveUpperHypothesis (H_A, crible Selberg degre 4),
  SecondMomentHypothesis (H_B), RichCentreHypothesis (L1,
  Tchebychev elementaire enonce comme entree).
- THEOREME dense_coverage : c0^4/(16 K^2 K_M S2^4) * m <= |C_D^-|
  assemble sous hA, hB, hRich (r >= 6, m >= 4, ln m >= 1).

Verdict : la combinatoire du theoreme est verifiee par le noyau ;
les bornes analytiques restent des entrees litterature
enoncees, jamais pretendues derivees du noyau.
