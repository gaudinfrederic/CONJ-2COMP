/-
descente_mod3_kernel.lean — port CORE pur (sans Mathlib) de
descente_mod3.lean : structure mod 3 du spectre S(m), descente
(enfants) et certificats « puits ».

Toolchain : leanprover/lean4:v4.35.0 — AUCUNE dependance, pas de lakefile.
Verifier : `~/.elan/bin/lean descente_mod3_kernel.lean`
ZERO sorry / admit / axiom / native_decide.

Enonces (adaptation Set/Finset -> Prop/List de descente_mod3.lean) :
  isRay m t   : 1 <= t, t <= m - 2, Premier (m-t), Premier (m+t)
  isChild m n : existe a < b rayons de m avec
                n = m - (b-a)/2 (canal-difference) ou
                n = m - (a+b)/2 (canal-somme)
  r m         = (rayList m).length  (comptage booleen via bPremier)

Machinerie reprise de descente_bijection.lean (Premier / bPremier /
bPremier_iff, lemmes de parite et de borne) — duplication volontaire :
les fichiers kernel sont autonomes (convention N5_kernel.lean).

Contenu :
  A. Primalite : Premier (spec), bPremier (calcul), pont bPremier_iff ;
     un premier divisible par 2 (resp. 3) vaut 2 (resp. 3) ; 3 premier.
  B. isRay / isChild ; parite des rayons (les deux bords impairs =>
     tous les rayons de meme parite) et borne t <= m-3.
  C. Dichotomie mod 3 :
       m % 3 = 0        : aucun rayon divisible par 3 ; pas de pont
                          (pont <=> Premier (2m-3), or 3 | 2m-3 > 3).
       m % 3 = c in {1,2} : tout rayon est « bulk » (3 | t) ou « pont »
                          (t = m-3) ; les deux cas s'excluent.
  D. Enfants : n < m et n >= 1 (descente bien fondee) ;
       paire bulk-bulk   => enfants = c     (restent dans la classe) ;
       paire avec pont   => enfants = 3-c   (classe opposee) ;
       sans pont         => tous les enfants = c ;
       enfant = 3-c      => le pont existe.
  E. Certificats : « min de classe sans pont est puits » (puits,
     puits_of_not_prime) et version generale avec pont
     (descente_split : l'enfant descend ou bascule en 3-c).
  F. Comptage (rayList / r / ray5List / r5) et exemples de verification.
  G. Contre-exemple a la forme litterale de la clause « m%3=0 => 3|t ».
-/

set_option linter.unusedSectionVars false

-- ============================================================
-- A. Primalite : Prop (spec), Bool (calcul), et le pont
-- ============================================================

/-- primalite mathematique (meme forme que `prime` de N5_kernel) -/
def Premier (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- test booleen : aucun diviseur dans [2, n) -/
def bPremier (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range' 2 (n - 2)).all (fun d => n % d != 0)

/-- pont spec/calcul : bPremier decide exactement Premier -/
theorem bPremier_iff (n : Nat) : bPremier n = true ↔ Premier n := by
  unfold bPremier
  by_cases h2 : n < 2
  · rw [ite_eq_left h2]
    exact ⟨fun h => absurd h (by simp),
           fun h => absurd h.1 (by omega)⟩
  · rw [ite_eq_right h2]
    have hn2 : 2 ≤ n := by omega
    rw [List.all_eq_true]
    constructor
    · intro hall
      refine ⟨hn2, fun d hdvd => ?_⟩
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      rcases Nat.lt_or_ge d n with hdlt | hdge
      · by_cases hd2 : 2 ≤ d
        · have hmem : d ∈ List.range' 2 (n - 2) :=
            List.mem_range'.mpr ⟨d - 2, by omega, by omega⟩
          have hnd : (n % d != 0) = true := hall d hmem
          rw [bne_iff_ne] at hnd
          exact absurd (Nat.dvd_iff_mod_eq_zero.mp hdvd) hnd
        · exact Or.inl (by omega)
      · exact Or.inr (Nat.le_antisymm hdle hdge)
    · rintro ⟨hn2', hprime⟩ d hd
      rw [List.mem_range'] at hd
      obtain ⟨i, hi, rfl⟩ := hd
      show ((n % (2 + 1 * i)) != 0) = true
      rw [bne_iff_ne]
      intro hmod
      have hdvd : (2 + 1 * i) ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hmod
      rcases hprime _ hdvd with h1 | h1
      · omega
      · omega

/-- un premier egal a 2 des que pair -/
theorem Premier.eq_two_of_two_dvd {n : Nat} (hn : Premier n) (h : 2 ∣ n) :
    n = 2 :=
  (hn.2 2 h).elim (fun e => by omega) (fun e => e.symm)

/-- un premier egal a 3 des que multiple de 3 -/
theorem Premier.eq_three_of_three_dvd {n : Nat} (hn : Premier n) (h : 3 ∣ n) :
    n = 3 :=
  (hn.2 3 h).elim (fun e => by omega) (fun e => e.symm)

/-- un premier est 2 ou impair -/
theorem Premier.eq_two_or_odd {n : Nat} (hn : Premier n) :
    n = 2 ∨ n % 2 = 1 := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h0 | h1
  · exact Or.inl (hn.eq_two_of_two_dvd (Nat.dvd_of_mod_eq_zero h0))
  · exact Or.inr h1

/-- 3 est premier (certificat booleen remonte par le pont) -/
theorem premier_three : Premier 3 := (bPremier_iff 3).mp rfl

-- ============================================================
-- B. Rayons et enfants : definitions, parite, borne
-- ============================================================

/-- rayon de m : 1 <= t <= m - 2 avec m - t et m + t premiers
    (la decomposition de Goldbach symetrique 2m = (m-t) + (m+t)) -/
def isRay (m t : Nat) : Prop :=
  1 ≤ t ∧ t ≤ m - 2 ∧ Premier (m - t) ∧ Premier (m + t)

/-- enfant de m : n = m - (b-a)/2 (canal-difference) ou
    n = m - (a+b)/2 (canal-somme) pour a < b rayons de m -/
def isChild (m n : Nat) : Prop :=
  ∃ a b : Nat, isRay m a ∧ isRay m b ∧ a < b ∧
    (n = m - (b - a) / 2 ∨ n = m - (a + b) / 2)

/-- pont de m : m-3 est un rayon (m-(m-3) = 3 toujours premier) -/
def hasPont (m : Nat) : Prop := isRay m (m - 3)

/-- tout rayon impose m >= 4 (S(m) est vide pour m <= 3) -/
theorem isRay.ge_four {m t : Nat} (ht : isRay m t) : 4 ≤ m := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  rcases Nat.lt_or_ge m 4 with hlt | hge
  · -- t <= m-2 et t >= 1 forcent m = 3, t = 1 : m + t = 4 non premier
    have ht1 : t = 1 := by omega
    subst ht1
    have hm3 : m = 3 := by omega
    subst hm3
    rcases hpp.2 2 ⟨2, rfl⟩ with e | e <;> omega
  · exact hge

/-- parite des bords : pour tout rayon t, m-t et m+t sont impairs
    (premiers >= 3 : m-t = 2 forcerait m+t pair >= 4). -/
theorem ray_edges_odd {m t : Nat} (ht : isRay m t) :
    (m - t) % 2 = 1 ∧ (m + t) % 2 = 1 := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  have hge : 4 ≤ m + t := by
    have hp2 : 2 ≤ m - t := hpm.1
    omega
  rcases hpm.eq_two_or_odd with hm1 | hm1
  · -- m - t = 2 : m + t = 2 + 2t pair, premier, >= 4 — absurde
    have hd : 2 ∣ m + t := ⟨(m + t) / 2, by omega⟩
    have e := hpp.eq_two_of_two_dvd hd
    omega
  · rcases hpp.eq_two_or_odd with hm2 | hm2
    · omega
    · exact ⟨hm1, hm2⟩

/-- tous les rayons de m ont la meme parite (opposee a m) :
    a±b est toujours pair — le canal est un vrai entier -/
theorem ray_both_odd {m a b : Nat} (_hm : 4 ≤ m) (ha : isRay m a)
    (hb : isRay m b) : a % 2 = b % 2 := by
  have pa := ray_edges_odd ha
  have pb := ray_edges_odd hb
  obtain ⟨ha1, ham, _, _⟩ := ha
  obtain ⟨hb1, _, _, _⟩ := hb
  omega

/-- borne : tout rayon de m est <= m - 3
    (t = m-2 donne m + t = 2m - 2 premier pair >= 4 : absurde) -/
theorem ray_le {m b : Nat} (hb : isRay m b) : b ≤ m - 3 := by
  obtain ⟨hb1, hbm, hpm, hpp⟩ := hb
  rcases (show b = m - 2 ∨ b ≤ m - 3 by omega) with h | h
  · have hd : 2 ∣ m + b := ⟨m - 1, by omega⟩
    rcases hpp.2 2 hd with e | e <;> omega
  · exact h

-- ============================================================
-- C. Dichotomie mod 3
-- ============================================================

/-- m = 0 (mod 3) : AUCUN rayon n'est divisible par 3. (Forme correcte
de l'enonce de mission — voir l'erratum de descente_mod3.lean.)
3 | t rendrait m-t et m+t multiples de 3, donc tous deux egaux a 3,
impossible. -/
theorem ray_ndvd3_of_m0 {m t : Nat} (hm : m % 3 = 0) (ht : isRay m t) :
    ¬ 3 ∣ t := by
  rintro ⟨j, rfl⟩
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  have hd1 : 3 ∣ m - 3 * j := ⟨(m - 3 * j) / 3, by omega⟩
  have hd2 : 3 ∣ m + 3 * j := ⟨(m + 3 * j) / 3, by omega⟩
  have e1 := hpm.eq_three_of_three_dvd hd1   -- m - t = 3
  have e2 := hpp.eq_three_of_three_dvd hd2   -- m + t = 3
  omega

/-- Le pont : m-3 est un rayon ssi 2m-3 est premier (pour m >= 4 ;
m-(m-3) = 3 est toujours premier). -/
theorem pont_iff {m : Nat} (hm : 4 ≤ m) :
    isRay m (m - 3) ↔ Premier (2 * m - 3) := by
  have h1 : m - (m - 3) = 3 := by omega
  have h2 : m + (m - 3) = 2 * m - 3 := by omega
  constructor
  · rintro ⟨_, _, hpm, hpp⟩
    rw [h2] at hpp
    exact hpp
  · intro hp
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [h1]; exact premier_three
    · rw [h2]; exact hp

/-- m = 0 (mod 3) n'a jamais de pont : 2m-3 est multiple de 3 > 3. -/
theorem no_pont_of_m0 {m : Nat} (hm : m % 3 = 0) (hm4 : 4 ≤ m) :
    ¬ isRay m (m - 3) := by
  intro hp
  have hp' := (pont_iff hm4).mp hp
  have hd : 3 ∣ 2 * m - 3 := ⟨(2 * m - 3) / 3, by omega⟩
  have e := hp'.eq_three_of_three_dvd hd    -- 2m - 3 = 3 => m = 3
  omega

/-- Dichotomie, m = c in {1,2} (mod 3) : tout rayon t est
  · « bulk » : 3 | t (les deux bords sont alors = c mod 3, premiers
    possibles), ou
  · « pont » : t = m-3, i.e. m-t = 3 (t = c mod 3 force m-t = 0).
La troisieme classe t = -c (mod 3) tuerait m+t (multiple de 3 >= 4). -/
theorem ray_dvd3_or_pont {m t c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (ht : isRay m t) : 3 ∣ t ∨ t = m - 3 := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  have hge : 4 ≤ m + t := by
    have hp2 : 2 ≤ m - t := hpm.1
    omega
  have htri : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hc with rfl | rfl
  · -- c = 1
    rcases htri with h0 | h1' | h2'
    · exact Or.inl ⟨t / 3, by omega⟩
    · right
      have hd : 3 ∣ m - t := ⟨(m - t) / 3, by omega⟩
      have e := hpm.eq_three_of_three_dvd hd   -- m - t = 3
      omega
    · have hd : 3 ∣ m + t := ⟨(m + t) / 3, by omega⟩
      have e := hpp.eq_three_of_three_dvd hd   -- m + t = 3, impossible (>= 4)
      omega
  · -- c = 2
    rcases htri with h0 | h1' | h2'
    · exact Or.inl ⟨t / 3, by omega⟩
    · have hd : 3 ∣ m + t := ⟨(m + t) / 3, by omega⟩
      have e := hpp.eq_three_of_three_dvd hd
      omega
    · right
      have hd : 3 ∣ m - t := ⟨(m - t) / 3, by omega⟩
      have e := hpm.eq_three_of_three_dvd hd   -- m - t = 3
      omega

-- ============================================================
-- D. Enfants : descente et classes mod 3
-- ============================================================

/-- Auxiliaire : x pair divisible par 3 => x/2 divisible par 3,
donc l'enfant m - x/2 reste dans la classe de m. -/
theorem child_aux_bulk {m x c : Nat} (hm : m % 3 = c) (_hc : c = 1 ∨ c = 2)
    (h0 : x % 3 = 0) (h2 : x % 2 = 0) (hle : x ≤ 2 * m) :
    (m - x / 2) % 3 = c := by
  have hx6 : x % 6 = 0 := by omega
  have hx2 : (x / 2) % 3 = 0 := by omega
  have hx2le : x / 2 ≤ m := by omega
  omega

/-- Auxiliaire : x pair = c (mod 3) => x/2 = 2c (mod 3), donc l'enfant
m - x/2 bascule dans la classe opposee 3-c. -/
theorem child_aux_pont {m x c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hxc : x % 3 = c) (h2 : x % 2 = 0) (hle : x ≤ 2 * m) :
    (m - x / 2) % 3 = 3 - c := by
  rcases hc with rfl | rfl
  · have hx6 : x % 6 = 4 := by omega   -- x = 1 (mod 3), pair
    have hx2 : (x / 2) % 3 = 2 := by omega
    have hx2le : x / 2 ≤ m := by omega
    omega
  · have hx6 : x % 6 = 2 := by omega   -- x = 2 (mod 3), pair
    have hx2 : (x / 2) % 3 = 1 := by omega
    have hx2le : x / 2 ≤ m := by omega
    omega

/-- Tout enfant est strictement plus petit que son parent :
la descente est bien fondee. -/
theorem child_lt {m n : Nat} (h : isChild m n) : n < m := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd hb
  have haL := ray_le ha
  have hbL := ray_le hb
  obtain ⟨ha1, _, _, _⟩ := ha
  obtain ⟨hb1, _, _, _⟩ := hb
  rcases hd with rfl | rfl <;> omega

/-- Tout enfant est >= 1 : en bas, (a+b)/2 <= m-3 ; en haut,
(b-a)/2 <= m-4 puisque b <= m-3 et a >= 1. -/
theorem child_ge {m n : Nat} (h : isChild m n) : 1 ≤ n := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd hb
  have haL := ray_le ha
  have hbL := ray_le hb
  obtain ⟨ha1, _, _, _⟩ := ha
  rcases hd with rfl | rfl <;> omega

/-- Classes des enfants, m = c in {1,2} : tout enfant est soit dans la
classe c (paire bulk-bulk) soit dans la classe opposee 3-c (paire
contenant le pont b = m-3). Le pont ne peut etre que le plus grand
element de la paire (tout rayon <= m-3). -/
theorem child_mod3 {m n c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (h : isChild m n) : n % 3 = c ∨ n % 3 = 3 - c := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hbL := ray_le hb
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd hb
  have hda := ray_dvd3_or_pont hm hc ha
  have hdb := ray_dvd3_or_pont hm hc hb
  rcases hda with ha3 | hap <;> rcases hdb with hb3 | hbp
  · -- a, b bulk (3 | a, 3 | b) : enfants dans la classe c
    obtain ⟨i, hi⟩ := ha3
    obtain ⟨j, hj⟩ := hb3
    rcases hd with rfl | rfl
    · exact Or.inl (child_aux_bulk hm hc (by omega) (by omega) (by omega))
    · exact Or.inl (child_aux_bulk hm hc (by omega) (by omega) (by omega))
  · -- a bulk, b = m-3 pont : enfants dans la classe opposee 3-c
    obtain ⟨i, hi⟩ := ha3
    subst hbp
    rcases hd with rfl | rfl
    · exact Or.inr (child_aux_pont hm hc (by omega) (by omega) (by omega))
    · exact Or.inr (child_aux_pont hm hc (by omega) (by omega) (by omega))
  · -- a = m-3 pont, b > a : impossible, tout rayon <= m-3
    subst hap
    omega
  · -- a = b = m-3 : impossible, a < b
    subst hap; subst hbp
    omega

/-- Sans pont, tous les rayons sont bulk : tous les enfants restent
dans la classe c. -/
theorem child_mod3_no_pont {m n c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hnop : ¬ isRay m (m - 3)) (h : isChild m n) : n % 3 = c := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have ha3 : 3 ∣ a :=
    (ray_dvd3_or_pont hm hc ha).resolve_right (fun hae => hnop (hae ▸ ha))
  have hb3 : 3 ∣ b :=
    (ray_dvd3_or_pont hm hc hb).resolve_right (fun hbe => hnop (hbe ▸ hb))
  obtain ⟨i, hi⟩ := ha3
  obtain ⟨j, hj⟩ := hb3
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd hb
  rcases hd with rfl | rfl
  · exact child_aux_bulk hm hc (by omega) (by omega) (by omega)
  · exact child_aux_bulk hm hc (by omega) (by omega) (by omega)

/-- Reciproque : un enfant dans la classe opposee 3-c certifie
l'existence du pont. (Sans by_contra : l'existence du pont se decide
par le calcul booleen `bPremier (2m-3)`.) -/
theorem pont_of_child_opp {m n c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (h : isChild m n) (hopp : n % 3 = 3 - c) : isRay m (m - 3) := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hm4 : 4 ≤ m := isRay.ge_four ha
  by_cases hB : bPremier (2 * m - 3) = true
  · exact (pont_iff hm4).mpr ((bPremier_iff _).mp hB)
  · exfalso
    have hcomp : ¬ Premier (2 * m - 3) :=
      fun hp => hB ((bPremier_iff _).mpr hp)
    have hnop : ¬ isRay m (m - 3) :=
      fun hp => hcomp ((pont_iff hm4).mp hp)
    have hcc := child_mod3_no_pont hm hc hnop ⟨a, b, ha, hb, hab, hd⟩
    rcases hc with rfl | rfl <;> omega

/-- Forme « par paire » : les enfants d'une paire de rayons bulk
restent dans la classe de m. -/
theorem child_of_bulk_pair {m a b n : Nat} (ha : isRay m a) (hb : isRay m b)
    (ha3 : 3 ∣ a) (hb3 : 3 ∣ b) (_hab : a < b)
    (hn : n = m - (b - a) / 2 ∨ n = m - (a + b) / 2) :
    n % 3 = m % 3 := by
  obtain ⟨i, hi⟩ := ha3
  obtain ⟨j, hj⟩ := hb3
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd hb
  obtain ⟨_, ham, _, _⟩ := ha
  obtain ⟨_, hbm, _, _⟩ := hb
  rcases hn with rfl | rfl
  · have hx6 : (b - a) % 6 = 0 := by omega
    have hx2 : (b - a) / 2 % 3 = 0 := by omega
    omega
  · have hx6 : (a + b) % 6 = 0 := by omega
    have hx2 : (a + b) / 2 % 3 = 0 := by omega
    omega

/-- Forme « par paire » : les enfants d'une paire contenant le pont
b = m-3 (l'autre rayon etant bulk) basculent dans la classe 3-c. -/
theorem child_of_pont_pair {m a b n c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (ha : isRay m a) (_hb : isRay m b)
    (ha3 : 3 ∣ a) (hbp : b = m - 3) (_hab : a < b)
    (hn : n = m - (b - a) / 2 ∨ n = m - (a + b) / 2) :
    n % 3 = 3 - c := by
  obtain ⟨i, hi⟩ := ha3
  have hpa := ray_edges_odd ha
  have hpb := ray_edges_odd _hb
  subst hbp
  rcases hn with rfl | rfl
  · exact child_aux_pont hm hc (by omega) (by omega) (by omega)
  · exact child_aux_pont hm hc (by omega) (by omega) (by omega)

-- ============================================================
-- E. Certificats : « min de classe sans pont est puits »
-- ============================================================

/-- PUIT (forme precise) : soit V_k = {u | r u >= k}. Si m = c in {1,2}
est le MINIMUM de sa classe dans V_k — i.e. forall u < m, u = c =>
r u < k — et si m n'a PAS de pont (m-3 non rayon), alors tout enfant
n de m verifie r n < k : m est un puits, la descente ne peut pas
rester >= k dans sa propre classe. -/
theorem puits {r : Nat → Nat} {m k c : Nat} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hnop : ¬ isRay m (m - 3))
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : Nat} (hn : isChild m n) : r n < k :=
  hmin n (child_lt hn) (child_mod3_no_pont hm hc hnop hn)

/-- Forme calculable du puits : l'absence de pont se teste par
« 2m-3 non premier » (m >= 4). -/
theorem puits_of_not_prime {r : Nat → Nat} {m k c : Nat} (hm : m % 3 = c)
    (hc : c = 1 ∨ c = 2) (hm4 : 4 ≤ m) (hnop : ¬ Premier (2 * m - 3))
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : Nat} (hn : isChild m n) : r n < k :=
  puits hm hc (fun hp => hnop ((pont_iff hm4).mp hp)) hmin hn

/-- Descente generale (pont autorise) : tout enfant de m minimal dans
sa classe descend (r n < k) OU bascule dans la classe opposee 3-c —
et alors le pont existe (pont_of_child_opp). -/
theorem descente_split {r : Nat → Nat} {m k c : Nat} (hm : m % 3 = c)
    (hc : c = 1 ∨ c = 2)
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : Nat} (hn : isChild m n) : r n < k ∨ n % 3 = 3 - c := by
  rcases child_mod3 hm hc hn with h1 | h1
  · exact Or.inl (hmin n (child_lt hn) h1)
  · exact Or.inr h1

-- ============================================================
-- F. Comptage : listes de rayons, r et r5
-- ============================================================

/-- predicat booleen « t est rayon de m » -/
def rayBool (m : Nat) : Nat → Bool :=
  fun t => bPremier (m - t) && bPremier (m + t)

/-- rayons de m en liste : t in [1, m-2] -/
def rayList (m : Nat) : List Nat :=
  (List.range' 1 (m - 2)).filter (rayBool m)

/-- r(m) = |S(m)| -/
def r (m : Nat) : Nat := (rayList m).length

/-- rayons avec petit membre >= 5 : t in [1, m-4] (t = m-3 exclu) -/
def ray5List (m : Nat) : List Nat :=
  (List.range' 1 (m - 4)).filter (rayBool m)

/-- r5(m) = #{ t in S(m) : t <= m-4 } -/
def r5 (m : Nat) : Nat := (ray5List m).length

/-- appartenance a rayList, depliee -/
theorem mem_rayList {m t : Nat} : t ∈ rayList m ↔
    1 ≤ t ∧ t ≤ m - 2 ∧ bPremier (m - t) = true ∧ bPremier (m + t) = true := by
  unfold rayList rayBool
  rw [List.mem_filter, List.mem_range', Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨by omega, by omega, hp.1, hp.2⟩
  · rintro ⟨h1, h2, hp1, hp2⟩
    exact ⟨⟨t - 1, by omega, by omega⟩, hp1, hp2⟩

/-- pont rayon <-> predicat booleen -/
theorem isRay_iff_bool {m t : Nat} : isRay m t ↔
    1 ≤ t ∧ t ≤ m - 2 ∧ bPremier (m - t) = true ∧ bPremier (m + t) = true :=
  ⟨fun ⟨h1, h2, hp1, hp2⟩ =>
     ⟨h1, h2, (bPremier_iff _).mpr hp1, (bPremier_iff _).mpr hp2⟩,
   fun ⟨h1, h2, hb1, hb2⟩ =>
     ⟨h1, h2, (bPremier_iff _).mp hb1, (bPremier_iff _).mp hb2⟩⟩

/-- tout element de rayList est un rayon -/
theorem isRay_of_mem_rayList {m t : Nat} (h : t ∈ rayList m) : isRay m t :=
  isRay_iff_bool.mpr (mem_rayList.mp h)

-- ============================================================
-- G. Contre-exemple a la forme litterale de l'enonce de mission
-- ============================================================

/-- m = 6 = 0 (mod 3), t = 1 dans S(6) : m-t = 5 et m+t = 7 premiers > 3,
et pourtant 3 ne divise pas 1. La clause « m = 0 => 3 | t » etait donc
fausse ; l'enonce prouve est `ray_ndvd3_of_m0` (3 ne divise pas t). -/
theorem counter_ex_m6 :
    ¬ ∀ m t : Nat, m % 3 = 0 → isRay m t → 3 < m - t → 3 < m + t → 3 ∣ t := by
  intro h
  have hr : isRay 6 1 :=
    ⟨by decide, by decide, (bPremier_iff _).mp rfl, (bPremier_iff _).mp rfl⟩
  have hd := h 6 1 (by decide) hr (by decide) (by decide)
  exact (fun ⟨c, hc⟩ => by omega : ¬ (3 : Nat) ∣ 1) hd

-- ============================================================
-- Verification : exemples constructifs + axiomes
-- ============================================================

/-- exemple : 8 est enfant de 14 par la paire (3, 9) en canal-somme :
    14 - (3+9)/2 = 14 - 6 = 8, avec 11, 17, 5, 23 premiers. -/
theorem isChild_14_8 : isChild 14 8 :=
  ⟨3, 9,
   ⟨by decide, by decide, (bPremier_iff _).mp rfl, (bPremier_iff _).mp rfl⟩,
   ⟨by decide, by decide, (bPremier_iff _).mp rfl, (bPremier_iff _).mp rfl⟩,
   by decide, Or.inr rfl⟩

/-- exemple : S(10) = {3, 7} — dont le pont t = 7 = 10 - 3. -/
theorem r_ten : r 10 = 2 := rfl

/-- exemple : rayons de 10 sans le pont : r5(10) = {3}. -/
theorem r5_ten : r5 10 = 1 := rfl

#check @puits
#check @puits_of_not_prime
#check @descente_split
#check @pont_of_child_opp
#check @counter_ex_m6
#print axioms puits
#print axioms puits_of_not_prime
#print axioms descente_split
#print axioms pont_of_child_opp
#print axioms counter_ex_m6
#print axioms isChild_14_8
#print axioms r_ten
