/-
descente_mod3.lean — structure mod 3 du spectre S(m), descente
(enfants) et certificats « puits ».

Mathlib requise (Nat.Prime, Finset, tactiques).
Compilation (toolchain leanprover/lean4:v4.35.0) :
    cd lean-artifact
    lake env lean descente_mod3.lean

====================================================================
OBJETS
  S(m)  = {t : 1 ≤ t < m, Prime (m−t) ∧ Prime (m+t)}   (rayons)
  r(n)  = |S(n)|                                      (rayCount)
  enfants de m : pour a < b dans S(m),
      n1 = m − (b−a)/2 ,  n2 = m − (a+b)/2            (isChild)
  pont de m : le rayon t = m−3 (i.e. m−t = 3)         (hasPont)

====================================================================
ERRATUM D'ÉNONCÉ DE MISSION — CLASSE 0.
La forme demandée était : « m ≡ 0 (mod 3), t ∈ S(m), m−t > 3,
m+t > 3 ⇒ 3 | t ». Le fait correct est L'INVERSE :
    m ≡ 0 (mod 3)  ⇒  3 ∤ t  pour TOUT rayon t ∈ S(m),
sans aucune hypothèse de taille (un t multiple de 3 rendrait m−t et
m+t multiples de 3, donc égaux à 3 — impossible puisque t ≥ 1).
Preuve : `ray_ndvd3_of_m0`. La forme littérale est réfutée par le
contre-exemple certifié `counter_ex_m6` (m = 6, t = 1 : m−t = 5,
m+t = 7 premiers, et pourtant 3 ∤ 1).

Contenu :
  A. Auxiliaires de primalité (diviseur 2, 3 d'un premier).
  B. Parité des rayons (les deux bords sont impairs) et borne t ≤ m−3.
  C. Dichotomie mod 3 :
       m ≡ 0            : aucun rayon divisible par 3 ; pas de pont
                          (pont ⇔ 2m−3 premier, or 3 | 2m−3).
       m ≡ c ∈ {1,2}    : tout rayon est « bulk » (3 | t) ou « pont »
                          (t = m−3) ; les deux cas s'excluent.
  D. Enfants : n < m et n ≥ 1 (descente bien fondée) ;
       paire bulk–bulk   ⇒ enfants ≡ c     (restent dans la classe) ;
       paire avec pont   ⇒ enfants ≡ 3−c   (classe opposée) ;
       sans pont         ⇒ tous les enfants ≡ c ;
       enfant ≡ 3−c      ⇒ le pont existe.
  E. Certificats : « min de classe sans pont est puits » (puits,
     puits_of_not_prime) et version générale avec pont : tout enfant
     descend (r n < k) ou bascule dans la classe opposée.
====================================================================
-/

import Mathlib

/-- Rayon de m : 1 ≤ t < m et m−t, m+t premiers — la décomposition de
Goldbach symétrique 2m = (m−t) + (m+t). -/
def isRay (m t : ℕ) : Prop :=
  1 ≤ t ∧ t < m ∧ Nat.Prime (m - t) ∧ Nat.Prime (m + t)

instance decIsRay (m t : ℕ) : Decidable (isRay m t) := by
  unfold isRay; infer_instance

/-- Le spectre S(m), ensembliste. -/
def S (m : ℕ) : Set ℕ := {t | isRay m t}

theorem mem_S {m t : ℕ} : t ∈ S m ↔ isRay m t := Iff.rfl

/-- Le spectre en Finset (la borne t < m est dans isRay). -/
def raysF (m : ℕ) : Finset ℕ := (Finset.range m).filter (isRay m)

theorem mem_raysF {m t : ℕ} : t ∈ raysF m ↔ isRay m t := by
  unfold raysF
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

/-- r(m) : le nombre de rayons de m. -/
def rayCount (m : ℕ) : ℕ := (raysF m).card

/-- m a un pont : m−3 est un rayon (équivaut, pour m ≥ 4, à 2m−3 premier). -/
def hasPont (m : ℕ) : Prop := isRay m (m - 3)

/-- Enfants de m : n = m−(b−a)/2 (enfant haut) ou n = m−(a+b)/2
(enfant bas) pour a < b rayons de m. -/
def isChild (m n : ℕ) : Prop :=
  ∃ a b, isRay m a ∧ isRay m b ∧ a < b ∧
    (n = m - (b - a) / 2 ∨ n = m - (a + b) / 2)

-- ============================================================
-- A. Auxiliaires de primalité
-- ============================================================

/-- Un premier divisible par 3 vaut 3. -/
theorem prime_eq3 {p : ℕ} (hp : p.Prime) (h : 3 ∣ p) : p = 3 :=
  (Nat.Prime.dvd_iff_eq hp (show (3 : ℕ) ≠ 1 by decide)).mp h

/-- Un premier divisible par 2 vaut 2. -/
theorem prime_eq2 {p : ℕ} (hp : p.Prime) (h : 2 ∣ p) : p = 2 :=
  (Nat.Prime.dvd_iff_eq hp (show (2 : ℕ) ≠ 1 by decide)).mp h

theorem prime_three : Nat.Prime 3 := by decide

-- ============================================================
-- B. Parité des rayons et borne supérieure
-- ============================================================

/-- Pour tout rayon t, m−t et m+t sont impairs (premiers ≥ 3) :
m−t = 2 forcerait m+t pair ≥ 4. En particulier tous les rayons ont
la même parité (opposée à m), donc a±b est toujours pair. -/
theorem ray_both_odd {m t : ℕ} (ht : isRay m t) :
    (m - t) % 2 = 1 ∧ (m + t) % 2 = 1 := by
  have hge : 4 ≤ m + t := by
    have h1 := ht.1
    have h2 := ht.2.2.1.two_le
    omega
  rcases ht.2.2.1.eq_two_or_odd with hm1 | hm1
  · -- m − t = 2 : m + t = 2 + 2t est pair, premier, ≥ 4 — absurde
    have hd : 2 ∣ m + t := ⟨(m + t) / 2, by omega⟩
    have e := prime_eq2 ht.2.2.2 hd
    omega
  · rcases ht.2.2.2.eq_two_or_odd with hm2 | hm2
    · omega
    · exact ⟨hm1, hm2⟩

/-- Tout rayon est ≤ m−3 : b = m−1 donne m−b = 1 non premier ;
b = m−2 donne m+b = 2m−2 pair > 2 non premier. -/
theorem ray_le {m b : ℕ} (hb : isRay m b) : b ≤ m - 3 := by
  have hb1 := hb.1
  have hb2 := hb.2.1
  rcases (show b = m - 1 ∨ b = m - 2 ∨ b ≤ m - 3 by omega) with h | h | h
  · have e : m - b = 1 := by omega
    have hp := hb.2.2.1
    rw [e] at hp
    exact (Nat.not_prime_one hp).elim
  · have hd : 2 ∣ m + b := ⟨(m + b) / 2, by omega⟩
    have e := prime_eq2 hb.2.2.2 hd      -- m + b = 2, mais b = m−2 ≥ 1 ⇒ m+b ≥ 4
    omega
  · exact h

-- ============================================================
-- C. Dichotomie mod 3
-- ============================================================

/-- m ≡ 0 (mod 3) : AUCUN rayon n'est divisible par 3. (Forme correcte
de l'énoncé de mission — voir l'erratum en tête.) 3 | t rendrait
m−t et m+t multiples de 3, donc tous deux égaux à 3, impossible. -/
theorem ray_ndvd3_of_m0 {m t : ℕ} (hm : m % 3 = 0) (ht : isRay m t) :
    ¬ 3 ∣ t := by
  rintro ⟨j, rfl⟩
  have hlt : 3 * j < m := ht.2.1
  have hd1 : 3 ∣ m - 3 * j := ⟨(m - 3 * j) / 3, by omega⟩
  have hd2 : 3 ∣ m + 3 * j := ⟨(m + 3 * j) / 3, by omega⟩
  have e1 := prime_eq3 ht.2.2.1 hd1   -- m − t = 3
  have e2 := prime_eq3 ht.2.2.2 hd2   -- m + t = 3
  have ht1 : 1 ≤ 3 * j := ht.1
  omega

/-- Le pont : m−3 est un rayon ssi 2m−3 est premier (pour m ≥ 4 ;
m−(m−3) = 3 est toujours premier). -/
theorem pont_iff {m : ℕ} (hm : 4 ≤ m) :
    isRay m (m - 3) ↔ Nat.Prime (2 * m - 3) := by
  have h1 : m - (m - 3) = 3 := by omega
  have h2 : m + (m - 3) = 2 * m - 3 := by omega
  unfold isRay
  rw [h1, h2]
  exact ⟨fun h => h.2.2.2, fun h => ⟨by omega, by omega, prime_three, h⟩⟩

/-- m ≡ 0 (mod 3) n'a jamais de pont : 2m−3 est multiple de 3 > 3. -/
theorem no_pont_of_m0 {m : ℕ} (hm : m % 3 = 0) (hm4 : 4 ≤ m) :
    ¬ isRay m (m - 3) := by
  intro hp
  rw [pont_iff hm4] at hp
  have hd : 3 ∣ 2 * m - 3 := ⟨(2 * m - 3) / 3, by omega⟩
  have e := prime_eq3 hp hd           -- 2m − 3 = 3 ⇒ m = 3
  omega

/-- Dichotomie, m ≡ c ∈ {1,2} (mod 3) : tout rayon t est
  · « bulk » : 3 | t (les deux bords sont alors ≡ c mod 3, premiers
    possibles), ou
  · « pont » : t = m−3, i.e. m−t = 3 (t ≡ c mod 3 force m−t ≡ 0).
La troisième classe t ≡ −c (mod 3) tuerait m+t (multiple de 3 ≥ 4). -/
theorem ray_dvd3_or_pont {m t c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (ht : isRay m t) : 3 ∣ t ∨ t = m - 3 := by
  have hlt := ht.2.1
  have hge : 4 ≤ m + t := by
    have := ht.1
    have := ht.2.2.1.two_le
    omega
  have htri : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hc with rfl | rfl
  · -- c = 1
    rcases htri with h0 | h1 | h2
    · exact Or.inl ⟨t / 3, by omega⟩
    · right
      have hd : 3 ∣ m - t := ⟨(m - t) / 3, by omega⟩
      have e := prime_eq3 ht.2.2.1 hd   -- m − t = 3
      omega
    · have hd : 3 ∣ m + t := ⟨(m + t) / 3, by omega⟩
      have e := prime_eq3 ht.2.2.2 hd   -- m + t = 3, impossible (≥ 4)
      omega
  · -- c = 2
    rcases htri with h0 | h1 | h2
    · exact Or.inl ⟨t / 3, by omega⟩
    · have hd : 3 ∣ m + t := ⟨(m + t) / 3, by omega⟩
      have e := prime_eq3 ht.2.2.2 hd
      omega
    · right
      have hd : 3 ∣ m - t := ⟨(m - t) / 3, by omega⟩
      have e := prime_eq3 ht.2.2.1 hd   -- m − t = 3
      omega

-- ============================================================
-- D. Enfants : descente et classes mod 3
-- ============================================================

/-- Auxiliaire : x pair divisible par 3 ⇒ x/2 est divisible par 3,
donc l'enfant m − x/2 reste dans la classe de m. -/
theorem child_aux_bulk {m x c : ℕ} (hm : m % 3 = c) (_hc : c = 1 ∨ c = 2)
    (h0 : x % 3 = 0) (h2 : x % 2 = 0) (hle : x ≤ 2 * m) :
    (m - x / 2) % 3 = c := by
  have hx6 : x % 6 = 0 := by omega
  have hx2 : (x / 2) % 3 = 0 := by omega
  have hx2le : x / 2 ≤ m := by omega
  omega

/-- Auxiliaire : x pair ≡ c (mod 3) ⇒ x/2 ≡ 2c (mod 3), donc l'enfant
m − x/2 bascule dans la classe opposée 3−c. -/
theorem child_aux_pont {m x c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hxc : x % 3 = c) (h2 : x % 2 = 0) (hle : x ≤ 2 * m) :
    (m - x / 2) % 3 = 3 - c := by
  rcases hc with rfl | rfl
  · have hx6 : x % 6 = 4 := by omega   -- x ≡ 1 (mod 3), pair
    have hx2 : (x / 2) % 3 = 2 := by omega
    have hx2le : x / 2 ≤ m := by omega
    omega
  · have hx6 : x % 6 = 2 := by omega   -- x ≡ 2 (mod 3), pair
    have hx2 : (x / 2) % 3 = 1 := by omega
    have hx2le : x / 2 ≤ m := by omega
    omega

/-- Tout enfant est strictement plus petit que son parent :
la descente est bien fondée. -/
theorem child_lt {m n : ℕ} (h : isChild m n) : n < m := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd hb
  have haL := ray_le ha
  have hbL := ray_le hb
  have ha1 := ha.1
  have hb1 := hb.1
  rcases hd with rfl | rfl <;> omega

/-- Tout enfant est ≥ 1 : en bas, (a+b)/2 ≤ m−3 ; en haut,
(b−a)/2 ≤ m−4 puisque b ≤ m−3 et a ≥ 1. -/
theorem child_ge {m n : ℕ} (h : isChild m n) : 1 ≤ n := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd hb
  have haL := ray_le ha
  have hbL := ray_le hb
  have ha1 := ha.1
  rcases hd with rfl | rfl <;> omega

/-- Classes des enfants, m ≡ c ∈ {1,2} : tout enfant est soit dans la
classe c (paire bulk–bulk) soit dans la classe opposée 3−c (paire
contenant le pont b = m−3). Le pont ne peut être que le plus grand
élément de la paire (tout rayon ≤ m−3). -/
theorem child_mod3 {m n c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (h : isChild m n) : n % 3 = c ∨ n % 3 = 3 - c := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have hbL := ray_le hb
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd hb
  have hda := ray_dvd3_or_pont hm hc ha
  have hdb := ray_dvd3_or_pont hm hc hb
  rcases hda with ha3 | hap <;> rcases hdb with hb3 | hbp
  · -- a, b bulk (3 | a, 3 | b) : enfants dans la classe c
    obtain ⟨i, hi⟩ := ha3
    obtain ⟨j, hj⟩ := hb3
    rcases hd with rfl | rfl
    · exact Or.inl (child_aux_bulk hm hc (by omega) (by omega) (by omega))
    · exact Or.inl (child_aux_bulk hm hc (by omega) (by omega) (by omega))
  · -- a bulk, b = m−3 pont : enfants dans la classe opposée 3−c
    obtain ⟨i, hi⟩ := ha3
    subst hbp
    rcases hd with rfl | rfl
    · exact Or.inr (child_aux_pont hm hc (by omega) (by omega) (by omega))
    · exact Or.inr (child_aux_pont hm hc (by omega) (by omega) (by omega))
  · -- a = m−3 pont, b > a : impossible, tout rayon ≤ m−3
    subst hap
    omega
  · -- a = b = m−3 : impossible, a < b
    subst hap; subst hbp
    omega

/-- Sans pont, tous les rayons sont bulk : tous les enfants restent
dans la classe c. -/
theorem child_mod3_no_pont {m n c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hnop : ¬ isRay m (m - 3)) (h : isChild m n) : n % 3 = c := by
  obtain ⟨a, b, ha, hb, hab, hd⟩ := h
  have ha3 : 3 ∣ a :=
    (ray_dvd3_or_pont hm hc ha).resolve_right (fun hae => hnop (hae ▸ ha))
  have hb3 : 3 ∣ b :=
    (ray_dvd3_or_pont hm hc hb).resolve_right (fun hbe => hnop (hbe ▸ hb))
  obtain ⟨i, hi⟩ := ha3
  obtain ⟨j, hj⟩ := hb3
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd hb
  rcases hd with rfl | rfl
  · exact child_aux_bulk hm hc (by omega) (by omega) (by omega)
  · exact child_aux_bulk hm hc (by omega) (by omega) (by omega)

/-- Réciproque : un enfant dans la classe opposée 3−c certifie
l'existence du pont. -/
theorem pont_of_child_opp {m n c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (h : isChild m n) (hopp : n % 3 = 3 - c) : isRay m (m - 3) := by
  by_contra hnop
  have hcc := child_mod3_no_pont hm hc hnop h
  rcases hc with rfl | rfl <;> omega

/-- Forme « par paire » : les enfants d'une paire de rayons bulk
restent dans la classe de m. -/
theorem child_of_bulk_pair {m a b n : ℕ} (ha : isRay m a) (hb : isRay m b)
    (ha3 : 3 ∣ a) (hb3 : 3 ∣ b) (_hab : a < b)
    (hn : n = m - (b - a) / 2 ∨ n = m - (a + b) / 2) :
    n % 3 = m % 3 := by
  obtain ⟨i, hi⟩ := ha3
  obtain ⟨j, hj⟩ := hb3
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd hb
  rcases hn with rfl | rfl
  · have hx6 : (b - a) % 6 = 0 := by omega
    have hx2 : (b - a) / 2 % 3 = 0 := by omega
    omega
  · have hx6 : (a + b) % 6 = 0 := by omega
    have hx2 : (a + b) / 2 % 3 = 0 := by omega
    omega

/-- Forme « par paire » : les enfants d'une paire contenant le pont
b = m−3 (l'autre rayon étant bulk) basculent dans la classe 3−c. -/
theorem child_of_pont_pair {m a b n c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (ha : isRay m a) (_hb : isRay m b)
    (ha3 : 3 ∣ a) (hbp : b = m - 3) (_hab : a < b)
    (hn : n = m - (b - a) / 2 ∨ n = m - (a + b) / 2) :
    n % 3 = 3 - c := by
  obtain ⟨i, hi⟩ := ha3
  have hpa := ray_both_odd ha
  have hpb := ray_both_odd _hb
  subst hbp
  rcases hn with rfl | rfl
  · exact child_aux_pont hm hc (by omega) (by omega) (by omega)
  · exact child_aux_pont hm hc (by omega) (by omega) (by omega)

-- ============================================================
-- E. Certificats : « min de classe sans pont est puits »
-- ============================================================

/-- PUIT (forme précise) : soit V_k = {u | r u ≥ k}. Si m ≡ c ∈ {1,2}
est le MINIMUM de sa classe dans V_k — i.e. ∀ u < m, u ≡ c ⇒ r u < k —
et si m n'a PAS de pont (m−3 non rayon), alors tout enfant n de m
vérifie r n < k : m est un puits, la descente ne peut pas rester
≥ k dans sa propre classe. -/
theorem puits {r : ℕ → ℕ} {m k c : ℕ} (hm : m % 3 = c) (hc : c = 1 ∨ c = 2)
    (hnop : ¬ isRay m (m - 3))
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : ℕ} (hn : isChild m n) : r n < k :=
  hmin n (child_lt hn) (child_mod3_no_pont hm hc hnop hn)

/-- Forme calculable du puits : l'absence de pont se teste par
« 2m−3 non premier » (m ≥ 4). -/
theorem puits_of_not_prime {r : ℕ → ℕ} {m k c : ℕ} (hm : m % 3 = c)
    (hc : c = 1 ∨ c = 2) (hm4 : 4 ≤ m) (hnop : ¬ Nat.Prime (2 * m - 3))
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : ℕ} (hn : isChild m n) : r n < k :=
  puits hm hc ((pont_iff hm4).not.mpr hnop) hmin hn

/-- Descente générale (pont autorisé) : tout enfant de m minimal dans
sa classe descend (r n < k) OU bascule dans la classe opposée 3−c —
et alors le pont existe (pont_of_child_opp). -/
theorem descente_split {r : ℕ → ℕ} {m k c : ℕ} (hm : m % 3 = c)
    (hc : c = 1 ∨ c = 2)
    (hmin : ∀ u, u < m → u % 3 = c → r u < k)
    {n : ℕ} (hn : isChild m n) : r n < k ∨ n % 3 = 3 - c := by
  rcases child_mod3 hm hc hn with h1 | h1
  · exact Or.inl (hmin n (child_lt hn) h1)
  · exact Or.inr h1

-- ============================================================
-- Contre-exemple à la forme littérale de l'énoncé de mission
-- ============================================================

/-- m = 6 ≡ 0 (mod 3), t = 1 ∈ S(6) : m−t = 5 et m+t = 7 premiers > 3,
et pourtant 3 ∤ 1. La clause « m ≡ 0 ⇒ 3 | t » était donc fausse ;
l'énoncé prouvé est `ray_ndvd3_of_m0` (3 ∤ t). -/
theorem counter_ex_m6 :
    ¬ ∀ m t : ℕ, m % 3 = 0 → isRay m t → 3 < m - t → 3 < m + t → 3 ∣ t := by
  intro h
  have hr : isRay 6 1 := ⟨by decide, by decide, by decide, by decide⟩
  have hd := h 6 1 (by decide) hr (by decide) (by decide)
  exact (by decide : ¬ (3 : ℕ) ∣ 1) hd

-- Audit (attendu : propext, Classical.choice, Quot.sound)
#print axioms puits
#print axioms puits_of_not_prime
#print axioms descente_split
#print axioms pont_of_child_opp
#print axioms counter_ex_m6
