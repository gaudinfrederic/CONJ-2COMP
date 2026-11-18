/-
descente_bijection.lean — verification machine de la bijection du goulot
(les temoins p d'un enfant u1 vis-a-vis de son parent u2).

Contexte (digraphe de re-pairage) :
  S(m) = { t : 1 <= t < m, m - t et m + t premiers } (les rayons).
  Pour a < b dans S(m), les enfants de m le long de {a,b} sont
  n1 = m - (b-a)/2 (canal-difference) et n2 = m - (a+b)/2 (canal-somme).

ENONCE PRINCIPAL (bijection du goulot) : pour u1 < u2, v = u2 - u1,

    ChildGen u1 u2  : existe a < b dans S(u2) avec (b-a)/2 = v ou (a+b)/2 = v
    N_witness u1 u2 : existe p dans [3, u1-1] avec p, 2u1-p, p+2v, 2u2-p
                      premiers et p /= 2u1 - u2

    theorem goulot_bijection : ChildGen u1 u2 <-> N_witness u1 u2

  Sens <- : p temoin, d = u1 - p (rayon associe de u1), a = |v - d|,
  b = v + d ; les quatre primalites donnent u2 - a, u2 + a, u2 - b,
  u2 + b premiers. La condition p /= 2u1 - u2 est exactement v /= d,
  i.e. a >= 1.
  Sens -> : la paire a < b produisant le canal v donne p = u2 - b ;
  les quatre primalites se recasent sur u2 - a / u2 + a selon le canal.

BORNE : N(u1,u2) = nombre de temoins (witList). Chaque temoin p donne
  un rayon t = u1 - p de u1 (repond p / 2u1 - p) et un rayon t = u2 - p
  de u2 (repond p / 2u2 - p), injections :
    NN_le_r_u1 / NN_le_r_u2, et NN_le_min_r : NN <= min (r u1) (r u2)
    [inconditionnel, compte TOUT rayon t in [1, m-2]].
  Pour r5 (rayons t <= m - 4, i.e. le rayon t = m - 3 exclu) : p = 3 est
  le seul temoin qui tombe sur le rayon exclu, et il exige 2u2 - 3
  premier. Donc sous `~ Premier (2u2 - 3)` :
    NN_le_min_r5 : NN u1 u2 <= min (r5 u1) (r5 u2).
  CONTRE-EXEMPLE montrant que la borne r5 est fausse sans cette
  hypothese : (u1,u2) = (4,11) admet le temoin p = 3 (3, 5, 17, 19
  premiers, 3 /= 2*4-11 = 0 en Nat) mais r5(4) = 0.

PLAFOND : si u2 % 3 /= 0 et 2u2 - 3 compose, alors tout rayon de u2 est
  = 0 mod 3 (ray_mod3 : u2 - t = 3 est exclu par la composite, u2 + t
  = 3 est trop petit), donc tout enfant n de u2 verifie n < u2 et
  n % 3 = u2 % 3 (child_class). Si u1 < u2 est dans la meme classe et
  majore { r u : u < u2, u % 3 = u2 % 3 } (le maximum de la classe sous
  le record), alors tout enfant a r n <= r u1 (plafond). Le cas
  u2 % 3 = 0 n'est pas couvert : des enfants peuvent sortir de la
  classe (ex. u2 = 12 : enfant 10 = 12 - (5-1)/2 = 1 mod 3).

Mathlib ABSENT (.lake/packages vide) : Lean 4 core seul, predicat
Premier local + test booleen bPremier avec le pont bPremier_iff.
Verifier : `lean descente_bijection.lean`.
ZERO sorry / admit / axiom / native_decide.
-/

set_option linter.unusedSectionVars false

-- ============================================================
-- 1. Primalite : Prop (spec), Bool (calcul), et le pont
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

-- ============================================================
-- 2. Rayons S(m) et lemmes de parite / bornes
-- ============================================================

/-- S(m) : les rayons de m, t in [1, m) avec m-t et m+t premiers -/
def S_of (m t : Nat) : Prop :=
  1 ≤ t ∧ t < m ∧ Premier (m - t) ∧ Premier (m + t)

/-- tout rayon impose m >= 4 (S(m) est vide pour m <= 3) -/
theorem S_of.ge_four {m t : Nat} (ht : S_of m t) : 4 ≤ m := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  rcases Nat.lt_or_ge m 4 with hlt | hge
  · have hm23 : m = 2 ∨ m = 3 := by omega
    rcases hm23 with rfl | rfl
    · have ht1 : t = 1 := by omega
      subst ht1
      have hq : Premier 1 := hpm
      exact absurd hq.1 (by decide)
    · have ht12 : t = 1 ∨ t = 2 := by omega
      rcases ht12 with rfl | rfl
      · have hq : Premier 4 := hpp
        rcases hq.2 2 ⟨2, rfl⟩ with e | e <;> omega
      · have hq : Premier 1 := hpm
        exact absurd hq.1 (by decide)
  · exact hge

/-- parite : pour m >= 4, tout rayon de m a la parite opposee a m
    (sinon m - t premier pair = 2, t = m - 2, et m + t = 2m - 2 est
    premier pair >= 4 : absurde) -/
theorem S_of.parity {m t : Nat} (hm : 4 ≤ m) (ht : S_of m t) :
    t % 2 ≠ m % 2 := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  intro hpar
  have hdvd : 2 ∣ m - t := Nat.dvd_of_mod_eq_zero (by omega)
  have h2 : m - t = 2 := hpm.eq_two_of_two_dvd hdvd
  have hdvd2 : 2 ∣ m + t := ⟨m - 1, by omega⟩
  rcases hpp.2 2 hdvd2 with e | e <;> omega

/-- borne : tout rayon de m est <= m - 3
    (t = m - 1 donne m - t = 1 ; t = m - 2 donne m + t = 2m - 2 premier
    pair : absurde dans les deux cas) -/
theorem S_of.le_sub_three {m t : Nat} (ht : S_of m t) : t ≤ m - 3 := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  rcases Nat.lt_or_ge (m - 3) t with hlt | hge
  · have htm2 : t = m - 2 ∨ t = m - 1 := by omega
    rcases htm2 with h | h
    · have hdvd : 2 ∣ m + t := ⟨m - 1, by omega⟩
      rcases hpp.2 2 hdvd with e | e <;> omega
    · have hq : Premier 1 := by
        have e : m - t = 1 := by omega
        rw [e] at hpm; exact hpm
      exact absurd hq.1 (by decide)
  · exact hge

-- ============================================================
-- 3. Le goulot : ChildGen <-> N_witness
-- ============================================================

/-- u1 enfant de u2 : une paire a < b de rayons de u2 produit le canal
    v = u2 - u1, par difference (b-a)/2 ou par somme (a+b)/2 -/
def ChildGen (u1 u2 : Nat) : Prop :=
  ∃ a b : Nat, S_of u2 a ∧ S_of u2 b ∧ a < b ∧
    ((b - a) / 2 = u2 - u1 ∨ (a + b) / 2 = u2 - u1)

/-- p temoin du canal u2 -> u1 : p dans [3, u1-1], les quatre reponses
    p, 2u1 - p, p + 2v, 2u2 - p premieres, et p /= 2u1 - u2 -/
def N_witness (u1 u2 : Nat) : Prop :=
  ∃ p : Nat, 3 ≤ p ∧ p ≤ u1 - 1 ∧ Premier p ∧ Premier (2 * u1 - p) ∧
    Premier (p + 2 * (u2 - u1)) ∧ Premier (2 * u2 - p) ∧ p ≠ 2 * u1 - u2

/-- THEOREME PRINCIPAL : bijection du goulot. -/
theorem goulot_bijection {u1 u2 : Nat} (h : u1 < u2) :
    ChildGen u1 u2 ↔ N_witness u1 u2 := by
  obtain ⟨v, hv⟩ : ∃ v : Nat, u2 = u1 + v := ⟨u2 - u1, by omega⟩
  have hv1 : 1 ≤ v := by omega
  constructor
  · -- ChildGen -> temoin p = u2 - b
    rintro ⟨a, b, ha, hb, hab, hchan⟩
    have hu4 : 4 ≤ u2 := ha.ge_four
    have hpar : a % 2 = b % 2 := by
      have pa := ha.parity hu4; have pb := hb.parity hu4; omega
    have hb3 : b ≤ u2 - 3 := hb.le_sub_three
    obtain ⟨ha1, ham, ham1, ham2⟩ := ha
    obtain ⟨hb1, hbm, hbm1, hbm2⟩ := hb
    refine ⟨u2 - b, by omega, by omega, hbm1, ?_, ?_, ?_, ?_⟩
    · rcases hchan with hd | hs
      · -- canal-difference : b - a = 2v
        have hbd : b - a = 2 * v := by omega
        have e : 2 * u1 - (u2 - b) = u2 + a := by omega
        rw [e]; exact ham2
      · -- canal-somme : a + b = 2v
        have hbs : a + b = 2 * v := by omega
        have e : 2 * u1 - (u2 - b) = u2 - a := by omega
        rw [e]; exact ham1
    · rcases hchan with hd | hs
      · have hbd : b - a = 2 * v := by omega
        have e : (u2 - b) + 2 * (u2 - u1) = u2 - a := by omega
        rw [e]; exact ham1
      · have hbs : a + b = 2 * v := by omega
        have e : (u2 - b) + 2 * (u2 - u1) = u2 + a := by omega
        rw [e]; exact ham2
    · have e : 2 * u2 - (u2 - b) = u2 + b := by omega
      rw [e]; exact hbm2
    · -- p /= 2u1 - u2, i.e. u2 - b /= 2u1 - u2
      rcases hchan with hd | hs
      · have hbd : b - a = 2 * v := by omega
        omega
      · have hbs : a + b = 2 * v := by omega
        omega
  · -- temoin p -> paire (|v-d|, v+d) avec d = u1 - p
    rintro ⟨p, hp3, hpu1, hpp, hp2u1, hpp2v, hp2u2, hpne⟩
    obtain ⟨d, hd⟩ : ∃ d : Nat, u1 = p + d := ⟨u1 - p, by omega⟩
    have hd1 : 1 ≤ d := by omega
    have hvd : v ≠ d := by omega
    rcases Nat.lt_or_ge d v with hdv | hdv
    · -- d < v : canal-somme, a = v - d, b = v + d
      refine ⟨v - d, v + d, ?_, ?_, by omega, Or.inr (by omega)⟩
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · have e : u2 - (v - d) = 2 * u1 - p := by omega
          rw [e]; exact hp2u1
        · have e : u2 + (v - d) = p + 2 * (u2 - u1) := by omega
          rw [e]; exact hpp2v
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · have e : u2 - (v + d) = p := by omega
          rw [e]; exact hpp
        · have e : u2 + (v + d) = 2 * u2 - p := by omega
          rw [e]; exact hp2u2
    · -- d > v (d /= v) : canal-difference, a = d - v, b = d + v
      have hdv' : v < d := by omega
      refine ⟨d - v, d + v, ?_, ?_, by omega, Or.inl (by omega)⟩
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · have e : u2 - (d - v) = p + 2 * (u2 - u1) := by omega
          rw [e]; exact hpp2v
        · have e : u2 + (d - v) = 2 * u1 - p := by omega
          rw [e]; exact hp2u1
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · have e : u2 - (d + v) = p := by omega
          rw [e]; exact hpp
        · have e : u2 + (d + v) = 2 * u2 - p := by omega
          rw [e]; exact hp2u2

/-- tout enfant est strictement plus petit que son parent
    (point fixe impossible : les canaux sont >= 1) -/
theorem childGen_lt {n u2 : Nat} (hn : ChildGen n u2) : n < u2 := by
  obtain ⟨a, b, ha, hb, hab, hchan⟩ := hn
  have hu4 : 4 ≤ u2 := ha.ge_four
  have hpar : a % 2 = b % 2 := by
    have pa := ha.parity hu4; have pb := hb.parity hu4; omega
  obtain ⟨ha1, _, _, _⟩ := ha
  obtain ⟨hb1, _, _, _⟩ := hb
  rcases hchan with hd | hs <;> omega

-- ============================================================
-- 4. Comptage : listes de rayons et de temoins, borne N <= r
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

/-- predicat booleen « p temoin du canal u2 -> u1 » -/
def witBool (u1 u2 : Nat) : Nat → Bool := fun p =>
  bPremier p && bPremier (2 * u1 - p) && bPremier (p + 2 * (u2 - u1)) &&
    bPremier (2 * u2 - p) && (p != 2 * u1 - u2)

/-- temoins en liste : p in [3, u1-1] -/
def witList (u1 u2 : Nat) : List Nat :=
  (List.range' 3 (u1 - 3)).filter (witBool u1 u2)

/-- N(u1,u2) = nombre de temoins -/
def NN (u1 u2 : Nat) : Nat := (witList u1 u2).length

/-- witBool deplie : la conjonction booleenne en Prop -/
theorem witBool_true {u1 u2 p : Nat} : witBool u1 u2 p = true ↔
    bPremier p = true ∧ bPremier (2 * u1 - p) = true ∧
      bPremier (p + 2 * (u2 - u1)) = true ∧ bPremier (2 * u2 - p) = true ∧
      p ≠ 2 * u1 - u2 := by
  unfold witBool
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    bne_iff_ne]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

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

/-- appartenance a ray5List, depliee -/
theorem mem_ray5List {m t : Nat} : t ∈ ray5List m ↔
    1 ≤ t ∧ t ≤ m - 4 ∧ bPremier (m - t) = true ∧ bPremier (m + t) = true := by
  unfold ray5List rayBool
  rw [List.mem_filter, List.mem_range', Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨by omega, by omega, hp.1, hp.2⟩
  · rintro ⟨h1, h2, hp1, hp2⟩
    exact ⟨⟨t - 1, by omega, by omega⟩, hp1, hp2⟩

/-- appartenance a witList, depliee -/
theorem mem_witList {u1 u2 p : Nat} : p ∈ witList u1 u2 ↔
    3 ≤ p ∧ p ≤ u1 - 1 ∧ witBool u1 u2 p = true := by
  unfold witList
  rw [List.mem_filter, List.mem_range']
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨by omega, by omega, hp⟩
  · rintro ⟨h1, h2, hp⟩
    exact ⟨⟨p - 3, by omega, by omega⟩, hp⟩

/-- pont entre le temoin propositionnel et le temoin en liste -/
theorem n_witness_iff_exists_mem {u1 u2 : Nat} :
    N_witness u1 u2 ↔ ∃ p, p ∈ witList u1 u2 := by
  constructor
  · rintro ⟨p, hp3, hpu1, hp1, hp2, hp3', hp4, hpne⟩
    exact ⟨p, mem_witList.mpr ⟨hp3, hpu1, witBool_true.mpr
        ⟨(bPremier_iff _).mpr hp1, (bPremier_iff _).mpr hp2,
         (bPremier_iff _).mpr hp3', (bPremier_iff _).mpr hp4, hpne⟩⟩⟩
  · rintro ⟨p, hp⟩
    obtain ⟨hp3, hpu1, hb⟩ := mem_witList.mp hp
    obtain ⟨hb1, hb2, hb3, hb4, hne⟩ := witBool_true.mp hb
    exact ⟨p, hp3, hpu1, (bPremier_iff _).mp hb1, (bPremier_iff _).mp hb2,
      (bPremier_iff _).mp hb3, (bPremier_iff _).mp hb4, hne⟩

/-- une liste non vide a un element -/
theorem exists_mem_of_length_pos {l : List Nat} (h : 0 < l.length) :
    ∃ x, x ∈ l := by
  cases l with
  | nil => simp at h
  | cons x t => exact ⟨x, List.mem_cons.mpr (Or.inl rfl)⟩

/-- N(u1,u2) > 0 <-> il existe un temoin -/
theorem NN_pos_iff {u1 u2 : Nat} : 0 < NN u1 u2 ↔ N_witness u1 u2 := by
  constructor
  · intro h
    exact n_witness_iff_exists_mem.mpr (exists_mem_of_length_pos h)
  · intro h
    obtain ⟨p, hp⟩ := n_witness_iff_exists_mem.mp h
    exact List.length_pos_of_mem hp

/-- corollaire : la bijection reecrite en comptage -/
theorem childGen_iff_NN_pos {u1 u2 : Nat} (h : u1 < u2) :
    ChildGen u1 u2 ↔ 0 < NN u1 u2 :=
  (goulot_bijection h).trans NN_pos_iff.symm

/-- pigeonhole fini : une liste sans doublon qui s'injecte (par f)
    dans une autre liste est au plus aussi longue -/
theorem length_le_of_inj_mem {l m : List Nat} (f : Nat → Nat) :
    l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    (∀ x ∈ l, f x ∈ m) →
    l.length ≤ m.length := by
  revert m
  induction l with
  | nil => intro m _ _ _; simp
  | cons a t iht =>
      intro m hl hinj hmap
      obtain ⟨hat, ht⟩ := List.nodup_cons.mp hl
      have hfam : f a ∈ m := hmap a (List.mem_cons.mpr (Or.inl rfl))
      have hmpos : 0 < m.length := List.length_pos_of_mem hfam
      have hinj' : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y :=
        fun x hx y hy hxy => hinj x (List.mem_cons.mpr (Or.inr hx)) y
          (List.mem_cons.mpr (Or.inr hy)) hxy
      have hmap' : ∀ x ∈ t, f x ∈ m.erase (f a) := by
        intro x hx
        have hne : f x ≠ f a := by
          intro hEq
          have hxa : x = a := hinj x (List.mem_cons.mpr (Or.inr hx)) a
            (List.mem_cons.mpr (Or.inl rfl)) hEq
          exact hat (hxa ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr
          (hmap x (List.mem_cons.mpr (Or.inr hx)))
      have ih := iht ht hinj' hmap'
      have hlen := List.length_erase_of_mem hfam
      simp only [List.length_cons]
      omega

/-- witList est sans doublon (sous-liste de range') -/
theorem witList_nodup (u1 u2 : Nat) : (witList u1 u2).Nodup :=
  List.filter_sublist.nodup (List.nodup_range' 1 (by omega))

/-- injectivite de p -> c - p sur [1, c-1] -/
theorem sub_inj {c x y : Nat} (hx : x ≤ c - 1) (hy : y ≤ c - 1)
    (h : c - x = c - y) : x = y := by omega

/-- BORNE inconditionnelle cote u1 : chaque temoin p donne le rayon
    t = u1 - p de u1 (reponses p et 2u1 - p). -/
theorem NN_le_r_u1 {u1 u2 : Nat} (h : u1 < u2) : NN u1 u2 ≤ r u1 := by
  refine length_le_of_inj_mem (fun p => u1 - p) (witList_nodup u1 u2) ?_ ?_
  · intro x hx y hy hxy
    obtain ⟨_, hxu, _⟩ := mem_witList.mp hx
    obtain ⟨_, hyu, _⟩ := mem_witList.mp hy
    exact sub_inj hxu hyu hxy
  · intro x hx
    obtain ⟨hx3, hxu, hb⟩ := mem_witList.mp hx
    obtain ⟨hp1, hp2, _, _, _⟩ := witBool_true.mp hb
    refine mem_rayList.mpr ⟨by omega, by omega, ?_, ?_⟩
    · have e : u1 - (u1 - x) = x := by omega
      rw [e]; exact hp1
    · have e : u1 + (u1 - x) = 2 * u1 - x := by omega
      rw [e]; exact hp2

/-- BORNE inconditionnelle cote u2 : chaque temoin p donne le rayon
    t = u2 - p de u2 (reponses p et 2u2 - p). -/
theorem NN_le_r_u2 {u1 u2 : Nat} (h : u1 < u2) : NN u1 u2 ≤ r u2 := by
  refine length_le_of_inj_mem (fun p => u2 - p) (witList_nodup u1 u2) ?_ ?_
  · intro x hx y hy hxy
    obtain ⟨_, hxu, _⟩ := mem_witList.mp hx
    obtain ⟨_, hyu, _⟩ := mem_witList.mp hy
    -- u2 - x = u2 - y avec x, y < u1 < u2 : injectif
    omega
  · intro x hx
    obtain ⟨hx3, hxu, hb⟩ := mem_witList.mp hx
    obtain ⟨hp1, _, _, hp4, _⟩ := witBool_true.mp hb
    refine mem_rayList.mpr ⟨by omega, by omega, ?_, ?_⟩
    · have e : u2 - (u2 - x) = x := by omega
      rw [e]; exact hp1
    · have e : u2 + (u2 - x) = 2 * u2 - x := by omega
      rw [e]; exact hp4

/-- la borne inconditionnelle correcte : N <= min(r u1, r u2) -/
theorem NN_le_min_r {u1 u2 : Nat} (h : u1 < u2) :
    NN u1 u2 ≤ min (r u1) (r u2) :=
  Nat.le_min.mpr ⟨NN_le_r_u1 h, NN_le_r_u2 h⟩

/-- sous `~ Premier (2u2 - 3)`, aucun temoin ne vaut 3 -/
theorem wit_ne_three {u1 u2 : Nat} (hcomp : ¬ Premier (2 * u2 - 3))
    {p : Nat} (hp : p ∈ witList u1 u2) : p ≠ 3 := by
  obtain ⟨_, _, hb⟩ := mem_witList.mp hp
  obtain ⟨_, _, _, hp4, _⟩ := witBool_true.mp hb
  intro h3
  rw [h3] at hp4
  exact hcomp ((bPremier_iff _).mp hp4)

/-- BORNE r5 (rayons t <= m-4) : sous `~ Premier (2u2 - 3)` tous les
    temoins valent >= 4, donc t = u1-p <= u1-4 et t = u2-p <= u2-4. -/
theorem NN_le_min_r5 {u1 u2 : Nat} (h : u1 < u2)
    (hcomp : ¬ Premier (2 * u2 - 3)) :
    NN u1 u2 ≤ min (r5 u1) (r5 u2) := by
  have h4 : ∀ p ∈ witList u1 u2, 4 ≤ p := by
    intro p hp
    have hp3 := (mem_witList.mp hp).1
    have hpne := wit_ne_three hcomp hp
    omega
  apply Nat.le_min.mpr
  constructor
  · -- NN <= r5 u1 : injection p -> u1 - p
    refine length_le_of_inj_mem (fun p => u1 - p) (witList_nodup u1 u2) ?_ ?_
    · intro x hx y hy hxy
      obtain ⟨_, hxu, _⟩ := mem_witList.mp hx
      obtain ⟨_, hyu, _⟩ := mem_witList.mp hy
      exact sub_inj hxu hyu hxy
    · intro x hx
      obtain ⟨hx3, hxu, hb⟩ := mem_witList.mp hx
      obtain ⟨hp1, hp2, _, _, _⟩ := witBool_true.mp hb
      have hx4 := h4 x hx
      refine mem_ray5List.mpr ⟨by omega, by omega, ?_, ?_⟩
      · have e : u1 - (u1 - x) = x := by omega
        rw [e]; exact hp1
      · have e : u1 + (u1 - x) = 2 * u1 - x := by omega
        rw [e]; exact hp2
  · -- NN <= r5 u2 : injection p -> u2 - p
    refine length_le_of_inj_mem (fun p => u2 - p) (witList_nodup u1 u2) ?_ ?_
    · intro x hx y hy hxy
      obtain ⟨_, hxu, _⟩ := mem_witList.mp hx
      obtain ⟨_, hyu, _⟩ := mem_witList.mp hy
      omega
    · intro x hx
      obtain ⟨hx3, hxu, hb⟩ := mem_witList.mp hx
      obtain ⟨hp1, _, _, hp4, _⟩ := witBool_true.mp hb
      have hx4 := h4 x hx
      refine mem_ray5List.mpr ⟨by omega, by omega, ?_, ?_⟩
      · have e : u2 - (u2 - x) = x := by omega
        rw [e]; exact hp1
      · have e : u2 + (u2 - x) = 2 * u2 - x := by omega
        rw [e]; exact hp4

-- ============================================================
-- 5. Plafond : les enfants d'un record mod 3 restent dans la classe
-- ============================================================

/-- si m % 3 /= 0 et 2m - 3 compose, tout rayon de m est = 0 mod 3 :
    t = m - 3 donnerait m + t = 2m - 3 premier (exclu), et m + t = 3
    est impossible (m + t >= 5). Donc t % 3 evite m%3 et -m%3. -/
theorem ray_mod3 {m t : Nat} (hm : 4 ≤ m) (hc : m % 3 ≠ 0)
    (hcomp : ¬ Premier (2 * m - 3)) (ht : S_of m t) : t % 3 = 0 := by
  obtain ⟨h1, htm, hpm, hpp⟩ := ht
  have hsub : (m - t) % 3 ≠ 0 := by
    intro h3
    have hmeq : m - t = 3 :=
      hpm.eq_three_of_three_dvd (Nat.dvd_of_mod_eq_zero h3)
    have e : m + t = 2 * m - 3 := by omega
    rw [e] at hpp
    exact hcomp hpp
  have hadd : (m + t) % 3 ≠ 0 := by
    intro h3
    have hmeq : m + t = 3 :=
      hpp.eq_three_of_three_dvd (Nat.dvd_of_mod_eq_zero h3)
    omega
  -- t % 3 /= m % 3 (sinon (m-t)%3 = 0) et t % 3 /= -m % 3
  -- (sinon (m+t)%3 = 0) ; comme m % 3 /= 0, il ne reste que t % 3 = 0.
  have ht3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases ht3 with e | e | e
  · exact e
  · rcases hm3 with em | em
    · have hz : (m - t) % 3 = 0 := by omega
      exact absurd hz hsub
    · have hz : (m + t) % 3 = 0 := by omega
      exact absurd hz hadd
  · rcases hm3 with em | em
    · have hz : (m + t) % 3 = 0 := by omega
      exact absurd hz hadd
    · have hz : (m - t) % 3 = 0 := by omega
      exact absurd hz hsub

/-- les enfants d'un parent =/= 0 mod 3 (avec 2u2-3 compose) restent
    dans sa classe et lui sont strictement inferieurs -/
theorem child_class {u2 n : Nat} (hm : 4 ≤ u2) (hc : u2 % 3 ≠ 0)
    (hcomp : ¬ Premier (2 * u2 - 3)) (hn : ChildGen n u2) :
    n % 3 = u2 % 3 ∧ n < u2 := by
  obtain ⟨a, b, ha, hb, hab, hchan⟩ := hn
  have hpar : a % 2 = b % 2 := by
    have pa := ha.parity hm; have pb := hb.parity hm; omega
  have ha3 : a % 3 = 0 := ray_mod3 hm hc hcomp ha
  have hb3 : b % 3 = 0 := ray_mod3 hm hc hcomp hb
  obtain ⟨ha1, _, _, _⟩ := ha
  obtain ⟨hb1, hbm, _, _⟩ := hb
  -- (b-a)/2 et (a+b)/2 sont = 0 mod 3 (differences/sommes de multiples
  -- de 3, paires) ; n = u2 - canal donne n % 3 = u2 % 3 et n < u2.
  rcases hchan with hd | hs <;> omega

/-- PLAFOND : si u2 est un parent =/= 0 mod 3 avec 2u2-3 compose, et
    u1 est le maximum de sa classe (r u1 >= r u pour tout u < u2 dans
    la classe de u2), alors tout enfant n de u2 a r n <= r u1.
    (L'hypothese « u2 record » n'intervient pas : le plafond vient de
    ce que les enfants retombent dans la classe sous u2 ; le record
    motive l'enonce car il dit que le maximum saute de u1 a u2.) -/
theorem plafond {u1 u2 : Nat}
    (_hu1 : u1 < u2) (_hu1c : u1 % 3 = u2 % 3)
    (hmax : ∀ u : Nat, u < u2 → u % 3 = u2 % 3 → r u ≤ r u1)
    (hm : 4 ≤ u2) (hc : u2 % 3 ≠ 0) (hcomp : ¬ Premier (2 * u2 - 3))
    {n : Nat} (hchild : ChildGen n u2) : r n ≤ r u1 := by
  obtain ⟨hcn, hlt⟩ := child_class hm hc hcomp hchild
  exact hmax n hlt hcn

-- Audit (attendu : propext, Classical.choice, Quot.sound)
#print axioms goulot_bijection
#print axioms NN_le_min_r
#print axioms NN_le_min_r5
#print axioms plafond
