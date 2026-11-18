/-
descente_tiroirs.lean — reduction finie par principe des tiroirs
(item (c) du triptyque Lean annonce dans FALSIFICATION.md sec.5)

Source (enonces) : ../FALSIFICATION.md (depot CONJ-2COMP)
  S(m) = {t >= 1 : m-t, m+t premiers} ; r(m) = |S(m)| (= A061357)
  Enfants n = m-v, v = (b-a)/2 ou (a+b)/2 ; retenu si n < m et r(n) >= k.
  V_k = {m : r(m) >= k} ; puits = vital sans enfant retenu.
  M_cut(k,L) = L+1+floor((L-4)/(2k-3)).

Conventions prime/bprime/rays/r recopiees de N5_kernel.lean
(duplication volontaire : chaque fichier du dossier reste standalone,
convention « lean fichier.lean », pas d'import entre fichiers).

Core Lean seul (pas d'import Mathlib dans ce fichier) : pas de Finset,
les listes trichees jouent le role des ensembles finis.
ZERO sorry / admit / native_decide / decide dans ce fichier.

Chaine de deduction :
  A. Lemme de parite des rayons (rays_mem_spec, recopie de N5) :
     tout rayon de m (m >= 4) a la parite opposee a m et t <= m-3 ;
     donc tous les rayons ont meme parite et les ecarts consecutifs
     sont pairs — la division par 2 des ecarts est exacte.
  B. gaps (zipWith) : ecarts consecutifs d'une liste ; leur somme
     telescopique vaut dernier - premier <= B - A.
  C. Tiroirs (exists_adj_gap) : >= k elements dans [A,B] de meme
     parite => un ecart adjacent v verifie v/2 <= (B-A)/(2*(k-1)),
     sinon la somme depasserait (k-1)*2*(D+1) > B-A.
  D. descente_tiroirs : m vital (r(m) >= k) et m >= M_cut =>
     enfant retenu n* = m - v/2 > L => r(n*) >= k => m pas puits.
-/

set_option linter.unusedSectionVars false

namespace Descente

-- ============================================================
-- 1. Primalite : Prop (spec) et Bool (calcul), avec le pont
--    (copie verbatim de N5_kernel.lean sec.1)
-- ============================================================

/-- primalite mathematique -/
def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- test booleen : aucun diviseur dans [2, n) -/
def bprime (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range' 2 (n - 2)).all (fun d => n % d != 0)

/-- pont spec/calcul : bprime decide exactement prime -/
theorem bprime_iff_prime (n : Nat) : bprime n = true ↔ prime n := by
  unfold bprime
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

-- ============================================================
-- 2. Rayons S(m), r(m), lemme de parite (copie N5_kernel sec.2)
-- ============================================================

/-- S(m) : les rayons de m, t in [1, m-2] avec m-t et m+t premiers.
    Liste (sans doublon par construction) : le « Finset » du core. -/
def rays (m : Nat) : List Nat :=
  (List.range' 1 (m - 2)).filter
    (fun t => bprime (m - t) && bprime (m + t))

/-- r(m) = |S(m)| -/
def r (m : Nat) : Nat := (rays m).length

/-- appartenance a S(m), depliee -/
theorem mem_rays {m t : Nat} : t ∈ rays m ↔
    (1 ≤ t ∧ t ≤ m - 2) ∧ bprime (m - t) = true ∧ bprime (m + t) = true := by
  unfold rays
  rw [List.mem_filter, List.mem_range', Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp.1, hp.2⟩
  · rintro ⟨⟨h1, h2⟩, hp1, hp2⟩
    exact ⟨⟨t - 1, by omega, by omega⟩, hp1, hp2⟩

/-- L-PARITE + borne : tout rayon de m (m >= 4) a la parite
    opposee a m et est <= m-3. Coeur de l'integralite des
    demi-ecarts (division par 2 exacte). -/
theorem rays_mem_spec {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ rays m) :
    1 ≤ t ∧ t ≤ m - 3 ∧ t % 2 ≠ m % 2 := by
  obtain ⟨⟨h1, h2⟩, hp1, hp2⟩ := mem_rays.mp ht
  have hpm := (bprime_iff_prime (m - t)).mp hp1
  have hpp := (bprime_iff_prime (m + t)).mp hp2
  -- parite : si t % 2 = m % 2, alors m - t est premier pair = 2,
  -- donc t = m - 2 et m + t = 2m - 2 est pair >= 6 : absurde.
  have hpar : t % 2 ≠ m % 2 := by
    intro hpar
    have hdvd : 2 ∣ m - t := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hpm.2 _ hdvd with h21 | h2mt
    · omega
    · have ht2 : t = m - 2 := by omega
      have hdvd2 : 2 ∣ m + t := ⟨m - 1, by omega⟩
      rcases hpp.2 _ hdvd2 with h1' | h2'
      · omega
      · omega
  -- borne : t <= m-2 ; t = m-2 donnerait meme parite que m.
  have hb : t ≤ m - 3 := by
    rcases Nat.eq_or_lt_of_le h2 with hteq | hlt
    · exfalso
      exact hpar (by omega)
    · omega
  exact ⟨h1, hb, hpar⟩

-- ============================================================
-- 3. Tous les rayons ont meme parite ; la liste est triee
-- ============================================================

/-- uniformite de parite : deux rayons quelconques ont meme parite
    (tous deux opposes a m, et % 2 n'a que deux valeurs) -/
theorem rays_same_parity {m : Nat} (hm : 4 ≤ m) :
    ∀ a ∈ rays m, ∀ b ∈ rays m, a % 2 = b % 2 := by
  intro a ha b hb
  have h1 := (rays_mem_spec hm ha).2.2
  have h2 := (rays_mem_spec hm hb).2.2
  omega

/-- les rayons sont ranges en ordre strictement croissant :
    filter conserve l'ordre de range' -/
theorem rays_sorted (m : Nat) : (rays m).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range'

-- ============================================================
-- 4. Ecarts consecutifs (gaps) et telescopage
-- ============================================================

/-- ecarts consecutifs d'une liste : [(b-a) | (a,b) adjacents] -/
def gaps (l : List Nat) : List Nat :=
  l.zipWith (fun a b => b - a) l.tail

/-- nombre d'ecarts consecutifs = longueur - 1 -/
theorem gaps_length : ∀ l : List Nat, (gaps l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := gaps_length (b :: t)
      have hg : gaps (a :: b :: t) = (b - a) :: gaps (b :: t) := rfl
      rw [hg, List.length_cons, ih]
      simp only [List.length_cons]
      omega

/-- un element de gaps l est un ecart l[i+1] - l[i] -/
theorem mem_gaps {l : List Nat} {x : Nat} (hx : x ∈ gaps l) :
    ∃ i a b : Nat, l[i]? = some a ∧ l[i + 1]? = some b ∧ x = b - a := by
  rw [List.mem_iff_getElem?] at hx
  obtain ⟨i, hi⟩ := hx
  unfold gaps at hi
  rw [List.getElem?_zipWith_eq_some] at hi
  obtain ⟨a, b, ha, hb, hf⟩ := hi
  rw [List.getElem?_tail] at hb
  exact ⟨i, a, b, ha, hb, hf.symm⟩

/-- telescopage : somme des ecarts consecutifs + premier = dernier
    (croissance necessaire pour que les soustractions Nat soient
    les vraies differences) -/
theorem gaps_sum (a : Nat) : ∀ (t : List Nat),
    (a :: t).Pairwise (· ≤ ·) →
    (gaps (a :: t)).sum + a = (a :: t).getLast (List.cons_ne_nil a t) := by
  intro t
  induction t generalizing a with
  | nil => intro _; simp [gaps]
  | cons b u ih =>
      intro hs
      have hbu : (b :: u).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hab : a ≤ b :=
        (List.pairwise_cons.mp hs).1 b List.mem_cons_self
      have hg : gaps (a :: b :: u) = (b - a) :: gaps (b :: u) := rfl
      have hih := ih b hbu
      rw [hg, List.sum_cons, List.getLast_cons (List.cons_ne_nil b u)]
      omega

/-- les ecarts d'elements de meme parite sont pairs :
    c'est la que la division par 2 des ecarts devient exacte -/
theorem gaps_even {l : List Nat} {x : Nat}
    (hp : ∀ a ∈ l, ∀ b ∈ l, a % 2 = b % 2) (hx : x ∈ gaps l) :
    x % 2 = 0 := by
  obtain ⟨i, a, b, ha, hb, rfl⟩ := mem_gaps hx
  have ha2 : a ∈ l := List.mem_iff_getElem?.mpr ⟨i, ha⟩
  have hb2 : b ∈ l := List.mem_iff_getElem?.mpr ⟨i + 1, hb⟩
  have h := hp a ha2 b hb2
  omega

/-- un element de gaps l est l'ecart de deux elements consecutifs ;
    sous croissance stricte, a < b -/
theorem gaps_pair {l : List Nat} (hs : l.Pairwise (· < ·)) {x : Nat}
    (hx : x ∈ gaps l) :
    ∃ a b : Nat, a ∈ l ∧ b ∈ l ∧ a < b ∧ x = b - a := by
  obtain ⟨i, a, b, ha, hb, hxeq⟩ := mem_gaps hx
  obtain ⟨hi1, hbi⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  have hab : l[i]'hi < l[i + 1]'hi1 :=
    List.Pairwise.rel_getElem_of_lt hi hi1 hs (Nat.lt_succ_self i)
  rw [hai, hbi] at hab
  exact ⟨a, b, List.mem_iff_getElem?.mpr ⟨i, ha⟩,
         List.mem_iff_getElem?.mpr ⟨i + 1, hb⟩, hab, hxeq⟩

-- ============================================================
-- 5. Principe des tiroirs sur les ecarts
-- ============================================================

/-- si tous les elements depassent c, la somme depasse length*c -/
theorem list_sum_lb (l : List Nat) (c : Nat) (h : ∀ x ∈ l, c ≤ x) :
    l.length * c ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      rw [List.length_cons, List.sum_cons, Nat.add_one_mul]
      omega

/-- TIROIRS : dans une liste strictement croissante a parite
    constante, >= k elements dans [A,B], il existe deux elements
    consecutifs a < b dont le demi-ecart verifie
    (b-a)/2 <= (B-A)/(2*(k-1)).
    Preuve : sinon chaque demi-ecart >= D+1, donc chaque ecart
    (pair) >= 2*(D+1), et la somme telescopique >= (k-1)*2*(D+1)
    > B-A >= dernier - premier : contradiction. -/
theorem exists_adj_gap (l : List Nat) (hs : l.Pairwise (· < ·))
    (hp : ∀ a ∈ l, ∀ b ∈ l, a % 2 = b % 2)
    {k A B : Nat} (hk : 2 ≤ k) (hkl : k ≤ l.length)
    (hA : ∀ x ∈ l, A ≤ x) (hB : ∀ x ∈ l, x ≤ B) :
    ∃ a b : Nat, a ∈ l ∧ b ∈ l ∧ a < b ∧
      (b - a) / 2 ≤ (B - A) / (2 * (k - 1)) := by
  -- la liste est non vide : >= k >= 2 elements
  have hne : l ≠ [] := by
    rintro rfl
    simp at hkl
    omega
  obtain ⟨a0, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hsort : (a0 :: t).Pairwise (· ≤ ·) :=
    List.Pairwise.imp Nat.le_of_lt hs
  -- telescopage : somme des ecarts = dernier - premier <= B - A
  have hsum : (gaps (a0 :: t)).sum ≤ B - A := by
    have hts := gaps_sum a0 t hsort
    have h1 := hB _ (List.getLast_mem (List.cons_ne_nil a0 t))
    have h2 := hA _ List.mem_cons_self
    omega
  by_cases hEx : ∃ x ∈ gaps (a0 :: t),
      x / 2 ≤ (B - A) / (2 * (k - 1))
  · -- un demi-ecart <= D : c'est le tiroir cherche
    obtain ⟨x, hx, hxD⟩ := hEx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := gaps_pair hs hx
    exact ⟨a, b, ha, hb, hab, hxD⟩
  · -- tous les demi-ecarts > D : la somme explose
    have hEx' : ∀ x ∈ gaps (a0 :: t),
        (B - A) / (2 * (k - 1)) < x / 2 := by
      intro x hx
      have hle : ¬ x / 2 ≤ (B - A) / (2 * (k - 1)) :=
        fun hle => hEx ⟨x, hx, hle⟩
      omega
    exfalso
    have hlb : (gaps (a0 :: t)).length *
        (2 * ((B - A) / (2 * (k - 1)) + 1)) ≤ (gaps (a0 :: t)).sum :=
      list_sum_lb _ _ fun x hx => by
        have hxp := gaps_even hp hx
        have hxD := hEx' x hx
        omega
    have hlen : (gaps (a0 :: t)).length = (a0 :: t).length - 1 :=
      gaps_length _
    have hN : k - 1 ≤ (gaps (a0 :: t)).length := by rw [hlen]; omega
    -- (R-1) * 2*(D+1) >= (k-1) * 2*(D+1) > B - A
    have hbig : B - A <
        (gaps (a0 :: t)).length * (2 * ((B - A) / (2 * (k - 1)) + 1)) := by
      have hc : 0 < 2 * (k - 1) := by omega
      have h1 : B - A <
          (B - A) / (2 * (k - 1)) * (2 * (k - 1)) + 2 * (k - 1) :=
        Nat.lt_div_mul_add (by omega)
      -- (k-1)*(2*(D+1)) = D*(2*(k-1)) + 2*(k-1)
      have h2 : (k - 1) * (2 * ((B - A) / (2 * (k - 1)) + 1)) =
          (B - A) / (2 * (k - 1)) * (2 * (k - 1)) + (2 * (k - 1)) := by
        rw [Nat.mul_left_comm, Nat.mul_comm (k - 1) _,
            ← Nat.mul_left_comm, Nat.add_mul, Nat.one_mul]
      have h3 := Nat.mul_le_mul_right
        (2 * ((B - A) / (2 * (k - 1)) + 1)) hN
      rw [← h2] at h1
      exact Nat.lt_of_lt_of_le h1 h3
    omega

/-- instanciation sur S(m) : les rayons vivent dans [1, m-3] avec
    parite constante, donc un enfant-candidat a distance
    v/2 <= (m-4)/(2*(k-1)) existe des que r(m) >= k -/
theorem rays_gap {m k : Nat} (hm : 4 ≤ m) (hk : 2 ≤ k) (hr : k ≤ r m) :
    ∃ a b : Nat, a ∈ rays m ∧ b ∈ rays m ∧ a < b ∧
      (b - a) / 2 ≤ (m - 4) / (2 * (k - 1)) := by
  obtain ⟨a, b, ha, hb, hab, hg⟩ := exists_adj_gap (rays m)
    (rays_sorted m) (rays_same_parity hm) hk hr
    (fun x hx => (rays_mem_spec hm hx).1)
    (fun x hx => (rays_mem_spec hm hx).2.1)
  exact ⟨a, b, ha, hb, hab, hg⟩

-- ============================================================
-- 6. Enfants, puits, seuil M_cut
-- ============================================================

/-- enfant de m (FALSIFICATION : « n = m-v, v = (b-a)/2 ou
    (a+b)/2 », paire de rayons a < b) -/
def enfant (m n : Nat) : Prop :=
  ∃ a b : Nat, a ∈ rays m ∧ b ∈ rays m ∧ a < b ∧
    (n = m - (b - a) / 2 ∨ n = m - (a + b) / 2)

/-- enfant retenu au seuil k : n < m et r(n) >= k -/
def enfantRetenu (k m n : Nat) : Prop :=
  enfant m n ∧ n < m ∧ k ≤ r n

/-- vital au seuil k : m ∈ V_k = {m : r(m) >= k} -/
def vital (k m : Nat) : Prop := k ≤ r m

/-- puits au seuil k : vital sans enfant retenu -/
def puits (k m : Nat) : Prop :=
  vital k m ∧ ∀ n : Nat, ¬ enfantRetenu k m n

/-- seuil de coupure : M_cut(k,L) = L+1+floor((L-4)/(2k-3)) -/
def Mcut (k L : Nat) : Nat := L + 1 + (L - 4) / (2 * k - 3)

-- ============================================================
-- 7. Le theoreme : aucun puits au-dessus de M_cut
-- ============================================================

/-- TH-DESCENTE-TIROIRS (reduction finie) : pour L >= 4, sous
    l'hypothese « ∀ u > L, r(u) >= k » (k >= 2), tout m vital
    >= M_cut possede un enfant retenu. Justification : le tiroir
    donne deux rayons consecutifs a < b avec v = (b-a)/2 <=
    (m-4)/(2*(k-1)) ; l'enfant n* = m - v verifie n* > L car
    m >= L+1+floor((L-4)/(2k-3)) equivaut a
    (m-L)*2*(k-1) > m-4 >= 2*(k-1)*v - donc r(n*) >= k. -/
theorem descente_tiroirs {k L : Nat} (hk : 2 ≤ k) (hL : 4 ≤ L)
    (hrich : ∀ u : Nat, L < u → k ≤ r u)
    {m : Nat} (hm : Mcut k L ≤ m) (hv : k ≤ r m) :
    ∃ n : Nat, enfantRetenu k m n := by
  -- m >= Mcut >= L+1 >= 5 (omega ne lit pas la division par
  -- un diviseur variable : on reste en deductions terme a terme)
  have hm4 : 4 ≤ m :=
    Nat.le_trans (show 4 ≤ L + 1 by omega)
      (Nat.le_trans (Nat.le_add_right _ _) hm)
  obtain ⟨a, b, ha, hb, hab, hgap⟩ := rays_gap hm4 hk hv
  -- n* = m - (b-a)/2 : enfant car v = (b-a)/2, a < b rayons
  refine ⟨m - (b - a) / 2, ⟨⟨a, b, ha, hb, hab, Or.inl rfl⟩, ?_, ?_⟩⟩
  · -- n* < m : l'ecart pair de deux rayons distincts est >= 2,
    -- donc v >= 1, et v <= b <= m-3 < m
    have hpar : a % 2 = b % 2 := rays_same_parity hm4 a ha b hb
    have hbb : b ≤ m - 3 := (rays_mem_spec hm4 hb).2.1
    omega
  · -- L < n* : le demi-ecart v <= D = (m-4)/(2*(k-1)) est
    -- strictement inferieur a m - L
    have hbig : L < m - (b - a) / 2 := by
      have hc : 0 < 2 * k - 3 := by omega
      have h1 : L - 4 <
          (L - 4) / (2 * k - 3) * (2 * k - 3) + (2 * k - 3) :=
        Nat.lt_div_mul_add hc
      have hw : (L - 4) / (2 * k - 3) + 1 ≤ m - L := by
        -- de m >= Mcut = L+1+q on tire q+1 <= m-L, sans omega sur
        -- la division variable
        have hs : Mcut k L - L ≤ m - L := Nat.sub_le_sub_right hm L
        have heq : Mcut k L - L = (L - 4) / (2 * k - 3) + 1 := by
          unfold Mcut
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]
          omega
        rw [heq] at hs
        exact hs
      -- (m-L)*(2k-3) >= (q+1)*(2k-3) > L-4
      rw [← Nat.add_one_mul] at h1
      have hA : L - 4 < (m - L) * (2 * k - 3) :=
        Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hw)
      -- (m-L)*2*(k-1) = (m-L)*(2k-3) + (m-L) > m-4
      have hB : m - 4 < (m - L) * (2 * (k - 1)) := by
        have h2k : 2 * (k - 1) = 2 * k - 3 + 1 := by omega
        rw [h2k, Nat.mul_add_one]
        omega
      -- donc v <= D = (m-4)/(2*(k-1)) < m - L
      have hD : (m - 4) / (2 * (k - 1)) < m - L :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * (k - 1))).mpr hB
      omega
    exact hrich _ hbig

/-- aucun puits dans V_k ∩ [M_cut, +∞) : c'est l'enonce exact de
    FALSIFICATION sec.1 « fermeture inconditionnelle [M_cut, 10^6]
    par tiroirs » (la borne superieure 10^6 releve du scan, pas du
    theoreme) -/
theorem no_puits_ge_Mcut {k L : Nat} (hk : 2 ≤ k) (hL : 4 ≤ L)
    (hrich : ∀ u : Nat, L < u → k ≤ r u)
    {m : Nat} (hm : Mcut k L ≤ m) :
    ¬ puits k m := by
  rintro ⟨hv, hnone⟩
  obtain ⟨n, hr⟩ := descente_tiroirs hk hL hrich hm hv
  exact hnone n hr

-- Audit (attendu : propext, Classical.choice, Quot.sound)
#print axioms descente_tiroirs
#print axioms no_puits_ge_Mcut

end Descente
