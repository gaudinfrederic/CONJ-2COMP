/-
ThmDense.lean - formalisation noyau-pur de thm:dense (CONJ-2COMP, rev.8)

Couverture locale type Schnirelmann par les Delta-arcs.

Noyau-pur : les pas combinatoires sont prouves dans le noyau.
Les inputs (crible superieur Selberg H_A, second moment H_B,
centre riche L1 via Tchebychev) sont enonces comme hypotheses
explicites - litterature classique absente de mathlib pour
H_A/H_B, entree elementaire pour L1.
-/

import Mathlib

namespace Conj2comp

/-- S(m) = {t >= 1 : m - t et m + t premiers} (rayons). -/
def S (m : Nat) : Finset Nat :=
  (Finset.Icc 1 m).filter fun t => (m - t).Prime ∧ (m + t).Prime

/-- r(m) = |S(m)| (richesse). -/
def rayCount (m : Nat) : Nat := (S m).card

theorem mem_S_le {m t : Nat} (h : t ∈ S m) : t ≤ m := by
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at h
  exact h.1.2

/-- Paires ordonnees de rayons a < b avec b - a >= 2 : l'enfant
Delta descend strictement. Les paires adjacentes (b = a + 1)
donneraient n = m ; elles sont au plus r(m) et absorbees dans
la borne inferieure. -/
def rayPairs (m : Nat) : Finset (Nat × Nat) :=
  ((S m) ×ˢ (S m)).filter fun (a, b) => a + 2 ≤ b

/-- Enfant Delta de la paire (a,b) : n = m - (b-a)/2. -/
def deltaChild (m : Nat) (ab : Nat × Nat) : Nat :=
  m - (ab.2 - ab.1) / 2

/-- C_Delta^-(m) : image des paires de rayons. -/
def deltaChildren (m : Nat) : Finset Nat :=
  (rayPairs m).image (deltaChild m)

/-- w_D(m,n) : nombre de paires engendrant l'enfant n. -/
def wDelta (m n : Nat) : Nat :=
  ((rayPairs m).filter fun ab => deltaChild m ab = n).card

/-- Tout enfant Delta descend strictement : n < m (m >= 1). -/
theorem deltaChild_lt {m : Nat} (_hm : 1 ≤ m) {ab : Nat × Nat}
    (hab : ab ∈ rayPairs m) : deltaChild m ab < m := by
  have hf := Finset.mem_filter.1 hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.1 hf.1
  have hlt : ab.1 + 2 ≤ ab.2 := hf.2
  have hd : 0 < (ab.2 - ab.1) / 2 :=
    Nat.div_pos (by omega) (by norm_num)
  have hbm : ab.2 ≤ m := mem_S_le hb
  have hdm : (ab.2 - ab.1) / 2 ≤ m :=
    le_trans (Nat.div_le_self _ _) (by omega)
  exact Nat.sub_lt_self hd hdm

/-- Les enfants vivent dans range m. -/
theorem deltaChildren_subset_range {m : Nat} (hm : 1 ≤ m) :
    deltaChildren m ⊆ Finset.range m := by
  intro n hn
  obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hn
  exact Finset.mem_range.2 (deltaChild_lt hm hab)

/-- sum_n w(m,n) = |paires| : chaque paire tombe dans exactement
un enfant du support. -/
theorem card_rayPairs_eq_sum_wDelta (m : Nat) :
    (rayPairs m).card = ∑ n ∈ deltaChildren m, wDelta m n := by
  unfold wDelta deltaChildren
  exact Finset.card_eq_sum_card_image (deltaChild m) (rayPairs m)

/-- Comptage des paires : r^2 <= 2*|rayPairs| + 3r.
    2|T| + r = r^2 (symetrie swap sur offDiag) ; les paires
    supprimees (b = a+1) sont au plus r (projection injective
    sur la 1re coordonnee). -/
theorem card_rayPairs_bound {m : Nat} :
    rayCount m * rayCount m
      ≤ 2 * (rayPairs m).card + 3 * rayCount m := by
  set r := rayCount m with hr
  set T := ((S m) ×ˢ (S m)).filter fun (a, b) => a < b
  set T' := ((S m) ×ˢ (S m)).filter fun (a, b) => b < a
  set U := ((S m) ×ˢ (S m)).filter fun (a, b) => a < b ∧ b ≤ a + 1
  -- rayPairs = T \ U
  have hsub : rayPairs m = T \ U := by
    ext ⟨a, b⟩
    simp only [rayPairs, T, U, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      exact ⟨⟨⟨ha, hb⟩, by omega⟩, fun ⟨_, h2⟩ => by omega⟩
    · rintro ⟨⟨⟨ha, hb⟩, hlt⟩, hnot⟩
      refine ⟨⟨ha, hb⟩, ?_⟩
      by_contra hc
      exact hnot ⟨⟨ha, hb⟩, ⟨hlt, by omega⟩⟩
  have hUT : U ⊆ T := by
    intro x hx
    have hf := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨hf.1, hf.2.1⟩
  have hP : (rayPairs m).card = T.card - U.card := by
    rw [hsub]; exact Finset.card_sdiff_of_subset hUT
  have hUleT : U.card ≤ T.card := Finset.card_le_card hUT
  -- symetrie swap : T.image swap = T'
  have himg : T.image Prod.swap = T' := by
    ext ⟨a, b⟩
    constructor
    · intro h
      obtain ⟨⟨x1, x2⟩, hxT, hx⟩ := Finset.mem_image.1 h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hx
      subst h1; subst h2
      obtain ⟨hmem, hxlt⟩ := Finset.mem_filter.1 hxT
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hmem
      exact Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hx2, hx1⟩, hxlt⟩
    · intro h
      obtain ⟨hmem, hlt⟩ := Finset.mem_filter.1 h
      obtain ⟨ha, hb⟩ := Finset.mem_product.1 hmem
      exact Finset.mem_image.2 ⟨⟨b, a⟩,
        Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨hb, ha⟩, hlt⟩, rfl⟩
  have hswap : T.card = T'.card := by
    rw [← himg, Finset.card_image_of_injOn]
    exact fun _ _ _ _ h => Prod.swap_injective h
  -- partition : filter (a /= b) = T ⊔ T'
  have hpart : ((S m) ×ˢ (S m)).filter (fun ab => ab.1 ≠ ab.2) =
      T ∪ T' := by
    ext ⟨a, b⟩
    simp only [T, T', Finset.mem_filter, Finset.mem_product,
      Finset.mem_union, ne_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl (by tauto)
      · exact Or.inr (by tauto)
    · rintro (h | h)
      · exact ⟨h.1, ne_of_lt h.2⟩
      · exact ⟨h.1, ne_of_gt h.2⟩
  have hdisj : Disjoint T T' := by
    rw [Finset.disjoint_left]
    intro ⟨a, b⟩ hab hab2
    have h1 := (Finset.mem_filter.1 hab).2
    have h2 := (Finset.mem_filter.1 hab2).2
    omega
  have hoff2 : T.card + T'.card + r = r * r := by
    have hoff : (T ∪ T').card = r * r - r := by
      rw [← hpart]
      have heq : ((S m) ×ˢ (S m)).filter (fun ab => ab.1 ≠ ab.2)
          = (S m).offDiag := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product,
          Finset.mem_offDiag]
        tauto
      rw [heq]
      show (S m).offDiag.card = (S m).card * (S m).card - (S m).card
      exact Finset.offDiag_card (S m)
    rw [Finset.card_union_of_disjoint hdisj] at hoff
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · simp only [h0] at hoff ⊢; omega
    · rw [hoff]; exact Nat.sub_add_cancel (Nat.le_mul_self _)
  -- |U| <= r : projection injective sur la 1re coordonnee
  have hcardU : U.card ≤ r := by
    refine le_trans (Finset.card_le_card_of_injOn (fun ab => ab.1)
      (fun ab hab => ?_) (fun a ha b hb h => ?_)) le_rfl
    · have hf := Finset.mem_filter.1 (Finset.mem_coe.1 hab)
      exact (Finset.mem_product.1 hf.1).1
    · have hfa := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hfb := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      obtain ⟨hlt1, hle1⟩ := hfa.2
      obtain ⟨hlt2, hle2⟩ := hfb.2
      have hb1 : a.1 = b.1 := h
      have hb2 : a.2 = b.2 := by omega
      exact Prod.ext hb1 hb2
  omega

/-- L2 (noyau-pur) : Cauchy-Schwarz sur le support.
    |paires|^2 <= |C_D| * sum w^2. -/
theorem dense_combinatorial (m : Nat) :
    ((rayPairs m).card : ℝ) ^ 2
      ≤ ((deltaChildren m).card : ℝ) *
          ∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2 := by
  have h2 : ((rayPairs m).card : ℝ)
      = ∑ n ∈ deltaChildren m, (wDelta m n : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast card_rayPairs_eq_sum_wDelta m
  rw [h2]
  exact sq_sum_le_card_mul_sum_sq

/-- Hypothese H_A : borne superieure du crible de Selberg pour
w_D(m,n) - entree litterature explicite. -/
def SieveUpperHypothesis (K : ℝ) (S4 : Nat → Nat → ℝ) : Prop :=
  ∀ m n : Nat, n < m →
    (wDelta m n : ℝ) ≤ K * S4 n m * (m : ℝ) / (Real.log m) ^ 4

/-- Hypothese H_B : borne du second moment de la serie
singuliere S_4 sur n < m. -/
def SecondMomentHypothesis (K_M : ℝ) (S2 : Nat → ℝ)
    (S4 : Nat → Nat → ℝ) : Prop :=
  ∀ m : Nat,
    ∑ n ∈ Finset.range m, (S4 n m) ^ 2
      ≤ K_M * (m : ℝ) * S2 (2 * m) ^ 4

/-- Hypothese L1 : existence d'un centre riche (elementaire via
Tchebychev, enoncee comme entree). -/
def RichCentreHypothesis (c0 X0 : ℝ) : Prop :=
  ∀ X : ℝ, X0 ≤ X → ∃ m : Nat, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * X ∧
    c0 * m / (Real.log m) ^ 2 ≤ (rayCount m : ℝ)

/-- THEOREME : sous les hypotheses explicites, un centre riche m
verifie |C_Delta^-(m)| >= c1 * m avec
c1 = c0^4 / (16 K^2 K_M S_2(2m)^4). -/
theorem dense_coverage
    (S2 : Nat → ℝ) (S4 : Nat → Nat → ℝ)
    (K K_M c0 : ℝ) (hK : 0 < K) (hKM : 0 < K_M) (hc0 : 0 < c0)
    (hS2 : ∀ m, 0 < S2 m) (hS4 : ∀ n m, 0 ≤ S4 n m)
    (hA : SieveUpperHypothesis K S4)
    (hB : SecondMomentHypothesis K_M S2 S4)
    (m : Nat) (hm4 : 4 ≤ m)
    (hRich : c0 * (m : ℝ) / (Real.log m) ^ 2 ≤ rayCount m)
    (hlog : 1 ≤ Real.log m)
    (hr6 : 6 ≤ rayCount m) :
    c0 ^ 4 / (16 * K ^ 2 * K_M * S2 (2 * m) ^ 4) * (m : ℝ)
      ≤ ((deltaChildren m).card : ℝ) := by
  set L := Real.log m with hL
  have hm0 : (0:ℝ) < m := by exact_mod_cast by omega
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hS2p : 0 < S2 (2 * m) := hS2 _
  -- enfants < m
  have hchild : ∀ n ∈ deltaChildren m, n < m := by
    intro n hn
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hn
    exact deltaChild_lt (by omega) hab
  -- borne ponctuelle non negative
  have hbnd : ∀ n ∈ deltaChildren m,
      0 ≤ K * S4 n m * (m : ℝ) / L ^ 4 := fun n _ =>
    div_nonneg
      (mul_nonneg (mul_nonneg hK.le (hS4 n m)) hm0.le)
      (pow_pos hL0 _).le
  -- W <= B
  have hW : (∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2)
      ≤ K ^ 2 * K_M * S2 (2 * m) ^ 4 * (m : ℝ) ^ 3 / L ^ 8 := by
    have h1 : (∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2)
        ≤ ∑ n ∈ deltaChildren m,
          (K * S4 n m * (m : ℝ) / L ^ 4) ^ 2 :=
      Finset.sum_le_sum fun n hn =>
        (sq_le_sq₀ (Nat.cast_nonneg _) (hbnd n hn)).2
          (hA m n (hchild n hn))
    have h2 : (∑ n ∈ deltaChildren m,
          (K * S4 n m * (m : ℝ) / L ^ 4) ^ 2)
        = (K * (m : ℝ) / L ^ 4) ^ 2 *
            ∑ n ∈ deltaChildren m, (S4 n m) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    have h3 : ∑ n ∈ deltaChildren m, (S4 n m) ^ 2
        ≤ ∑ n ∈ Finset.range m, (S4 n m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (deltaChildren_subset_range (by omega))
        fun i _ _ => sq_nonneg _
    have h4 := hB m
    have hpos2 : (0:ℝ) ≤ (K * (m : ℝ) / L ^ 4) ^ 2 := sq_nonneg _
    have e1 : (K * (m : ℝ) / L ^ 4) ^ 2 *
          (K_M * (m : ℝ) * S2 (2 * m) ^ 4)
        = K ^ 2 * K_M * S2 (2 * m) ^ 4 * (m : ℝ) ^ 3 / L ^ 8 := by
      have e0 : (K * (m : ℝ) / L ^ 4) ^ 2
          = K ^ 2 * (m : ℝ) ^ 2 / L ^ 8 := by
        have h2 : (L ^ 4) ^ 2 = L ^ 8 := by ring
        rw [div_pow, h2, mul_pow]
      rw [e0]; field_simp
    calc (∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2)
        ≤ (K * (m : ℝ) / L ^ 4) ^ 2 *
          ∑ n ∈ deltaChildren m, (S4 n m) ^ 2 := h2 ▸ h1
      _ ≤ (K * (m : ℝ) / L ^ 4) ^ 2 *
          ∑ n ∈ Finset.range m, (S4 n m) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 hpos2
      _ ≤ (K * (m : ℝ) / L ^ 4) ^ 2 *
          (K_M * (m : ℝ) * S2 (2 * m) ^ 4) :=
        mul_le_mul_of_nonneg_left h4 hpos2
      _ = _ := e1
  -- P >= r^2/4
  have hP : (rayCount m : ℝ) ^ 2 / 4 ≤ (rayPairs m).card := by
    have hle : (rayCount m : ℝ) * rayCount m
        ≤ 2 * (rayPairs m).card + 3 * rayCount m := by
      exact_mod_cast card_rayPairs_bound (m := m)
    have hr6r : (6:ℝ) ≤ rayCount m := by exact_mod_cast hr6
    nlinarith
  -- Cauchy-Schwarz en reel
  have hCS : ((rayPairs m).card : ℝ) ^ 2
      ≤ (deltaChildren m).card *
          ∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2 :=
    dense_combinatorial m
  -- P > 0
  have hP0 : (0:ℝ) < (rayPairs m).card := by
    have hr6r : (6:ℝ) ≤ rayCount m := by exact_mod_cast hr6
    nlinarith [hP]
  -- W > 0 et C > 0
  have hW0 : (0:ℝ) < ∑ n ∈ deltaChildren m,
      (wDelta m n : ℝ) ^ 2 := by
    by_contra h
    have hle := not_lt.mp h
    have hz : (∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2) = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [hz, mul_zero] at hCS
    nlinarith [hP0]
  have hC0 : (0:ℝ) < (deltaChildren m).card := by
    by_contra h
    have hle := not_lt.mp h
    have hz : ((deltaChildren m).card : ℝ) = 0 :=
      le_antisymm hle (Nat.cast_nonneg _)
    rw [hz, zero_mul] at hCS
    nlinarith [hP0]
  -- B > 0
  have hB0 : (0:ℝ) <
      K ^ 2 * K_M * S2 (2 * m) ^ 4 * (m : ℝ) ^ 3 / L ^ 8 := by
    positivity
  -- borne sur P^2
  have hx0 : (0:ℝ) ≤ c0 ^ 2 * (m : ℝ) ^ 2 / (4 * L ^ 4) := by
    positivity
  have hPge : c0 ^ 2 * (m : ℝ) ^ 2 / (4 * L ^ 4)
      ≤ (rayPairs m).card := by
    have h1b : 0 ≤ c0 * (m : ℝ) / L ^ 2 :=
      div_nonneg (mul_nonneg hc0.le hm0.le) (pow_pos hL0 _).le
    have h1c : (c0 * (m : ℝ) / L ^ 2) ^ 2 ≤ (rayCount m : ℝ) ^ 2 :=
      (sq_le_sq₀ h1b (Nat.cast_nonneg _)).2 hRich
    rw [div_pow] at h1c
    have e1 : (c0 * (m : ℝ)) ^ 2 / (L ^ 2) ^ 2
        = c0 ^ 2 * (m : ℝ) ^ 2 / L ^ 4 := by
      rw [mul_pow]
      have : (L ^ 2) ^ 2 = L ^ 4 := by ring
      rw [this]
    rw [e1] at h1c
    have e2 : c0 ^ 2 * (m : ℝ) ^ 2 / (4 * L ^ 4)
        = (c0 ^ 2 * (m : ℝ) ^ 2 / L ^ 4) / 4 := by
      rw [div_div, mul_comm (L ^ 4) 4]
    rw [e2]; linarith [h1c, hP]
  have h2x : (c0 ^ 2 * (m : ℝ) ^ 2 / (4 * L ^ 4)) ^ 2
      ≤ ((rayPairs m).card : ℝ) ^ 2 :=
    (sq_le_sq₀ hx0 (le_trans hx0 hPge)).2 hPge
  -- assemblage
  have hL4 : (0:ℝ) < 4 * L ^ 4 := by positivity
  calc c0 ^ 4 / (16 * K ^ 2 * K_M * S2 (2 * m) ^ 4) * (m : ℝ)
      = (c0 ^ 2 * (m : ℝ) ^ 2 / (4 * L ^ 4)) ^ 2 /
          (K ^ 2 * K_M * S2 (2 * m) ^ 4 * (m : ℝ) ^ 3 / L ^ 8) := by
        field_simp
        ring
    _ ≤ ((rayPairs m).card : ℝ) ^ 2 /
          (K ^ 2 * K_M * S2 (2 * m) ^ 4 * (m : ℝ) ^ 3 / L ^ 8) :=
      (div_le_div_iff_of_pos_right hB0).2 h2x
    _ ≤ ((rayPairs m).card : ℝ) ^ 2 /
          ∑ n ∈ deltaChildren m, (wDelta m n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hW0 hW
    _ ≤ (deltaChildren m).card :=
      (div_le_iff₀ hW0).2 hCS

-- Audit (attendu : propext, Classical.choice, Quot.sound)
#print axioms dense_combinatorial
#print axioms dense_coverage


/-- Finite power-sum inequality over Nat weights, q >= 1 :
    (sum_x in C w x)^q <= C.card^{q-1} * sum_x in C (w x)^q.
    Wrapper du lemme Mathlib pow_sum_le_card_mul_sum_pow
    (convention exposant n+1 / n ; passage par R car IsStrictOrderedRing
    est requis). Utilise dans le renforcement q-moment de thm:dense. -/
theorem pow_sum_le_card_pow_pred_mul_sum_pow
    (C : Finset Nat) (w : Nat → Nat) (q : Nat) (hq : 1 ≤ q) :
    (∑ x ∈ C, w x) ^ q ≤ C.card ^ (q - 1) * ∑ x ∈ C, w x ^ q := by
  rcases q with _ | n
  · omega
  · rw [Nat.add_sub_cancel]
    have hR : (∑ x ∈ C, (w x : ℝ)) ^ (n + 1)
        ≤ (C.card : ℝ) ^ n * ∑ x ∈ C, (w x : ℝ) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun i _ => Nat.cast_nonneg _) n
    exact_mod_cast hR

end Conj2comp
