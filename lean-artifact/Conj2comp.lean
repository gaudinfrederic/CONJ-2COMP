/-
Conj2comp.lean - artefact Lean du papier CONJ-2COMP
(digraphe de re-appariement sur {m >= 4} ; theoreme de la vanne mod-3).

Source des enonces : CONJ-2COMP-paper.tex
  def:rays  (S(m), r(m), Part(m))        l.161
  def:arc   (arc m -> n, re-pairing)     l.176
  def:extr  (rayon extremal t* = m-3)    l.215
  def:children (forme des enfants)       l.184
  lem:ray3  (classes des rayons mod 3)   l.482
  lem:ray3 (classes des enfants)        l.506
  thm:valve (a)(b)(c)                  l.559
  thm:pgates   (temoins p = 5,7,11,13)      l.615
  permeabilite + fibre auto-alimentee    l.683, l.688

Scope : le noyau inconditionnel du papier (classes de rayons,
vanne mod-3, temoins premiers). Graphe global, donnees et
conjectures hors scope de cet artefact.

Style : pas de native_decide ; decide/norm_num/omega sur
l'arithmetique finie. Les sorries restantes sont documentees
en place et dans STATUS.md.
-/

import Mathlib

namespace Conj2comp

/-! ## Definitions (paper sec. 2) -/

/-- def:rays - S(m) = {t >= 1 : m - t and m + t prime} (the rays of m). -/
def S (m : Nat) : Finset Nat :=
  (Finset.Icc 1 m).filter fun t => (m - t).Prime ∧ (m + t).Prime

/-- def:rays - r(m) = |S(m)|. -/
def rayCount (m : Nat) : Nat := (S m).card

/-- def:rays - Part(m) = {p prime : 2m - p prime, p != m} (the partners). -/
def Part (m : Nat) : Finset Nat :=
  (Finset.Icc 2 (2 * m)).filter fun p => p.Prime ∧ (2 * m - p).Prime ∧ p ≠ m

/-- def:arc - arc m -> n iff exists p < q prime, p + q = 2n,
    {p,q} ⊆ Part(m), m ≠ n. -/
def Arc (m n : Nat) : Prop :=
  m ≠ n ∧ ∃ p q : Nat, p.Prime ∧ q.Prime ∧ p < q ∧ p + q = 2 * n ∧
    p ∈ Part m ∧ q ∈ Part m

/-- def:extr - the extremal ray t*(m) = m - 3. -/
def extRay (m : Nat) : Nat := m - 3

/-! ## Membership lemmas -/

theorem mem_S {m t : Nat} :
    t ∈ S m ↔ 1 ≤ t ∧ (m - t).Prime ∧ (m + t).Prime := by
  simp only [S, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, hp, hq⟩
    have hle : 2 ≤ m - t := hp.two_le
    exact ⟨⟨h1, by omega⟩, hp, hq⟩

theorem mem_Part {m p : Nat} :
    p ∈ Part m ↔ p.Prime ∧ (2 * m - p).Prime ∧ p ≠ m := by
  simp only [Part, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, -⟩, h⟩; exact h
  · rintro ⟨hp, hq, hne⟩
    have h1 : 2 ≤ 2 * m - p := hq.two_le
    have h2 : 2 ≤ p := hp.two_le
    exact ⟨⟨h2, by omega⟩, hp, hq, hne⟩

/-- partners = {m - t, m + t : t ∈ S(m)} (def:rays, second equality). -/
theorem part_iff_ray {m p : Nat} :
    p ∈ Part m ↔ ∃ t ∈ S m, p = m - t ∨ p = m + t := by
  constructor
  · intro hp
    rw [mem_Part] at hp
    obtain ⟨hp1, hp2, hne⟩ := hp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- p < m : t := m - p, then p = m - t and m + t = 2m - p
      refine ⟨m - p, ?_, Or.inl ?_⟩
      · rw [mem_S]
        refine ⟨by omega, ?_, ?_⟩
        · have hsub : m - (m - p) = p := Nat.sub_sub_self hlt.le
          rw [hsub]; exact hp1
        · have hsum : m + (m - p) = 2 * m - p := by omega
          rw [hsum]; exact hp2
      · exact (Nat.sub_sub_self hlt.le).symm
    · -- p > m : t := p - m, then p = m + t and m - t = 2m - p
      refine ⟨p - m, ?_, Or.inr ?_⟩
      · rw [mem_S]
        refine ⟨by omega, ?_, ?_⟩
        · have hsub : m - (p - m) = 2 * m - p := by omega
          rw [hsub]; exact hp2
        · have hsum : m + (p - m) = p := Nat.add_sub_cancel' hgt.le
          rw [hsum]; exact hp1
      · exact (Nat.add_sub_cancel' hgt.le).symm
  · rintro ⟨t, ht, hp⟩
    rw [mem_S] at ht
    obtain ⟨h1, hpt, hps⟩ := ht
    have hle : t ≤ m := by have h2 := hpt.two_le; omega
    rw [mem_Part]
    rcases hp with rfl | rfl
    · have hsub : 2 * m - (m - t) = m + t := by omega
      exact ⟨hpt, by rw [hsub]; exact hps, by omega⟩
    · have hsub : 2 * m - (m + t) = m - t := by omega
      exact ⟨hps, by rw [hsub]; exact hpt, by omega⟩

/-- def:extr - m - 3 ∈ S(m) iff 2m - 3 is prime. -/
theorem mem_S_ext {m : Nat} (hm : 4 ≤ m) :
    m - 3 ∈ S m ↔ (2 * m - 3).Prime := by
  rw [mem_S]
  constructor
  · rintro ⟨-, -, hps⟩
    have hsum : m + (m - 3) = 2 * m - 3 := by omega
    rw [← hsum]; exact hps
  · intro h
    refine ⟨by omega, ?_, ?_⟩
    · have hsub : m - (m - 3) = 3 := by omega
      rw [hsub]; norm_num
    · have hsum : m + (m - 3) = 2 * m - 3 := by omega
      rw [hsum]; exact h

/-! ## def:children(1) - ray bound and parity -/

/-- def:children(1), bound : every ray t ∈ S(m) satisfies t ≤ m - 3
    (m - t = 2 would force the even composite m + t = 2m - 2 >= 6). -/
theorem ray_le_ext {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m) : t ≤ m - 3 := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  by_contra h
  have hmt : m - t = 2 := by have h2 := hpt.two_le; omega
  have hd : 2 ∣ m + t := ⟨m - 1, by omega⟩
  rcases hps.eq_one_or_self_of_dvd 2 hd with h2 | h2 <;> omega

/-- def:children(1), parity : t and m have opposite parity, i.e. m + t odd. -/
theorem ray_parity {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m) : (m + t) % 2 = 1 := by
  have hle := ray_le_ext hm ht
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  have ho : (m - t) % 2 = 1 := by
    rcases hpt.eq_two_or_odd with h | h
    · omega
    · exact h
  omega

/-- two rays of the same m have equal parity (both opposite to m). -/
theorem rays_same_parity {m t1 t2 : Nat} (hm : 4 ≤ m) (h1 : t1 ∈ S m)
    (h2 : t2 ∈ S m) : (t1 + t2) % 2 = 0 := by
  have p1 := ray_parity hm h1
  have p2 := ray_parity hm h2
  omega

/-! ## lem:ray3 - ray classes mod 3 -/

/-- lem:ray3(1) : t ≡ -m (mod 3) is impossible (3 | m + t > 3). -/
theorem ray_mod3_ne_neg {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m) :
    (m + t) % 3 ≠ 0 := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  intro h
  rcases hps.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h) with h3 | h3 <;>
    omega

/-- lem:ray3(2) : t ≡ m (mod 3) forces t = t*(m) = m - 3 (and then
    2m - 3 prime). -/
theorem ray_mod3_eq_ext {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m)
    (h : t % 3 = m % 3) : t = m - 3 ∧ (2 * m - 3).Prime := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  have hle : 2 ≤ m - t := hpt.two_le
  have hd0 : (m - t) % 3 = 0 := by omega
  rcases hpt.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hd0) with h3 | h3
  · omega
  · have ht3 : t = m - 3 := by omega
    have hsum : m + t = 2 * m - 3 := by omega
    exact ⟨ht3, hsum ▸ hps⟩

/-- lem:ray3(3), charged m : a ray is ≡ 0 or is the extremal ray. -/
theorem ray3_charged {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m)
    (hm3 : m % 3 ≠ 0) : t % 3 = 0 ∨ t = m - 3 := by
  have hne := ray_mod3_ne_neg hm ht
  by_cases h : t % 3 = m % 3
  · exact Or.inr (ray_mod3_eq_ext hm ht h).1
  · left; omega

/-- lem:ray3(3), neutral m : no ray is ≡ 0 (and t* fails its own test). -/
theorem ray3_neutral {m t : Nat} (hm : 4 ≤ m) (ht : t ∈ S m)
    (hm3 : m % 3 = 0) : t % 3 ≠ 0 := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  intro h
  have hd : (m - t) % 3 = 0 := by omega
  rcases hpt.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hd) with h3 | h3
  · omega
  · -- m - t = 3, hence m + t = 2m - 3 ≡ 0 mod 3, so m + t = 3 < m
    have h2 : (m + t) % 3 = 0 := by omega
    rcases hps.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h2) with h4 | h4 <;>
      omega

/-- thm:valve(c) degeneration at p = 2 : the boundary ray m - 2 never
    exists (2m - 2 is an even composite). -/
theorem boundary_ray_p2_absent {m : Nat} (hm : 4 ≤ m) : m - 2 ∉ S m := by
  intro h
  rw [mem_S] at h
  obtain ⟨h1, hpt, hps⟩ := h
  have h6 : 6 ≤ m + (m - 2) := by omega
  have hd : 2 ∣ m + (m - 2) := ⟨m - 1, by omega⟩
  rcases hps.eq_one_or_self_of_dvd 2 hd with hh | hh <;> omega

/-! ## def:children(2) - the four children -/

/-- def:children(2) : the arc m -> n holds iff, for some pair
    t1 < t2 in S(m),
    n ∈ {m - (t2-t1)/2, m + (t2-t1)/2, m - (t1+t2)/2, m + (t1+t2)/2}. -/
theorem children_form {m n : Nat} (hm : 4 ≤ m) :
    Arc m n ↔ ∃ t1 t2 : Nat, t1 ∈ S m ∧ t2 ∈ S m ∧ t1 < t2 ∧
      (n = m - (t2 - t1) / 2 ∨ n = m + (t2 - t1) / 2 ∨
       n = m - (t1 + t2) / 2 ∨ n = m + (t1 + t2) / 2) := by
  constructor
  · -- arc -> pair + sign reading
    rintro ⟨hne, p, q, hpp, hqp, hpq, hsum, hpm, hqm⟩
    rw [part_iff_ray] at hpm hqm
    obtain ⟨tp, htp, hpc⟩ := hpm
    obtain ⟨tq, htq, hqc⟩ := hqm
    have htpb := ray_le_ext hm htp
    have htqb := ray_le_ext hm htq
    have htp1 : 1 ≤ tp := (mem_S.mp htp).1
    have htq1 : 1 ≤ tq := (mem_S.mp htq).1
    have hpar := rays_same_parity hm htp htq
    rcases hpc with hp | hp <;> rcases hqc with hq | hq
    · -- p = m - tp, q = m - tq : tq < tp (p < q), child m - (tp+tq)/2
      refine ⟨tq, tp, htq, htp, by omega, Or.inr (Or.inr (Or.inl ?_))⟩
      omega
    · -- p = m - tp, q = m + tq : children m -/+ (tp-tq)/2
      by_cases hcmp : tq < tp
      · refine ⟨tq, tp, htq, htp, hcmp, Or.inl ?_⟩
        omega
      · by_cases hcmp2 : tp < tq
        · refine ⟨tp, tq, htp, htq, hcmp2, Or.inr (Or.inl ?_)⟩
          omega
        · -- tp = tq forces n = m, the excluded self-arc
          exfalso
          have heq : tp = tq := by omega
          subst heq
          omega
    · -- p = m + tp, q = m - tq : impossible (p < q fails)
      exfalso; omega
    · -- p = m + tp, q = m + tq : tp < tq, child m + (tp+tq)/2
      refine ⟨tp, tq, htp, htq, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
      omega
  · -- pair + sign choice -> arc
    rintro ⟨t1, t2, ht1, ht2, hlt, hn⟩
    have hb1 := ray_le_ext hm ht1
    have hb2 := ray_le_ext hm ht2
    have hpar := rays_same_parity hm ht1 ht2
    rw [mem_S] at ht1 ht2
    obtain ⟨h11, hp1, hs1⟩ := ht1
    obtain ⟨h12, hp2, hs2⟩ := ht2
    rcases hn with hn | hn | hn | hn
    · -- n = m - (t2-t1)/2 : p = m - t2, q = m + t1
      refine ⟨by omega, m - t2, m + t1, hp2, hs1, by omega, by omega,
        part_iff_ray.mpr ⟨t2, mem_S.mpr ⟨h12, hp2, hs2⟩, Or.inl rfl⟩,
        part_iff_ray.mpr ⟨t1, mem_S.mpr ⟨h11, hp1, hs1⟩, Or.inr rfl⟩⟩
    · -- n = m + (t2-t1)/2 : p = m - t1, q = m + t2
      refine ⟨by omega, m - t1, m + t2, hp1, hs2, by omega, by omega,
        part_iff_ray.mpr ⟨t1, mem_S.mpr ⟨h11, hp1, hs1⟩, Or.inl rfl⟩,
        part_iff_ray.mpr ⟨t2, mem_S.mpr ⟨h12, hp2, hs2⟩, Or.inr rfl⟩⟩
    · -- n = m - (t1+t2)/2 : p = m - t2, q = m - t1
      refine ⟨by omega, m - t2, m - t1, hp2, hp1, by omega, by omega,
        part_iff_ray.mpr ⟨t2, mem_S.mpr ⟨h12, hp2, hs2⟩, Or.inl rfl⟩,
        part_iff_ray.mpr ⟨t1, mem_S.mpr ⟨h11, hp1, hs1⟩, Or.inl rfl⟩⟩
    · -- n = m + (t1+t2)/2 : p = m + t1, q = m + t2
      refine ⟨by omega, m + t1, m + t2, hs1, hs2, by omega, by omega,
        part_iff_ray.mpr ⟨t1, mem_S.mpr ⟨h11, hp1, hs1⟩, Or.inr rfl⟩,
        part_iff_ray.mpr ⟨t2, mem_S.mpr ⟨h12, hp2, hs2⟩, Or.inr rfl⟩⟩

/-- def:children(1), smallest child : every child of m is >= 4. -/
theorem child_ge_four {m n : Nat} (hm : 4 ≤ m) (h : Arc m n) : 4 ≤ n := by
  rcases (children_form hm).mp h with ⟨t1, t2, ht1, ht2, hlt, hn⟩
  have hb1 := ray_le_ext hm ht1
  have hb2 := ray_le_ext hm ht2
  have hpar := rays_same_parity hm ht1 ht2
  rcases hn with rfl | rfl | rfl | rfl <;> omega

/-! ## lem:ray3 - the mod-3 transition table -/

/-- lem:ray3, charged rows : for a charged parent m ≡ ε ≠ 0 and a pair
    t1 < t2 of rays, a regular pair (t2 non-extremal) gives all four
    children ≡ ε ; the extremal pair {t1, m-3} gives descendants ≡ -ε
    (i.e. child + m ≡ 0) and ascendants ≡ 0. -/
theorem table_charged {m t1 t2 : Nat} (hm : 4 ≤ m) (hm3 : m % 3 ≠ 0)
    (h1 : t1 ∈ S m) (h2 : t2 ∈ S m) (hlt : t1 < t2) :
    -- regular pair : all four children stay in class m % 3
    (t2 ≠ m - 3 →
      (m - (t2 - t1) / 2) % 3 = m % 3 ∧ (m + (t2 - t1) / 2) % 3 = m % 3 ∧
      (m - (t1 + t2) / 2) % 3 = m % 3 ∧ (m + (t1 + t2) / 2) % 3 = m % 3) ∧
    -- extremal pair : descendants flip sign, ascendants are neutral
    (t2 = m - 3 →
      ((m - (t2 - t1) / 2) + m) % 3 = 0 ∧ ((m - (t1 + t2) / 2) + m) % 3 = 0 ∧
      (m + (t2 - t1) / 2) % 3 = 0 ∧ (m + (t1 + t2) / 2) % 3 = 0) := by
  have hb1 := ray_le_ext hm h1
  have hb2 := ray_le_ext hm h2
  have hpar := rays_same_parity hm h1 h2
  have hc1 := ray3_charged hm h1 hm3
  have hc2 := ray3_charged hm h2 hm3
  refine ⟨fun hreg => ?_, fun hext => ?_⟩
  · have ht2 : t2 % 3 = 0 := by
      rcases hc2 with h | h
      · exact h
      · omega
    have ht1 : t1 % 3 = 0 := by
      rcases hc1 with h | h
      · exact h
      · omega
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have ht2 : t2 % 3 = m % 3 := by omega
    have ht1 : t1 % 3 = 0 := by
      rcases hc1 with h | h
      · exact h
      · omega
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- lem:ray3, neutral rows : a neutral parent emits exactly
    {0, -s2} in descent and {0, +s2} in ascent (s2 = class of the
    larger ray). -/
theorem table_neutral {m t1 t2 : Nat} (hm : 4 ≤ m) (hm3 : m % 3 = 0)
    (h1 : t1 ∈ S m) (h2 : t2 ∈ S m) (hlt : t1 < t2) :
    -- descending children : {0, -t2}
    (((m - (t2 - t1) / 2) % 3 = 0 ∧ (m - (t1 + t2) / 2) % 3 = (3 - t2 % 3) % 3) ∨
     ((m - (t2 - t1) / 2) % 3 = (3 - t2 % 3) % 3 ∧ (m - (t1 + t2) / 2) % 3 = 0)) ∧
    -- ascending children : {0, +t2}
    (((m + (t2 - t1) / 2) % 3 = 0 ∧ (m + (t1 + t2) / 2) % 3 = t2 % 3) ∨
     ((m + (t2 - t1) / 2) % 3 = t2 % 3 ∧ (m + (t1 + t2) / 2) % 3 = 0)) := by
  have hb1 := ray_le_ext hm h1
  have hb2 := ray_le_ext hm h2
  have hpar := rays_same_parity hm h1 h2
  have hc1 := ray3_neutral hm h1 hm3
  have hc2 := ray3_neutral hm h2 hm3
  have ht1 : t1 % 3 = 1 ∨ t1 % 3 = 2 := by omega
  have ht2 : t2 % 3 = 1 ∨ t2 % 3 = 2 := by omega
  rcases ht1 with h1' | h1' <;> rcases ht2 with h2' | h2' <;>
    · refine ⟨?_, ?_⟩ <;> omega

/-! ## thm:valve - the mod-3 valve -/

/-- thm:valve(a) - barrier (level-free) : no descending arc goes from
    the charged fibre to the neutral fibre. -/
theorem barrier_a {m n : Nat} (hm : 4 ≤ m) (h : Arc m n) (hm3 : m % 3 ≠ 0)
    (hlt : n < m) : n % 3 ≠ 0 := by
  obtain ⟨hne, p, q, hpp, hqp, hpq, hsum, hpm, hqm⟩ := h
  rw [part_iff_ray] at hpm hqm
  obtain ⟨tp, htp, hpc⟩ := hpm
  obtain ⟨tq, htq, hqc⟩ := hqm
  have htpb := ray_le_ext hm htp
  have htqb := ray_le_ext hm htq
  have htp1 : 1 ≤ tp := (mem_S.mp htp).1
  have htq1 : 1 ≤ tq := (mem_S.mp htq).1
  have hpar := rays_same_parity hm htp htq
  have hc1 := ray3_charged hm htp hm3
  have hc2 := ray3_charged hm htq hm3
  rcases hpc with hp | hp <;> rcases hqc with hq | hq <;> omega

/-- thm:valve(b) - unidirectionality : the only charged -> neutral arcs
    are ascending, emitted exactly by extremal pairs {t, m-3} when
    2m - 3 is prime. -/
theorem barrier_b {m n : Nat} (hm : 4 ≤ m) (h : Arc m n) (hm3 : m % 3 ≠ 0)
    (hn3 : n % 3 = 0) :
    m < n ∧ m - 3 ∈ S m ∧
      ∃ t ∈ S m, t ≠ m - 3 ∧
        (2 * n = (m - t) + (2 * m - 3) ∨ 2 * n = (m + t) + (2 * m - 3)) := by
  obtain ⟨hne, p, q, hpp, hqp, hpq, hsum, hpm, hqm⟩ := h
  rw [part_iff_ray] at hpm hqm
  obtain ⟨tp, htp, hpc⟩ := hpm
  obtain ⟨tq, htq, hqc⟩ := hqm
  have htpb := ray_le_ext hm htp
  have htqb := ray_le_ext hm htq
  have htp1 : 1 ≤ tp := (mem_S.mp htp).1
  have htq1 : 1 ≤ tq := (mem_S.mp htq).1
  have hpar := rays_same_parity hm htp htq
  have hc1 := ray3_charged hm htp hm3
  have hc2 := ray3_charged hm htq hm3
  rcases hpc with hp | hp <;> rcases hqc with hq | hq
  · -- p = m - tp, q = m - tq : n ≡ 0 forces tp = tq = m-3, contra p < q
    exfalso
    have he1 : tp = m - 3 := by
      rcases hc1 with h0 | h0
      · omega
      · exact h0
    have he2 : tq = m - 3 := by
      rcases hc2 with h0 | h0
      · omega
      · exact h0
    omega
  · -- p = m - tp, q = m + tq : n ≡ 0 forces tq = m-3, tp % 3 = 0
    have heq : tq = m - 3 := by
      rcases hc2 with h0 | h0
      · omega
      · exact h0
    have htp0 : tp % 3 = 0 := by
      rcases hc1 with h1 | h1
      · exact h1
      · omega
    have hsub : q = 2 * m - 3 := by omega
    have hext : m - 3 ∈ S m := (mem_S_ext hm).mpr (hsub ▸ hqp)
    refine ⟨by omega, hext, tp, htp, by omega, Or.inl ?_⟩
    omega
  · -- p = m + tp, q = m - tq : impossible
    exfalso; omega
  · -- p = m + tp, q = m + tq : n ≡ 0 forces exactly one of tp,tq = m-3
    have hcase : tp = m - 3 ∨ tq = m - 3 := by
      rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2
      · omega
      · exact Or.inr h2
      · exact Or.inl h1
      · omega
    rcases hcase with he | he
    · have hsub : p = 2 * m - 3 := by omega
      have hext : m - 3 ∈ S m := (mem_S_ext hm).mpr (hsub ▸ hpp)
      have htq0 : tq % 3 = 0 := by
        rcases hc2 with h2 | h2
        · exact h2
        · omega
      have htqne : tq ≠ m - 3 := by omega
      refine ⟨by omega, hext, tq, htq, htqne, Or.inr ?_⟩
      omega
    · have hsub : q = 2 * m - 3 := by omega
      have hext : m - 3 ∈ S m := (mem_S_ext hm).mpr (hsub ▸ hqp)
      have htp0 : tp % 3 = 0 := by
        rcases hc1 with h1 | h1
        · exact h1
        · omega
      have htpne : tp ≠ m - 3 := by omega
      refine ⟨by omega, hext, tp, htp, htpne, Or.inr ?_⟩
      omega

/-! ## thm:valve(c) - uniqueness of the mechanism at p = 3 -/

/-- thm:valve(c), defect class : t ≡ -m (mod p) is impossible for any
    prime modulus p < m (p | m + t would force the prime m + t = p < m). -/
theorem ray_class_neg_forbidden {p m t : Nat} (hp : p.Prime) (hpm : p < m)
    (ht : t ∈ S m) : (m + t) % p ≠ 0 := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  intro h
  rcases hps.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero h) with hh | hh
  · exact hp.ne_one hh
  · omega

/-- thm:valve(c), boundary representative : class t ≡ +m (mod p) hits
    only t = m - p (then m - t = p is the boundary prime). -/
theorem ray_class_boundary {p m t : Nat} (hp : p.Prime) (hpm : p < m)
    (ht : t ∈ S m) (h : p ∣ m - t) : t = m - p := by
  rw [mem_S] at ht
  obtain ⟨h1, hpt, hps⟩ := ht
  have hle : t ≤ m := by have h2 := hpt.two_le; omega
  rcases hpt.eq_one_or_self_of_dvd p h with hh | hh
  · exact absurd hh hp.ne_one
  · omega

/-- classes mod p forbidden to non-extremal rays of a charged m :
    class -m always ; class +m when its boundary representative m - p is
    the extremal defect (i.e. p = 3). Stated on {0,...,p-1}. -/
def forbiddenClasses (p m : Nat) : Finset Nat :=
  {(p - m % p) % p} ∪ (if m - p = m - 3 then {m % p} else ∅)

/-- the two forbidden classes are distinct when m ≢ 0 (p odd). -/
theorem forbidden_classes_ne {p m : Nat} (hp : p.Prime) (hpodd : p ≠ 2)
    (hm0 : m % p ≠ 0) : (p - m % p) % p ≠ m % p := by
  intro h
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : m % p < p := Nat.mod_lt m (by omega)
  have hr : 0 < m % p := Nat.pos_of_ne_zero hm0
  -- (p - r) % p = p - r since 0 < r < p, so h reads p - r = r, i.e. p = 2r
  have hpr : (p - m % p) % p = p - m % p := Nat.mod_eq_of_lt (by omega)
  rw [hpr] at h
  have hd : p = 2 * (m % p) := by omega
  rcases hp.eq_one_or_self_of_dvd 2 ⟨m % p, hd⟩ with hh | hh
  · omega
  · exact hpodd hh.symm

/-- thm:valve(c), the count : for odd prime p and charged m > p, the
    classes a-priori admissible to non-extremal rays number exactly 1 at
    p = 3 (the class 0, the barrier of (a)) and p - 1 >= 4 otherwise, so
    no class obstruction can operate for p >= 5. -/
theorem admissible_card {p m : Nat} (hp : p.Prime) (hpodd : p ≠ 2)
    (hpm : p < m) (hm0 : m % p ≠ 0) :
    ((Finset.range p) \ forbiddenClasses p m).card =
      if p = 3 then 1 else p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsub : forbiddenClasses p m ⊆ Finset.range p := by
    intro x hx
    simp only [forbiddenClasses, Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
    · by_cases hb : m - p = m - 3
      · rw [ite_eq_left hb, Finset.mem_singleton] at hx
        rw [hx]; exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      · rw [ite_eq_right hb] at hx
        simp at hx
  rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hsub]
  by_cases hb : m - p = m - 3
  · have hp3 : p = 3 := by omega
    have hne : (p - m % p) % p ≠ m % p := forbidden_classes_ne hp hpodd hm0
    unfold forbiddenClasses
    rw [ite_eq_left hb, Finset.singleton_union, Finset.card_pair hne]
    rw [ite_eq_left hp3]; omega
  · have hp3 : p ≠ 3 := by omega
    unfold forbiddenClasses
    rw [ite_eq_right hb, Finset.union_empty, Finset.card_singleton]
    rw [ite_eq_right hp3]

/-- thm:valve(c) restated : the a-priori-admissible set is a singleton
    iff p = 3. -/
theorem admissible_singleton_iff {p m : Nat} (hp : p.Prime) (hpodd : p ≠ 2)
    (hpm : p < m) (hm0 : m % p ≠ 0) :
    ((Finset.range p) \ forbiddenClasses p m).card = 1 ↔ p = 3 := by
  have hcard := admissible_card hp hpodd hpm hm0
  have hp2 : 2 ≤ p := hp.two_le
  by_cases h3 : p = 3
  · rw [ite_eq_left h3] at hcard
    exact ⟨fun _ => h3, fun _ => hcard⟩
  · rw [ite_eq_right h3] at hcard
    have hp3 : 3 ≤ p := by omega
    exact ⟨fun h => by omega, fun h => absurd h h3⟩

/-- thm:valve(c), packaged : at p = 3 the non-extremal rays of a
    charged m are confined to the single class 0 ; for odd p ≠ 3 the
    boundary representative m - p is a regular (non-extremal) ray
    candidate, so class +m stays admissible. -/
theorem barrier_c {p m : Nat} (hp : p.Prime) (hpodd : p ≠ 2) (hpm : p < m)
    (hm0 : m % p ≠ 0) :
    -- (i) class -m : unconditionally forbidden to all rays
    (∀ t ∈ S m, (m + t) % p ≠ 0) ∧
    -- (ii) class +m : hits only the boundary representative t = m - p
    (∀ t ∈ S m, t % p = m % p → t = m - p) ∧
    -- (iii) the boundary representative is non-extremal iff p ≠ 3
    (p ≠ 3 → m - p ≠ m - 3) ∧
    -- (iv) at p = 3 non-extremal rays are confined to class 0
    (p = 3 → ∀ t ∈ S m, t ≠ m - 3 → t % p = 0) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hm : 4 ≤ m := by omega
  refine ⟨fun t ht => ray_class_neg_forbidden hp hpm ht, ?_, ?_, ?_⟩
  · intro t ht h
    have hle : t ≤ m := by
      have hge : 2 ≤ m - t := (mem_S.mp ht).2.1.two_le
      omega
    have hdvd : p ∣ m - t := (Nat.modEq_iff_dvd' hle).mp h
    exact ray_class_boundary hp hpm ht hdvd
  · intro _; omega
  · intro h3 t ht hne
    subst h3
    rcases ray3_charged hm ht hm0 with h | h
    · exact h
    · exact absurd h hne

/-- thm:valve(c), p = 2 degeneration : +m ≡ -m (single excluded class),
    the boundary ray m - 2 never exists, and the conclusion fails anyway :
    9 -> 8 is a descending arc with S(9) = {2,4}, from odd to even
    (formalized below as `arc_9_8`). -/
theorem barrier_fails_p2 {m : Nat} (hm : 4 ≤ m) : m - 2 ∉ S m :=
  boundary_ray_p2_absent hm

/-! ## Corollaries of the barrier -/

/-- consequence de thm:valve, impermeability in ascent : an arc between the two charged
    classes (+1 <-> -1) can only descend. -/
theorem cor_perm_asc {m n : Nat} (hm : 4 ≤ m) (h : Arc m n) (hm3 : m % 3 ≠ 0)
    (hn3 : (n + m) % 3 = 0) : n < m := by
  obtain ⟨hne, p, q, hpp, hqp, hpq, hsum, hpm, hqm⟩ := h
  rw [part_iff_ray] at hpm hqm
  obtain ⟨tp, htp, hpc⟩ := hpm
  obtain ⟨tq, htq, hqc⟩ := hqm
  have htpb := ray_le_ext hm htp
  have htqb := ray_le_ext hm htq
  have htp1 : 1 ≤ tp := (mem_S.mp htp).1
  have htq1 : 1 ≤ tq := (mem_S.mp htq).1
  have hpar := rays_same_parity hm htp htq
  have hc1 := ray3_charged hm htp hm3
  have hc2 := ray3_charged hm htq hm3
  rcases hpc with hp | hp <;> rcases hqc with hq | hq <;> omega

/-- consequence de thm:valve, permeability in descent : an extremal pair {t, m-3} (with
    t ≡ 0 another ray) emits two descending children ≡ -m (mod 3). -/
theorem cor_perm_desc {m t : Nat} (hm : 4 ≤ m) (hm3 : m % 3 ≠ 0)
    (ht : t ∈ S m) (ht0 : t % 3 = 0) (hext : m - 3 ∈ S m) :
    Arc m ((m + 3 + t) / 2) ∧ (m + 3 + t) / 2 < m ∧
    (((m + 3 + t) / 2) + m) % 3 = 0 ∧
    Arc m ((m + 3 - t) / 2) ∧ (m + 3 - t) / 2 < m ∧
    (((m + 3 - t) / 2) + m) % 3 = 0 := by
  have htb := ray_le_ext hm ht
  have hpar := ray_parity hm ht
  have heb := ray_le_ext hm hext
  rw [mem_S] at ht hext
  obtain ⟨h1, hpt, hps⟩ := ht
  obtain ⟨he1, hpe, hpe2⟩ := hext
  have hne : t ≠ m - 3 := by
    intro hh; subst hh; omega
  have hlt : t < m - 3 := by omega
  have hgt : 3 < m - t := by omega
  have hpart3 : (3 : Nat) ∈ Part m := by
    rw [part_iff_ray]
    exact ⟨m - 3, mem_S.mpr ⟨he1, hpe, hpe2⟩, Or.inl (by omega)⟩
  have hpartt : m + t ∈ Part m :=
    part_iff_ray.mpr ⟨t, mem_S.mpr ⟨h1, hpt, hps⟩, Or.inr rfl⟩
  have hpartmt : m - t ∈ Part m :=
    part_iff_ray.mpr ⟨t, mem_S.mpr ⟨h1, hpt, hps⟩, Or.inl rfl⟩
  refine ⟨⟨by omega, 3, m + t, by norm_num, hps, by omega, by omega, hpart3,
      hpartt⟩,
    by omega, by omega,
    ⟨by omega, 3, m - t, by norm_num, hpt, hgt, by omega, hpart3, hpartmt⟩,
    by omega, by omega⟩

/-- consequence de thm:valve - the neutral fibre is self-fed : for m ≡ 0 (mod 3), r(m) ≥ 2
    guarantees a descending child ≡ 0 (exactly one per pair). -/
theorem cor_self {m : Nat} (hm : 4 ≤ m) (hm3 : m % 3 = 0) (hr : 2 ≤ rayCount m) :
    ∃ n, Arc m n ∧ n < m ∧ n % 3 = 0 := by
  have aux : ∀ t1 t2 : Nat, t1 ∈ S m → t2 ∈ S m → t1 < t2 →
      ∃ n, Arc m n ∧ n < m ∧ n % 3 = 0 := by
    intro a b ha hb hlt
    have hc1 := ray3_neutral hm ha hm3
    have hc2 := ray3_neutral hm hb hm3
    have hb1 := ray_le_ext hm ha
    have hb2 := ray_le_ext hm hb
    have hpar := rays_same_parity hm ha hb
    have hpa' : m - a ∈ Part m := part_iff_ray.mpr ⟨a, ha, Or.inl rfl⟩
    have hpb' : m - b ∈ Part m := part_iff_ray.mpr ⟨b, hb, Or.inl rfl⟩
    have hsa' : m + a ∈ Part m := part_iff_ray.mpr ⟨a, ha, Or.inr rfl⟩
    rw [mem_S] at ha hb
    obtain ⟨ha1, hpa, hsa⟩ := ha
    obtain ⟨hb1, hpb, hsb⟩ := hb
    by_cases hs : a % 3 = b % 3
    · -- s1 = s2 : v_d ≡ 0, child n = m - (b-a)/2 via {m-b, m+a}
      refine ⟨m - (b - a) / 2,
        ⟨by omega, m - b, m + a, hpb, hsa, by omega, by omega, hpb', hsa'⟩,
        by omega, by omega⟩
    · -- s1 = -s2 : v_s ≡ 0, child n = m - (a+b)/2 via {m-b, m-a}
      refine ⟨m - (a + b) / 2,
        ⟨by omega, m - b, m - a, hpb, hpa, by omega, by omega, hpb', hpa'⟩,
        by omega, by omega⟩
  have hcard : 1 < (S m).card := hr
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hab⟩
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact aux a b ha hb hlt
  · exact aux b a hb ha hgt

/-! ## Witnesses (thm:pgates) and the p = 2 counterexample -/

theorem S9_eq : S 9 = {2, 4} := by decide
theorem S11_eq : S 11 = {6, 8} := by decide
theorem S15_eq : S 15 = {2, 4, 8} := by decide
theorem S14_eq : S 14 = {3, 9} := by decide

/-- counterexample at p = 2 : 9 -> 8 descending, odd to even. -/
theorem arc_9_8 : Arc 9 8 := by
  refine ⟨by norm_num, 5, 11, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, ?_⟩ <;> decide

/-- thm:pgates, p = 5 : arc 11 -> 10, 11 ≡ 1, 10 ≡ 0 (mod 5). -/
theorem wit_p5 : Arc 11 10 ∧ 10 < 11 ∧ 11 % 5 ≠ 0 ∧ 10 % 5 = 0 := by
  refine ⟨⟨by norm_num, 3, 17, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩, by norm_num, by norm_num, by norm_num⟩ <;> decide

/-- thm:pgates, p = 7 : arc 15 -> 14, 15 ≡ 1, 14 ≡ 0 (mod 7). -/
theorem wit_p7 : Arc 15 14 ∧ 14 < 15 ∧ 15 % 7 ≠ 0 ∧ 14 % 7 = 0 := by
  refine ⟨⟨by norm_num, 11, 17, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩, by norm_num, by norm_num, by norm_num⟩ <;> decide

/-- thm:pgates, p = 11 : arc 14 -> 11, 14 ≡ 3, 11 ≡ 0 (mod 11). -/
theorem wit_p11 : Arc 14 11 ∧ 11 < 14 ∧ 14 % 11 ≠ 0 ∧ 11 % 11 = 0 := by
  refine ⟨⟨by norm_num, 5, 17, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩, by norm_num, by norm_num, by norm_num⟩ <;> decide

/-- thm:pgates, p = 13 : arc 15 -> 13, 15 ≡ 2, 13 ≡ 0 (mod 13). -/
theorem wit_p13 : Arc 15 13 ∧ 13 < 15 ∧ 15 % 13 ≠ 0 ∧ 13 % 13 = 0 := by
  refine ⟨⟨by norm_num, 7, 19, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩, by norm_num, by norm_num, by norm_num⟩ <;> decide

/-- thm:pgates / thm:valve(c) conclusion : for every p ∈ {5,7,11,13} a
    descending arc non-0 -> 0 mod p exists (finite verification). -/
theorem wit_desc_arcs :
    (∃ m n, Arc m n ∧ n < m ∧ m % 5 ≠ 0 ∧ n % 5 = 0) ∧
    (∃ m n, Arc m n ∧ n < m ∧ m % 7 ≠ 0 ∧ n % 7 = 0) ∧
    (∃ m n, Arc m n ∧ n < m ∧ m % 11 ≠ 0 ∧ n % 11 = 0) ∧
    (∃ m n, Arc m n ∧ n < m ∧ m % 13 ≠ 0 ∧ n % 13 = 0) :=
  ⟨⟨11, 10, wit_p5.1, wit_p5.2.1, wit_p5.2.2.1, wit_p5.2.2.2⟩,
   ⟨15, 14, wit_p7.1, wit_p7.2.1, wit_p7.2.2.1, wit_p7.2.2.2⟩,
   ⟨14, 11, wit_p11.1, wit_p11.2.1, wit_p11.2.2.1, wit_p11.2.2.2⟩,
   ⟨15, 13, wit_p13.1, wit_p13.2.1, wit_p13.2.2.1, wit_p13.2.2.2⟩⟩

/-- arc 9 -> 8 again through children_form : pair {2,4} of S(9) emits the
    descending child 9 - (4-2)/2 = 8. -/
theorem arc_9_8_children :
    ∃ t1 t2 : Nat, t1 ∈ S 9 ∧ t2 ∈ S 9 ∧ t1 < t2 ∧
      8 = 9 - (t2 - t1) / 2 :=
  ⟨2, 4, by decide, by decide, by norm_num, by norm_num⟩

end Conj2comp

#print axioms Conj2comp.barrier_a
#print axioms Conj2comp.barrier_b
#print axioms Conj2comp.barrier_c
