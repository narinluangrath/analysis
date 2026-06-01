import Mathlib.Tactic
import Mathlib.Algebra.Field.Power

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  induction N, hN using Int.le_induction with
  | base =>
    show example_7_2_4.partial 1 = _
    unfold Series.partial
    rw [Finset.Icc_self, Finset.sum_singleton]
    rw [Series.eval_mk' _ (le_refl 1)]
    norm_num
  | succ N hN ih =>
    have hm : example_7_2_4.m = 1 := rfl
    rw [Series.partial_succ example_7_2_4 (by rw [hm]; omega), ih,
      Series.eval_mk' _ (by omega : N + 1 ≥ 1)]
    have e : (2:ℝ)^(-(N+1)) = 2^(-N) * 2⁻¹ := by
      rw [show -(N+1) = -N + (-1:ℤ) by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      norm_num
    rw [e]; ring

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  have hg : Filter.Tendsto (fun N:ℤ => (2:ℝ)^(-N)) Filter.atTop (nhds 0) := by
    have hnat := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    have htn : Filter.Tendsto Int.toNat Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun b => ⟨(b:ℤ), fun a ha => by omega⟩)
    apply (hnat.comp htn).congr'
    filter_upwards [Filter.eventually_ge_atTop (0:ℤ)] with N hN
    simp only [Function.comp]
    rw [one_div, inv_pow, zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg hN]
  have hlim : Filter.Tendsto (fun N:ℤ => 1 - (2:ℝ)^(-N)) Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop)).sub hg
    simpa using this
  show Filter.Tendsto example_7_2_4.partial Filter.atTop (nhds 1)
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (1:ℤ)] with N hN
  exact (example_7_2_4a hN).symm

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := sum_of_converges example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  induction N, hN using Int.le_induction with
  | base =>
    show example_7_2_4'.partial 1 = _
    unfold Series.partial
    rw [Finset.Icc_self, Finset.sum_singleton, Series.eval_mk' _ (le_refl 1)]
    norm_num
  | succ N hN ih =>
    have hm : example_7_2_4'.m = 1 := rfl
    rw [Series.partial_succ example_7_2_4' (by rw [hm]; omega), ih,
      Series.eval_mk' _ (by omega : N + 1 ≥ 1)]
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) (N+1) 1]; ring

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  have hsum : ∀ p:ℤ, s.m ≤ p → ∀ q:ℤ, p-1 ≤ q →
      ∑ n ∈ Finset.Icc p q, s.seq n = s.partial q - s.partial (p-1) := by
    intro p hp q hq
    induction q, hq using Int.le_induction with
    | base => rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_self]
    | succ q hq ih =>
      rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : p ≤ q+1),
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
        Series.partial_succ s (by omega)]
      ring
  constructor
  · intro hconv ε hε
    have hcs : CauchySeq s.partial := (convergesTo_sum hconv).cauchySeq
    rw [Metric.cauchySeq_iff] at hcs
    obtain ⟨N0, hN0⟩ := hcs ε hε
    refine ⟨max (N0+1) s.m, le_max_right _ _, fun p hp q hq => ?_⟩
    rcases le_or_gt p q with hpq | hpq
    · rw [hsum p (le_trans (le_max_right _ _) hp) q (by omega), abs_sub_comm, ← Real.dist_eq]
      exact le_of_lt (hN0 (p-1) (by omega) q (by omega))
    · rw [Finset.Icc_eq_empty (by omega : ¬ p ≤ q), Finset.sum_empty, abs_zero]
      exact le_of_lt hε
  · intro htail
    have hcs : CauchySeq s.partial := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN, hcond⟩ := htail (ε/2) (by linarith)
      refine ⟨max N s.m, fun a ha b hb => ?_⟩
      have hma : s.m ≤ a := le_trans (le_max_right _ _) ha
      have hmb : s.m ≤ b := le_trans (le_max_right _ _) hb
      have hNa : N ≤ a := le_trans (le_max_left _ _) ha
      have hNb : N ≤ b := le_trans (le_max_left _ _) hb
      rw [Real.dist_eq]
      rcases le_total a b with hab | hab
      · have he : s.partial a - s.partial b = -(∑ n ∈ Finset.Icc (a+1) b, s.seq n) := by
          have h1 : ((a+1)-1:ℤ) = a := by omega
          rw [hsum (a+1) (by omega) b (by omega), h1]; ring
        rw [he, abs_neg]
        exact lt_of_le_of_lt (hcond (a+1) (by omega) b (by omega)) (by linarith)
      · have he : s.partial a - s.partial b = ∑ n ∈ Finset.Icc (b+1) a, s.seq n := by
          have h1 : ((b+1)-1:ℤ) = b := by omega
          rw [hsum (b+1) (by omega) a (by omega), h1]
        rw [he]
        exact lt_of_le_of_lt (hcond (b+1) (by omega) a (by omega)) (by linarith)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨L, hL⟩

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  obtain ⟨L, hL⟩ := h
  have h2 : Filter.Tendsto (fun n:ℤ => s.partial (n-1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-1) Filter.tendsto_id)
  have key : Filter.Tendsto (fun n:ℤ => s.partial n - s.partial (n-1)) Filter.atTop (nhds 0) := by
    have := hL.sub h2; rwa [sub_self] at this
  apply key.congr'
  filter_upwards [Filter.eventually_ge_atTop s.m] with n hn
  have hps := Series.partial_succ s (N := n-1) (by linarith)
  rw [sub_add_cancel] at hps
  linarith

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  intro hc
  exact h (decay_of_converges hc)

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  apply diverges_of_nodecay
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have hk := hN (max N 1) (le_max_left _ _)
  rw [Series.eval_mk' _ (by omega : max N 1 ≥ 1), Real.dist_eq, sub_zero,
    abs_of_pos (by positivity)] at hk
  have h2 : (1:ℝ) ≤ (2:ℝ)^(max N 1) := one_le_zpow₀ (by norm_num) (by omega)
  linarith

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have := hN (max N 0) (le_max_left _ _)
  rw [show (max N 0:ℤ) = (((max N 0).toNat:ℕ):ℤ) by omega] at this
  simp only [Series.eval_coe, Real.dist_eq, sub_zero] at this
  norm_num at this

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have := hN (max N 0) (le_max_left _ _)
  rw [show (max N 0:ℤ) = (((max N 0).toNat:ℕ):ℤ) by omega] at this
  simp only [Series.eval_coe, Real.dist_eq, sub_zero, abs_pow] at this
  norm_num at this

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Splitting a partial sum across a cut point `a ≤ b` (both `≥ s.m`). -/
theorem Series.partial_split {s:Series} {a:ℤ} (hma: s.m ≤ a) :
    ∀ b:ℤ, a ≤ b → s.partial b = s.partial a + ∑ k ∈ Finset.Icc (a+1) b, s.seq k := by
  intro b hab
  induction b, hab using Int.le_induction with
  | base => simp [Finset.Icc_eq_empty (by omega : ¬ a+1 ≤ a)]
  | succ b hb ih =>
    rw [Series.partial_succ s (by omega), ih,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega : a+1 ≤ b+1),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    ring

/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  have habsm : s.abs.m = s.m := rfl
  have habsseq : ∀ n:ℤ, n ≥ s.m → s.abs.seq n = |s.seq n| := fun n hn =>
    Series.eval_mk' (fun k ↦ |s.seq (k:ℤ)|) hn
  have hord : ∀ a b:ℤ, s.m ≤ a → a ≤ b →
      |s.partial b - s.partial a| ≤ s.abs.partial b - s.abs.partial a := by
    intro a b hma hab
    rw [Series.partial_split hma b hab, Series.partial_split (s := s.abs) (by rw [habsm]; exact hma) b hab]
    simp only [add_sub_cancel_left]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro k hk; simp only [Finset.mem_Icc] at hk
    exact (habsseq k (by omega)).symm
  obtain ⟨A, hA⟩ := h
  have hcs : CauchySeq s.partial := by
    have hcabs : CauchySeq s.abs.partial := hA.cauchySeq
    rw [Metric.cauchySeq_iff] at hcabs ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcabs ε hε
    refine ⟨max N s.m, fun a ha b hb => ?_⟩
    have hma : s.m ≤ a := le_trans (le_max_right _ _) ha
    have hmb : s.m ≤ b := le_trans (le_max_right _ _) hb
    have hNa : N ≤ a := le_trans (le_max_left _ _) ha
    have hNb : N ≤ b := le_trans (le_max_left _ _) hb
    rw [Real.dist_eq]
    rcases le_total a b with hab | hab
    · calc |s.partial a - s.partial b| = |s.partial b - s.partial a| := abs_sub_comm _ _
        _ ≤ s.abs.partial b - s.abs.partial a := hord a b hma hab
        _ ≤ |s.abs.partial b - s.abs.partial a| := le_abs_self _
        _ = |s.abs.partial a - s.abs.partial b| := abs_sub_comm _ _
        _ = dist (s.abs.partial a) (s.abs.partial b) := (Real.dist_eq _ _).symm
        _ < ε := hN a hNa b hNb
    · calc |s.partial a - s.partial b| ≤ s.abs.partial a - s.abs.partial b := hord b a hmb hab
        _ ≤ |s.abs.partial a - s.abs.partial b| := le_abs_self _
        _ = dist (s.abs.partial a) (s.abs.partial b) := (Real.dist_eq _ _).symm
        _ < ε := hN a hNa b hNb
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  exact ⟨L, hL⟩

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hs : s.convergesTo s.sum := convergesTo_sum (converges_of_absConverges h)
  have habs : s.abs.convergesTo s.abs.sum := convergesTo_sum h
  have hpt : ∀ N:ℤ, |s.partial N| ≤ s.abs.partial N := by
    intro N
    have heq : s.abs.partial N = ∑ k ∈ Finset.Icc s.m N, |s.seq k| := by
      unfold Series.partial
      rw [show s.abs.m = s.m from rfl]
      apply Finset.sum_congr rfl
      intro k hk; simp only [Finset.mem_Icc] at hk
      exact Series.eval_mk' (fun j ↦ |s.seq (j:ℤ)|) hk.1
    rw [heq]
    exact Finset.abs_sum_le_sum_abs _ _
  exact le_of_tendsto_of_tendsto' hs.abs habs hpt

/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction k with
    | zero => simp
    | succ k ih =>
      have heven : Even (N + 2*(k:ℤ)) := h'.add (even_two_mul _)
      calc S (N+2*(↑(k+1):ℤ)) = S ((N+2*(k:ℤ))+2) := by congr 1; push_cast; ring
        _ ≤ S (N+2*(k:ℤ)) := claim3 (by omega) heven
        _ ≤ S N := ih
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    have heven : Even (N + 2*(k:ℤ)) := h'.add (even_two_mul _)
    have hodd : Odd (N + 2*(k:ℤ) + 1) := heven.add_one
    have hc0 := claim0 (N := N + 2*(k:ℤ)) (by omega)
    rw [show N+2*(k:ℤ)+1 = (N+2*(k:ℤ))+1 by ring, hc0, hodd.neg_one_zpow]
    have hpos := ha ⟨ N + 2*(k:ℤ) + 1, by grind ⟩
    nlinarith [hpos]
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, add_zero]
      have hodd : Odd (N+1) := h'.add_one
      rw [claim0 hN, hodd.neg_one_zpow]; linarith
    | succ k ih =>
      have hodd : Odd (N + 2*(k:ℤ) + 1) := (h'.add (even_two_mul _)).add_one
      calc S (N+2*(↑(k+1):ℤ)+1) = S ((N+2*(k:ℤ)+1)+2) := by congr 1; push_cast; ring
        _ ≥ S (N+2*(k:ℤ)+1) := claim2 (by omega) hodd
        _ ≥ S N - a ⟨ N+1, by grind ⟩ := ih
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    obtain ⟨j, hj⟩ : ∃ j:ℕ, n = N + j := ⟨(n-N).toNat, by omega⟩
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hn2 : n = N + 2*(k:ℤ) := by rw [hj, hk]; push_cast; ring
      rw [hn2]
      obtain ⟨c1, c2, c3⟩ := claim4 hN h' k
      exact ⟨le_trans c1 c2, c3⟩
    · have hn2 : n = N + 2*(k:ℤ) + 1 := by rw [hj, hk]; push_cast; ring
      rw [hn2]
      obtain ⟨c1, c2, c3⟩ := claim4 hN h' k
      exact ⟨c1, le_trans c2 c3⟩
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    haveI : Nonempty {n:ℤ // n ≥ m} := ⟨⟨m, le_refl m⟩⟩
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N0, hN0⟩ := h ε hε
    set B : ℤ := max (max N0.val m) 0 with hB
    have hEeven : Even (2*B) := even_two_mul B
    have hEm : 2*B ≥ m := by omega
    have haE : a ⟨2*B+1, by omega⟩ ≤ ε := by
      have hidx : N0 ≤ (⟨2*B+1, by omega⟩ : {n//n≥m}) := by show N0.val ≤ 2*B+1; omega
      have hd := hN0 _ hidx
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha _)] at hd
      linarith
    refine ⟨2*B, ?_⟩
    intro n hn m2 hm2
    obtain ⟨l1, r1⟩ := why4 hEm hEeven hn
    obtain ⟨l2, r2⟩ := why4 hEm hEeven hm2
    rw [_root_.abs_le]
    constructor
    · linarith
    · linarith
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  sorry

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry

theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  have key : ∀ N, (s+t).partial N = s.partial N + t.partial N := by
    intro N
    show ∑ n ∈ Finset.Icc (min s.m t.m) N, (s.seq n + t.seq n) = s.partial N + t.partial N
    rw [Finset.sum_add_distrib]
    congr 1
    · symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_left _ _))
      intro n hn hn'; simp only [Finset.mem_Icc] at hn hn'; exact s.vanish n (by omega)
    · symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_right _ _))
      intro n hn hn'; simp only [Finset.mem_Icc] at hn hn'; exact t.vanish n (by omega)
  have hpe : (s+t).partial = fun N => s.partial N + t.partial N := funext key
  show Filter.Tendsto (s+t).partial Filter.atTop (nhds (L+M))
  rw [hpe]
  exact Filter.Tendsto.add hs ht

theorem Series.convergesTo.sum_eq {s:Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  have hc : s.converges := ⟨L, h⟩
  unfold Series.sum
  rw [dif_pos hc]
  exact tendsto_nhds_unique hc.choose_spec h

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by
  obtain ⟨L, hL⟩ := hs
  obtain ⟨M, hM⟩ := ht
  have hadd : (s+t).convergesTo (L+M) := hL.add hM
  exact ⟨⟨L+M, hadd⟩, by rw [hadd.sum_eq, hL.sum_eq, hM.sum_eq]⟩

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  have hpe : (c • s).partial = fun N => c * s.partial N := by
    funext N
    show ∑ n ∈ Finset.Icc s.m N, (if n ≥ s.m then c * s.seq n else 0) = c * s.partial N
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn; simp only [Finset.mem_Icc] at hn; rw [if_pos hn.1]
  show Filter.Tendsto (c • s).partial Filter.atTop (nhds (c * L))
  rw [hpe]
  exact Filter.Tendsto.const_mul c hs

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by
  obtain ⟨L, hL⟩ := hs
  have hsm : (c • s).convergesTo (c * L) := hL.smul
  exact ⟨⟨c*L, hsm⟩, by rw [hsm.sum_eq, hL.sum_eq]⟩

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  have key : ∀ N, (s-t).partial N = s.partial N - t.partial N := by
    intro N
    show ∑ n ∈ Finset.Icc (min s.m t.m) N, (s.seq n - t.seq n) = s.partial N - t.partial N
    rw [Finset.sum_sub_distrib]
    congr 1
    · symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_left _ _))
      intro n hn hn'; simp only [Finset.mem_Icc] at hn hn'; exact s.vanish n (by omega)
    · symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_right _ _))
      intro n hn hn'; simp only [Finset.mem_Icc] at hn hn'; exact t.vanish n (by omega)
  have hpe : (s-t).partial = fun N => s.partial N - t.partial N := funext key
  show Filter.Tendsto (s-t).partial Filter.atTop (nhds (L-M))
  rw [hpe]
  exact Filter.Tendsto.sub hs ht

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by
  obtain ⟨L, hL⟩ := hs
  obtain ⟨M, hM⟩ := ht
  have hsub : (s-t).convergesTo (L-M) := hL.sub hM
  exact ⟨⟨L-M, hsub⟩, by rw [hsub.sum_eq, hL.sum_eq, hM.sum_eq]⟩

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

theorem Series.partial_from (s:Series) (k:ℕ) {N:ℤ} (hN: N ≥ s.m + k - 1) :
    (s.from (s.m+k)).partial N = s.partial N - ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n := by
  have htm : (s.from (s.m+↑k)).m = s.m + ↑k := by show max s.m (s.m+↑k) = s.m+↑k; omega
  induction N, hN using Int.le_induction with
  | base =>
    have e1 : (s.from (s.m+↑k)).partial (s.m+↑k-1) = 0 := by
      unfold Series.partial; rw [htm, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    rw [e1]; symm; rw [sub_eq_zero]
    show ∑ n ∈ Finset.Icc s.m (s.m+↑k-1), s.seq n = ∑ n ∈ Finset.Ico s.m (s.m+↑k), s.seq n
    rw [Finset.Icc_sub_one_right_eq_Ico]
  | succ N hN ih =>
    rw [Series.partial_succ (s.from (s.m+↑k)) (by rw [htm]; omega), ih]
    have hsq : (s.from (s.m+↑k)).seq (N+1) = s.seq (N+1) :=
      Series.eval_mk' (fun n ↦ s.seq (n:ℤ)) (by omega : N+1 ≥ max s.m (s.m+↑k))
    rw [hsq, Series.partial_succ s (by omega)]
    ring

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - ∑ n ∈ Finset.Ico s.m (s.m+↑k), s.seq n, ?_⟩
    apply (hL.sub_const _).congr'
    filter_upwards [Filter.eventually_ge_atTop (s.m+↑k-1)] with N hN
    exact (Series.partial_from s k hN).symm
  · rintro ⟨L, hL⟩
    refine ⟨L + ∑ n ∈ Finset.Ico s.m (s.m+↑k), s.seq n, ?_⟩
    apply (hL.add_const _).congr'
    filter_upwards [Filter.eventually_ge_atTop (s.m+↑k-1)] with N hN
    have h := Series.partial_from s k hN
    show (s.from (s.m+↑k)).partial N + (∑ n ∈ Finset.Ico s.m (s.m+↑k), s.seq n) = s.partial N
    rw [h]; ring

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  obtain ⟨L, hL⟩ := h
  have hfrom : (s.from (s.m+↑k)).convergesTo
      (L - ∑ n ∈ Finset.Ico s.m (s.m+↑k), s.seq n) := by
    apply (hL.sub_const _).congr'
    filter_upwards [Filter.eventually_ge_atTop (s.m+↑k-1)] with N hN
    exact (Series.partial_from s k hN).symm
  rw [hL.sum_eq, hfrom.sum_eq]; ring

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  set t := mk' (m := s.m + L) (fun n ↦ s.seq (n - L)) with ht_def
  have htm : t.m = s.m + L := rfl
  have hpe : ∀ M:ℤ, M ≥ s.m + L - 1 → t.partial M = s.partial (M - L) := by
    intro M hM
    induction M, hM using Int.le_induction with
    | base =>
      unfold Series.partial
      rw [htm, Finset.Icc_eq_empty (by omega), Finset.sum_empty,
        Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    | succ M hM ih =>
      rw [Series.partial_succ t (by rw [htm]; omega), ih, show M+1-L = (M-L)+1 by ring,
        Series.partial_succ s (by omega)]
      congr 1
      rw [ht_def, Series.eval_mk' _ (show M+1 ≥ s.m+L by omega)]
      congr 1; push_cast; ring
  show Filter.Tendsto t.partial Filter.atTop (nhds x)
  have hg : Filter.Tendsto (fun M:ℤ => M - L) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-L) Filter.tendsto_id
  have hcomp := h.comp hg
  apply hcomp.congr'
  filter_upwards [Filter.eventually_ge_atTop (s.m+L-1)] with M hM
  exact (hpe M hM).symm

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  set g : ℕ → ℝ := fun n ↦ a n - a (n+1) with hg_def
  have hm : (g:Series).m = 0 := rfl
  have hpe : ∀ N:ℤ, N ≥ 0 → (g:Series).partial N = a 0 - a (N.toNat + 1) := by
    intro N hN
    induction N, hN using Int.le_induction with
    | base =>
      have h0 : (g:Series).seq 0 = g 0 := Series.eval_coe g 0
      unfold Series.partial
      rw [hm, Finset.Icc_self, Finset.sum_singleton, h0]
      simp [hg_def]
    | succ N hN ih =>
      rw [Series.partial_succ (g:Series) (by rw [hm]; omega), ih]
      have hk : (N + 1 : ℤ) = ((N.toNat + 1 : ℕ):ℤ) := by omega
      have hseq : (g:Series).seq (N+1) = g (N.toNat + 1) := by
        rw [hk, Series.eval_coe]
      rw [hseq, show (N+1).toNat = N.toNat + 1 by omega]
      simp only [hg_def]; ring
  show Filter.Tendsto (g:Series).partial Filter.atTop (nhds (a 0))
  have hidx : Filter.Tendsto (fun N:ℤ => N.toNat + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨(b:ℤ), fun n hn => by omega⟩)
  have hlim : Filter.Tendsto (fun N:ℤ => a 0 - a (N.toNat + 1)) Filter.atTop (nhds (a 0)) := by
    have := (tendsto_const_nhds (x := a 0) (f := Filter.atTop)).sub (ha.comp hidx)
    simpa using this
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (0:ℤ)] with N hN
  exact (hpe N hN).symm

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  sorry


end Chapter7
