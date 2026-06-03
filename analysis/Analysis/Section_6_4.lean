import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    constructor
    · intro h ε hε N hN
      obtain ⟨n, hn, hclose⟩ := h ε hε N hN
      have hnN : n ≥ N := le_trans (le_max_right _ _) hn
      refine ⟨n, hnN, ?_⟩
      rwa [Sequence.from_eval a hnN, Real.Close, Real.dist_eq] at hclose
    · intro h ε hε N hN
      obtain ⟨n, hnN, hbound⟩ := h ε hε N hN
      refine ⟨n, max_le (le_trans hN hnN) hnN, ?_⟩
      rw [Sequence.from_eval a hnN, Real.Close, Real.dist_eq]
      exact hbound

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

private theorem E3_eval {n:ℤ} (hn: 0 ≤ n) :
    Example_6_4_3 n = 1 - (10:ℝ)^(-(n.toNat:ℤ)-1) := by
  simp only [Example_6_4_3, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn]

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  refine ⟨0, le_refl _, ?_⟩
  rw [Real.Close, Real.dist_eq, E3_eval (le_refl 0)]
  norm_num

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  intro h
  obtain ⟨n, hn, hclose⟩ := h 1 (by norm_num)
  rw [show (Example_6_4_3.from 1).m = max Example_6_4_3.m 1 from rfl] at hn
  have hn1 : (1:ℤ) ≤ n := le_trans (le_max_right _ _) hn
  rw [Sequence.from_eval Example_6_4_3 hn1, Real.Close, Real.dist_eq,
    E3_eval (by omega)] at hclose
  have hpow : (10:ℝ)^(-(n.toNat:ℤ)-1) ≤ (10:ℝ)^(-2:ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num); omega
  rw [abs_le] at hclose
  have h001 : (10:ℝ)^(-2:ℤ) = 0.01 := by norm_num
  rw [h001] at hpow
  linarith [hclose.2, hpow]

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN
  have hN0 : (0:ℤ) ≤ N := hN
  refine ⟨N, (max_eq_right hN).le, ?_⟩
  rw [Sequence.from_eval Example_6_4_3 (le_refl N), Real.Close, Real.dist_eq, E3_eval hN0]
  rw [show (1:ℝ) - 10^(-(N.toNat:ℤ)-1) - 1 = -(10^(-(N.toNat:ℤ)-1)) by ring, abs_neg,
    abs_of_pos (by positivity), show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  apply zpow_le_zpow_right₀ (by norm_num); omega

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/10 < 1)
  refine ⟨max N (k:ℤ), le_max_left _ _, ?_⟩
  set n := max N (k:ℤ)
  have hn0 : (0:ℤ) ≤ n := le_trans hN (le_max_left _ _)
  rw [E3_eval hn0, show (1:ℝ) - 10^(-(n.toNat:ℤ)-1) - 1 = -(10^(-(n.toNat:ℤ)-1)) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have hbound : (10:ℝ)^(-(n.toNat:ℤ)-1) ≤ (1/10:ℝ)^n.toNat := by
    have e : (1/10:ℝ)^n.toNat = (10:ℝ)^(-(n.toNat:ℤ)) := by
      rw [div_pow, one_pow, one_div, ← zpow_natCast, ← zpow_neg]
    rw [e]; apply zpow_le_zpow_right₀ (by norm_num); omega
  have hmono : (1/10:ℝ)^n.toNat ≤ (1/10:ℝ)^k := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    have : (k:ℤ) ≤ n := le_max_right _ _
    omega
  linarith [hbound, hmono, hk]

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

private theorem E4_eval {n:ℤ} (hn: 0 ≤ n) :
    Example_6_4_4 n = (-1:ℝ)^n.toNat * (1 + (10:ℝ)^(-(n.toNat:ℤ)-1)) := by
  simp only [Example_6_4_4, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn]

/-- For any `ε > 0`, the tail `10^(-m-1)` is eventually below `ε`. -/
private theorem tail_le {ε:ℝ} (hε: 0 < ε) : ∃ k:ℕ, ∀ m:ℕ, k ≤ m → (10:ℝ)^(-(m:ℤ)-1) ≤ ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/10 < 1)
  refine ⟨k, fun m hm => ?_⟩
  have hbound : (10:ℝ)^(-(m:ℤ)-1) ≤ (1/10:ℝ)^m := by
    have e : (1/10:ℝ)^m = (10:ℝ)^(-(m:ℤ)) := by
      rw [div_pow, one_pow, one_div, ← zpow_natCast, ← zpow_neg]
    rw [e]; apply zpow_le_zpow_right₀ (by norm_num); omega
  have hmono : (1/10:ℝ)^m ≤ (1/10:ℝ)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  linarith

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  refine ⟨0, le_refl _, ?_⟩
  rw [Real.Close, Real.dist_eq, E4_eval (le_refl 0)]
  norm_num

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  intro N hN
  have hN0 : (0:ℤ) ≤ N := hN
  refine ⟨2*N, ?_, ?_⟩
  · rw [show (Example_6_4_4.from N).m = max Example_6_4_4.m N from rfl, max_eq_right hN0]; omega
  · have h2N : (0:ℤ) ≤ 2*N := by omega
    rw [Sequence.from_eval Example_6_4_4 (by omega : 2*N ≥ N), Real.Close, Real.dist_eq, E4_eval h2N]
    have heven : Even (2*N).toNat := ⟨N.toNat, by omega⟩
    rw [Even.neg_one_pow heven, one_mul,
      show (1:ℝ) + 10^(-((2*N).toNat:ℤ)-1) - 1 = 10^(-((2*N).toNat:ℤ)-1) by ring,
      abs_of_pos (by positivity), show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
    apply zpow_le_zpow_right₀ (by norm_num); omega

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hNt : (N.toNat:ℤ) = N := Int.toNat_of_nonneg hN
  obtain ⟨k, hk⟩ := tail_le hε
  set n := 2 * (max N.toNat k : ℤ) with hndef
  have hn0 : 0 ≤ n := by positivity
  refine ⟨n, by omega, ?_⟩
  rw [E4_eval hn0]
  have heven : Even n.toNat := ⟨max N.toNat k, by omega⟩
  rw [Even.neg_one_pow heven, one_mul,
    show (1:ℝ) + 10^(-(n.toNat:ℤ)-1) - 1 = 10^(-(n.toNat:ℤ)-1) by ring, abs_of_pos (by positivity)]
  apply hk; omega

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hNt : (N.toNat:ℤ) = N := Int.toNat_of_nonneg hN
  obtain ⟨k, hk⟩ := tail_le hε
  set n := 2 * (max N.toNat k : ℤ) + 1 with hndef
  have hn0 : 0 ≤ n := by positivity
  have hodd : Odd n.toNat := ⟨max N.toNat k, by omega⟩
  refine ⟨n, by omega, ?_⟩
  have hval : Example_6_4_4 n - (-1) = -(10^(-(n.toNat:ℤ)-1)) := by
    rw [E4_eval hn0, Odd.neg_one_pow hodd]; ring
  rw [hval, abs_neg, abs_of_pos (by positivity)]
  apply hk; omega

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def]; push_neg
  refine ⟨0.5, by norm_num, 0, le_refl _, fun n hn => ?_⟩
  rw [sub_zero, E4_eval hn]
  have ht : (0:ℝ) < 10^(-(n.toNat:ℤ)-1) := by positivity
  rcases Nat.even_or_odd n.toNat with he | ho
  · rw [Even.neg_one_pow he, one_mul, abs_of_pos (by linarith)]; linarith
  · rw [Odd.neg_one_pow ho, neg_one_mul, abs_neg, abs_of_pos (by linarith)]; linarith

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [limit_point_def]
  intro ε hε N hN
  rw [Sequence.tendsTo_iff] at h
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨max N M, le_max_left _ _, hM (max N M) (le_max_right _ _)⟩

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

private theorem tail_unbounded_above {a:Sequence} (hnb: ¬a.BddAbove) {N:ℤ} (hN: N ≥ a.m) (M:ℝ) :
    ∃ n ≥ N, a n > M := by
  obtain ⟨K, hK⟩ : ∃ K:ℝ, ∀ n ∈ Finset.Ico a.m N, a n ≤ K := by
    rcases (Finset.Ico a.m N).eq_empty_or_nonempty with he | hne
    · exact ⟨0, fun n hn => by simp [he] at hn⟩
    · obtain ⟨n0, _, hmax⟩ := (Finset.Ico a.m N).exists_max_image a hne
      exact ⟨a n0, fun n hn => hmax n hn⟩
  simp only [Sequence.BddAbove, Sequence.BddAboveBy, not_exists, not_forall, not_le] at hnb
  obtain ⟨n, hnm, hgt⟩ := hnb (max M K)
  refine ⟨n, ?_, lt_of_le_of_lt (le_max_left _ _) hgt⟩
  by_contra hlt; push_neg at hlt
  exact absurd (le_trans (hK n (Finset.mem_Ico.mpr ⟨hnm, hlt⟩)) (le_max_right _ _)) (not_le.mpr hgt)

private theorem tail_unbounded_below {a:Sequence} (hnb: ¬a.BddBelow) {N:ℤ} (hN: N ≥ a.m) (M:ℝ) :
    ∃ n ≥ N, a n < M := by
  obtain ⟨K, hK⟩ : ∃ K:ℝ, ∀ n ∈ Finset.Ico a.m N, K ≤ a n := by
    rcases (Finset.Ico a.m N).eq_empty_or_nonempty with he | hne
    · exact ⟨0, fun n hn => by simp [he] at hn⟩
    · obtain ⟨n0, _, hmin⟩ := (Finset.Ico a.m N).exists_min_image a hne
      exact ⟨a n0, fun n hn => hmin n hn⟩
  simp only [Sequence.BddBelow, Sequence.BddBelowBy, not_exists, not_forall, not_le, ge_iff_le] at hnb
  obtain ⟨n, hnm, hlt⟩ := hnb (min M K)
  refine ⟨n, ?_, lt_of_lt_of_le hlt (min_le_left _ _)⟩
  by_contra hN'; push_neg at hN'
  exact absurd (le_trans (min_le_right _ _) (hK n (Finset.mem_Ico.mpr ⟨hnm, hN'⟩))) (not_le.mpr hlt)

/-- If `a` is unbounded above, every tail has supremum `⊤`. -/
private theorem tail_sup_top {a:Sequence} (hnb: ¬a.BddAbove) {N:ℤ} (hN: N ≥ a.m) :
    (a.from N).sup = ⊤ := by
  unfold Sequence.sup
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
  · obtain ⟨n, hn, hgt⟩ := tail_unbounded_above hnb hN y
    exact ⟨((a n:ℝ):EReal), ⟨n, max_le (le_trans hN hn) hn, by rw [Sequence.from_eval a hn]⟩,
      by exact_mod_cast hgt⟩
  · exact absurd hb (lt_irrefl _)
  · obtain ⟨n, hn, _⟩ := tail_unbounded_above hnb hN 0
    exact ⟨((a n:ℝ):EReal), ⟨n, max_le (le_trans hN hn) hn, by rw [Sequence.from_eval a hn]⟩,
      bot_lt_coe _⟩

/-- If `a` is unbounded below, every tail has infimum `⊥`. -/
private theorem tail_inf_bot {a:Sequence} (hnb: ¬a.BddBelow) {N:ℤ} (hN: N ≥ a.m) :
    (a.from N).inf = ⊥ := by
  unfold Sequence.inf
  apply sInf_eq_bot.mpr
  intro b hb
  obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
  · obtain ⟨n, hn, hlt⟩ := tail_unbounded_below hnb hN y
    exact ⟨((a n:ℝ):EReal), ⟨n, max_le (le_trans hN hn) hn, by rw [Sequence.from_eval a hn]⟩,
      by exact_mod_cast hlt⟩
  · obtain ⟨n, hn, _⟩ := tail_unbounded_below hnb hN 0
    exact ⟨((a n:ℝ):EReal), ⟨n, max_le (le_trans hN hn) hn, by rw [Sequence.from_eval a hn]⟩,
      coe_lt_top _⟩
  · exact absurd hb (lt_irrefl _)

private theorem limsup_top_of_not_bddAbove {a:Sequence} (hnb: ¬a.BddAbove) : a.limsup = ⊤ := by
  unfold Sequence.limsup
  apply sInf_eq_top.mpr
  rintro x ⟨N, hN, rfl⟩
  exact tail_sup_top hnb hN

private theorem liminf_bot_of_not_bddBelow {a:Sequence} (hnb: ¬a.BddBelow) : a.liminf = ⊥ := by
  unfold Sequence.liminf
  apply sSup_eq_bot.mpr
  rintro x ⟨N, hN, rfl⟩
  exact tail_inf_bot hnb hN

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

example (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  sorry

example : Example_6_4_7.limsup = 1 := by sorry

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example : Example_6_4_7.liminf = -1 := by sorry

example : Example_6_4_7.sup = (1.1:ℝ) := by sorry

example : Example_6_4_7.inf = (-1.01:ℝ) := by sorry

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

private theorem E8_not_bddAbove : ¬ Example_6_4_8.BddAbove := by
  rintro ⟨M, hM⟩
  obtain ⟨j, hj⟩ := exists_nat_gt M
  have hev := hM (2*j : ℤ) (by positivity)
  simp only [Example_6_4_8, Sequence.instCoeFun, Sequence.ofNatFun] at hev
  rw [if_pos (by positivity), show ((2*(j:ℤ)).toNat) = 2*j by omega, if_pos (even_two_mul j)] at hev
  push_cast at hev; linarith

private theorem E8_not_bddBelow : ¬ Example_6_4_8.BddBelow := by
  rintro ⟨M, hM⟩
  obtain ⟨j, hj⟩ := exists_nat_gt (-M)
  have hev := hM (2*j+1 : ℤ) (by positivity)
  simp only [Example_6_4_8, Sequence.instCoeFun, Sequence.ofNatFun] at hev
  rw [if_pos (by positivity), show ((2*(j:ℤ)+1).toNat) = 2*j+1 by omega,
    if_neg (by simp [Nat.even_add_one, parity_simps])] at hev
  push_cast at hev; linarith

example (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := tail_sup_top E8_not_bddAbove (by positivity)

example : Example_6_4_8.limsup = ⊤ := limsup_top_of_not_bddAbove E8_not_bddAbove

example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := tail_inf_bot E8_not_bddBelow (by positivity)

example : Example_6_4_8.liminf = ⊥ := liminf_bot_of_not_bddBelow E8_not_bddBelow

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else -(n+2:ℝ)⁻¹ := by sorry

example : Example_6_4_9.limsup = 0 := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by sorry

example : Example_6_4_9.liminf = 0 := by sorry

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

private theorem E10_not_bddAbove : ¬ Example_6_4_10.BddAbove := by
  rintro ⟨M, hM⟩
  obtain ⟨j, hj⟩ := exists_nat_gt M
  have hev := hM (j : ℤ) (by positivity)
  simp only [Example_6_4_10, Sequence.instCoeFun, Sequence.ofNatFun] at hev
  rw [if_pos (by positivity), show ((j:ℤ).toNat) = j by omega] at hev
  push_cast at hev; linarith

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := tail_sup_top E10_not_bddAbove (by positivity)

example : Example_6_4_9.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = n+1 := by sorry

example : Example_6_4_9.liminf = ⊤ := by sorry

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp only [limsup, sInf_lt_iff] at h
  obtain ⟨y, hy, ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy
  rw [hNy] at ha; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp only [liminf, lt_sSup_iff] at h
  obtain ⟨z, hz, ha⟩ := h
  obtain ⟨N, hN, hNz⟩ := hz
  rw [hNz] at ha; use N
  simp [hN, lowerseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_lt_of_le ha ((a.from N).ge_inf hn') using 1
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx : a.lowerseq N < x := by apply lt_of_le_of_lt (le_sSup _) h; simp; use N
  choose n hn hxn _ using exists_between_gt_inf hx
  grind

/-- The value set of `a.from a.m` is the same as that of `a`. -/
private theorem from_self_value_set (a:Sequence) :
    {x:EReal | ∃ n ≥ (a.from a.m).m, x = (a.from a.m) n} = {x:EReal | ∃ n ≥ a.m, x = a n} := by
  have hm : (a.from a.m).m = a.m := by show max a.m a.m = a.m; omega
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [hm] at hn
    exact ⟨n, hn, by rw [Sequence.from_eval a hn]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by rw [hm]; exact hn, by rw [Sequence.from_eval a hn]⟩

private theorem from_self_inf (a:Sequence) : (a.from a.m).inf = a.inf := by
  unfold Sequence.inf; rw [from_self_value_set]

private theorem from_self_sup (a:Sequence) : (a.from a.m).sup = a.sup := by
  unfold Sequence.sup; rw [from_self_value_set]

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  apply le_sSup
  exact ⟨a.m, le_refl _, (from_self_inf a).symm⟩

/-- The value set of a later tail is contained in that of an earlier tail. -/
private theorem from_tail_subset {a:Sequence} {N K:ℤ} (hN: a.m ≤ N) (hNK: N ≤ K) :
    {x:EReal | ∃ n ≥ (a.from K).m, x = (a.from K) n}
    ⊆ {x:EReal | ∃ n ≥ (a.from N).m, x = (a.from N) n} := by
  have hmK : (a.from K).m = K := by show max a.m K = K; omega
  have hmN : (a.from N).m = N := by show max a.m N = N; omega
  rintro x ⟨n, hn, rfl⟩
  rw [hmK] at hn
  refine ⟨n, by rw [hmN]; omega, ?_⟩
  rw [Sequence.from_eval a (show n ≥ K by omega), Sequence.from_eval a (show n ≥ N by omega)]

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  apply sSup_le
  rintro l ⟨N, hN, rfl⟩
  apply le_sInf
  rintro u ⟨M, hM, rfl⟩
  show (a.from N).inf ≤ (a.from M).sup
  set K := max N M with hK
  have hNK : N ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have hmid : (a.from K).inf ≤ (a.from K).sup := by
    have hmem : ((a.from K) ((a.from K).m) : EReal)
        ∈ {x:EReal | ∃ n ≥ (a.from K).m, x = (a.from K) n} := ⟨(a.from K).m, le_refl _, rfl⟩
    exact le_trans (sInf_le hmem) (le_sSup hmem)
  calc (a.from N).inf ≤ (a.from K).inf := sInf_le_sInf (from_tail_subset hN hNK)
    _ ≤ (a.from K).sup := hmid
    _ ≤ (a.from M).sup := sSup_le_sSup (from_tail_subset hM hMK)

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  apply sInf_le
  exact ⟨a.m, le_refl _, (from_self_sup a).symm⟩

private lemma ereal_lt_coe_exists_real {L:EReal} {c:ℝ} (h: L < (c:EReal)) :
    ∃ d:ℝ, L < (d:EReal) ∧ d < c := by
  obtain ⟨z, hz1, hz2⟩ := exists_between h
  have hzt : z ≠ ⊤ := ne_top_of_lt hz2
  have hzb : z ≠ ⊥ := by rintro rfl; exact not_lt_bot hz1
  exact ⟨z.toReal, by rwa [EReal.coe_toReal hzt hzb],
    by rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hzt hzb]; exact hz2⟩

private lemma ereal_coe_lt_exists_real {L:EReal} {c:ℝ} (h: (c:EReal) < L) :
    ∃ d:ℝ, c < d ∧ (d:EReal) < L := by
  obtain ⟨z, hz1, hz2⟩ := exists_between h
  have hzt : z ≠ ⊤ := by rintro rfl; exact not_top_lt hz2
  have hzb : z ≠ ⊥ := ne_bot_of_gt hz1
  exact ⟨z.toReal, by rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hzt hzb]; exact hz1,
    by rwa [EReal.coe_toReal hzt hzb]⟩

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  refine ⟨?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨d, hcd, hdL⟩ := ereal_coe_lt_exists_real hcon
    obtain ⟨N, hN, hbnd⟩ := a.lt_liminf_bounds hdL
    rw [Sequence.limit_point_def] at h
    obtain ⟨n, hn, hclose⟩ := h (d - c) (by linarith) N hN
    have hgt := hbnd n hn
    rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hgt
    rw [abs_le] at hclose
    linarith [hclose.2]
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨d, hLd, hdc⟩ := ereal_lt_coe_exists_real hcon
    obtain ⟨N, hN, hbnd⟩ := a.gt_limsup_bounds hLd
    rw [Sequence.limit_point_def] at h
    obtain ⟨n, hn, hclose⟩ := h (c - d) (by linarith) N hN
    have hlt := hbnd n hn
    rw [EReal.coe_lt_coe_iff] at hlt
    rw [abs_le] at hclose
    linarith [hclose.1]

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hup : (↑(L_plus + ε):EReal) > a.limsup := by
    rw [h]; exact_mod_cast show L_plus < L_plus + ε by linarith
  obtain ⟨N', hN', hbU⟩ := a.gt_limsup_bounds hup
  have hlow : (↑(L_plus - ε):EReal) < a.limsup := by
    rw [h]; exact_mod_cast show L_plus - ε < L_plus by linarith
  obtain ⟨n, hn, hbL⟩ := a.lt_limsup_bounds hlow (N := max N N') (le_trans hN (le_max_left _ _))
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hUn := hbU n (le_trans (le_max_right _ _) hn)
  rw [EReal.coe_lt_coe_iff] at hUn
  rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hbL
  rw [abs_le]; constructor <;> linarith

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hlow : (↑(L_minus - ε):EReal) < a.liminf := by
    rw [h]; exact_mod_cast show L_minus - ε < L_minus by linarith
  obtain ⟨N', hN', hbL⟩ := a.lt_liminf_bounds hlow
  have hup : (↑(L_minus + ε):EReal) > a.liminf := by
    rw [h]; exact_mod_cast show L_minus < L_minus + ε by linarith
  obtain ⟨n, hn, hbU⟩ := a.gt_liminf_bounds hup (N := max N N') (le_trans hN (le_max_left _ _))
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hLn := hbL n (le_trans (le_max_right _ _) hn)
  rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hLn
  rw [EReal.coe_lt_coe_iff] at hbU
  rw [abs_le]; constructor <;> linarith

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · intro hconv
    have hlp : a.LimitPoint c := Sequence.limit_point_of_limit hconv
    obtain ⟨hli, hls⟩ := Sequence.limit_point_between_liminf_limsup hlp
    rw [Sequence.tendsTo_iff] at hconv
    have hls2 : a.limsup ≤ (c:EReal) := by
      by_contra hcon; rw [not_le] at hcon
      obtain ⟨d, hcd, hdL⟩ := ereal_coe_lt_exists_real hcon
      obtain ⟨Nc, hNc⟩ := hconv ((d-c)/2) (by linarith)
      obtain ⟨n, hn, hgt⟩ := a.lt_limsup_bounds hdL (N := max Nc a.m) (le_max_right _ _)
      have hUn := hNc n (le_trans (le_max_left _ _) hn)
      rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hgt
      rw [abs_le] at hUn; linarith [hUn.2]
    have hli2 : (c:EReal) ≤ a.liminf := by
      by_contra hcon; rw [not_le] at hcon
      obtain ⟨d, hLd, hdc⟩ := ereal_lt_coe_exists_real hcon
      obtain ⟨Nc, hNc⟩ := hconv ((c-d)/2) (by linarith)
      obtain ⟨n, hn, hlt⟩ := a.gt_liminf_bounds hLd (N := max Nc a.m) (le_max_right _ _)
      have hLn := hNc n (le_trans (le_max_left _ _) hn)
      rw [EReal.coe_lt_coe_iff] at hlt
      rw [abs_le] at hLn; linarith [hLn.1]
    exact ⟨le_antisymm hli hli2, le_antisymm hls2 hls⟩
  · rintro ⟨hli, hls⟩
    rw [Sequence.tendsTo_iff]
    intro ε hε
    have hup : (↑(c + ε):EReal) > a.limsup := by
      rw [hls]; exact_mod_cast show c < c + ε by linarith
    obtain ⟨N1, hN1, hbU⟩ := a.gt_limsup_bounds hup
    have hlow : (↑(c - ε):EReal) < a.liminf := by
      rw [hli]; exact_mod_cast show c - ε < c by linarith
    obtain ⟨N2, hN2, hbL⟩ := a.lt_liminf_bounds hlow
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hUn := hbU n (le_trans (le_max_left _ _) hn)
    have hLn := hbL n (le_trans (le_max_right _ _) hn)
    rw [EReal.coe_lt_coe_iff] at hUn
    rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hLn
    rw [abs_le]; constructor <;> linarith

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  calc (↑(a n):EReal) ≤ ↑(b n) := by exact_mod_cast hab n hn
    _ ≤ b.sup := b.le_sup (hm ▸ hn)

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
  apply le_sInf
  rintro x ⟨n, hn, rfl⟩
  have hn' : n ≥ a.m := hm ▸ hn
  calc a.inf ≤ (↑(a n):EReal) := a.ge_inf hn'
    _ ≤ ↑(b n) := by exact_mod_cast hab n hn'

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  apply le_sInf
  rintro x ⟨N, hN, rfl⟩
  have hN' : N ≥ a.m := hm ▸ hN
  calc a.limsup ≤ a.upperseq N := sInf_le ⟨N, hN', rfl⟩
    _ ≤ b.upperseq N := by
        apply Sequence.sup_mono (by show max a.m N = max b.m N; rw [hm])
        intro n hn
        have hnN : n ≥ N := le_trans (le_max_right a.m N) hn
        rw [Sequence.from_eval a hnN, Sequence.from_eval b hnN]
        exact hab n (le_trans (le_max_left a.m N) hn)

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
  apply sSup_le
  rintro x ⟨N, hN, rfl⟩
  have hN' : N ≥ b.m := hm ▸ hN
  calc a.lowerseq N ≤ b.lowerseq N := by
        apply Sequence.inf_mono (by show max a.m N = max b.m N; rw [hm])
        intro n hn
        have hnN : n ≥ N := le_trans (le_max_right a.m N) hn
        rw [Sequence.from_eval a hnN, Sequence.from_eval b hnN]
        exact hab n (le_trans (le_max_left a.m N) hn)
    _ ≤ b.liminf := le_sSup ⟨N, hN', rfl⟩

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rw [Sequence.tendsTo_iff] at ha hb
  obtain ⟨Na, hA⟩ := ha ε hε
  obtain ⟨Nc, hC⟩ := hb ε hε
  refine ⟨max (max Na Nc) a.m, fun n hn => ?_⟩
  have hna : n ≥ Na := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : n ≥ Nc := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnm : n ≥ a.m := le_trans (le_max_right _ _) hn
  have h1 := hA n hna
  have h2 := hC n hnc
  obtain ⟨hab1, hab2⟩ := hab n hnm
  rw [abs_le] at h1 h2 ⊢
  exact ⟨by linarith [h1.1], by linarith [h2.2]⟩

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2/ε)
  refine ⟨(N:ℤ), fun n hn => ?_⟩
  have hn0 : (0:ℤ) ≤ n := le_trans (Int.natCast_nonneg N) hn
  simp only [Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn0, sub_zero, abs_of_pos (by positivity)]
  have hle : (N:ℤ) ≤ (n.toNat:ℤ) := by rw [Int.toNat_of_nonneg hn0]; exact hn
  have hNn : (N:ℝ) ≤ (n.toNat:ℝ) := by exact_mod_cast hle
  have hNe : (2:ℝ) < N * ε := (div_lt_iff₀ hε).mp hN
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hNe, hNn, hε]

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2/ε)
  refine ⟨(N:ℤ), fun n hn => ?_⟩
  have hn0 : (0:ℤ) ≤ n := le_trans (Int.natCast_nonneg N) hn
  simp only [Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn0, sub_zero,
    show (-2:ℝ)/((n.toNat:ℝ)+1) = -(2/((n.toNat:ℝ)+1)) by ring, abs_neg, abs_of_pos (by positivity)]
  have hle : (N:ℤ) ≤ (n.toNat:ℤ) := by rw [Int.toNat_of_nonneg hn0]; exact hn
  have hNn : (N:ℝ) ≤ (n.toNat:ℝ) := by exact_mod_cast hle
  have hNe : (2:ℝ) < N * ε := (div_lt_iff₀ hε).mp hN
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hNe, hNn, hε]

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4/ε)
  refine ⟨(N:ℤ), fun n hn => ?_⟩
  have hn0 : (0:ℤ) ≤ n := le_trans (Int.natCast_nonneg N) hn
  simp only [Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn0, sub_zero]
  set m := n.toNat
  have hm1 : (0:ℝ) < (m:ℝ)+1 := by positivity
  have htri : |(-1:ℝ)^m/((m:ℝ)+1) + 1/((m:ℝ)+1)^2| ≤ 2/((m:ℝ)+1) := by
    have h1 : |(-1:ℝ)^m/((m:ℝ)+1)| = 1/((m:ℝ)+1) := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hm1]
    have h2 : |1/((m:ℝ)+1)^2| = 1/((m:ℝ)+1)^2 := abs_of_pos (by positivity)
    have h3 : (1:ℝ)/((m:ℝ)+1)^2 ≤ 1/((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le hm1
      nlinarith [hm1]
    calc |(-1:ℝ)^m/((m:ℝ)+1) + 1/((m:ℝ)+1)^2|
        ≤ |(-1:ℝ)^m/((m:ℝ)+1)| + |1/((m:ℝ)+1)^2| := abs_add_le _ _
      _ = 1/((m:ℝ)+1) + 1/((m:ℝ)+1)^2 := by rw [h1, h2]
      _ ≤ 2/((m:ℝ)+1) := by
          have h4 : (1:ℝ)/((m:ℝ)+1) + 1/((m:ℝ)+1) = 2/((m:ℝ)+1) := by
            rw [div_add_div_same]; norm_num
          linarith [h3, h4]
  refine le_trans htri ?_
  have hle : (N:ℤ) ≤ (m:ℤ) := by rw [Int.toNat_of_nonneg hn0]; exact hn
  have hNn : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hle
  have hNe : (4:ℝ) < N * ε := (div_lt_iff₀ hε).mp hN
  rw [div_le_iff₀ hm1]
  nlinarith [hNe, hNn, hε]

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/2 < 1)
  refine ⟨(k:ℤ), fun n hn => ?_⟩
  have hn0 : (0:ℤ) ≤ n := le_trans (Int.natCast_nonneg k) hn
  simp only [Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn0, sub_zero, abs_of_pos (by positivity)]
  have e : (2:ℝ)^(-(n.toNat:ℤ)) = (1/2:ℝ)^n.toNat := by
    rw [div_pow, one_pow, one_div, ← zpow_natCast, ← zpow_neg]
  rw [e]
  have hkn : k ≤ n.toNat := by
    have hle : (k:ℤ) ≤ (n.toNat:ℤ) := by rw [Int.toNat_of_nonneg hn0]; exact hn
    exact_mod_cast hle
  calc (1/2:ℝ)^n.toNat ≤ (1/2:ℝ)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn
    _ ≤ ε := le_of_lt hk

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  rw [Sequence.tendsTo_iff, Sequence.tendsTo_iff]
  have key : ∀ n:ℤ, |a.abs n - 0| = |a n - 0| := by
    intro n
    show |(|a n|) - 0| = |a n - 0|
    rw [sub_zero, sub_zero, abs_abs]
  simp only [key]

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  refine ⟨fun n => (n:ℝ), fun n => (n:ℝ)+1, fun n => by linarith, ?_⟩
  have hsup : ((fun (n:ℕ) => (n:ℝ)):Sequence).sup = ⊤ := by
    unfold Sequence.sup
    apply sSup_eq_top.mpr
    intro b hb
    obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
    · obtain ⟨k, hk⟩ := exists_nat_gt y
      refine ⟨((k:ℝ):EReal), ⟨(k:ℤ), by positivity, ?_⟩, by exact_mod_cast hk⟩
      simp [Sequence.instCoeFun, Sequence.ofNatFun]
    · exact absurd hb (lt_irrefl _)
    · exact ⟨((0:ℝ):EReal), ⟨0, le_refl _, by simp [Sequence.instCoeFun, Sequence.ofNatFun]⟩,
        bot_lt_iff_ne_bot.mpr (by decide)⟩
  rw [hsup]
  exact not_top_lt

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h
  have hconst : ((fun (n:ℕ) => (-1:ℝ)):Sequence).TendsTo (-1) := by
    rw [Sequence.tendsTo_iff]
    intro ε hε
    refine ⟨0, fun n hn => ?_⟩
    simp only [Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos hn]; simp; linarith
  have habs := (h _ _).mp hconst
  rw [Sequence.tendsTo_iff] at habs
  obtain ⟨N, hN⟩ := habs 1 (by norm_num)
  have hbad := hN (max N 0) (le_max_left _ _)
  have heval : ((fun (n:ℕ) => (-1:ℝ)):Sequence).abs (max N 0) = 1 := by
    show |((fun (n:ℕ) => (-1:ℝ)):Sequence) (max N 0)| = 1
    simp only [Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos (le_max_right _ _)]; norm_num
  rw [heval] at hbad
  norm_num at hbad

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  unfold Sequence.ExtendedLimitPoint
  split_ifs with h1 h2
  · rintro ⟨M, hM⟩
    have hle : a.limsup ≤ (M:EReal) :=
      a.limsup_le_sup.trans (a.sup_le_upper (fun n hn => by exact_mod_cast hM n hn))
    rw [h1] at hle; exact absurd hle (not_le.mpr (EReal.coe_lt_top M))
  · rintro ⟨M, hM⟩
    have hge : (M:EReal) ≤ a.limsup :=
      (a.inf_ge_lower (fun n hn => by exact_mod_cast hM n hn)).trans
        (a.inf_le_liminf.trans a.liminf_le_limsup)
    rw [h2] at hge; exact absurd hge (not_le.mpr (EReal.bot_lt_coe M))
  · exact limit_point_of_limsup (EReal.coe_toReal h1 h2).symm

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by
  unfold Sequence.ExtendedLimitPoint
  split_ifs with h1 h2
  · rintro ⟨M, hM⟩
    have hle : a.liminf ≤ (M:EReal) :=
      a.liminf_le_limsup.trans (a.limsup_le_sup.trans (a.sup_le_upper (fun n hn => by exact_mod_cast hM n hn)))
    rw [h1] at hle; exact absurd hle (not_le.mpr (EReal.coe_lt_top M))
  · rintro ⟨M, hM⟩
    have hge : (M:EReal) ≤ a.liminf :=
      (a.inf_ge_lower (fun n hn => by exact_mod_cast hM n hn)).trans a.inf_le_liminf
    rw [h2] at hge; exact absurd hge (not_le.mpr (EReal.bot_lt_coe M))
  · exact limit_point_of_liminf (EReal.coe_toReal h1 h2).symm


theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  unfold Sequence.ExtendedLimitPoint at h
  split_ifs at h with h1 h2
  · rw [h1, limsup_top_of_not_bddAbove h]
  · rw [h2]; exact bot_le
  · obtain ⟨_, hub⟩ := a.limit_point_between_liminf_limsup h
    rw [← EReal.coe_toReal h1 h2]; exact hub

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by
  unfold Sequence.ExtendedLimitPoint at h
  split_ifs at h with h1 h2
  · rw [h1]; exact le_top
  · rw [h2, liminf_bot_of_not_bddBelow h]
  · obtain ⟨hlb, _⟩ := a.limit_point_between_liminf_limsup h
    rw [ge_iff_le, ← EReal.coe_toReal h1 h2]; exact hlb

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry


end Chapter6
