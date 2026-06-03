import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Value set of a coerced `ℕ → ℝ` sequence as a subset of `EReal`. -/
private theorem coe_value_set (f:ℕ→ℝ) :
    {x : EReal | ∃ n ≥ ((f:Sequence)).m, x = ((f:Sequence)) n} = {x | ∃ k:ℕ, x = ((f k:ℝ):EReal)} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.toNat, ?_⟩
    simp only [Sequence.instCoeFun, Sequence.ofNatFun] at hn ⊢
    rw [if_pos hn]
  · rintro ⟨k, rfl⟩
    refine ⟨(k:ℤ), by simp [Sequence.ofNatFun], ?_⟩
    simp only [Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos (by positivity)]
    norm_num

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  show sSup _ = _
  rw [coe_value_set]
  apply IsGreatest.csSup_eq
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  rintro x ⟨k, rfl⟩
  rw [show (1:EReal) = ((1:ℝ):EReal) from rfl, EReal.coe_le_coe_iff]
  rcases Nat.even_or_odd (k+1) with h | h
  · rw [Even.neg_one_pow h]
  · rw [Odd.neg_one_pow h]; norm_num

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  show sInf _ = _
  rw [coe_value_set]
  apply IsLeast.csInf_eq
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  rintro x ⟨k, rfl⟩
  rw [show (-1:EReal) = ((-1:ℝ):EReal) from rfl, EReal.coe_le_coe_iff]
  rcases Nat.even_or_odd (k+1) with h | h
  · rw [Even.neg_one_pow h]; norm_num
  · rw [Odd.neg_one_pow h]

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  show sSup _ = _
  rw [coe_value_set]
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  rintro x ⟨k, rfl⟩
  rw [show (1:EReal) = ((1:ℝ):EReal) from rfl, EReal.coe_le_coe_iff]
  rw [div_le_one (by positivity)]
  have : (0:ℝ) ≤ (k:ℝ) := by positivity
  linarith

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  show sInf _ = _
  rw [coe_value_set]
  refine IsGLB.csInf_eq ⟨?_, ?_⟩ ⟨_, 0, rfl⟩
  · rintro x ⟨k, rfl⟩
    rw [show (0:EReal) = ((0:ℝ):EReal) from rfl, EReal.coe_le_coe_iff]
    positivity
  · intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
    · rw [show (0:EReal) = ((0:ℝ):EReal) from rfl, EReal.coe_lt_coe_iff] at hlt
      obtain ⟨k, hk⟩ := exists_nat_gt (1/y)
      have hmem := hb ⟨k, rfl⟩
      rw [EReal.coe_le_coe_iff] at hmem
      rw [div_lt_iff₀ hlt] at hk
      rw [le_div_iff₀ (by positivity)] at hmem
      nlinarith
    · exact absurd (hb ⟨0, rfl⟩) (not_le.mpr (EReal.coe_lt_top _))
    · exact absurd bot_le (not_le.mpr hlt)

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  show sSup _ = _
  rw [coe_value_set]
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
  · obtain ⟨n, hn⟩ := exists_nat_gt y
    refine ⟨(((n:ℝ)+1:ℝ):EReal), ⟨n, rfl⟩, ?_⟩
    push_cast
    exact_mod_cast lt_trans (by exact_mod_cast hn) (by norm_num)
  · exact absurd hb (lt_irrefl _)
  · exact ⟨((((0:ℕ):ℝ)+1:ℝ):EReal), ⟨0, rfl⟩, bot_lt_iff_ne_bot.mpr (by decide)⟩

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  show sInf _ = _
  rw [coe_value_set]
  apply IsLeast.csInf_eq
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  rintro x ⟨k, rfl⟩
  show ((1:ℝ):EReal) ≤ (((k:ℝ)+1:ℝ):EReal)
  rw [EReal.coe_le_coe_iff]
  have : (0:ℝ) ≤ (k:ℝ) := by positivity
  linarith

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  constructor
  · rintro ⟨M, _, hM⟩
    exact ⟨⟨M, fun n _ => (abs_le.mp (hM n)).2⟩, ⟨-M, fun n _ => (abs_le.mp (hM n)).1⟩⟩
  · rintro ⟨⟨M1, hM1⟩, ⟨M2, hM2⟩⟩
    refine ⟨max (|M1|) (|M2|), le_trans (abs_nonneg _) (le_max_left _ _), fun n => ?_⟩
    rcases lt_or_ge n a.m with hn | hn
    · rw [a.vanish n hn, abs_zero]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    · rw [abs_le]
      exact ⟨by linarith [neg_abs_le M2, le_max_right (|M1|) (|M2|), hM2 n hn],
        by linarith [le_abs_self M1, le_max_left (|M1|) (|M2|), hM1 n hn]⟩

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  rw [bounded_iff] at h
  obtain ⟨⟨M1, hM1⟩, _⟩ := h
  by_contra hcon
  replace hcon := (EReal.infinite_iff_not_finite _).mpr hcon
  rcases hcon with htop | hbot
  · have hle : a.sup ≤ (M1:EReal) := by
      apply sSup_le; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hM1 n hn
    rw [htop] at hle
    exact absurd hle (not_le.mpr (EReal.coe_lt_top M1))
  · have hge : (a a.m : EReal) ≤ a.sup := le_sSup ⟨a.m, le_refl _, rfl⟩
    rw [hbot] at hge
    exact absurd hge (not_le.mpr (EReal.bot_lt_coe _))

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  rw [bounded_iff] at h
  obtain ⟨_, ⟨M2, hM2⟩⟩ := h
  by_contra hcon
  replace hcon := (EReal.infinite_iff_not_finite _).mpr hcon
  rcases hcon with htop | hbot
  · have hle : a.inf ≤ (a a.m : EReal) := sInf_le ⟨a.m, le_refl _, rfl⟩
    rw [htop] at hle
    exact absurd hle (not_le.mpr (EReal.coe_lt_top _))
  · have hge : (M2:EReal) ≤ a.inf := by
      apply le_sInf; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hM2 n hn
    rw [hbot] at hge
    exact absurd hge (not_le.mpr (EReal.bot_lt_coe M2))

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup :=
  le_sSup ⟨n, hn, rfl⟩

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
  rw [lt_sSup_iff] at h
  obtain ⟨x, ⟨n, hn, rfl⟩, hyx⟩ := h
  exact ⟨n, hn, hyx, le_sup hn⟩

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf :=
  sInf_le ⟨n, hn, rfl⟩

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  apply le_sInf
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
  rw [gt_iff_lt, sInf_lt_iff] at h
  obtain ⟨x, ⟨n, hn, rfl⟩, hyx⟩ := h
  exact ⟨n, hn, hyx, ge_inf hn⟩

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- A monotone sequence is increasing over its whole range. -/
private theorem Sequence.mono_le {a:Sequence} (hmono: a.IsMonotone) {j k:ℤ}
    (hj: a.m ≤ j) (hjk: j ≤ k) : a j ≤ a k := by
  induction k, hjk using Int.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact le_trans ih (hmono k (le_trans hj hk))

/-- The supremum of a monotone sequence bounded above is a finite real, and the sequence
converges to it. -/
private theorem Sequence.tendsTo_toReal_sup {a:Sequence} (hbound: a.BddAbove)
    (hmono: a.IsMonotone) :
    a.sup ≠ ⊤ ∧ a.sup ≠ ⊥ ∧ a.TendsTo a.sup.toReal := by
  obtain ⟨M, hM⟩ := hbound
  have hsup_ne_top : a.sup ≠ ⊤ := by
    intro h
    have hle : a.sup ≤ (M:EReal) := by
      apply sSup_le; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hM n hn
    rw [h] at hle; exact absurd hle (not_le.mpr (EReal.coe_lt_top M))
  have hsup_ne_bot : a.sup ≠ ⊥ := by
    intro h
    have hge : (a a.m : EReal) ≤ a.sup := le_sSup ⟨a.m, le_refl _, rfl⟩
    rw [h] at hge; exact absurd hge (not_le.mpr (EReal.bot_lt_coe _))
  refine ⟨hsup_ne_top, hsup_ne_bot, ?_⟩
  set L := a.sup.toReal with hLdef
  have hLsup : (L:EReal) = a.sup := EReal.coe_toReal hsup_ne_top hsup_ne_bot
  rw [tendsTo_iff]
  intro ε hε
  have hlt : ((L - ε:ℝ):EReal) < a.sup := by
    rw [← hLsup]; exact_mod_cast (by linarith : L - ε < L)
  obtain ⟨N, hNm, hN1, hN2⟩ := exists_between_lt_sup hlt
  refine ⟨N, fun n hn => ?_⟩
  have han : a N ≤ a n := mono_le hmono hNm hn
  have hub : a n ≤ L := by
    have hle : (a n : EReal) ≤ a.sup := le_sSup ⟨n, le_trans hNm hn, rfl⟩
    rw [← hLsup] at hle; exact_mod_cast hle
  have hlb : L - ε < a n := by
    rw [EReal.coe_lt_coe_iff] at hN1
    linarith
  rw [abs_le]; constructor <;> linarith

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := ⟨_, (tendsTo_toReal_sup hbound hmono).2.2⟩

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
  obtain ⟨hne_top, hne_bot, htends⟩ := tendsTo_toReal_sup hbound hmono
  rw [(lim_eq.mp htends).2]
  exact EReal.coe_toReal hne_top hne_bot

/-- An antitone sequence is decreasing over its whole range. -/
private theorem Sequence.anti_ge {a:Sequence} (hmono: a.IsAntitone) {j k:ℤ}
    (hj: a.m ≤ j) (hjk: j ≤ k) : a k ≤ a j := by
  induction k, hjk using Int.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact le_trans (hmono k (le_trans hj hk)) ih

private theorem Sequence.tendsTo_toReal_inf {a:Sequence} (hbound: a.BddBelow)
    (hmono: a.IsAntitone) :
    a.inf ≠ ⊤ ∧ a.inf ≠ ⊥ ∧ a.TendsTo a.inf.toReal := by
  obtain ⟨M, hM⟩ := hbound
  have hinf_ne_bot : a.inf ≠ ⊥ := by
    intro h
    have hge : (M:EReal) ≤ a.inf := by
      apply le_sInf; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hM n hn
    rw [h] at hge; exact absurd hge (not_le.mpr (EReal.bot_lt_coe M))
  have hinf_ne_top : a.inf ≠ ⊤ := by
    intro h
    have hle : a.inf ≤ (a a.m : EReal) := sInf_le ⟨a.m, le_refl _, rfl⟩
    rw [h] at hle; exact absurd hle (not_le.mpr (EReal.coe_lt_top _))
  refine ⟨hinf_ne_top, hinf_ne_bot, ?_⟩
  set L := a.inf.toReal with hLdef
  have hLinf : (L:EReal) = a.inf := EReal.coe_toReal hinf_ne_top hinf_ne_bot
  rw [tendsTo_iff]
  intro ε hε
  have hgt : a.inf < ((L + ε:ℝ):EReal) := by
    rw [← hLinf]; exact_mod_cast (by linarith : L < L + ε)
  obtain ⟨N, hNm, hN1, hN2⟩ := exists_between_gt_inf hgt
  refine ⟨N, fun n hn => ?_⟩
  have han : a n ≤ a N := anti_ge hmono hNm hn
  have hlb : L ≤ a n := by
    have hge : a.inf ≤ (a n : EReal) := sInf_le ⟨n, le_trans hNm hn, rfl⟩
    rw [← hLinf] at hge; exact_mod_cast hge
  have hub : a n < L + ε := by
    rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hN1
    linarith
  rw [abs_le]; constructor <;> linarith

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := ⟨_, (tendsTo_toReal_inf hbound hmono).2.2⟩

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
  obtain ⟨hne_top, hne_bot, htends⟩ := tendsTo_toReal_inf hbound hmono
  rw [(lim_eq.mp htends).2]
  exact EReal.coe_toReal hne_top hne_bot

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded :=
  ⟨bounded_of_convergent, fun h => convergent_of_monotone ((bounded_iff _).mp h).1 ha⟩

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded :=
  ⟨bounded_of_convergent, fun h => convergent_of_antitone ((bounded_iff _).mp h).2 ha⟩

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

private theorem Example_6_3_9_bdd : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  intro n hn
  simp only [Example_6_3_9, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn]
  have h10 : (0:ℝ) < 10^n.toNat := by positivity
  rw [div_le_iff₀ h10]
  have hfloor : (⌊Real.pi * 10^n.toNat⌋:ℝ) ≤ Real.pi * 10^n.toNat := Int.floor_le _
  nlinarith [hfloor, Real.pi_le_four, h10]

private theorem Example_6_3_9_mono : (Example_6_3_9:Sequence).IsMonotone := by
  intro k hk
  have hk0 : (0:ℤ) ≤ k := hk
  show (Example_6_3_9:Sequence) k ≤ (Example_6_3_9:Sequence) (k+1)
  simp only [Example_6_3_9, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hk0, if_pos (by linarith), show (k+1).toNat = k.toNat + 1 by omega]
  set m := k.toNat
  have key : (10:ℝ) * (⌊Real.pi * 10^m⌋:ℝ) ≤ (⌊Real.pi * 10^(m+1)⌋:ℝ) := by
    have keyZ : (10:ℤ) * ⌊Real.pi * 10^m⌋ ≤ ⌊Real.pi * 10^(m+1)⌋ := by
      rw [Int.le_floor]; push_cast [pow_succ]
      nlinarith [Int.floor_le (Real.pi * 10^m), (by positivity : (0:ℝ) ≤ (10:ℝ)^m)]
    exact_mod_cast keyZ
  have hrw : (⌊Real.pi * 10^m⌋:ℝ)/10^m = (10*⌊Real.pi * 10^m⌋)/10^(m+1) := by
    rw [pow_succ]; field_simp
  rw [hrw, div_le_div_iff_of_pos_right (by positivity)]
  exact key

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := Example_6_3_9_mono

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := Example_6_3_9_bdd

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent :=
  Sequence.convergent_of_monotone ⟨4, Example_6_3_9_bdd⟩ Example_6_3_9_mono

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by
  have hle : ((lim (Example_6_3_9:Sequence):ℝ):EReal) ≤ ((4:ℝ):EReal) := by
    rw [Sequence.lim_of_monotone ⟨4, Example_6_3_9_bdd⟩ Example_6_3_9_mono]
    apply sSup_le
    rintro x ⟨n, hn, rfl⟩
    exact_mod_cast Example_6_3_9_bdd n hn
  exact_mod_cast hle

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := by
    intro k hk
    have hk0 : (0:ℤ) ≤ k := hk
    show a (k+1) ≤ a k
    simp only [a, Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos hk0, if_pos (by linarith), show (k+1).toNat = k.toNat+1 by omega, pow_succ]
    nlinarith [pow_nonneg hpos.le k.toNat, hbound]
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
    have hbtend : ((fun (n:ℕ) ↦ x^(n+1)):Sequence).TendsTo L := by
      have hatend := Sequence.lim_def hconv
      rw [Sequence.tendsTo_iff] at hatend ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hatend ε hε
      refine ⟨max N 0, fun n hn => ?_⟩
      have hn0 : (0:ℤ) ≤ n := le_trans (le_max_right _ _) hn
      have heval : ((fun (n:ℕ) ↦ x^(n+1)):Sequence) n = a (n+1) := by
        simp only [a, Sequence.instCoeFun, Sequence.ofNatFun]
        rw [if_pos hn0, if_pos (by linarith), show (n+1).toNat = n.toNat+1 by omega]
      rw [heval]
      apply hN
      have : N ≤ n := le_trans (le_max_left _ _) hn
      linarith
    exact (Sequence.lim_eq.mp hbtend).2
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by sorry

end Chapter6
