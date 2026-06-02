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

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by sorry

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by sorry

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

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by sorry

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by sorry

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by sorry

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := sorry
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by sorry

end Chapter6
