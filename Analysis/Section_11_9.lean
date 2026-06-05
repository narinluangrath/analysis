import Mathlib.Tactic
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Analysis.Section_7_3
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_11_6
import Analysis.Section_11_8


/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/

namespace Chapter11
open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus)-/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  choose M hM using hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx.1 (le_of_lt hxy))).2
    simp [F, this.2, abs_le']
    constructor
    . convert this.1.mono (g := fun _ ↦ M) (IntegrableOn.const _ _).1 _
      . simp [IntegrableOn.const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at *; grind
      grind [abs_le']
    rw [neg_le]
    convert (IntegrableOn.const _ _).1.mono (f := fun _ ↦ -M) this.1 _
    . simp [IntegrableOn.const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at *; grind
    grind [abs_le']
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    obtain h | rfl | h := lt_trichotomy x y
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; apply le_max_left
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  simp [(ContinuousWithinAt.tfae _ f x₀).out 0 2] at hcts
  peel hcts with ε hε δ hδ hconv; intro y hy hyδ
  obtain hx₀y | rfl | hx₀y := lt_trichotomy x₀ y
  . have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      split_ands
      . convert h1 using 1; ring
      . simp [←sub_nonneg] at *; convert h2 using 1; ring
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith
  . simp
  · have := ((hf.join (join_Icc_Ioc hx₀.1 hx₀.2)).1.join (join_Icc_Ioc hy.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_neg (show y - x₀ < 0 by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      split_ands
      . nlinarith [h2]
      . nlinarith [h1]
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) :=
  integ_of_monotone (StrictMonoOn.of_f_9_8_5.mono (by simp)).monotoneOn

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (.Icc 0 1) := cts_of_integ IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) .of_f_9_8_5 hx' (ContinuousAt.of_f_9_8_5 hx).continuousWithinAt
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  exact ⟨_, this⟩

/-- Exercise 11.9.1 -/
theorem DifferentiableOn.of_F_11_9_2' {q:ℚ} (hq: (q:ℝ) ∈ Set.Icc 0 1) : ¬ DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) q := by sorry

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

theorem AntiderivOn.mono {F f: ℝ → ℝ} {I J: BoundedInterval}
  (h: AntiderivOn F f I) (hIJ: J ⊆ I) : AntiderivOn F f J :=
  ⟨ h.1.mono hIJ, by intro x hx; rw [subset_iff] at hIJ; exact (h.2 x (hIJ hx)).mono hIJ ⟩

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antideriv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by
  -- This proof is written to follow the structure of the original text.
  obtain h | h := lt_or_eq_of_le h
  . have hF_cts : ContinuousOn F (.Icc a b) := by
      intro x hx; exact ContinuousWithinAt.of_differentiableWithinAt (hF.1 x hx)
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦ F (max (min x b) a)

    have hFF' {x:ℝ} (hx: x ∈ Set.Icc a b) : F' x = F x := by simp_all [F']

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      convert (hF_cts.comp_continuous (f := fun x ↦ max (min x b) a) (by fun_prop) ?_).continuousOn using 1
      intros; simp [le_of_lt h]

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ = F' d - F' c := rfl
                _ = (d - c) * f e := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = f e * |J|ₗ := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ ≤ _ := by
                  gcongr; apply le_csSup
                  . rw [bddAbove_def]
                    choose M hM using hf.1; use M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); tauto
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≤ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ ≤ f e * |J|ₗ := by
                  gcongr; apply csInf_le
                  . rw [bddBelow_def]
                    choose M hM using hf.1; use -M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); linarith [hM.1, hM.2]
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
                _ = (d - c) * f e := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ = F' d - F' c := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = _ := rfl
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]; apply le_csInf <;> simp [Set.range_nonempty]
      grind
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]; apply csSup_le <;> simp [Set.range_nonempty]
      grind
    linarith [hf.2]
  simp [h]; exact (integ_on_subsingleton (by simp [length])).2


open Real

noncomputable abbrev F_11_9 : ℝ → ℝ := fun x ↦ if x = 0 then 0 else x^2 * sin (1 / x^3)

theorem Differentiable.of_F_11_9 : Differentiable ℝ F_11_9 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have hd : HasDerivAt F_11_9 0 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      apply squeeze_zero_norm (a := fun y => |y|)
      · intro y
        by_cases hy : y = 0
        · simp [slope, F_11_9, hy]
        · have hval : slope F_11_9 0 y = y * sin (1/y^3) := by
            simp only [slope, F_11_9, if_neg hy, vsub_eq_sub, sub_zero, smul_eq_mul, reduceIte]
            field_simp
          rw [hval, norm_eq_abs, abs_mul]
          calc |y| * |sin (1/y^3)| ≤ |y| * 1 :=
                mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _)
            _ = |y| := by ring
      · have h : Filter.Tendsto (fun y:ℝ => |y|) (nhds (0:ℝ)) (nhds 0) := by
          have := (_root_.continuous_abs.tendsto (0:ℝ)); simpa using this
        exact h.mono_left nhdsWithin_le_nhds
    exact hd.differentiableAt
  · have heq : F_11_9 =ᶠ[nhds x] (fun x => x^2 * sin (1/x^3)) := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [F_11_9, hy]
    have h3 : x^3 ≠ 0 := pow_ne_zero _ hx
    have hg : DifferentiableAt ℝ (fun x:ℝ => 1/x^3) x := by
      apply DifferentiableAt.div <;> [fun_prop; fun_prop; exact h3]
    have hinner : DifferentiableAt ℝ (fun x:ℝ => x^2 * sin (1/x^3)) x :=
      (differentiableAt_pow 2).mul (hg.sin)
    exact hinner.congr_of_eventuallyEq heq

theorem hasDerivAt_F_11_9 (x:ℝ) (hx : x ≠ 0) :
    HasDerivAt F_11_9 (2*x*sin (1/x^3) - 3/x^2 * cos (1/x^3)) x := by
  have heq : F_11_9 =ᶠ[nhds x] (fun x => x^2 * sin (1/x^3)) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp [F_11_9, hy]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  have hx3 : (x:ℝ)^3 ≠ 0 := pow_ne_zero _ hx
  have hcube : HasDerivAt (fun x:ℝ => x^3) (3*x^2) x := by simpa using (hasDerivAt_pow 3 x)
  have h3 : HasDerivAt (fun x:ℝ => 1/x^3) (-3/x^4) x := by
    have := (hasDerivAt_const x (1:ℝ)).div hcube hx3
    convert this using 1
    field_simp; ring
  have hsin : HasDerivAt (fun x:ℝ => sin (1/x^3)) (cos (1/x^3) * (-3/x^4)) x :=
    (Real.hasDerivAt_sin _).comp x h3
  have hsq : HasDerivAt (fun x:ℝ => x^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
  have := hsq.mul hsin
  convert this using 1
  field_simp; ring

example : ¬ BddOn (deriv F_11_9) (.Icc (-1) 1) := by
  rintro ⟨M, hM⟩
  -- choose n with 3*(2πn)^(2/3) > M, then x_n = (2πn)^(-1/3) gives |deriv| = 3(2πn)^(2/3)
  obtain ⟨n, hn1, hbig⟩ : ∃ n:ℕ, 1 ≤ n ∧ M < 3*(2*π*(n:ℝ))^((2:ℝ)/3) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((max (M/3) 0)^((3:ℝ)/2))
    refine ⟨max n 1, le_max_right _ _, ?_⟩
    have hpi : (0:ℝ) < π := pi_pos
    set m : ℝ := ((max n 1:ℕ):ℝ) with hm_def
    have hm1 : (1:ℝ) ≤ m := by rw [hm_def]; exact_mod_cast le_max_right _ _
    have h0 : (0:ℝ) ≤ max (M/3) 0 := le_max_right _ _
    have hlt : (max (M/3) 0)^((3:ℝ)/2) < m := by
      have : ((n:ℝ)) ≤ m := by rw [hm_def]; exact_mod_cast le_max_left _ _
      linarith
    have hbase : max (M/3) 0 < m^((2:ℝ)/3) := by
      have := Real.rpow_lt_rpow (by positivity) hlt (show (0:ℝ) < (2:ℝ)/3 by norm_num)
      rw [← Real.rpow_mul h0, show (3:ℝ)/2 * (2/3) = 1 by norm_num, Real.rpow_one] at this
      exact this
    have hM3 : M/3 < m^((2:ℝ)/3) := lt_of_le_of_lt (le_max_left _ _) hbase
    have ht : m^((2:ℝ)/3) ≤ (2*π*m)^((2:ℝ)/3) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith [Real.two_le_pi]
    have hpos : 0 < (2*π*m)^((2:ℝ)/3) := Real.rpow_pos_of_pos (by positivity) _
    rw [hm_def] at hM3 ht; linarith
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  set t : ℝ := 2*π*n with ht_def
  have hpi : (0:ℝ) < π := pi_pos
  have htpos : 0 < t := by rw [ht_def]; positivity
  have ht1 : 1 ≤ t := by rw [ht_def]; nlinarith [Real.two_le_pi]
  set x : ℝ := t^(-(1:ℝ)/3) with hx_def
  have hxpos : 0 < x := by rw [hx_def]; positivity
  have hxle : x ≤ 1 := by rw [hx_def]; exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hx3 : x^3 = t⁻¹ := by
    rw [hx_def, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (le_of_lt htpos)]
    norm_num; rw [Real.rpow_neg_one]
  have hx2 : x^2 = t^(-(2:ℝ)/3) := by
    rw [hx_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt htpos)]
    norm_num
  have hinv3 : 1/x^3 = t := by rw [hx3, one_div, inv_inv]
  -- cos(t)=1, sin(t)=0 since t = n*(2π)
  have htn : t = (n:ℝ)*(2*π) := by rw [ht_def]; ring
  have hcos : cos (1/x^3) = 1 := by rw [hinv3, htn]; exact Real.cos_nat_mul_two_pi n
  have hsin : sin (1/x^3) = 0 := by
    rw [hinv3, htn]
    have := Real.sin_int_mul_pi (2*n); push_cast at this ⊢; convert this using 2; ring
  -- deriv value
  have hderiv : deriv F_11_9 x = -3 * t^((2:ℝ)/3) := by
    rw [(hasDerivAt_F_11_9 x hxne).deriv, hsin, hcos]
    rw [hx2]
    rw [show -(2:ℝ)/3 = -((2:ℝ)/3) by ring, Real.rpow_neg (le_of_lt htpos)]
    have h : (t^((2:ℝ)/3)) ≠ 0 := by positivity
    field_simp
    ring
  -- membership
  have hmem : x ∈ (BoundedInterval.Icc (-1:ℝ) 1 : Set ℝ) := by
    rw [BoundedInterval.set_Icc]; constructor <;> [linarith; exact hxle]
  -- bound contradiction: |deriv| = 3 t^(2/3) > M
  have hbig' : M < 3 * t^((2:ℝ)/3) := by rw [ht_def]; exact hbig
  have hb := hM x hmem
  rw [hderiv, abs_le] at hb
  have h2 := hb.1
  rw [neg_mul] at h2
  linarith

example : AntiderivOn F_11_9 (deriv F_11_9) (Icc (-1) 1) := by
  refine ⟨Differentiable.of_F_11_9.differentiableOn, fun x hx => ?_⟩
  exact (Differentiable.of_F_11_9 x).hasDerivAt.hasDerivWithinAt

/-- Lemma 11.9.5 / Exercise 11.9.2 -/
theorem antideriv_eq_antideriv_add_const {I:BoundedInterval} {f F G : ℝ → ℝ}
  (hfF: AntiderivOn F f I) (hfG: AntiderivOn G f I) :
   ∃ C, ∀ x ∈ (I:Set ℝ), F x = G x + C := by
    rcases (↑I:Set ℝ).eq_empty_or_nonempty with hIe | ⟨x₀, hx₀⟩
    · exact ⟨0, fun x hx => by rw [hIe] at hx; exact absurd hx (Set.notMem_empty x)⟩
    refine ⟨F x₀ - G x₀, fun x hx => ?_⟩
    by_cases hsub : (↑I:Set ℝ).Subsingleton
    · rw [hsub hx hx₀]; ring
    rw [Set.not_subsingleton_iff] at hsub
    have hconv : Convex ℝ (↑I:Set ℝ) := by
      cases I with
      | Ioo a b => rw [BoundedInterval.set_Ioo]; exact convex_Ioo a b
      | Icc a b => rw [BoundedInterval.set_Icc]; exact convex_Icc a b
      | Ioc a b => rw [BoundedInterval.set_Ioc]; exact convex_Ioc a b
      | Ico a b => rw [BoundedInterval.set_Ico]; exact convex_Ico a b
    have hab : I.a < I.b := by
      rcases lt_or_ge I.a I.b with h | h
      · exact h
      · exact absurd ((Set.subsingleton_coe _).mp (BoundedInterval.length_of_subsingleton.mpr
          (by simp only [BoundedInterval.length]; exact max_eq_right (by linarith)))) hsub.not_subsingleton
    have huniq : UniqueDiffOn ℝ (↑I:Set ℝ) := by
      cases I with
      | Ioo a b => rw [BoundedInterval.set_Ioo]; exact uniqueDiffOn_Ioo a b
      | Icc a b => rw [BoundedInterval.set_Icc]; exact uniqueDiffOn_Icc hab
      | Ioc a b => rw [BoundedInterval.set_Ioc]; exact uniqueDiffOn_Ioc a b
      | Ico a b => rw [BoundedInterval.set_Ico]; exact uniqueDiffOn_Ico a b
    have key : (F - G) x = (F - G) x₀ := by
      apply hconv.is_const_of_fderivWithin_eq_zero (hfF.1.sub hfG.1) _ hx hx₀
      intro y hy
      have hd : HasDerivWithinAt (F - G) 0 (↑I) y := by
        have h1 := hfF.2 y ((BoundedInterval.mem_iff I y).mpr hy)
        have h2 := hfG.2 y ((BoundedInterval.mem_iff I y).mpr hy)
        simpa using h1.sub h2
      rw [hd.hasFDerivWithinAt.fderivWithin (huniq y hy)]
      ext z; simp
    simp only [Pi.sub_apply] at key
    linarith

/-- Exercise 11.9.3 -/
example {a b x₀:ℝ} (hab: a < b) (hx₀: x₀ ∈ Icc a b) {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
  ContinuousWithinAt f (Icc a b) x₀ := by
  sorry

end Chapter11

/-- Exercise 11.6.5, moved to Section 11.9 -/
theorem Chapter7.Series.converges_qseries' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).converges ↔ (p>1) := by
  rcases le_or_gt p 0 with hp | hp
  · constructor
    · intro hconv
      exfalso
      have hd := Chapter7.Series.decay_of_converges hconv
      rw [Metric.tendsto_atTop] at hd
      obtain ⟨N, hN⟩ := hd 1 (by norm_num)
      have hge : max N 1 ≥ N := le_max_left _ _
      specialize hN (max N 1) hge
      rw [Real.dist_eq, sub_zero, Chapter7.Series.eval_mk' _ (by omega : (max N 1) ≥ 1)] at hN
      have h1 : (1:ℝ) ≤ ((max N 1 : ℤ):ℝ) := by
        have : (1:ℤ) ≤ max N 1 := by omega
        exact_mod_cast this
      have hpos : (0:ℝ) < ((max N 1 : ℤ):ℝ) := by linarith
      have hle1 : ((max N 1 : ℤ):ℝ) ^ p ≤ 1 := by
        rw [show (1:ℝ) = ((max N 1:ℤ):ℝ)^(0:ℝ) by rw [Real.rpow_zero]]
        exact Real.rpow_le_rpow_of_exponent_le h1 hp
      have : (1:ℝ) ≤ 1 / ((max N 1:ℤ):ℝ)^p := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [abs_of_pos (by positivity)] at hN
      linarith
    · intro h; linarith
  · exact Chapter7.Series.converges_qseries p hp

theorem Chapter7.Series.converges_qseries'' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).absConverges ↔ (p>1) := by
  rw [← Chapter7.Series.converges_qseries' p]
  unfold Chapter7.Series.absConverges
  have heq : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).abs = (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series) := by
    unfold Chapter7.Series.abs
    have : (fun n : { n : ℤ // n ≥ 1 } ↦ |(mk' (m := 1) fun k ↦ 1 / (k:ℝ) ^ p : Series).seq n|)
         = (fun n : { n : ℤ // n ≥ 1 } ↦ 1 / ((n:ℤ):ℝ) ^ p) := by
      ext ⟨n, hn⟩
      rw [Chapter7.Series.eval_mk' _ hn]
      rw [abs_of_nonneg]
      have : (1:ℝ) ≤ ((n:ℤ):ℝ) := by exact_mod_cast hn
      positivity
    rw [this]
  rw [heq]
