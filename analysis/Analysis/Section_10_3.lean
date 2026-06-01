import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Analysis I, Section 10.3: Monotone functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relations between monotonicity and differentiability.

-/

namespace Chapter10

/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀
  have hd := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hslope : ∀ᶠ y in nhdsWithin x₀ (X \ {x₀}), 0 ≤ slope f x₀ y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hy
    rw [slope_def_field]
    rcases lt_trichotomy y x₀ with h | h | h
    · rw [div_nonneg_iff]; right; exact ⟨by linarith [hmono h.le], by linarith⟩
    · exact absurd h hy.2
    · exact div_nonneg (by linarith [hmono h.le]) (by linarith)
  exact ge_of_tendsto hd hslope

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  have h := derivative_of_monotone X hx₀ hmono.neg hderiv.neg
  rw [show (fun x => -f x) = (-f) from rfl, derivWithin.neg] at h
  linarith

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hderiv.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact hpos x hx

theorem strictAnti_of_negative_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  have h := strictMono_of_positive_derivative hab hderiv.neg (fun x hx => by
    rw [derivWithin.neg]; linarith [hneg x hx])
  intro x hx y hy hxy
  have := h hx hy hxy; simp at this; exact this

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by
  refine ⟨fun x => 2 * x + |x|, ?_, ?_, ?_⟩
  · exact (continuous_const.mul continuous_id).add continuous_abs
  · intro a b hab
    simp only
    have h1 : |b| - |a| ≥ -(b - a) := by
      have h2 := abs_sub_abs_le_abs_sub a b
      have h3 : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      linarith
    linarith
  · intro h
    apply not_differentiableAt_abs_zero
    have h2 : DifferentiableAt ℝ (fun x:ℝ => 2 * x) 0 :=
      (differentiableAt_const 2).mul differentiableAt_id
    have h3 := h.sub h2
    have : (fun x:ℝ => 2 * x + |x|) - (fun x:ℝ => 2 * x) = (fun x:ℝ => |x|) := by ext x; simp
    rwa [this] at h3

/-- Exercise 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by
  refine ⟨fun x => x ^ 3, fun a b hab => ?_, ?_, ?_⟩
  · exact Odd.strictMono_pow (by norm_num : Odd 3) hab
  · exact fun x => differentiableAt_pow 3
  · simp [deriv_pow]

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  sorry

end Chapter10
