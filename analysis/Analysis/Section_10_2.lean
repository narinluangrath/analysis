import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Analysis.Section_9_6

/-!
# Analysis I, Section 10.2: Local maxima, local minima, and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives.
- Rolle's theorem.
- mean value theorem.

-/

open Chapter9
namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's `IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

example : ¬ IsMinOn f_10_2_3 .univ 0 := by
  intro h
  rw [isMinOn_iff] at h
  have := h 2 (Set.mem_univ 2)
  simp only [f_10_2_3] at this
  norm_num at this

example : IsMinOn f_10_2_3 (.Ioo (-1) 1) 0 := by
  rw [isMinOn_iff]
  intro x hx
  simp only [Set.mem_Ioo] at hx
  simp only [f_10_2_3]
  have h1 : (0:ℝ) ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  nlinarith [mul_nonneg (sq_nonneg x) h1]

example : IsLocalMaxOn f_10_2_3 .univ 0 := by sorry

/-- Example 10.2.4 -/
example : ¬ ∃ x, IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  rintro ⟨x, hx⟩
  rw [isMaxOn_iff] at hx
  obtain ⟨n, hn⟩ := exists_int_gt x
  have := hx (n:ℝ) ⟨n, Set.mem_univ n, rfl⟩
  simp only at this
  linarith

example : ¬ ∃ x, IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  rintro ⟨x, hx⟩
  rw [isMinOn_iff] at hx
  obtain ⟨n, hn⟩ := exists_int_lt x
  have := hx (n:ℝ) ⟨n, Set.mem_univ n, rfl⟩
  simp only at this
  linarith

example (n:ℤ) : IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by sorry

example (n:ℤ) : IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by sorry

/-- Remark 10.2.5 -/
theorem IsLocalMaxOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMaxOn f X x₀) : IsLocalMaxOn f Y x₀ :=
  h.filter_mono (nhdsWithin_mono _ hXY)

theorem IsLocalMinOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMinOn f X x₀) : IsLocalMinOn f Y x₀ :=
  h.filter_mono (nhdsWithin_mono _ hXY)

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMaxOn.deriv_eq_zero {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMaxOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  have hnhds : Set.Ioo a b ∈ nhds x₀ := Ioo_mem_nhds hx₀.1 hx₀.2
  exact (h.isLocalMax hnhds).hasDerivAt_eq_zero (hderiv.hasDerivAt hnhds)

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMinOn.deriv_eq_zero {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMinOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  have hnhds : Set.Ioo a b ∈ nhds x₀ := Ioo_mem_nhds hx₀.1 hx₀.2
  exact (h.isLocalMin hnhds).hasDerivAt_eq_zero (hderiv.hasDerivAt hnhds)

theorem IsMaxOn.deriv_eq_zero_counter : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ)
  (x₀:ℝ) (hx₀: x₀ ∈ Set.Icc a b) (h: IsMaxOn f (.Icc a b) x₀) (L:ℝ)
  (hderiv: HasDerivWithinAt f L (.Icc a b) x₀), L ≠ 0 := by
  refine ⟨0, 1, by norm_num, id, 1, by norm_num, ?_, 1, hasDerivWithinAt_id 1 _, by norm_num⟩
  rw [isMaxOn_iff]
  intro x hx
  exact (Set.mem_Icc.mp hx).2

/-- Theorem 10.2.7 (Rolle's theorem) / Exercise 10.2.4 -/
theorem _root_.HasDerivWithinAt.exist_zero {a b:ℝ} (hab: a < b) {g:ℝ → ℝ}
  (hcont: ContinuousOn g (.Icc a b)) (hderiv: DifferentiableOn ℝ g (.Ioo a b))
  (hgab: g a = g b) : ∃ x ∈ Set.Ioo a b, HasDerivWithinAt g 0 (.Ioo a b) x := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont hgab
    (fun x hx => ((hderiv x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt)
  refine ⟨c, hc, ?_⟩
  have hd : HasDerivAt g (deriv g c) c :=
    ((hderiv c hc).differentiableAt (Ioo_mem_nhds hc.1 hc.2)).hasDerivAt
  rw [hc0] at hd
  exact hd.hasDerivWithinAt

/-- Corollary 10.2.9 (Mean value theorem ) / Exercise 10.2.5 -/
theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_slope f (deriv f) hab hcont
    (fun x hx => ((hderiv x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt)
  refine ⟨c, hc, ?_⟩
  have hd : HasDerivAt f (deriv f c) c :=
    ((hderiv c hc).differentiableAt (Ioo_mem_nhds hc.1 hc.2)).hasDerivAt
  rw [hc0] at hd
  exact hd.hasDerivWithinAt

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (.Icc (-1) 1) ∧
  IsMaxOn f (.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (.Icc (-1) 1) 0 := by
  refine ⟨fun x => -|x|, by fun_prop, ?_, ?_⟩
  · rw [isMaxOn_iff]
    intro x _
    simp only [abs_zero, neg_zero]
    exact neg_nonpos_of_nonneg (abs_nonneg x)
  · intro h
    have h2 : DifferentiableWithinAt ℝ (fun x => |x|) (Set.Icc (-1:ℝ) 1) 0 := by
      simpa using h.neg
    exact not_differentiableAt_abs_zero
      (h2.differentiableAt (Icc_mem_nhds (by norm_num) (by norm_num)))

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (.Icc (-1) 1) 0 := by
  refine ⟨fun x => x^3, by fun_prop, ?_, ?_, ?_⟩
  · have : HasDerivAt (fun x:ℝ => x^3) 0 0 := by simpa using hasDerivAt_pow 3 (0:ℝ)
    exact this.hasDerivWithinAt
  · intro h
    have hlm := h.isLocalMax (Icc_mem_nhds (by norm_num) (by norm_num))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlm
    have h2 := hball (show dist (ε/2:ℝ) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    simp only at h2; nlinarith [hε, h2, pow_pos (show (0:ℝ) < ε/2 by linarith) 3]
  · intro h
    have hlm := h.isLocalMin (Icc_mem_nhds (by norm_num) (by norm_num))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlm
    have h2 := hball (show dist (-ε/2:ℝ) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith)
    simp only at h2; nlinarith [hε, h2, pow_pos (show (0:ℝ) < ε/2 by linarith) 3]

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b))
  (hderiv: DifferentiableOn ℝ f (.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  sorry

/-- Exercise 10.2.7 -/
theorem _root_.UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f .univ)
  (hderiv: DifferentiableOn ℝ f .univ)
  (hlip: BddOn (deriv f) .univ) :
  UniformContinuousOn f (.univ) := by
  sorry


end Chapter10
