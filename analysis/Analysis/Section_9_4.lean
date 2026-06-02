import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_9_3

/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/

namespace Chapter9

/-- Definition 9.4.1.  Here we use the Mathlib definition of continuity.  The hypothesis `x ∈ X` is not needed! -/
theorem ContinuousWithinAt.iff (X:Set ℝ) (f: ℝ → ℝ)  (x₀:ℝ) :
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ := by
  rw [ContinuousWithinAt.eq_1, Convergesto.iff, nhdsWithin.eq_1]

#check ContinuousOn.eq_1
#check continuousOn_univ
#check continuousWithinAt_univ

/-- Example 9.4.2 --/
example (c x₀:ℝ) : ContinuousWithinAt (fun x ↦ c) .univ x₀ := continuousWithinAt_const

example (c x₀:ℝ) : ContinuousAt (fun x ↦ c) x₀ := continuousAt_const

example (c:ℝ) : ContinuousOn (fun x:ℝ ↦ c) .univ := continuousOn_const

example (c:ℝ) : Continuous (fun x:ℝ ↦ c) := continuous_const

/-- Example 9.4.3 --/
example : Continuous (fun x:ℝ ↦ x) := continuous_id

/-- Example 9.4.4 --/
example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt Real.sign x₀ := by
  rcases lt_or_gt_of_ne h with hx | hx
  · refine (continuousAt_const (y := (-1:ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy using (Real.sign_of_neg hy).symm
  · refine (continuousAt_const (y := (1:ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy using (Real.sign_of_pos hy).symm

example  :¬ ContinuousAt Real.sign 0 := by
  intro hcont
  have h1 : Filter.Tendsto Real.sign (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sign 0)) :=
    hcont.continuousWithinAt.tendsto
  have h2 : Filter.Tendsto Real.sign (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [self_mem_nhdsWithin] with x hx using Real.sign_of_pos hx
  have := tendsto_nhds_unique h1 h2
  rw [Real.sign_zero] at this
  norm_num at this

/-- Example 9.4.5 --/
example (x₀:ℝ) : ¬ ContinuousAt f_9_3_21 x₀ := by
  intro hcont
  obtain ⟨a, ha_mem, ha_lim⟩ := mem_closure_iff_seq_limit.mp (Rat.denseRange_cast x₀)
  obtain ⟨b, hb_mem, hb_lim⟩ := mem_closure_iff_seq_limit.mp (dense_irrational x₀)
  have hfa : Filter.Tendsto (fun n => f_9_3_21 (a n)) Filter.atTop (nhds (f_9_3_21 x₀)) :=
    hcont.tendsto.comp ha_lim
  have hfb : Filter.Tendsto (fun n => f_9_3_21 (b n)) Filter.atTop (nhds (f_9_3_21 x₀)) :=
    hcont.tendsto.comp hb_lim
  have ha1 : ∀ n, f_9_3_21 (a n) = 1 := fun n => by
    obtain ⟨q, hq⟩ := ha_mem n
    simp only [f_9_3_21]; rw [if_pos ⟨q, Set.mem_univ q, hq⟩]
  have hb0 : ∀ n, f_9_3_21 (b n) = 0 := fun n => by
    simp only [f_9_3_21]; rw [if_neg]
    rintro ⟨q, -, hq⟩; exact hb_mem n ⟨q, hq⟩
  rw [Filter.tendsto_congr ha1] at hfa
  rw [Filter.tendsto_congr hb0] at hfb
  have e1 : f_9_3_21 x₀ = 1 := tendsto_nhds_unique hfa tendsto_const_nhds
  have e0 : f_9_3_21 x₀ = 0 := tendsto_nhds_unique hfb tendsto_const_nhds
  rw [e1] at e0; norm_num at e0

/-- Example 9.4.6 --/
noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt f_9_4_6 x₀ := by
  rcases lt_or_gt_of_ne h with hx | hx
  · refine (continuousAt_const (y := (0:ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    have : ¬ (y ≥ 0) := by simp only [Set.mem_Iio] at hy; linarith
    simp [f_9_4_6, this]
  · refine (continuousAt_const (y := (1:ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have : y ≥ 0 := by simp only [Set.mem_Ioi] at hy; linarith
    simp [f_9_4_6, this]

example : ¬ ContinuousAt f_9_4_6 0 := by
  intro hcont
  have h1 : Filter.Tendsto f_9_4_6 (nhdsWithin 0 (Set.Iio 0)) (nhds (f_9_4_6 0)) :=
    hcont.continuousWithinAt.tendsto
  have h2 : Filter.Tendsto f_9_4_6 (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : ¬ (x ≥ 0) := by simp only [Set.mem_Iio] at hx; linarith
    simp [f_9_4_6, this]
  have := tendsto_nhds_unique h1 h2
  simp [f_9_4_6] at this

example : ContinuousWithinAt f_9_4_6 (.Ici 0) 0 := by
  show Filter.Tendsto f_9_4_6 (nhdsWithin 0 (Set.Ici 0)) (nhds (f_9_4_6 0))
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [f_9_4_6, Set.mem_Ici.mp hx]

/-- Proposition 9.4.7 / Exercise 9.4.1.  It is possible that the hypothesis `x₀ ∈ X` is unnecessary. -/
theorem ContinuousWithinAt.tfae (X:Set ℝ) (f: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X) :
  [
    ContinuousWithinAt f X x₀,
    ∀ a:ℕ → ℝ, (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds x₀) → Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)),
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| < δ → |f x - f x₀| < ε
  ].TFAE := by
  sorry

/-- Remark 9.4.8 --/
theorem _root_.Filter.Tendsto.comp_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h : x₀ ∈ X)
  (h_cont: ContinuousWithinAt f X x₀) {a: ℕ → ℝ} (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)):
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) := by
  have := (ContinuousWithinAt.tfae X f h).out 0 1
  grind

/- Proposition 9.4.9 -/
theorem ContinuousWithinAt.add {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f + g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.add (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.sub {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f - g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.sub (AdherentPt.of_mem h) hg using 1

theorem ContinuousWithinAt.max {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (max f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.max (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.min {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (min f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.min (AdherentPt.of_mem h) hg using 1


theorem ContinuousWithinAt.mul' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f * g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.mul (AdherentPt.of_mem h) hg using 1

theorem ContinuousWithinAt.div' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (h : x₀ ∈ X) (hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f / g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.div (AdherentPt.of_mem h) hM hg using 1

/-- Proposition 9.4.10 / Exercise 9.4.3  -/
theorem Continuous.exp {a:ℝ} (ha: a>0) : Continuous (fun x:ℝ ↦ a ^ x) :=
  Real.continuous_const_rpow (ne_of_gt ha)

/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inl (Set.mem_Ioi.mp hx).ne')).continuousWithinAt

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := continuous_abs

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) {x₀:ℝ} (hx₀: x ∈ X) (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)): ContinuousWithinAt (g ∘ f) X x₀ :=
  _root_.ContinuousWithinAt.comp hg_cont hf_cont hf

/-- Example 9.4.14 -/
example : Continuous (fun x:ℝ ↦ 3*x + 1) := by fun_prop

example : Continuous (fun x:ℝ ↦ (5:ℝ)^x) := Real.continuous_const_rpow (by norm_num)

example : Continuous (fun x:ℝ ↦ (5:ℝ)^(3*x+1)) :=
  (Real.continuous_const_rpow (by norm_num)).comp (by fun_prop)

example : Continuous (fun x:ℝ ↦ |x^2-8*x+8|^(Real.sqrt 2) / (x^2 + 1)) := by
  apply Continuous.div
  · exact (continuous_abs.comp (by fun_prop)).rpow_const (fun x => Or.inr (Real.sqrt_nonneg 2))
  · fun_prop
  · intro x; positivity

/-- Exercise 9.4.6 -/
theorem ContinuousOn.restrict {X Y:Set ℝ} {f: ℝ → ℝ} (hY: Y ⊆ X) (hf: ContinuousOn f X) : ContinuousOn f Y :=
  hf.mono hY

/-- Exercise 9.4.7 -/
theorem Continuous.polynomial {n:ℕ} (c: Fin n → ℝ) : Continuous (fun x:ℝ ↦ ∑ i, c i * x ^ (i:ℕ)) := by
  apply continuous_finset_sum
  intro i _
  fun_prop
