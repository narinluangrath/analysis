import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6
/-!
# Analysis I, Section 9.9: Uniform continuity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`UniformContinuousOn`.
- Continuous functions on compact intervals are uniformly continuous.

-/

open Chapter6 Filter

namespace Chapter9

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  sorry

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  sorry

/-- Example 9.9.1 -/
example (x : ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 1/11
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets f ε x₀ δ
  intro h
  simp only [f, ε, x₀, δ, div_one] at *
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have hxpos : (0:ℝ) < x := by linarith
  rw [abs_le]
  have ha : (0.9:ℝ) ≤ 1/x := by rw [le_div_iff₀ hxpos]; nlinarith
  have hb : (1:ℝ)/x ≤ 1.1 := by rw [div_le_iff₀ hxpos]; nlinarith
  constructor <;> linarith

example (x:ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 0.1
  let δ : ℝ := 1/1010
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets -merge f ε x₀ δ -- need the `-merge` flag due to the collision of `ε` and `x₀`
  intro h
  simp only [f, ε, x₀, δ] at *
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have hxpos : (0:ℝ) < x := by linarith
  rw [show (1:ℝ)/(0.1:ℝ) = 10 by norm_num, abs_le]
  have ha : (9.9:ℝ) ≤ 1/x := by rw [le_div_iff₀ hxpos]; nlinarith
  have hb : (1:ℝ)/x ≤ 10.1 := by rw [div_le_iff₀ hxpos]; nlinarith
  constructor <;> linarith

example (x:ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε x₀ δ
  intro h; simp only [g]; rw [show 2*x - 2*x₀ = 2*(x - x₀) from by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; simp only [ε, δ] at *; linarith

example (x₀ x : ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε δ
  intro h; simp only [g]; rw [show 2*x - 2*x₀ = 2*(x - x₀) from by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; simp only [ε, δ] at *; linarith

/-- Definition 9.9.2.  Here we use the Mathlib term {name}`UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  grind

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X :=
  hf.continuousOn

example : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 2) := by
  sorry

end Chapter9

/--
Definition 9.9.5.  This is similar but not identical to {name}`Real.CloseSeq` from
Section 6.1.
-/
abbrev Real.CloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.EventuallyCloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyCloseSeqs a b

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  a.equiv b ↔ ∀ ε > (0:ℚ), (ε:ℝ).EventuallyCloseSeqs a b := by
  constructor
  · intro h ε hε
    exact h (ε:ℝ) (by exact_mod_cast hε)
  · intro h ε hε
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    obtain ⟨N, hN, hm, hcl⟩ := h q (by exact_mod_cast hq0)
    refine ⟨N, hN, hm, fun n hn ↦ ?_⟩
    have := hcl n hn
    rw [Real.Close, Real.dist_eq] at this ⊢
    have hqle : ((q:ℝ)) ≤ ε := le_of_lt hqε
    linarith

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  a.equiv b ↔ atTop.Tendsto (fun n ↦ a n - b n) (nhds 0) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN, _, hclose⟩ := h (ε/2) (by linarith)
    refine ⟨max a.m N, fun n hn ↦ ?_⟩
    have h1 : n ≥ N := le_trans (le_max_right _ _) hn
    have hm : (a.from N).m = max a.m N := rfl
    have := hclose n (by rw [hm]; exact hn)
    rw [Sequence.from_eval a h1, Sequence.from_eval b h1, Real.Close, Real.dist_eq] at this
    rw [Real.dist_eq, sub_zero]; linarith
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    set M : ℤ := max (max a.m b.m) N with hMdef
    refine ⟨M, le_trans (le_max_left _ _) (le_max_left _ _), ?_, fun n hn ↦ ?_⟩
    · show max a.m M = max b.m M
      have h1 : a.m ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      have h2 : b.m ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      omega
    · have hmM : (a.from M).m = max a.m M := rfl
      have hnM : n ≥ M := by rw [hmM] at hn; exact le_trans (le_max_right _ _) hn
      have hnN : n ≥ N := le_trans (le_max_right _ _) hnM
      have := hN n hnN
      rw [Real.dist_eq, sub_zero] at this
      rw [Sequence.from_eval a hnM, Sequence.from_eval b hnM, Real.Close, Real.dist_eq]
      linarith


theorem Chapter6.Sequence.equiv_iff_coe (x y:ℕ → ℝ) :
  (x:Sequence).equiv (y:Sequence) ↔ atTop.Tendsto (fun n:ℕ ↦ x n - y n) (nhds 0) := by
  rw [Sequence.equiv_iff]
  have heval : ∀ n:ℤ, n ≥ 0 →
      (x:Sequence) n - (y:Sequence) n = x n.toNat - y n.toNat := by
    intro n hn
    simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le]
    rw [if_pos (by omega), if_pos (by omega)]
  rw [Metric.tendsto_atTop, Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N.toNat, fun n hn ↦ ?_⟩
    have := hN (n:ℤ) (by simp; omega); rw [Real.dist_eq] at this
    rw [heval n (by positivity)] at this
    rw [Real.dist_eq]; simpa using this
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨(N:ℤ), fun n hn ↦ ?_⟩
    have hn0 : n ≥ 0 := le_trans (Int.ofNat_nonneg N) hn
    rw [heval n hn0]
    have := hN n.toNat (by omega); rw [Real.dist_eq] at this ⊢; simpa using this

namespace Chapter9


/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  (x:Sequence).equiv (y:Sequence) →
  (f ∘ x:Sequence).equiv (f ∘ y:Sequence) := by
  constructor
  · intro hf x y hxX hyX hequiv
    rw [Chapter6.Sequence.equiv_iff_coe] at hequiv ⊢
    rw [UniformContinuousOn.iff] at hf
    rw [Metric.tendsto_atTop] at hequiv ⊢
    intro ε hε
    obtain ⟨δ, hδ, hfδ⟩ := hf (ε/2) (by linarith)
    obtain ⟨N, hN⟩ := hequiv δ hδ
    refine ⟨N, fun n hn ↦ ?_⟩
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    have := hfδ (y n) (hyX n) (x n) (hxX n) (by rw [Real.Close, Real.dist_eq]; linarith)
    rw [Real.Close, Real.dist_eq] at this
    simp only [Function.comp_apply]
    rw [Real.dist_eq, sub_zero]; linarith
  · intro hpres
    rw [UniformContinuousOn.iff]
    by_contra hcon
    push_neg at hcon
    obtain ⟨ε, hε, hbad⟩ := hcon
    choose a ha b hb hclose hsep using fun n:ℕ ↦ hbad (1/(n+1)) (by positivity)
    have hequiv : (b:Sequence).equiv (a:Sequence) := by
      rw [Chapter6.Sequence.equiv_iff_coe, Metric.tendsto_atTop]
      intro η hη
      obtain ⟨N, hNη⟩ := exists_nat_gt (1/η)
      refine ⟨N+1, fun n hn ↦ ?_⟩
      have hcn := hclose n
      rw [Real.Close, Real.dist_eq] at hcn
      rw [Real.dist_eq, sub_zero]
      have h1 : (1:ℝ)/(n+1) ≤ 1/(N+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N:ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
        linarith
      have hNpos : (0:ℝ) < N+1 := by positivity
      have h2 : 1/((N:ℝ)+1) < η := by
        rw [div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hη] at hNη
        nlinarith
      calc |b n - a n| ≤ 1/(n+1) := hcn
        _ ≤ 1/(N+1) := h1
        _ < η := h2
    have hfeq := hpres b a hb ha hequiv
    rw [Chapter6.Sequence.equiv_iff_coe, Metric.tendsto_atTop] at hfeq
    obtain ⟨N, hN⟩ := hfeq ε hε
    have hs := hsep N
    rw [Real.dist_eq] at hs
    have hle : |f (b N) - f (a N)| < ε := by
      have hh := hN N (le_refl N); simp only [Function.comp_apply] at hh
      rw [Real.dist_eq, sub_zero] at hh; exact hh
    linarith

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : atTop.Tendsto x (nhds x₀) ↔
  (x:Sequence).equiv (fun n:ℕ ↦ x₀:Sequence) := by
  rw [Sequence.equiv_iff]
  have heval : ∀ n:ℤ, n ≥ 0 →
      (x:Sequence) n - ((fun _:ℕ ↦ x₀):Sequence) n = x n.toNat - x₀ := by
    intro n hn
    simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le]
    rw [if_pos (by omega), if_pos (by omega)]
  rw [Metric.tendsto_atTop, Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨(N:ℤ), fun n hn ↦ ?_⟩
    have hn0 : n ≥ 0 := le_trans (Int.ofNat_nonneg N) hn
    rw [heval n hn0]
    have := hN n.toNat (by omega); rw [Real.dist_eq] at this ⊢; simpa using this
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N.toNat, fun n hn ↦ ?_⟩
    have := hN (n:ℤ) (by simp; omega); rw [Real.dist_eq] at this
    rw [heval n (by positivity)] at this
    simpa using this


/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

example : (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence).equiv (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff_coe]
  have h1 : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : atTop.Tendsto (fun n:ℕ ↦ 1/(2*(n+1):ℝ)) (nhds 0) := by
    have h3 := h1.const_mul (1/2:ℝ)
    rw [mul_zero] at h3
    refine h3.congr (fun n ↦ ?_)
    rw [mul_one_div, div_div]
  have := h1.sub h2; rw [sub_zero] at this; exact this

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  refine ⟨by positivity, ?_⟩
  have : (n:ℝ) + 1 > 0 := by positivity
  rw [div_lt_iff₀ this]; linarith

example (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by
  refine ⟨by positivity, ?_⟩
  have : 2 * ((n:ℝ) + 1) > 0 := by positivity
  rw [div_lt_iff₀ this]; nlinarith

example : ¬ (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence).equiv (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff_coe]
  intro h
  have heq : (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)) - f_9_9_10 (1/(2*(n+1):ℝ)))
      = (fun n:ℕ ↦ -(n+1:ℝ)) := by
    funext n
    simp only [f_9_9_10, one_div_one_div]
    ring
  rw [heq] at h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have hd := hN N (le_refl N)
  rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)] at hd
  have : (N:ℝ) ≥ 0 := by positivity
  linarith

example : ¬ UniformContinuousOn f_9_9_10 (.Ioo 0 2) := by
  intro hU
  rw [UniformContinuousOn.iff_preserves_equiv] at hU
  have hxmem : ∀ n:ℕ, (1/(n+1:ℝ)) ∈ Set.Ioo (0:ℝ) 2 := by
    intro n; refine ⟨by positivity, ?_⟩
    have : (n:ℝ)+1 > 0 := by positivity
    rw [div_lt_iff₀ this]; linarith
  have hymem : ∀ n:ℕ, (1/(2*(n+1):ℝ)) ∈ Set.Ioo (0:ℝ) 2 := by
    intro n; refine ⟨by positivity, ?_⟩
    have : 2*((n:ℝ)+1) > 0 := by positivity
    rw [div_lt_iff₀ this]; nlinarith
  have hequiv : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ 1/(2*(n+1):ℝ)):Sequence) := by
    rw [Chapter6.Sequence.equiv_iff_coe]
    have h1 : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : atTop.Tendsto (fun n:ℕ ↦ 1/(2*(n+1):ℝ)) (nhds 0) := by
      have h3 := h1.const_mul (1/2:ℝ); rw [mul_zero] at h3
      refine h3.congr (fun n ↦ ?_); rw [mul_one_div, div_div]
    have := h1.sub h2; rw [sub_zero] at this; exact this
  have := hU (fun n:ℕ ↦ 1/(n+1:ℝ)) (fun n:ℕ ↦ 1/(2*(n+1):ℝ)) hxmem hymem hequiv
  -- this : (f_9_9_10 ∘ x).equiv (f_9_9_10 ∘ y), contradiction with non-equiv
  rw [Chapter6.Sequence.equiv_iff_coe, Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this 1 one_pos
  have hd := hN N (le_refl N)
  simp only [Function.comp_apply, f_9_9_10, one_div_one_div] at hd
  rw [Real.dist_eq, sub_zero] at hd
  have : |((N:ℝ)+1) - (2*((N:ℝ)+1))| = (N:ℝ)+1 := by
    rw [show ((N:ℝ)+1) - (2*((N:ℝ)+1)) = -((N:ℝ)+1) by ring, abs_neg, abs_of_pos (by positivity)]
  rw [this] at hd
  have : (N:ℝ) ≥ 0 := by positivity
  linarith

/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

example : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff_coe]
  have h1 : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := h1.neg; rw [neg_zero] at h2
  refine h2.congr (fun n ↦ ?_); ring

example : ¬ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff_coe]
  intro h
  have heq : (fun n:ℕ ↦ f_9_9_11 (n+1:ℝ) - f_9_9_11 ((n+1)+1/(n+1:ℝ)))
      = (fun n:ℕ ↦ -2 - 1/(n+1:ℝ)^2) := by
    funext n
    simp only [f_9_9_11]
    have hn : (n:ℝ)+1 > 0 := by positivity
    field_simp
    ring
  rw [heq] at h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have hd := hN N (le_refl N)
  rw [Real.dist_eq, sub_zero] at hd
  have hpos : (0:ℝ) < 1/((N:ℝ)+1)^2 := by positivity
  rw [abs_of_neg (by nlinarith)] at hd
  nlinarith

example : ¬ UniformContinuousOn f_9_9_11 .univ := by
  intro hU
  rw [UniformContinuousOn.iff_preserves_equiv] at hU
  have hequiv : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
    rw [Chapter6.Sequence.equiv_iff_coe]
    have h1 : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.neg; rw [neg_zero] at h2
    refine h2.congr (fun n ↦ ?_); ring
  have := hU (fun n:ℕ ↦ (n+1:ℝ)) (fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)) (fun n ↦ Set.mem_univ _) (fun n ↦ Set.mem_univ _) hequiv
  rw [Chapter6.Sequence.equiv_iff_coe, Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this 1 one_pos
  have hd := hN N (le_refl N)
  simp only [Function.comp_apply, f_9_9_11] at hd
  rw [Real.dist_eq, sub_zero] at hd
  have hn : (N:ℝ)+1 > 0 := by positivity
  have heq : ((N:ℝ)+1)^2 - ((N+1)+1/((N:ℝ)+1))^2 = -2 - 1/((N:ℝ)+1)^2 := by
    field_simp; ring
  rw [heq] at hd
  have hpos : (0:ℝ) < 1/((N:ℝ)+1)^2 := by positivity
  rw [abs_of_neg (by nlinarith)] at hd
  nlinarith

/-- Proposition 9.9.12 / Exercise 9.9.3  -/
theorem UniformContinuousOn.ofCauchy  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x: ℕ → ℝ} (hx: (x:Sequence).IsCauchy) (hmem : ∀ n, x n ∈ X) :
  (f ∘ x:Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  rw [Sequence.IsCauchy.coe] at hx
  rw [UniformContinuousOn.iff] at hf
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  obtain ⟨N, hN⟩ := hx δ hδ
  refine ⟨N, fun j hj k hk ↦ ?_⟩
  have hd := hN j hj k hk
  have := hfδ (x k) (hmem k) (x j) (hmem j) (by rw [Real.Close]; exact hd)
  rw [Real.Close] at this
  simpa using this

/-- Example 9.9.13 -/
example : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  have hconv : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcau := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcau
  intro ε hε
  obtain ⟨N, hN⟩ := hcau ε hε
  exact ⟨N, fun j hj k hk ↦ (hN j hj k hk).le⟩

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  refine ⟨by positivity, ?_⟩
  have : (n:ℝ) + 1 > 0 := by positivity
  rw [div_lt_iff₀ this]; linarith

example : ¬ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  have hd := hN N (le_refl N) (N+1) (by omega)
  have he : ∀ m:ℕ, f_9_9_10 (1/(m+1:ℝ)) = (m+1:ℝ) := by
    intro m; simp only [f_9_9_10, one_div_one_div]
  rw [he, he, Real.dist_eq] at hd
  have : |(N:ℝ)+1 - ((N+1:ℕ)+1)| = 1 := by push_cast; rw [show (N:ℝ)+1-(N+1+1) = -1 by ring]; norm_num
  rw [this] at hd; linarith

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  intro hU
  rw [UniformContinuousOn.iff_preserves_equiv] at hU
  have hxmem : ∀ n:ℕ, (1/(n+1:ℝ)) ∈ Set.Ioo (0:ℝ) 2 := by
    intro n; refine ⟨by positivity, ?_⟩
    have : (n:ℝ)+1 > 0 := by positivity
    rw [div_lt_iff₀ this]; linarith
  have hymem : ∀ n:ℕ, (1/(2*(n+1):ℝ)) ∈ Set.Ioo (0:ℝ) 2 := by
    intro n; refine ⟨by positivity, ?_⟩
    have : 2*((n:ℝ)+1) > 0 := by positivity
    rw [div_lt_iff₀ this]; nlinarith
  have hequiv : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ 1/(2*(n+1):ℝ)):Sequence) := by
    rw [Chapter6.Sequence.equiv_iff_coe]
    have h1 : atTop.Tendsto (fun n:ℕ ↦ 1/(n+1:ℝ)) (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : atTop.Tendsto (fun n:ℕ ↦ 1/(2*(n+1):ℝ)) (nhds 0) := by
      have h3 := h1.const_mul (1/2:ℝ); rw [mul_zero] at h3
      refine h3.congr (fun n ↦ ?_); rw [mul_one_div, div_div]
    have := h1.sub h2; rw [sub_zero] at this; exact this
  have := hU (fun n:ℕ ↦ 1/(n+1:ℝ)) (fun n:ℕ ↦ 1/(2*(n+1):ℝ)) hxmem hymem hequiv
  -- this : (f_9_9_10 ∘ x).equiv (f_9_9_10 ∘ y), contradiction with non-equiv
  rw [Chapter6.Sequence.equiv_iff_coe, Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this 1 one_pos
  have hd := hN N (le_refl N)
  simp only [Function.comp_apply, f_9_9_10, one_div_one_div] at hd
  rw [Real.dist_eq, sub_zero] at hd
  have : |((N:ℝ)+1) - (2*((N:ℝ)+1))| = (N:ℝ)+1 := by
    rw [show ((N:ℝ)+1) - (2*((N:ℝ)+1)) = -((N:ℝ)+1) by ring, abs_neg, abs_of_pos (by positivity)]
  rw [this] at hd
  have : (N:ℝ) ≥ 0 := by positivity
  linarith

/-- Corollary 9.9.14 / Exercise 9.9.4 -/
theorem UniformContinuousOn.limit_at_adherent  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x₀:ℝ} (hx₀: AdherentPt x₀ X) :
  ∃ L:ℝ, (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  rw [AdherentPt_def] at hx₀
  haveI : (nhdsWithin x₀ X).NeBot := hx₀
  rw [UniformContinuousOn.iff] at hf
  have hcau : Cauchy (Filter.map f (nhdsWithin x₀ X)) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hfδ⟩ := hf (ε/2) (by linarith)
    refine ⟨f '' (X ∩ Metric.ball x₀ (δ/2)), ?_, ?_⟩
    · rw [Filter.mem_map]
      have hmem : X ∩ Metric.ball x₀ (δ/2) ∈ nhdsWithin x₀ X := by
        rw [mem_nhdsWithin]
        exact ⟨Metric.ball x₀ (δ/2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith), by rw [Set.inter_comm]⟩
      apply Filter.mem_of_superset hmem
      intro y hy; exact Set.mem_image_of_mem f hy
    · rintro u ⟨a, ⟨haX, hab⟩, rfl⟩ v ⟨b, ⟨hbX, hbb⟩, rfl⟩
      rw [Metric.mem_ball, Real.dist_eq] at hab hbb
      have hclose : δ.Close a b := by
        rw [Real.Close, Real.dist_eq]
        have htri : |a - b| ≤ |a - x₀| + |b - x₀| := by
          have := abs_sub_le a x₀ b
          rw [abs_sub_comm x₀ b] at this; linarith
        linarith
      have hf2 := hfδ b hbX a haX hclose
      rw [Real.Close, Real.dist_eq] at hf2
      rw [Real.dist_eq]; linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcau
  exact ⟨L, hL⟩

/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  have hu : UniformContinuous (E.restrict f) := (hf.mono hEX).restrict
  have htb : TotallyBounded E := hE.isCompact_closure.totallyBounded.subset (subset_closure E)
  have hi : IsUniformInducing ((↑) : E → ℝ) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have htbU : TotallyBounded (Set.univ : Set E) := by
    apply (totallyBounded_image_iff hi).1
    have : (Subtype.val '' (Set.univ : Set E)) = E := by simp
    rw [this]; exact htb
  have himg : TotallyBounded (E.restrict f '' Set.univ) := htbU.image hu
  have heq : E.restrict f '' Set.univ = f '' E := by
    rw [Set.image_univ, Set.restrict_eq, Set.range_comp]; simp
  rw [heq] at himg
  exact himg.isBounded

/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) :
  UniformContinuousOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; rw [iff_preserves_equiv] at h
  simp [-Set.mem_Icc] at h
  choose x hx y hy hequiv ε hε h using h
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace hclose2 : ε.EventuallyCloseSeqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      have hfin : (E : Set ℕ).Finite := Set.toFinite E
      obtain ⟨M, hM⟩ := hfin.bddAbove
      refine ⟨(M:ℤ)+1, by positivity, ?_, ?_⟩
      · show max (0:ℤ) ((M:ℤ)+1) = max (0:ℤ) ((M:ℤ)+1); rfl
      · intro p hp
        have hpm : (Sequence.from (fun n ↦ f (x n):Sequence) ((M:ℤ)+1)).m = max 0 ((M:ℤ)+1) := rfl
        rw [hpm] at hp
        have hp1 : p ≥ (M:ℤ)+1 := le_trans (le_max_right _ _) hp
        have hp0 : p ≥ 0 := le_trans (le_max_left _ _) hp
        rw [Sequence.from_eval _ hp1, Sequence.from_eval _ hp1]
        simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le]
        rw [if_pos (by omega), if_pos (by omega)]
        have hnotmem : p.toNat ∉ E := by
          intro hmem
          have : (p.toNat : ℕ) ≤ M := hM hmem
          omega
        simp only [E, Set.mem_setOf_eq, not_not] at hnotmem
        exact hnotmem
    obtain ⟨N, hN, _, hcl⟩ := hclose2
    obtain ⟨q, hq0, hqN, hqclose⟩ := h N (by omega)
    have hmN : (Sequence.from (fun n ↦ f (x n):Sequence) N).m = max 0 N := rfl
    have := hcl q (by rw [hmN]; exact max_le (by omega) hqN)
    rw [Sequence.from_eval _ hqN, Sequence.from_eval _ hqN] at this
    simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le] at this
    rw [if_pos (by omega), if_pos (by omega)] at this
    simp only [Real.Close, Real.dist_eq] at this
    simp only [hq0, hqN, and_self, if_true] at hqclose
    rw [Real.dist_eq] at hqclose
    linarith
  observe : Countable E
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by apply_rules [Nat.nth_strictMono]
  have hmem (j:ℕ) : n j ∈ E := j.nth_mem_of_infinite hE
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simpa [E, Real.Close, Real.dist_eq] using hmem
  observe hxmem : ∀ j, x (n j) ∈ Set.Icc a b
  observe hymem : ∀ j, y (n j) ∈ Set.Icc a b
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := hconv.comp_of_continuous hcont (fun k ↦ hxmem (j k))
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : atTop.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) (nhds 0) := by
    observe hj' : atTop.Tendsto j .atTop
    observe hn' : atTop.Tendsto n .atTop
    observe hcoe : atTop.Tendsto (fun n:ℕ ↦ (n:ℤ)) .atTop
    exact hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : atTop.Tendsto (fun k ↦ y (n (j k))) (nhds L) := by
    convert hconv.sub hequiv with k
    . abel
    simp
  replace hyconv := hyconv.comp_of_continuous hcont (fun k ↦ hymem (j k))
  have hcontra : atTop.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) (nhds 0) := by
    convert hconv'.sub hyconv; simp
  rw [Metric.tendsto_atTop] at hcontra
  obtain ⟨K, hK⟩ := hcontra ε hε
  have hd := hK K (le_refl K)
  rw [Real.dist_eq, sub_zero] at hd
  have := hsep (j K)
  linarith


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  rw [UniformContinuousOn.iff] at *
  intro ε hε
  obtain ⟨δ', hδ', hg'⟩ := hg ε hε
  obtain ⟨δ, hδ, hf'⟩ := hf δ' hδ'
  refine ⟨δ, hδ, fun x₀ hx₀ x hx hclose ↦ ?_⟩
  have hfx₀ : f x₀ ∈ Y := hrange ⟨x₀, hx₀, rfl⟩
  have hfx : f x ∈ Y := hrange ⟨x, hx, rfl⟩
  exact hg' (f x₀) hfx₀ (f x) hfx (hf' x₀ hx₀ x hx hclose)

end Chapter9
