import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) : BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  constructor
  · intro ⟨M, hM⟩
    exact ⟨⟨M, fun x hx => (abs_le.mp (hM x hx)).2⟩,
           ⟨M, fun x hx => by linarith [(abs_le.mp (hM x hx)).1]⟩⟩
  · intro ⟨⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩⟩
    exact ⟨max M₁ M₂, fun x hx => abs_le.mpr
      ⟨by have := hM₂ x hx; linarith [le_max_right M₁ M₂],
       by have := hM₁ x hx; linarith [le_max_left M₁ M₂]⟩⟩

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  rw [isBounded_iff_forall_norm_le]
  constructor
  · intro ⟨M, hM⟩
    exact ⟨M, fun y ⟨x, hx, hfx⟩ => by rw [← hfx, Real.norm_eq_abs]; exact hM x hx⟩
  · intro ⟨M, hM⟩
    exact ⟨M, fun x hx => by rw [← Real.norm_eq_abs]; exact hM _ ⟨x, hx, rfl⟩⟩

theorem BddOn.of_bounded {f :ℝ → ℝ} {X: Set ℝ} {M:ℝ} (h: ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

example : Continuous (fun x:ℝ ↦ x) := continuous_id

example : ¬ BddOn (fun x:ℝ ↦ x) .univ  := by
  intro ⟨M, hM⟩
  have := hM (M + 1) (Set.mem_univ _)
  linarith [abs_le.mp this]

example : BddOn (fun x:ℝ ↦ x) (.Icc 1 2) := by
  exact ⟨2, fun x hx => abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx; exact ne_of_gt hx.1

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  intro ⟨M, hM⟩
  have hM' : M ≥ 0 := by
    have := hM (1/2) (by norm_num)
    simp at this; linarith
  have h1 : (1:ℝ) / (M + 2) ∈ Set.Ioo 0 1 := by
    refine ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  have h2 := hM _ h1
  rw [abs_le] at h2
  have h3 : (fun x:ℝ ↦ 1/x) (1 / (M + 2)) = M + 2 := by simp [one_div_one_div]
  linarith [h2.2]

theorem why_7_6_3 {n: ℕ → ℕ} (hn: StrictMono n) (j:ℕ) : n j ≥ j := by
  induction j with
  | zero => omega
  | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hn (Nat.lt_succ_of_le le_rfl)))

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (_h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b) ) :
  BddOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound; simp at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n:ℕ): x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/- Definition 9.6.5.  Use the Mathlib `IsMaxOn` type. -/
#check isMaxOn_iff
#check isMinOn_iff

/-- Remark 9.6.6 -/
theorem BddAboveOn.isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMaxOn f X x₀): BddAboveOn f X := by
  exact ⟨f x₀, fun x hx => h hx⟩

theorem BddBelowOn.isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMinOn f X x₀): BddBelowOn f X := by
  exact ⟨-f x₀, fun x hx => by simp; exact h hx⟩

/-- Proposition 9.6.7 (Maximum principle) -/
theorem IsMaxOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sSup E
  have claim1 {y:ℝ} (hy: y ∈ E) : y ≤ m := le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  . obtain ⟨xmax, hxmax, hfmax⟩ := h
    exact ⟨xmax, hxmax, fun x hx => by rw [hfmax]; exact claim1 ⟨x, hx, rfl⟩⟩
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1:ℝ) < f x := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : m - 1/(n+1:ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_lt_csSup hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : m - 1/(n+1:ℝ) < f (x n) := (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmax)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmax) (fun j ↦ hx (n j))
  have hlower (j:ℕ) : m - 1/(j+1:ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j)); gcongr; grind
  have hupper (j:ℕ) : f (x (n j)) ≤ m := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1:ℝ)) (h := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub m (c:=0); simp
    . exact tendsto_const_nhds
    . intro _; grind
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm






theorem IsMinOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, IsMinOn f (.Icc a b) xmin := by
  obtain ⟨xmax, hxmax, hmax⟩ := IsMaxOn.of_continuous_on_compact h hf.neg
  refine ⟨xmax, hxmax, fun x hx => ?_⟩
  have := hmax hx
  simp only [Pi.neg_apply, neg_le_neg_iff] at this
  exact this

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) 2 := by
  intro x hx; simp; nlinarith [hx.1, hx.2, sq_nonneg x, sq_nonneg (x - 2), sq_nonneg (x + 2)]

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) (-2) := by
  intro x hx; simp; nlinarith [hx.1, hx.2, sq_nonneg x, sq_nonneg (x - 2), sq_nonneg (x + 2)]

theorem sSup.of_isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMaxOn f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMinOn f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

/-- Exercise 9.6.1 a) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ioo 1 2) ∧ BddOn f (.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀
  := by
  refine ⟨fun x => (x - 3/2)^2, by fun_prop, ⟨1/4, ?_⟩, 3/2, by norm_num, ?_, ?_⟩
  · intro x hx; rw [Set.mem_Ioo] at hx; rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]
  · rw [isMinOn_iff]; intro x _; nlinarith [sq_nonneg (x - 3/2)]
  · rintro ⟨x₀, hx₀, hmax⟩
    rw [Set.mem_Ioo] at hx₀; rw [isMaxOn_iff] at hmax
    have ht5 : |x₀ - 3/2| < 1/2 := by rw [abs_lt]; constructor <;> linarith [hx₀.1, hx₀.2]
    have hy : (3/2 + (|x₀ - 3/2|+1/2)/2) ∈ Set.Ioo (1:ℝ) 2 := by
      rw [Set.mem_Ioo]; constructor <;> nlinarith [abs_nonneg (x₀ - 3/2), ht5]
    have hle := hmax _ hy
    nlinarith [hle, sq_abs (x₀ - 3/2), abs_nonneg (x₀ - 3/2), ht5,
      mul_pos (by linarith [ht5] : (0:ℝ) < 1/2 - |x₀ - 3/2|)
              (by linarith [abs_nonneg (x₀ - 3/2)] : (0:ℝ) < 3*|x₀ - 3/2| + 1/2)]

/-- Exercise 9.6.1 b) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ici 0) ∧ BddOn f (.Ici 0) ∧
  ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀
  := by
  refine ⟨fun x => 1/(x+1), ?_, ?_, 0, Set.left_mem_Ici, ?_, ?_⟩
  · exact ContinuousOn.div continuousOn_const (by fun_prop)
      (fun x hx => by rw [Set.mem_Ici] at hx; intro h; linarith)
  · refine ⟨1, fun x hx => ?_⟩
    rw [Set.mem_Ici] at hx
    rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]; linarith
  · rw [isMaxOn_iff]; intro x hx
    rw [Set.mem_Ici] at hx
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · rintro ⟨x₀, hx₀, hmin⟩
    rw [Set.mem_Ici] at hx₀
    have hlt : 1/((x₀+1)+1) < 1/(x₀+1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    have hge := isMinOn_iff.1 hmin (x₀+1) (by rw [Set.mem_Ici]; linarith)
    simp only at hge
    linarith

/-- Exercise 9.6.1 c) -/
example : ∃ f: ℝ → ℝ, BddOn f (.Icc (-1) 1) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMinOn f (.Icc (-1) 1) x₀) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMaxOn f (.Icc (-1) 1) x₀)
  := by
  refine ⟨fun x => if |x| < 1 then x else 0, ?_, ?_, ?_⟩
  · refine ⟨1, fun x _ => ?_⟩
    show |(if |x| < 1 then x else 0)| ≤ 1
    split_ifs with h
    · exact le_of_lt h
    · simp
  · rintro ⟨x₀, _, hmin⟩
    rw [isMinOn_iff] at hmin
    by_cases h : |x₀| < 1
    · have h' := abs_lt.1 h
      have hymem : ((x₀-1)/2) ∈ Set.Icc (-1:ℝ) 1 := by rw [Set.mem_Icc]; constructor <;> linarith [h'.1, h'.2]
      have hyabs : |(x₀-1)/2| < 1 := by rw [abs_lt]; constructor <;> linarith [h'.1, h'.2]
      have := hmin _ hymem
      simp only [if_pos h, if_pos hyabs] at this
      linarith [h'.1]
    · have hymem : (-1/2:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by norm_num
      have := hmin _ hymem
      simp only [if_neg h, show |(-1/2:ℝ)| < 1 by norm_num, if_true] at this
      norm_num at this
  · rintro ⟨x₀, _, hmax⟩
    rw [isMaxOn_iff] at hmax
    by_cases h : |x₀| < 1
    · have h' := abs_lt.1 h
      have hymem : ((x₀+1)/2) ∈ Set.Icc (-1:ℝ) 1 := by rw [Set.mem_Icc]; constructor <;> linarith [h'.1, h'.2]
      have hyabs : |(x₀+1)/2| < 1 := by rw [abs_lt]; constructor <;> linarith [h'.1, h'.2]
      have := hmax _ hymem
      simp only [if_pos h, if_pos hyabs] at this
      linarith [h'.2]
    · have hymem : (1/2:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by norm_num
      have := hmax _ hymem
      simp only [if_neg h, show |(1/2:ℝ)| < 1 by norm_num, if_true] at this
      norm_num at this

/-- Exercise 9.6.1 d) -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (.Icc (-1) 1) ∧ ¬ BddBelowOn f (.Icc (-1) 1) := by
  refine ⟨fun x => 1/x, ?_, ?_⟩
  · rintro ⟨M, hM⟩
    have hpos : (0:ℝ) < 1/(|M|+2) := by positivity
    have hx : (1/(|M|+2)) ∈ Set.Icc (-1:ℝ) 1 :=
      ⟨by linarith, by rw [div_le_one (by positivity)]; nlinarith [abs_nonneg M]⟩
    have h := hM _ hx
    simp only [one_div_one_div] at h
    linarith [le_abs_self M]
  · rintro ⟨M, hM⟩
    have hpos : (0:ℝ) < 1/(|M|+2) := by positivity
    have hle1 : 1/(|M|+2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [abs_nonneg M]
    have hx : (-(1/(|M|+2))) ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := hM _ hx
    rw [show (fun x:ℝ => 1/x) (-(1/(|M|+2))) = -(|M|+2) by simp [one_div_one_div]] at h
    linarith [le_abs_self M]

/-- Exercise 9.6.2 -/
theorem BddOn.add (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f + g) X := by
  obtain ⟨Mf, hMf⟩ := hf; obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.1 (hMf x hx); obtain ⟨h3, h4⟩ := abs_le.1 (hMg x hx)
  simp only [Pi.add_apply]; rw [abs_le]; constructor <;> linarith

theorem BddOn.sub (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f - g) X := by
  obtain ⟨Mf, hMf⟩ := hf; obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.1 (hMf x hx); obtain ⟨h3, h4⟩ := abs_le.1 (hMg x hx)
  simp only [Pi.sub_apply]; rw [abs_le]; constructor <;> linarith

theorem BddOn.mul (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f * g) X := by
  obtain ⟨Mf, hMf⟩ := hf; obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf * Mg, fun x hx => ?_⟩
  have h1 := hMf x hx; have h2 := hMg x hx
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

def BddOn.div : Decidable (∀ (f g : ℝ → ℝ) (X : Set ℝ) (_ : ∀ x ∈ X, g x ≠ 0) (_ : BddOn f X)
    (_: BddOn g X), (BddOn (f / g) X)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  apply isFalse
  intro h
  obtain ⟨M, hM⟩ := h (fun _ => 1) (fun x => x) (Set.Ioo 0 1) (fun x hx => ne_of_gt hx.1)
    ⟨1, fun x _ => by norm_num⟩ ⟨1, fun x hx => by rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]⟩
  have hx : 1/(|M|+2) ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by positivity)]; nlinarith [abs_nonneg M]⟩
  have := hM _ hx
  simp only [Pi.div_apply, one_div_one_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ |M|+2)] at this
  linarith [le_abs_self M]

end Chapter9
