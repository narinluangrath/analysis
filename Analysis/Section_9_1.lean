import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Analysis.Section_6_4
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/

variable (I : Type*)

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ := Set.Icc_eq_empty (not_le.mpr h)

example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ := Set.Ico_eq_empty (not_lt.mpr h)

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ := Set.Ioc_eq_empty (not_lt.mpr h)

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ := Set.Ioo_eq_empty (not_lt.mpr h)

example {a b: EReal} (h: a = b) : Set.Icc a b = {a} := by
  subst h; exact Set.Icc_self a

/--
Definition 9.1.5.  Note that a slightly different {name}`Real.Adherent` was defined in
Chapter 6.4
-/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  refine ⟨0.9, by norm_num [Set.mem_Ioo], ?_⟩
  rw [abs_le]; norm_num

example : ¬ (0.1:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  rintro ⟨y, hy, hle⟩
  simp only [Set.mem_Ioo] at hy
  rw [abs_le] at hle
  linarith [hy.2, hle.2]

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by
  refine ⟨1, by norm_num, ?_⟩
  rw [abs_le]; norm_num


namespace Chapter9

/-- Definition 9.1.-/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (.Ioo 0 1) := by
  intro ε hε
  have hm : (0:ℝ) < min ε 1 := lt_min hε one_pos
  refine ⟨1 - min ε 1 / 2, ?_, ?_⟩
  · simp only [Set.mem_Ioo]
    constructor <;> nlinarith [min_le_right ε 1, min_le_left ε 1]
  · rw [show (1:ℝ) - (1 - min ε 1 / 2) = min ε 1 / 2 by ring, abs_of_nonneg (by linarith)]
    nlinarith [min_le_left ε 1]

example : ¬ AdherentPt 2 (.Ioo 0 1) := by
  intro h
  obtain ⟨y, hy, hle⟩ := h (1/2) (by norm_num)
  simp only [Set.mem_Ioo] at hy
  rw [abs_le] at hle
  linarith [hy.2, hle.2]

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathilb version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := _root_.subset_closure

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := _root_.closure_union

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
  closure_inter_subset_inter_closure X Y

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := closure_mono h

/-- Exercise 9.1.6 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by
  apply Set.Subset.antisymm
  · calc closure Y ⊆ closure (closure X) := closure_mono h'
      _ = closure X := closure_closure
  · exact closure_mono h

/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (.Ioo a b) = .Icc a b :=
  closure_Ioo (ne_of_lt h)

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (.Ioc a b) = .Icc a b :=
  closure_Ioc (ne_of_lt h)

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (.Ico a b) = .Icc a b :=
  closure_Ico (ne_of_lt h)

theorem closure_of_Icc {a b:ℝ} (h:a ≤ b) : closure (.Icc a b) = .Icc a b :=
  closure_Icc a b

theorem closure_of_Ioi {a:ℝ} : closure (.Ioi a) = .Ici a := closure_Ioi a

theorem closure_of_Ici {a:ℝ} : closure (.Ici a) = .Ici a := isClosed_Ici.closure_eq

theorem closure_of_Iio {a:ℝ} : closure (.Iio a) = .Iic a := closure_Iio a

theorem closure_of_Iic {a:ℝ} : closure (.Iic a) = .Iic a := isClosed_Iic.closure_eq

theorem closure_of_R : closure (.univ: Set ℝ) = .univ := closure_univ

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' .univ) = ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
    rw [Set.image_univ]; exact Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' .univ) = ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
    rw [Set.image_univ]; exact Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' .univ) = .univ := by
    rw [Set.image_univ]; exact Rat.denseRange_cast.closure_range

/-- Lemma 9.1.14 / Exercise 9.1.4-/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.atTop.Tendsto a (nhds x) := by
    rw [← closure_def', mem_closure_iff_seq_limit]

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} : IsClosed (.Icc a b) := isClosed_Icc

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (.Ici a) := isClosed_Ici

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (.Iic a) := isClosed_Iic

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (.univ : Set ℝ) := isClosed_univ

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ico a b) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [closure_Ico (ne_of_lt h)] at h2
  have hb : b ∈ Set.Ico a b := h2 ▸ Set.right_mem_Icc.mpr h.le
  exact absurd hb.2 (lt_irrefl b)

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioc a b) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [closure_Ioc (ne_of_lt h)] at h2
  have ha : a ∈ Set.Ioc a b := h2 ▸ Set.left_mem_Icc.mpr h.le
  exact absurd ha.1 (lt_irrefl a)

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioo a b) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [closure_Ioo (ne_of_lt h)] at h2
  have ha : a ∈ Set.Ioo a b := h2 ▸ Set.left_mem_Icc.mpr h.le
  exact absurd ha.1 (lt_irrefl a)

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (.Ioi a) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [closure_Ioi] at h2
  have ha : a ∈ Set.Ioi a := h2 ▸ Set.left_mem_Ici
  exact absurd ha (lt_irrefl a)

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (.Iio a) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [closure_Iio] at h2
  have ha : a ∈ Set.Iio a := h2 ▸ Set.right_mem_Iic
  exact absurd ha (lt_irrefl a)

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [Set.image_univ]; exact Nat.isClosedEmbedding_coe_real.isClosed_range

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [Set.image_univ]; exact Int.isClosedEmbedding_coe_real.isClosed_range

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  intro hcl
  have h2 := hcl.closure_eq
  rw [Set.image_univ, Rat.denseRange_cast.closure_range] at h2
  obtain ⟨x, hx⟩ := exists_irrational_btwn (show (0:ℝ) < 1 by norm_num)
  have : x ∈ Set.range (fun n:ℚ ↦ (n:ℝ)) := h2 ▸ Set.mem_univ x
  obtain ⟨q, hq⟩ := this
  exact hx.1 ⟨q, hq⟩

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's {name}`AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.18 (Isolated points) -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((.Ioo 1 2) ∪ {3}) :=
  AdherentPt.of_mem (Set.mem_union_right _ (Set.mem_singleton 3))

example : ¬ LimitPt 3 ((.Ioo 1 2) ∪ {3}) := by
  intro h
  obtain ⟨y, hy, hle⟩ := h (1/2) (by norm_num)
  simp only [Set.mem_diff, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff] at hy
  rw [abs_le] at hle
  obtain ⟨hyin, hyne⟩ := hy
  rcases hyin with ⟨h1, h2⟩ | h3
  · linarith [hle.2]
  · exact hyne h3

example : IsolatedPt 3 ((.Ioo 1 2) ∪ {3}) := by
  refine ⟨Set.mem_union_right _ (Set.mem_singleton 3), 1/2, by norm_num, ?_⟩
  intro y hy
  simp only [Set.mem_diff, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff] at hy
  obtain ⟨hyin, hyne⟩ := hy
  rcases hyin with ⟨h1, h2⟩ | h3
  · rw [gt_iff_lt, abs_of_pos (show (0:ℝ) < 3 - y by linarith)]; linarith
  · exact absurd h3 hyne

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [limit_of_AdherentPt]

/-- Helper: `x` is a limit point of `X` whenever some open subinterval of `X` with `x` removed has `x` in its
closure. -/
private theorem limitpt_of_sub {X: Set ℝ} {x p q:ℝ} (hpq: Set.Ioo p q ⊆ X \ {x})
    (hxc: x ∈ closure (Set.Ioo p q)) : LimitPt x X :=
  (closure_def' (X \ {x}) x).mp (closure_mono hpq hxc)

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (.Icc a b) := by
  obtain ⟨ha, hb⟩ := hx
  by_cases hxb : x < b
  · apply limitpt_of_sub (p := x) (q := b)
    · intro y hy; exact ⟨⟨ha.trans hy.1.le, hy.2.le⟩, (ne_of_lt hy.1).symm⟩
    · rw [closure_Ioo (ne_of_lt hxb)]; exact Set.left_mem_Icc.mpr hxb.le
  · have hax : a < x := by push_neg at hxb; linarith
    apply limitpt_of_sub (p := a) (q := x)
    · intro y hy; exact ⟨⟨hy.1.le, hy.2.le.trans hb⟩, (ne_of_lt hy.2)⟩
    · rw [closure_Ioo (ne_of_lt hax)]; exact Set.right_mem_Icc.mpr hax.le

theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (.Ico a b) := by
  obtain ⟨ha, hb⟩ := hx
  apply limitpt_of_sub (p := x) (q := b)
  · intro y hy; exact ⟨⟨ha.trans hy.1.le, hy.2⟩, (ne_of_lt hy.1).symm⟩
  · rw [closure_Ioo (ne_of_lt hb)]; exact Set.left_mem_Icc.mpr hb.le

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (.Ioc a b) := by
  obtain ⟨ha, hb⟩ := hx
  apply limitpt_of_sub (p := a) (q := x)
  · intro y hy; exact ⟨⟨hy.1, hy.2.le.trans hb⟩, (ne_of_lt hy.2)⟩
  · rw [closure_Ioo (ne_of_lt ha)]; exact Set.right_mem_Icc.mpr ha.le

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (.Ioo a b) := by
  obtain ⟨ha, hb⟩ := hx
  apply limitpt_of_sub (p := a) (q := x)
  · intro y hy; exact ⟨⟨hy.1, hy.2.trans hb⟩, (ne_of_lt hy.2)⟩
  · rw [closure_Ioo (ne_of_lt ha)]; exact Set.right_mem_Icc.mpr ha.le

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (.Ici a) := by
  apply limitpt_of_sub (p := x) (q := x + 1)
  · intro y hy; exact ⟨le_trans hx hy.1.le, (ne_of_lt hy.1).symm⟩
  · rw [closure_Ioo (ne_of_lt (by linarith))]; exact Set.left_mem_Icc.mpr (by linarith)

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (.Ioi a) := by
  apply limitpt_of_sub (p := x) (q := x + 1)
  · intro y hy; exact ⟨lt_trans hx hy.1, (ne_of_lt hy.1).symm⟩
  · rw [closure_Ioo (ne_of_lt (by linarith))]; exact Set.left_mem_Icc.mpr (by linarith)

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (.Iic a) := by
  apply limitpt_of_sub (p := x - 1) (q := x)
  · intro y hy; exact ⟨le_trans hy.2.le hx, (ne_of_lt hy.2)⟩
  · rw [closure_Ioo (ne_of_lt (by linarith))]; exact Set.right_mem_Icc.mpr (by linarith)

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (.Iio a) := by
  apply limitpt_of_sub (p := x - 1) (q := x)
  · intro y hy; exact ⟨lt_trans hy.2 hx, (ne_of_lt hy.2)⟩
  · rw [closure_Ioo (ne_of_lt (by linarith))]; exact Set.right_mem_Icc.mpr (by linarith)

theorem mem_R_isLimit {x:ℝ} : LimitPt x (.univ) := by
  apply limitpt_of_sub (p := x) (q := x + 1)
  · intro y hy; exact ⟨Set.mem_univ y, (ne_of_lt hy.1).symm⟩
  · rw [closure_Ioo (ne_of_lt (by linarith))]; exact Set.left_mem_Icc.mpr (by linarith)

/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (.Icc a b) := Metric.isBounded_Icc a b

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (.Ici a) := by
  rw [isBounded_def]; rintro ⟨M, hM, hsub⟩
  have := hsub (Set.mem_Ici.mpr (le_max_left a (M+1)))
  rw [Set.mem_Icc] at this; linarith [le_max_right a (M+1), this.2]

/-- Example 9.1.23 -/
theorem N_unbounded : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; rintro ⟨M, hM, hsub⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have := hsub (⟨n, Set.mem_univ _, rfl⟩ : (n:ℝ) ∈ (fun n:ℕ ↦ (n:ℝ)) '' Set.univ)
  rw [Set.mem_Icc] at this; linarith [this.2]

/-- Example 9.1.23 -/
theorem Z_unbounded : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; rintro ⟨M, hM, hsub⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have := hsub (⟨(n:ℤ), Set.mem_univ _, by push_cast; ring⟩ : (n:ℝ) ∈ (fun n:ℤ ↦ (n:ℝ)) '' Set.univ)
  rw [Set.mem_Icc] at this; linarith [this.2]

/-- Example 9.1.23 -/
theorem Q_unbounded : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; rintro ⟨M, hM, hsub⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have := hsub (⟨(n:ℚ), Set.mem_univ _, by push_cast; ring⟩ : (n:ℝ) ∈ (fun n:ℚ ↦ (n:ℝ)) '' Set.univ)
  rw [Set.mem_Icc] at this; linarith [this.2]

/-- Example 9.1.23 -/
theorem R_unbounded : ¬ Bornology.IsBounded (.univ: Set ℝ) := by
  rw [isBounded_def]; rintro ⟨M, hM, hsub⟩
  have := hsub (Set.mem_univ (M+1)); rw [Set.mem_Icc] at this; linarith [this.2]

/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds L)) := by
  rw [← Metric.isCompact_iff_isClosed_bounded, isCompact_iff_isSeqCompact]
  constructor
  · intro h a ha
    obtain ⟨L, hL, φ, hφ, htend⟩ := @h a ha
    exact ⟨φ, hφ, L, hL, htend⟩
  · intro h a ha
    obtain ⟨φ, hφ, L, hL, htend⟩ := @h a ha
    exact ⟨L, hL, φ, hφ, htend⟩

/-- Exercise 9.1.3 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  refine ⟨Set.Iio 0, Set.Ioi 0, ?_⟩
  have hempty : Set.Iio (0:ℝ) ∩ Set.Ioi 0 = ∅ := by ext x; simp; intro h; linarith
  rw [hempty, closure_empty, closure_Iio, closure_Ioi]
  intro h
  have h0 : (0:ℝ) ∈ Set.Iic 0 ∩ Set.Ici 0 := ⟨Set.mem_Iic.mpr (le_refl 0), Set.mem_Ici.mpr (le_refl 0)⟩
  rw [← h] at h0
  exact absurd h0 (by simp)

/-- Exercise 9.1.5 -/
example (X:Set ℝ) : IsClosed (closure X) := isClosed_closure

/-- Exercise 9.1.6 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := closure_minimal hXY hY

/-- Exercise 9.1.7 -/
example {n:ℕ} (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) := isClosed_iUnion_of_finite hX

/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) := isClosed_iInter hX

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  by_cases hlim : LimitPt x X
  · exact Or.inl hlim
  · right
    have hxX : x ∈ X := by
      by_contra hxni
      exact hlim (by rwa [LimitPt, Set.diff_singleton_eq_self hxni])
    unfold LimitPt AdherentPt at hlim
    push_neg at hlim
    obtain ⟨ε, hε, hsep⟩ := hlim
    exact ⟨hxX, ε, hε, hsep⟩

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  rintro ⟨hlim, _, ε, hε, hsep⟩
  obtain ⟨y, hy, hle⟩ := hlim ε hε
  exact absurd hle (not_le.mpr (hsep y hy))

/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hX
  set S := (fun x:ℝ ↦ (x:EReal)) '' X with hS
  constructor
  · intro hbdd
    rw [isBounded_def] at hbdd
    obtain ⟨M, hM, hsub⟩ := hbdd
    refine ⟨lt_of_le_of_lt (b := (M:EReal)) ?_ (EReal.coe_lt_top M),
      lt_of_lt_of_le (b := ((-M:ℝ):EReal)) (EReal.bot_lt_coe (-M)) ?_⟩
    · apply sSup_le; rintro z ⟨x, hx, rfl⟩
      show (x:EReal) ≤ (M:EReal)
      have := hsub hx; rw [Set.mem_Icc] at this; exact_mod_cast this.2
    · apply le_sInf; rintro z ⟨x, hx, rfl⟩
      show ((-M:ℝ):EReal) ≤ (x:EReal)
      have := hsub hx; rw [Set.mem_Icc] at this; exact_mod_cast this.1
  · rintro ⟨hsup, hinf⟩
    rw [isBounded_def]
    have hsup_bot : (⊥:EReal) < sSup S := lt_of_lt_of_le (EReal.bot_lt_coe x₀) (le_sSup ⟨x₀, hx₀, rfl⟩)
    have hinf_top : sInf S < (⊤:EReal) := lt_of_le_of_lt (sInf_le ⟨x₀, hx₀, rfl⟩) (EReal.coe_lt_top x₀)
    set a := (sSup S).toReal with ha
    set b := (sInf S).toReal with hb
    have hae : (a:EReal) = sSup S := EReal.coe_toReal (ne_of_lt hsup) (ne_of_gt hsup_bot)
    have hbe : (b:EReal) = sInf S := EReal.coe_toReal (ne_of_lt hinf_top) (ne_of_gt hinf)
    refine ⟨max (max a (-b)) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro x hx
    rw [Set.mem_Icc]
    have hxa : x ≤ a := by
      have : (x:EReal) ≤ (a:EReal) := hae ▸ le_sSup ⟨x, hx, rfl⟩
      exact_mod_cast this
    have hxb : b ≤ x := by
      have : (b:EReal) ≤ (x:EReal) := hbe ▸ sInf_le ⟨x, hx, rfl⟩
      exact_mod_cast this
    constructor
    · have : -b ≤ max (max a (-b)) 1 := le_trans (le_max_right a (-b)) (le_max_left _ _)
      linarith
    · exact le_trans hxa (le_trans (le_max_left a (-b)) (le_max_left _ _))

/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) := hX.closure

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with {lean}`[Fintype I]` removed. -/
example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) := Bornology.isBounded_iUnion.mpr hX

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) :=
  ⟨I.finite_toSet.isClosed, I.finite_toSet.isBounded⟩

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) (hnon: E.Nonempty): AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  constructor
  · intro ε hε
    obtain ⟨y, hyE, hy⟩ := exists_lt_of_lt_csSup hnon (show sSup E - ε < sSup E by linarith)
    have hle : y ≤ sSup E := le_csSup hE.bddAbove hyE
    exact ⟨y, hyE, by rw [abs_le]; constructor <;> linarith⟩
  · intro ε hε
    refine ⟨sSup E + ε/2, ?_, by rw [abs_le]; constructor <;> linarith⟩
    intro hmem
    have := le_csSup hE.bddAbove hmem
    linarith

end Chapter9
