import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/

namespace Chapter11
open BoundedInterval

/-- Definition 11.2.1 -/
abbrev Constant {X Y:Type} (f: X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y:Type} [hY: Nonempty Y] (f:X → Y) : Y :=
  if h: Constant f then h.choose else hY.some

theorem Constant.eq {X Y:Type} {f: X → Y} [Nonempty Y] (h: Constant f) (x:X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

theorem Constant.of_const {X Y:Type} {f:X → Y} {c:Y} (h: ∀ x, f x = c) :
  Constant f := by use c

theorem Constant.const_eq {X Y:Type} {f:X → Y} [hX: Nonempty X] [Nonempty Y] {c:Y} (h: ∀ x, f x = c) :
  constant_value f = c := by rw [←eq (of_const h) hX.some, h hX.some]

theorem Constant.of_subsingleton {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y] {f:X → Y} :
  Constant f := by
  by_cases h:Nonempty X
  . use f h.some; intros; congr; exact hs.elim _ h.some
  simp at h; exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f: ℝ → ℝ) (X: Set ℝ) : Prop := Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f:ℝ → ℝ) (X: Set ℝ) : ℝ := constant_value (fun x : X ↦ f ↑x)

theorem ConstantOn.eq {f: ℝ → ℝ} {X: Set ℝ} (h: ConstantOn f X) {x:ℝ} (hx: x ∈ X) :
  f x = constant_value_on f X := by
  convert Constant.eq h ⟨ _, hx ⟩

theorem ConstantOn.of_const {f:ℝ → ℝ} {X: Set ℝ} {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  ConstantOn f X := ⟨ c, by grind ⟩

theorem ConstantOn.of_const' (c:ℝ) (X:Set ℝ): ConstantOn (fun _ ↦ c) X := of_const (c := c) (by simp)

theorem ConstantOn.const_eq {f:ℝ → ℝ} {X: Set ℝ} (hX: X.Nonempty) {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  constant_value_on f X = c := by
    rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

theorem ConstantOn.congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
  simp_rw [ConstantOn, iff_iff_eq]; congr; grind

theorem ConstantOn.congr' {f g: ℝ → ℝ} {X: Set ℝ} (hf: ConstantOn f X) (h: ∀ x ∈ X, f x = g x) : ConstantOn g X := (congr h).mp hf

theorem ConstantOn.of_subsingleton {f: ℝ → ℝ} {X: Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

theorem constant_value_on_congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Definition 11.2.3 (Piecewise constant functions I) -/
abbrev PiecewiseConstantWith (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J:Set ℝ)

theorem PiecewiseConstantWith.def (f:ℝ → ℝ) {I: BoundedInterval} {P: Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

theorem PiecewiseConstantWith.congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Definition 11.2.5 (Piecewise constant functions I) -/
abbrev PiecewiseConstantOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

theorem PiecewiseConstantOn.def (f:ℝ → ℝ) (I: BoundedInterval):
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) := by rfl

theorem PiecewiseConstantOn.congr {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

theorem PiecewiseConstantOn.congr' {f g: ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  set P2 : Partition (Icc 1 3) := (⊥:Partition (Ico 1 3)).join (⊥:Partition (Icc 3 3))
    (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num))
  set P3 : Partition (Ico 1 6) := P2.join (⊥:Partition (Ioo 3 6))
    (BoundedInterval.join_Icc_Ioo (by norm_num) (by norm_num))
  set P4 : Partition (Icc 1 6) := P3.join (⊥:Partition (Icc 6 6))
    (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num)) with hP4
  refine ⟨P4, ?_⟩
  intro L hL
  have hL2 : L ∈ P4.intervals := hL
  simp only [hP4, P3, P2, Partition.intervals_of_join, Partition.intervals_of_bot,
    Finset.mem_union, Finset.mem_singleton] at hL2
  rcases hL2 with (((rfl | rfl) | rfl) | rfl)
  · refine ConstantOn.of_const (c := 7) (fun x hx => ?_)
    rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_4]; rw [if_neg (by linarith [hx.1]), if_pos (by linarith [hx.2])]
  · refine ConstantOn.of_const (c := 4) (fun x hx => ?_)
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    have : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_4, this]; norm_num
  · refine ConstantOn.of_const (c := 5) (fun x hx => ?_)
    rw [BoundedInterval.set_Ioo, Set.mem_Ioo] at hx
    simp only [f_11_2_4]
    rw [if_neg (by linarith [hx.1]), if_neg (by linarith [hx.1]), if_neg (by linarith [hx.1]),
      if_pos (by linarith [hx.2])]
  · refine ConstantOn.of_const (c := 2) (fun x hx => ?_)
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    have : x = 6 := le_antisymm hx.2 hx.1
    simp only [f_11_2_4, this]; norm_num

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  set P2 : Partition (Icc 1 2) := (⊥:Partition (Ico 1 2)).join (⊥:Partition (Icc 2 2))
    (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num))
  set P3 : Partition (Ico 1 3) := P2.join (⊥:Partition (Ioo 2 3))
    (BoundedInterval.join_Icc_Ioo (by norm_num) (by norm_num))
  set P4 : Partition (Icc 1 3) := P3.join (⊥:Partition (Icc 3 3))
    (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num))
  set P5 : Partition (Ico 1 5) := P4.join (⊥:Partition (Ioo 3 5))
    (BoundedInterval.join_Icc_Ioo (by norm_num) (by norm_num))
  set P6 : Partition (Ico 1 6) := P5.join (⊥:Partition (Ico 5 6))
    (BoundedInterval.join_Ico_Ico (by norm_num) (by norm_num))
  set P7 : Partition (Icc 1 6) := P6.join (⊥:Partition (Icc 6 6))
    (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num)) with hP7
  refine ⟨P7, ?_⟩
  intro L hL
  have hL2 : L ∈ P7.intervals := hL
  simp only [hP7, P6, P5, P4, P3, P2, Partition.intervals_of_join, Partition.intervals_of_bot,
    Finset.mem_union, Finset.mem_singleton] at hL2
  rcases hL2 with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · refine ConstantOn.of_const (c := 7) (fun x hx => ?_)
    rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx; obtain ⟨ha, hb⟩ := hx
    simp only [f_11_2_4]; split_ifs <;> first | rfl | (exfalso; linarith)
  · refine ConstantOn.of_const (c := 7) (fun x hx => ?_)
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    have : x = 2 := le_antisymm hx.2 hx.1
    simp only [f_11_2_4, this]; norm_num
  · refine ConstantOn.of_const (c := 7) (fun x hx => ?_)
    rw [BoundedInterval.set_Ioo, Set.mem_Ioo] at hx; obtain ⟨ha, hb⟩ := hx
    simp only [f_11_2_4]; split_ifs <;> first | rfl | (exfalso; linarith)
  · refine ConstantOn.of_const (c := 4) (fun x hx => ?_)
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    have : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_4, this]; norm_num
  · refine ConstantOn.of_const (c := 5) (fun x hx => ?_)
    rw [BoundedInterval.set_Ioo, Set.mem_Ioo] at hx; obtain ⟨ha, hb⟩ := hx
    simp only [f_11_2_4]; split_ifs <;> first | rfl | (exfalso; linarith)
  · refine ConstantOn.of_const (c := 5) (fun x hx => ?_)
    rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx; obtain ⟨ha, hb⟩ := hx
    simp only [f_11_2_4]; split_ifs <;> first | rfl | (exfalso; linarith)
  · refine ConstantOn.of_const (c := 2) (fun x hx => ?_)
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    have : x = 6 := le_antisymm hx.2 hx.1
    simp only [f_11_2_4, this]; norm_num

/-- Example 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f (I:Set ℝ)) :
  PiecewiseConstantOn f I := by
  use ⊥
  intro J hJ
  have : J ∈ (⊥:Partition I).intervals := hJ
  rw [Partition.intervals_of_bot, Finset.mem_singleton] at this
  subst this
  exact h

/-- Lemma 11.2.7 / Exercise 11.2.1 -/
theorem PiecewiseConstantWith.mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I} (hPP': P ≤ P')
  (hP: PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  intro J hJ
  obtain ⟨K, hK, hJK⟩ := hPP' J hJ
  obtain ⟨c, hc⟩ := hP K hK
  have hsub : (J:Set ℝ) ⊆ (K:Set ℝ) := (subset_iff J K).mp hJK
  exact ⟨c, fun y => hc ⟨y.val, hsub y.property⟩⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  refine ⟨P ⊔ Q, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP.mono (BoundedInterval.le_max P Q).1 J hJ
  obtain ⟨cg, hcg⟩ := hQ.mono (BoundedInterval.le_max P Q).2 J hJ
  exact ⟨cf + cg, fun y => by show f ↑y + g ↑y = cf + cg; simp only [hcf, hcg]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  refine ⟨P ⊔ Q, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP.mono (BoundedInterval.le_max P Q).1 J hJ
  obtain ⟨cg, hcg⟩ := hQ.mono (BoundedInterval.le_max P Q).2 J hJ
  exact ⟨cf - cg, fun y => by show f ↑y - g ↑y = cf - cg; simp only [hcf, hcg]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.max {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  refine ⟨P ⊔ Q, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP.mono (BoundedInterval.le_max P Q).1 J hJ
  obtain ⟨cg, hcg⟩ := hQ.mono (BoundedInterval.le_max P Q).2 J hJ
  exact ⟨Max.max cf cg, fun y => by show Max.max (f ↑y) (g ↑y) = Max.max cf cg; simp only [hcf, hcg]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.min {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  refine ⟨P ⊔ Q, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP.mono (BoundedInterval.le_max P Q).1 J hJ
  obtain ⟨cg, hcg⟩ := hQ.mono (BoundedInterval.le_max P Q).2 J hJ
  exact ⟨Min.min cf cg, fun y => by show Min.min (f ↑y) (g ↑y) = Min.min cf cg; simp only [hcf, hcg]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.mul {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  refine ⟨P ⊔ Q, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP.mono (BoundedInterval.le_max P Q).1 J hJ
  obtain ⟨cg, hcg⟩ := hQ.mono (BoundedInterval.le_max P Q).2 J hJ
  exact ⟨cf * cg, fun y => by show f ↑y * g ↑y = cf * cg; simp only [hcf, hcg]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.smul {f: ℝ → ℝ} {I: BoundedInterval}
  (c:ℝ) (hf: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P, fun J hJ => ?_⟩
  obtain ⟨cf, hcf⟩ := hP J hJ
  exact ⟨c • cf, fun y => by show c • f ↑y = c • cf; simp only [hcf]⟩

/-- Lemma 11.2.8 / Exercise 11.2.2.  I believe the hypothesis that `g` does not vanish is not needed. -/
theorem PiecewiseConstantOn.div {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn f I) : PiecewiseConstantOn (f / g) I := by
  sorry

/-- Definition 11.2.9 (Piecewise constant integral I)-/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ

theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Example 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥: Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

example : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  intro J hJ
  replace hJ : J ∈ P_11_2_12.intervals := hJ
  simp only [P_11_2_12, Partition.intervals_of_join, Partition.intervals_of_bot,
    Finset.mem_union, Finset.mem_singleton] at hJ
  rcases hJ with (rfl | rfl) | rfl
  · apply ConstantOn.of_const (c := 2)
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos hx.2]
  · apply ConstantOn.of_const (c := 4)
    intro x hx; simp only [set_Icc, Set.mem_Icc] at hx
    have : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_12, this]; norm_num
  · apply ConstantOn.of_const (c := 6)
    intro x hx; simp only [set_Ioc, Set.mem_Ioc] at hx
    simp only [f_11_2_12, if_neg (by linarith [hx.1] : ¬ x < 3),
      if_neg (by linarith [hx.1] : x ≠ 3)]

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  rw [PiecewiseConstantWith.integ,
    show P_11_2_12.intervals = {Ico 1 3, Icc 3 3, Ioc 3 4} from by
      simp [P_11_2_12, Partition.intervals_of_join, Partition.intervals_of_bot]]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hv1 : constant_value_on f_11_2_12 ↑(Ico 1 3) = 2 := by
    apply ConstantOn.const_eq ⟨1, by norm_num [set_Ico]⟩
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos hx.2]
  have hv2 : constant_value_on f_11_2_12 ↑(Icc 3 3) = 4 := by
    apply ConstantOn.const_eq ⟨3, by norm_num [set_Icc]⟩
    intro x hx; simp only [set_Icc, Set.mem_Icc] at hx
    have hx3 : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_12, hx3]; norm_num
  have hv3 : constant_value_on f_11_2_12 ↑(Ioc 3 4) = 6 := by
    apply ConstantOn.const_eq ⟨4, by norm_num [set_Ioc]⟩
    intro x hx; simp only [set_Ioc, Set.mem_Ioc] at hx
    simp only [f_11_2_12, if_neg (by linarith [hx.1] : ¬ x < 3),
      if_neg (by linarith [hx.1] : x ≠ 3)]
  rw [hv1, hv2, hv3]
  norm_num [BoundedInterval.length]

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥: Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥: Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  intro J hJ
  replace hJ : J ∈ P_11_2_12'.intervals := hJ
  simp only [P_11_2_12', Partition.intervals_of_add_empty, Partition.intervals_of_join,
    Partition.intervals_of_bot, Finset.mem_union, Finset.mem_singleton] at hJ
  rcases hJ with (((rfl | rfl) | rfl) | rfl) | rfl
  · apply ConstantOn.of_const (c := 2)
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos (by linarith [hx.2] : x < 3)]
  · apply ConstantOn.of_const (c := 2)
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos hx.2]
  · apply ConstantOn.of_const (c := 4)
    intro x hx; simp only [set_Icc, Set.mem_Icc] at hx
    have hx3 : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_12, hx3]; norm_num
  · apply ConstantOn.of_const (c := 6)
    intro x hx; simp only [set_Ioc, Set.mem_Ioc] at hx
    simp only [f_11_2_12, if_neg (by linarith [hx.1] : ¬ x < 3),
      if_neg (by linarith [hx.1] : x ≠ 3)]
  · rw [BoundedInterval.coe_empty]
    exact ConstantOn.of_subsingleton

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  rw [PiecewiseConstantWith.integ,
    show P_11_2_12'.intervals = {Ico 1 2, Ico 2 3, Icc 3 3, Ioc 3 4, ∅} from by
      simp [P_11_2_12', Partition.intervals_of_add_empty, Partition.intervals_of_join,
        Partition.intervals_of_bot]]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hv1 : constant_value_on f_11_2_12 ↑(Ico 1 2) = 2 := by
    apply ConstantOn.const_eq ⟨1, by norm_num [set_Ico]⟩
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos (by linarith [hx.2] : x < 3)]
  have hv2 : constant_value_on f_11_2_12 ↑(Ico 2 3) = 2 := by
    apply ConstantOn.const_eq ⟨2, by norm_num [set_Ico]⟩
    intro x hx; simp only [set_Ico, Set.mem_Ico] at hx
    simp only [f_11_2_12, if_pos hx.2]
  have hv3 : constant_value_on f_11_2_12 ↑(Icc 3 3) = 4 := by
    apply ConstantOn.const_eq ⟨3, by norm_num [set_Icc]⟩
    intro x hx; simp only [set_Icc, Set.mem_Icc] at hx
    have hx3 : x = 3 := le_antisymm hx.2 hx.1
    simp only [f_11_2_12, hx3]; norm_num
  have hv4 : constant_value_on f_11_2_12 ↑(Ioc 3 4) = 6 := by
    apply ConstantOn.const_eq ⟨4, by norm_num [set_Ioc]⟩
    intro x hx; simp only [set_Ioc, Set.mem_Ioc] at hx
    simp only [f_11_2_12, if_neg (by linarith [hx.1] : ¬ x < 3),
      if_neg (by linarith [hx.1] : x ≠ 3)]
  rw [hv1, hv2, hv3, hv4]
  norm_num [BoundedInterval.length, show (∅:BoundedInterval) = Ioo 0 0 from rfl]

/-- Refinement invariance: if `R` refines `Q` and `f` is piecewise constant with `Q`,
then the integrals agree. -/
theorem PiecewiseConstantWith.integ_eq_of_le {f:ℝ → ℝ} {I: BoundedInterval} {Q R: Partition I}
  (hQR: Q ≤ R) (hQ: PiecewiseConstantWith f Q) : integ f Q = integ f R := by
  classical
  -- assign each fine piece K of R to a coarse piece g K of Q containing it
  have hg : ∀ K ∈ R.intervals, ∃ J ∈ Q.intervals, (K:Set ℝ) ⊆ (J:Set ℝ) := by
    intro K hK; obtain ⟨J, hJ, hsub⟩ := hQR K hK
    rw [BoundedInterval.subset_iff] at hsub; exact ⟨J, hJ, hsub⟩
  choose! g hgmem hgsub using hg
  -- constant value on a (nonempty) fine piece equals that on its coarse piece
  have hcval : ∀ J ∈ Q.intervals, ∀ K, (K:Set ℝ).Nonempty → (K:Set ℝ) ⊆ (J:Set ℝ) →
      constant_value_on f (K:Set ℝ) = constant_value_on f (J:Set ℝ) := by
    intro J hJ K hKne hKJ
    obtain ⟨x, hx⟩ := hKne
    have hcK : ConstantOn f (K:Set ℝ) :=
      ConstantOn.of_const (fun y hy => ConstantOn.eq (hQ J hJ) (hKJ hy))
    rw [← ConstantOn.eq hcK hx, ← ConstantOn.eq (hQ J hJ) (hKJ hx)]
  -- each coarse piece's length is the sum of the lengths of its fine pieces
  have hsumlen : ∀ J ∈ Q.intervals,
      ∑ K ∈ R.intervals.filter (fun K => g K = J), |K|ₗ = |J|ₗ := by
    intro J hJ
    have hex : ∃ QJ : Partition J, QJ.intervals = R.intervals.filter (fun K => g K = J) := by
      refine ⟨⟨R.intervals.filter (fun K => g K = J), ?_, ?_⟩, rfl⟩
      · intro x hx
        have hxI : x ∈ (I:Set ℝ) := by
          have := Q.contains J hJ; rw [BoundedInterval.subset_iff] at this
          exact this ((BoundedInterval.mem_iff J x).mp hx)
        obtain ⟨K, ⟨hKmem, hxK⟩, hKuniq⟩ := R.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)
        have hgKJ : g K = J := by
          have hxgK : x ∈ (g K:Set ℝ) := hgsub K hKmem ((BoundedInterval.mem_iff K x).mp hxK)
          exact (Q.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).unique
            ⟨hgmem K hKmem, (BoundedInterval.mem_iff (g K) x).mpr hxgK⟩ ⟨hJ, hx⟩
        refine ⟨K, ⟨Finset.mem_filter.mpr ⟨hKmem, hgKJ⟩, hxK⟩, ?_⟩
        rintro K' ⟨hK'F, hxK'⟩
        exact hKuniq K' ⟨(Finset.mem_filter.mp hK'F).1, hxK'⟩
      · intro K hKF
        have hKmem := (Finset.mem_filter.mp hKF).1
        have hgKJ := (Finset.mem_filter.mp hKF).2
        rw [BoundedInterval.subset_iff]; intro y hy
        have := hgsub K hKmem hy; rw [hgKJ] at this; exact this
    obtain ⟨QJ, hQJ⟩ := hex
    have := Partition.sum_of_length J QJ; rw [hQJ] at this; exact this
  -- assemble
  show ∑ J ∈ Q.intervals, _ = ∑ K ∈ R.intervals, _
  rw [← Finset.sum_fiberwise_of_maps_to hgmem (fun K => constant_value_on f (K:Set ℝ) * |K|ₗ)]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← hsumlen J hJ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hKF
  have hKmem := (Finset.mem_filter.mp hKF).1
  have hgKJ := (Finset.mem_filter.mp hKF).2
  rcases eq_or_ne (K:Set ℝ) ∅ with hKe | hKne
  · rw [BoundedInterval.length_of_empty hKe]; ring
  · have hKsub : (K:Set ℝ) ⊆ (J:Set ℝ) := by
      have := hgsub K hKmem; rw [hgKJ] at this; exact this
    rw [hcval J hJ K (Set.nonempty_iff_ne_empty.mpr hKne) hKsub]

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  rw [integ_eq_of_le (BoundedInterval.le_max P P').1 hP,
      integ_eq_of_le (BoundedInterval.le_max P P').2 hP']

open Classical in
/-- Definition 11.2.14 (Piecewise constant integral II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f:ℝ → ℝ) (I: BoundedInterval) :
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f:ℝ → ℝ} {I: BoundedInterval} (_:PiecewiseConstantOn f I) := integ f I

theorem PiecewiseConstantOn.integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

theorem PiecewiseConstantOn.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Example 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_4 (Icc 1 6) = 10 := by
  sorry

/-- Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  have hfR : PiecewiseConstantWith f (P ⊔ Q) := hP.mono (BoundedInterval.le_max P Q).1
  have hgR : PiecewiseConstantWith g (P ⊔ Q) := hQ.mono (BoundedInterval.le_max P Q).2
  have hfgR : PiecewiseConstantWith (f + g) (P ⊔ Q) := fun J hJ => by
    obtain ⟨vf, hvf⟩ := hfR J hJ; obtain ⟨vg, hvg⟩ := hgR J hJ
    exact ⟨vf + vg, fun y => by show f ↑y + g ↑y = vf + vg; simp only [hvf, hvg]⟩
  rw [integ_def hfgR, integ_def hfR, integ_def hgR]
  simp only [PiecewiseConstantWith.integ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hlen : |J|ₗ = 0
  · rw [hlen]; ring
  · have hJne : (J:Set ℝ).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hlen (BoundedInterval.length_of_empty hemp)
    rw [show constant_value_on (f + g) ↑J = constant_value_on f ↑J + constant_value_on g ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show f x + g x = _; rw [(hfR J hJ).eq hx, (hgR J hJ).eq hx]]
    ring

/-- Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ) (hf: PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I
   := by
  obtain ⟨P, hP⟩ := hf
  have hcf : PiecewiseConstantWith (c • f) P := fun J hJ => by
    obtain ⟨v, hv⟩ := hP J hJ
    exact ⟨c • v, fun y => by show c • f ↑y = c • v; simp only [hv]⟩
  rw [integ_def hcf, integ_def hP]
  simp only [PiecewiseConstantWith.integ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hlen : |J|ₗ = 0
  · rw [hlen]; ring
  · have hJne : (J:Set ℝ).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hlen (BoundedInterval.length_of_empty hemp)
    rw [show constant_value_on (c • f) ↑J = c * constant_value_on f ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show c • f x = _; rw [(hP J hJ).eq hx, smul_eq_mul]]
    ring

/-- Theorem 11.2.16 (c) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  have hfR : PiecewiseConstantWith f (P ⊔ Q) := hP.mono (BoundedInterval.le_max P Q).1
  have hgR : PiecewiseConstantWith g (P ⊔ Q) := hQ.mono (BoundedInterval.le_max P Q).2
  have hfgR : PiecewiseConstantWith (f - g) (P ⊔ Q) := fun J hJ => by
    obtain ⟨vf, hvf⟩ := hfR J hJ; obtain ⟨vg, hvg⟩ := hgR J hJ
    exact ⟨vf - vg, fun y => by show f ↑y - g ↑y = vf - vg; simp only [hvf, hvg]⟩
  rw [integ_def hfgR, integ_def hfR, integ_def hgR]
  simp only [PiecewiseConstantWith.integ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hlen : |J|ₗ = 0
  · rw [hlen]; ring
  · have hJne : (J:Set ℝ).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hlen (BoundedInterval.length_of_empty hemp)
    rw [show constant_value_on (f - g) ↑J = constant_value_on f ↑J - constant_value_on g ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show f x - g x = _; rw [(hfR J hJ).eq hx, (hgR J hJ).eq hx]]
    ring

/-- Theorem 11.2.16 (d) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, 0 ≤ f x)
  (hf: PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  obtain ⟨P, hP⟩ := hf
  rw [integ_def hP]
  simp only [PiecewiseConstantWith.integ]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases hlen : |J|ₗ = 0
  · rw [hlen, mul_zero]
  · have hJne : (J:Set ℝ).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hlen (BoundedInterval.length_of_empty hemp)
    apply mul_nonneg _ (BoundedInterval.length_nonneg J)
    obtain ⟨x, hx⟩ := hJne
    have hxI : x ∈ I := by
      rw [mem_iff]; have hsub := P.contains J hJ; rw [subset_iff] at hsub; exact hsub hx
    rw [← (hP J hJ).eq hx]; exact h x hxI

/-- Theorem 11.2.16 (e) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, f x ≤ g x)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  have hnn := integ_of_nonneg (f := g - f) (I := I)
    (fun x hx => by show 0 ≤ g x - f x; linarith [h x hx]) (hg.sub hf)
  rw [integ_sub hg hf] at hnn
  linarith


/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c: ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hpc : PiecewiseConstantWith (fun _:ℝ ↦ c) (⊥:Partition I) := fun J hJ => by
    have hmem : J ∈ (⊥:Partition I).intervals := hJ
    rw [Partition.intervals_of_bot, Finset.mem_singleton] at hmem; subst hmem
    exact ConstantOn.of_const' c _
  rw [integ_def hpc]
  simp only [PiecewiseConstantWith.integ, Partition.intervals_of_bot, Finset.sum_singleton]
  by_cases hne : (I:Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hne (fun x _ => rfl)]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [BoundedInterval.length_of_empty hne]; ring

/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  have hpc : PiecewiseConstantWith f (⊥:Partition I) := fun J hJ => by
    have hmem : J ∈ (⊥:Partition I).intervals := hJ
    rw [Partition.intervals_of_bot, Finset.mem_singleton] at hmem; subst hmem; exact h
  rw [integ_def hpc]
  simp only [PiecewiseConstantWith.integ, Partition.intervals_of_bot, Finset.sum_singleton]

open Classical in
/-- The partition construction underlying the extend-by-zero lemmas: extends a partition `P`
of `I` to a partition of `J` by adjoining the left/right gap intervals, on which the extended
function vanishes. -/
private theorem PiecewiseConstantOn.of_extend_aux {I J: BoundedInterval} (hIJ: I ⊆ J)
    {f: ℝ → ℝ} {P: Partition I} (hP: PiecewiseConstantWith f P) (hIemp: (I:Set ℝ) ≠ ∅) :
    ∃ (Q : Partition J) (L R : BoundedInterval),
      PiecewiseConstantWith (fun x ↦ if x ∈ I then f x else 0) Q ∧
      Q.intervals = insert L (insert R P.intervals) ∧
      (∀ x ∈ (L:Set ℝ), x ∉ (I:Set ℝ)) ∧ (∀ x ∈ (R:Set ℝ), x ∉ (I:Set ℝ)) := by
  classical
  set g : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hgdef
  have hIsub : (I:Set ℝ) ⊆ (J:Set ℝ) := by rwa [subset_iff] at hIJ
  have hIcc : (I:Set ℝ) ⊆ Set.Icc I.a I.b := by have := I.subset_Icc; rwa [subset_iff, set_Icc] at this
  have hcoreI : Set.Ioo I.a I.b ⊆ (I:Set ℝ) := by
    have := I.Ioo_subset; rwa [subset_iff, set_Ioo] at this
  have hIne : (I:Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hIemp
  have hIab : I.a ≤ I.b := by obtain ⟨p, hp⟩ := hIne; exact le_trans (hIcc hp).1 (hIcc hp).2
  have hJconn : (J:Set ℝ).OrdConnected := by
    cases J with
    | Ioo a b => rw [set_Ioo]; exact Set.ordConnected_Ioo
    | Icc a b => rw [set_Icc]; exact Set.ordConnected_Icc
    | Ioc a b => rw [set_Ioc]; exact Set.ordConnected_Ioc
    | Ico a b => rw [set_Ico]; exact Set.ordConnected_Ico
  have hJbdd : Bornology.IsBounded (J:Set ℝ) := Bornology.IsBounded.of_boundedInterval J
  -- left gap interval
  have hLconn : ((J:Set ℝ) ∩ {x | x ≤ I.a ∧ x ∉ (I:Set ℝ)}).OrdConnected := by
    constructor
    intro x hx y hy z hz
    refine ⟨hJconn.out' hx.1 hy.1 hz, le_trans hz.2 hy.2.1, ?_⟩
    intro hzI
    have hzeq : z = I.a := le_antisymm (le_trans hz.2 hy.2.1) (hIcc hzI).1
    have hyeq : y = I.a := le_antisymm hy.2.1 (by rw [← hzeq]; exact hz.2)
    exact (hyeq ▸ hy.2.2) (hzeq ▸ hzI)
  have hRconn : ((J:Set ℝ) ∩ {x | I.b ≤ x ∧ x ∉ (I:Set ℝ)}).OrdConnected := by
    constructor
    intro x hx y hy z hz
    refine ⟨hJconn.out' hx.1 hy.1 hz, le_trans hx.2.1 hz.1, ?_⟩
    intro hzI
    have hzeq : z = I.b := le_antisymm (hIcc hzI).2 (le_trans hx.2.1 hz.1)
    have hxeq : x = I.b := le_antisymm (by rw [← hzeq]; exact hz.1) hx.2.1
    exact (hxeq ▸ hx.2.2) (hzeq ▸ hzI)
  obtain ⟨Lgap, hLgap⟩ := (ordConnected_iff _).mp ⟨hJbdd.subset Set.inter_subset_left, hLconn⟩
  obtain ⟨Rgap, hRgap⟩ := (ordConnected_iff _).mp ⟨hJbdd.subset Set.inter_subset_left, hRconn⟩
  -- Lgap and Rgap cannot both contain a point
  have hLRdisj : ∀ y ∈ (Lgap:Set ℝ), y ∉ (Rgap:Set ℝ) := by
    intro y hyL hyR
    rw [← hLgap] at hyL; rw [← hRgap] at hyR
    obtain ⟨_, hyLa, hynI⟩ := hyL
    obtain ⟨_, hyRb, _⟩ := hyR
    obtain ⟨p, hp⟩ := hIne
    have hpa := (hIcc hp).1; have hpb := (hIcc hp).2
    have hpeq : p = I.a := le_antisymm (by linarith) hpa
    have hyeqa : y = I.a := by linarith
    exact hynI (hyeqa ▸ hpeq ▸ hp)
  refine ⟨⟨insert Lgap (insert Rgap P.intervals), ?_, ?_⟩, Lgap, Rgap, ?_, rfl, ?_, ?_⟩
  · -- exists_unique
    intro x hx
    rw [mem_iff] at hx
    by_cases hxI : x ∈ (I:Set ℝ)
    · obtain ⟨K0, ⟨hK0mem, hxK0⟩, hK0uniq⟩ := P.exists_unique x (by rw [mem_iff]; exact hxI)
      refine ⟨K0, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hK0mem), hxK0⟩, ?_⟩
      rintro K' ⟨hK'mem, hxK'⟩
      rw [Finset.mem_insert] at hK'mem
      rcases hK'mem with rfl | hK'mem
      · exfalso; rw [mem_iff, ← hLgap] at hxK'; exact hxK'.2.2 hxI
      · rw [Finset.mem_insert] at hK'mem
        rcases hK'mem with rfl | hK'mem
        · exfalso; rw [mem_iff, ← hRgap] at hxK'; exact hxK'.2.2 hxI
        · exact hK0uniq K' ⟨hK'mem, hxK'⟩
    · have hcase : x ≤ I.a ∨ I.b ≤ x := by
        by_contra hc; push_neg at hc; exact hxI (hcoreI ⟨hc.1, hc.2⟩)
      rcases hcase with hle | hge
      · have hxL : x ∈ (Lgap:Set ℝ) := by rw [← hLgap]; exact ⟨hx, hle, hxI⟩
        refine ⟨Lgap, ⟨Finset.mem_insert_self _ _, by rw [mem_iff]; exact hxL⟩, ?_⟩
        rintro K' ⟨hK'mem, hxK'⟩
        rw [Finset.mem_insert] at hK'mem
        rcases hK'mem with rfl | hK'mem
        · rfl
        · exfalso
          rw [Finset.mem_insert] at hK'mem
          rcases hK'mem with rfl | hK'mem
          · rw [mem_iff] at hxK'; exact hLRdisj x hxL hxK'
          · rw [mem_iff] at hxK'; have := P.contains K' hK'mem
            rw [subset_iff] at this; exact hxI (this hxK')
      · have hxR : x ∈ (Rgap:Set ℝ) := by rw [← hRgap]; exact ⟨hx, hge, hxI⟩
        refine ⟨Rgap, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
          by rw [mem_iff]; exact hxR⟩, ?_⟩
        rintro K' ⟨hK'mem, hxK'⟩
        rw [Finset.mem_insert] at hK'mem
        rcases hK'mem with rfl | hK'mem
        · exfalso; rw [mem_iff] at hxK'; exact hLRdisj x hxK' hxR
        · rw [Finset.mem_insert] at hK'mem
          rcases hK'mem with rfl | hK'mem
          · rfl
          · exfalso; rw [mem_iff] at hxK'; have := P.contains K' hK'mem
            rw [subset_iff] at this; exact hxI (this hxK')
  · -- contains
    intro K hK
    rw [Finset.mem_insert] at hK
    rcases hK with rfl | hK
    · rw [subset_iff, ← hLgap]; exact Set.inter_subset_left
    · rw [Finset.mem_insert] at hK
      rcases hK with rfl | hK
      · rw [subset_iff, ← hRgap]; exact Set.inter_subset_left
      · have := P.contains K hK; rw [subset_iff] at this ⊢; exact this.trans hIsub
  · -- piecewise constant with this partition
    intro K hK
    replace hK : K ∈ insert Lgap (insert Rgap P.intervals) := hK
    rw [Finset.mem_insert] at hK
    rcases hK with rfl | hK
    · apply ConstantOn.of_const (c := 0); intro x hx
      rw [← hLgap] at hx
      rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by rw [mem_iff]; exact hx.2.2)]
    · rw [Finset.mem_insert] at hK
      rcases hK with rfl | hK
      · apply ConstantOn.of_const (c := 0); intro x hx
        rw [← hRgap] at hx
        rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by rw [mem_iff]; exact hx.2.2)]
      · refine (ConstantOn.congr (fun x hx => ?_)).mp (hP K hK)
        have hxI : x ∈ (I:Set ℝ) := by
          have := P.contains K hK; rw [subset_iff] at this; exact this hx
        show f x = g x
        rw [hgdef]; simp only [if_pos (show x ∈ I by rw [mem_iff]; exact hxI)]
  · intro x hx; rw [← hLgap] at hx; exact hx.2.2
  · intro x hx; rw [← hRgap] at hx; exact hx.2.2

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  classical
  by_cases hIemp : (I:Set ℝ) = ∅
  · refine (ConstantOn.of_const' (0:ℝ) (J:Set ℝ)).piecewiseConstantOn.congr' (fun x _ => ?_)
    simp only [if_neg (show ¬ (x ∈ I) by rw [mem_iff, hIemp]; exact Set.notMem_empty x)]
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, L, R, hpc, _, _, _⟩ := PiecewiseConstantOn.of_extend_aux hIJ hP hIemp
  exact ⟨Q, hpc⟩

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  classical
  set g : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hgdef
  by_cases hIemp : (I:Set ℝ) = ∅
  · have hgJ0 : integ g J = 0 := by
      rw [integ_congr (g := fun _ => (0:ℝ)) (fun x _ => by
        rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by rw [mem_iff, hIemp]; exact Set.notMem_empty x)]),
        integ_const, zero_mul]
    have hfI0 : integ f I = 0 := by
      have hc : ConstantOn f (I:Set ℝ) :=
        ConstantOn.of_const (c := 0) (fun x hx => absurd hx (by rw [hIemp]; exact Set.notMem_empty x))
      rw [integ_const' hc, BoundedInterval.length_of_empty hIemp, mul_zero]
    rw [hgJ0, hfI0]
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, L, R, hpcQ, hQint, hgL, hgR⟩ := PiecewiseConstantOn.of_extend_aux hIJ hP hIemp
  -- the gap terms vanish
  have hFzero : ∀ (K:BoundedInterval), (∀ x ∈ (K:Set ℝ), x ∉ (I:Set ℝ)) →
      constant_value_on g (K:Set ℝ) * |K|ₗ = 0 := by
    intro K hK
    rcases eq_or_ne (K:Set ℝ) ∅ with he | hne
    · rw [BoundedInterval.length_of_empty he, mul_zero]
    · have : constant_value_on g (K:Set ℝ) = 0 := by
        apply ConstantOn.const_eq (Set.nonempty_iff_ne_empty.mpr hne) (c := 0)
        intro x hx; rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by rw [mem_iff]; exact hK x hx)]
      rw [this, zero_mul]
  have key : ∀ (a:BoundedInterval) (s:Finset BoundedInterval),
      constant_value_on g (a:Set ℝ) * |a|ₗ = 0 →
      ∑ K ∈ insert a s, constant_value_on g (K:Set ℝ) * |K|ₗ
        = ∑ K ∈ s, constant_value_on g (K:Set ℝ) * |K|ₗ := by
    intro a s ha
    by_cases h : a ∈ s
    · rw [Finset.insert_eq_self.mpr h]
    · rw [Finset.sum_insert h, ha, zero_add]
  rw [integ_def hpcQ, integ_def hP]
  simp only [PiecewiseConstantWith.integ, hQint]
  rw [key L _ (hFzero L hgL), key R _ (hFzero R hgR)]
  apply Finset.sum_congr rfl
  intro K hK
  congr 1
  apply constant_value_on_congr
  intro x hx
  have hxI : x ∈ (I:Set ℝ) := by
    have := P.contains K hK; rw [subset_iff] at this; exact this hx
  rw [hgdef]; simp only [if_pos (show x ∈ I by rw [mem_iff]; exact hxI)]

/-- Restricting a piecewise constant function to a subinterval. -/
theorem PiecewiseConstantOn.restrict {K I: BoundedInterval} (hIK: I ⊆ K) {f: ℝ → ℝ}
  (h: PiecewiseConstantOn f K) : PiecewiseConstantOn f I := by
  classical
  obtain ⟨P, hP⟩ := h
  have hQ : ∃ Q : Partition I, Q.intervals = P.intervals.image (fun L => L ∩ I) := by
    refine ⟨⟨P.intervals.image (fun L => L ∩ I), ?_, ?_⟩, rfl⟩
    · intro x hx
      have hxK : x ∈ (K:Set ℝ) := by
        have := hIK; rw [BoundedInterval.subset_iff] at this
        exact this ((BoundedInterval.mem_iff I x).mp hx)
      obtain ⟨L, ⟨hLmem, hxL⟩, hLuniq⟩ := P.exists_unique x ((BoundedInterval.mem_iff K x).mpr hxK)
      refine ⟨L ∩ I, ⟨Finset.mem_image_of_mem _ hLmem, ?_⟩, ?_⟩
      · rw [BoundedInterval.mem_iff, BoundedInterval.inter_eq]
        exact ⟨(BoundedInterval.mem_iff L x).mp hxL, (BoundedInterval.mem_iff I x).mp hx⟩
      · rintro M ⟨hMmem, hxM⟩
        obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hMmem
        rw [BoundedInterval.mem_iff, BoundedInterval.inter_eq] at hxM
        rw [hLuniq L' ⟨hL'mem, (BoundedInterval.mem_iff L' x).mpr hxM.1⟩]
    · intro M hMmem
      obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hMmem
      rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      exact Set.inter_subset_right
  obtain ⟨Q, hQint⟩ := hQ
  refine ⟨Q, ?_⟩
  intro M hM
  rw [show (M ∈ Q) = (M ∈ Q.intervals) from rfl, hQint] at hM
  obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hM
  rw [BoundedInterval.inter_eq]
  exact ConstantOn.of_const (fun y hy => ConstantOn.eq (hP L' hL'mem) hy.1)

theorem PiecewiseConstantOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  (f: ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  have hIK : I ⊆ K := by
    rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by
    rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  constructor
  · intro h; exact ⟨h.restrict hIK, h.restrict hJK⟩
  · rintro ⟨⟨PI, hPI⟩, ⟨PJ, hPJ⟩⟩
    refine ⟨PI.join PJ hIJK, ?_⟩
    intro L hL
    rcases Finset.mem_union.mp hL with hL | hL
    · exact hPI L hL
    · exact hPJ L hL

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  classical
  have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  obtain ⟨PI, hPI⟩ := h.restrict hIK
  obtain ⟨PJ, hPJ⟩ := h.restrict hJK
  have hjoinpc : PiecewiseConstantWith f (PI.join PJ hIJK) := by
    intro L hL; rcases Finset.mem_union.mp hL with hL | hL
    · exact hPI L hL
    · exact hPJ L hL
  rw [integ_def hjoinpc, integ_def hPI, integ_def hPJ]
  simp only [PiecewiseConstantWith.integ]
  have hinter0 : ∑ L ∈ PI.intervals ∩ PJ.intervals, (constant_value_on f (L:Set ℝ) * |L|ₗ) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    rw [Finset.mem_inter] at hL
    have hLI := PI.contains L hL.1; rw [BoundedInterval.subset_iff] at hLI
    have hLJ := PJ.contains L hL.2; rw [BoundedInterval.subset_iff] at hLJ
    have hLe : (L:Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x hx
      have hxIJ : x ∈ (I:Set ℝ) ∩ (J:Set ℝ) := ⟨hLI hx, hLJ hx⟩
      rw [hIJK.1] at hxIJ; exact hxIJ
    rw [BoundedInterval.length_of_empty hLe, mul_zero]
  have hsui := Finset.sum_union_inter (s₁ := PI.intervals) (s₂ := PJ.intervals)
    (f := fun L => constant_value_on f (L:Set ℝ) * |L|ₗ)
  rw [hinter0, add_zero] at hsui
  exact hsui

end Chapter11
