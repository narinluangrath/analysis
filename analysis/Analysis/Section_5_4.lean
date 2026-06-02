import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨a, hcau, hbaz, rfl⟩ := boundedAwayZero_of_nonzero hx
  obtain ⟨c, hc, hac⟩ := hbaz
  obtain ⟨N, hN⟩ := (Sequence.IsCauchy.coe _).mp hcau c hc
  by_cases hsign : a N ≥ c
  · left
    set a' : ℕ → ℚ := fun n => if n < N then c else a n with ha'def
    have key : ∀ n, a' n ≥ c := by
      intro n
      simp only [ha'def]
      by_cases hn : n < N
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hd := hN n (by omega) N (le_refl N)
        rw [Section_4_3.dist_eq, abs_le] at hd
        have hn0 : a n ≥ 0 := by linarith [hd.1, hsign]
        have habs := hac n
        rwa [abs_of_nonneg hn0] at habs
    have ha'a : Sequence.Equiv a' a := by
      rw [Sequence.equiv_iff]
      intro δ hδ
      refine ⟨N, fun n hn => ?_⟩
      simp only [ha'def, if_neg (by omega : ¬ n < N), sub_self, abs_zero]
      linarith
    have ha'cau := (Sequence.isCauchy_of_equiv ha'a).mpr hcau
    exact ⟨a', ⟨c, hc, key⟩, ha'cau, ((Real.LIM_eq_LIM ha'cau hcau).mpr ha'a).symm⟩
  · right
    push_neg at hsign
    have haN : a N ≤ -c := by
      have habs := hac N
      rcases abs_cases (a N) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [linarith [habs, h1]; linarith [habs, h1]]
    set a' : ℕ → ℚ := fun n => if n < N then -c else a n with ha'def
    have key : ∀ n, a' n ≤ -c := by
      intro n
      simp only [ha'def]
      by_cases hn : n < N
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hd := hN n (by omega) N (le_refl N)
        rw [Section_4_3.dist_eq, abs_le] at hd
        have hn0 : a n ≤ 0 := by linarith [hd.2, haN]
        have habs := hac n
        rw [abs_of_nonpos hn0] at habs
        linarith
    have ha'a : Sequence.Equiv a' a := by
      rw [Sequence.equiv_iff]
      intro δ hδ
      refine ⟨N, fun n hn => ?_⟩
      simp only [ha'def, if_neg (by omega : ¬ n < N), sub_self, abs_zero]
      linarith
    have ha'cau := (Sequence.isCauchy_of_equiv ha'a).mpr hcau
    exact ⟨a', ⟨c, hc, key⟩, ha'cau, ((Real.LIM_eq_LIM ha'cau hcau).mpr ha'a).symm⟩

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rintro ⟨hx0, a, hpos, hcau, hxeq⟩
  rw [hxeq] at hx0
  exact lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayPos hpos) hcau hx0

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rintro ⟨hx0, a, hneg, hcau, hxeq⟩
  rw [hxeq] at hx0
  exact lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayNeg hneg) hcau hx0

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rintro ⟨⟨a, ⟨ca, hca, ha⟩, hacau, rfl⟩, b, ⟨cb, hcb, hb⟩, hbcau, hxeq⟩
  have hbaz : BoundedAwayZero (a - b) := by
    refine ⟨ca+cb, by linarith, fun n => ?_⟩
    simp only [Pi.sub_apply]
    rw [abs_of_pos (by linarith [ha n, hb n])]
    linarith [ha n, hb n]
  have hlim := lim_of_boundedAwayZero hbaz (Sequence.IsCauchy.sub hacau hbcau)
  rw [← Real.LIM_sub hacau hbcau, hxeq, sub_self] at hlim
  exact hlim rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  · rintro ⟨a, ⟨c, hc, ha⟩, hcau, rfl⟩
    refine ⟨-a, ⟨c, hc, fun n => ?_⟩, Sequence.IsCauchy.neg a hcau, ?_⟩
    · simp only [Pi.neg_apply]; linarith [ha n]
    · rw [Real.neg_LIM a hcau]
  · rintro ⟨a, ⟨c, hc, ha⟩, hcau, hx⟩
    refine ⟨-a, ⟨c, hc, fun n => ?_⟩, Sequence.IsCauchy.neg a hcau, ?_⟩
    · simp only [Pi.neg_apply]; linarith [ha n]
    · have hxe : x = -LIM a := by rw [← hx]; ring
      rw [hxe, Real.neg_LIM a hcau]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, ⟨ca, hca, ha⟩, hacau, rfl⟩ := hx
  obtain ⟨b, ⟨cb, hcb, hb⟩, hbcau, rfl⟩ := hy
  refine ⟨a+b, ⟨ca+cb, by linarith, fun n => ?_⟩, Sequence.IsCauchy.add hacau hbcau, ?_⟩
  · simp only [Pi.add_apply]; linarith [ha n, hb n]
  · rw [Real.LIM_add hacau hbcau]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, ⟨ca, hca, ha⟩, hacau, rfl⟩ := hx
  obtain ⟨b, ⟨cb, hcb, hb⟩, hbcau, rfl⟩ := hy
  refine ⟨a*b, ⟨ca*cb, by positivity, fun n => ?_⟩, Sequence.IsCauchy.mul hacau hbcau, ?_⟩
  · simp only [Pi.mul_apply]
    exact mul_le_mul (ha n) (hb n) hcb.le (le_trans hca.le (ha n))
  · rw [Real.LIM_mul hacau hbcau]

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  · rintro ⟨a, ⟨c, hc, ha⟩, hcau, heq⟩
    rw [Real.ratCast_def, Real.LIM_eq_LIM (Sequence.IsCauchy.const q) hcau,
      Sequence.equiv_iff] at heq
    by_contra hq; push_neg at hq
    obtain ⟨N, hN⟩ := heq (c/2) (by linarith)
    have h1 := hN N (le_refl N)
    have h2 := ha N
    simp only at h1
    rw [abs_le] at h1
    linarith [h1.1, h1.2, h2, hq]
  · intro hq
    exact ⟨fun _ => q, ⟨q, hq, fun _ => le_refl q⟩, Sequence.IsCauchy.const q, by
      rw [Real.ratCast_def]⟩

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  rw [Real.neg_iff_pos_of_neg, Real.neg_ratCast, Real.pos_of_coe]
  constructor <;> intro h <;> linarith

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  rw [gt_iff_lt, Real.lt_iff, Real.neg_iff_pos_of_neg, show -(y-x) = x-y from by ring]
theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [ge_iff_le, Real.le_iff, gt_iff_lt]
  constructor <;> rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h.symm
  · exact Or.inl h
  · exact Or.inr h.symm

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [Real.lt_iff, Real.ratCast_sub, Real.neg_of_coe]
  constructor <;> intro h <;> linarith

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by rw [Real.gt_iff, sub_zero]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by rw [Real.lt_iff, sub_zero]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  rcases Real.trichotomous (x-y) with h | h | h
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · exact Or.inl ((Real.gt_iff x y).mpr h)
  · exact Or.inr (Or.inl ((Real.lt_iff x y).mpr h))

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [Real.gt_iff, Real.lt_iff]; exact Real.not_pos_neg (x-y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rintro ⟨hgt, heq⟩
  rw [Real.gt_iff, heq, sub_self] at hgt
  exact Real.not_zero_pos 0 ⟨rfl, hgt⟩

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rintro ⟨hlt, heq⟩
  rw [Real.lt_iff, heq, sub_self] at hlt
  exact Real.not_zero_neg 0 ⟨rfl, hlt⟩

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := Iff.rfl

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [Real.lt_iff, Real.neg_iff_pos_of_neg] at hxy hyz ⊢
  have h := Real.pos_add hyz hxy
  rw [show -(y-z) + -(x-y) = -(x-z) from by ring] at h
  exact h

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [Real.lt_iff, show (x+z)-(y+z) = x-y from by ring, ← Real.lt_iff]; exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [Real.le_iff] at hxy ⊢
  rcases hxy with h | h
  · left; rw [mul_comm z x, mul_comm z y]; exact Real.mul_lt_mul_right h hz
  · right; rw [h]

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [Real.neg_iff_pos_of_neg, show -(x*y) = x*(-y) from by ring]
  exact Real.pos_mul hx ((Real.neg_iff_pos_of_neg y).mp hy)

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := fun x => Or.inr rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
    · exact Or.inl (Real.lt_trans h1 h2)
    · subst h2; exact Or.inl h1
    · subst h1; exact Or.inl h2
    · subst h1; exact Or.inr h2
  lt_iff_le_not_ge := by
    intro x y
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h2 | h2)
      · exact Real.not_gt_and_lt y x ⟨h, h2⟩
      · exact Real.not_lt_and_eq x y ⟨h, h2.symm⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with h | h
      · exact h
      · exact absurd (Or.inr h.symm) h2
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with h1 | h1
    · rcases hyx with h2 | h2
      · exact absurd ⟨h1, h2⟩ (Real.not_gt_and_lt y x)
      · exact h2.symm
    · exact h1
  le_total := by
    intro x y
    rcases Real.trichotomous' x y with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  toDecidableLE := Classical.decRel _

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq_mul_inv]; exact Real.pos_mul hx (Real.inv_of_pos hy)

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b h c
    rw [Real.le_iff] at h ⊢
    rcases h with h | h
    · left; exact Real.add_lt_add_right c h
    · right; rw [h]
  add_le_add_right := by
    intro a b h c
    rw [Real.le_iff] at h ⊢
    rcases h with h | h
    · left; rw [add_comm c a, add_comm c b]; exact Real.add_lt_add_right c h
    · right; rw [h]
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    rw [mul_comm a b, mul_comm a c]
    exact Real.mul_lt_mul_right hbc ((Real.isPos_iff a).mpr ha)
  mul_lt_mul_of_pos_right := by
    intro a ha b c hbc
    exact Real.mul_lt_mul_right hbc ((Real.isPos_iff a).mpr ha)
  le_of_add_le_add_left := by
    intro a b c h
    rw [Real.le_iff] at h ⊢
    rcases h with h | h
    · left; rw [Real.lt_iff, show (a+b)-(a+c) = b-c from by ring, ← Real.lt_iff] at h; exact h
    · right; exact add_left_cancel h
  zero_le_one := by
    rw [Real.le_iff]; left
    rw [Real.lt_iff, show (0:Real)-1 = ((-1:ℚ):Real) from by push_cast; ring, Real.neg_of_coe]
    norm_num

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  rcases Real.trichotomous x with h | h | h
  · subst h; rw [abs_zero, Real.abs_of_zero]
  · rw [_root_.abs_of_pos ((Real.isPos_iff x).mp h), Real.abs_of_pos x h]
  · rw [_root_.abs_of_neg ((Real.isNeg_iff x).mp h), Real.abs_of_neg x h]

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  sorry

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  classical
  have hgt : ∀ y:Real, ∃ N:ℤ, y < (N:Real) := by
    intro y
    obtain rfl | hy | hy := trichotomous y
    · exact ⟨1, by norm_num⟩
    · obtain ⟨N, hN⟩ := (exists_rat_le_and_nat_gt hy).2
      exact ⟨(N:ℤ), by exact_mod_cast hN⟩
    · exact ⟨1, by have := (isNeg_iff y).mp hy; push_cast; linarith⟩
  obtain ⟨N, hN⟩ := hgt x
  obtain ⟨M, hM⟩ := hgt (-x)
  have hMx : ((-M:ℤ):Real) ≤ x := by push_cast; push_cast at hM; linarith
  obtain ⟨n, hn_le, hn_max⟩ := Int.exists_greatest_of_bdd (P := fun z => (z:Real) ≤ x)
    ⟨N, fun z hz => by have : (z:Real) < (N:Real) := lt_of_le_of_lt hz hN; exact_mod_cast this.le⟩
    ⟨-M, hMx⟩
  refine ⟨n, ⟨hn_le, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : (n+1:ℤ) ≤ n := hn_max (n+1) (by push_cast; linarith)
    omega
  · rintro m ⟨hm1, hm2⟩
    have hmn : m ≤ n := hn_max m hm1
    have h2 : (n:Real) < ((m+1:ℤ):Real) := by push_cast; linarith
    have hnm : n < m+1 := by exact_mod_cast h2
    omega

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  obtain ⟨M, hM, hMx⟩ := le_mul hx 1
  refine ⟨(M:ℤ), by exact_mod_cast hM, ?_⟩
  have hMpos : (0:Real) < ((M:ℤ):Real) := by exact_mod_cast hM
  have key : ((M:ℤ):Real) * x > 1 := by push_cast; push_cast at hMx; linarith
  calc ((M:ℤ):Real)⁻¹ = ((M:ℤ):Real)⁻¹ * 1 := (mul_one _).symm
    _ < ((M:ℤ):Real)⁻¹ * (((M:ℤ):Real) * x) := mul_lt_mul_of_pos_left key (inv_pos.mpr hMpos)
    _ = x := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hMpos), one_mul]

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  have hpos : (y-x).IsPos := (isPos_iff _).mpr (by linarith)
  obtain ⟨N, hN, hNinv⟩ := exist_inv_nat_le hpos
  have hNr : (0:Real) < (N:Real) := by exact_mod_cast hN
  obtain ⟨m, ⟨hm1, hm2⟩, -⟩ := floor_exist ((N:Real)*x)
  have h1 : 1 < (N:Real)*(y-x) := by
    have := mul_lt_mul_of_pos_left hNinv hNr
    rwa [mul_inv_cancel₀ (ne_of_gt hNr)] at this
  set q : ℚ := ((m:ℚ)+1)/(N:ℚ) with hqdef
  have hq : (q:Real) = ((m:Real)+1)/((N:Real)) := by rw [hqdef]; push_cast; ring
  refine ⟨q, ?_, ?_⟩
  · rw [hq, lt_div_iff₀ hNr, mul_comm]; exact hm2
  · rw [hq, div_lt_iff₀ hNr]; nlinarith [hm1, h1]

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw [abs_lt]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hc; push_neg at hc
    have := h ((x-y)/2) (by linarith)
    linarith
  · intro h ε hε; linarith

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  · intro h
    by_contra hc
    have hpos : 0 < |x-y| := by rw [abs_pos]; exact sub_ne_zero.mpr hc
    have := h (|x-y|/2) (by linarith)
    linarith
  · intro h ε hε; rw [h, sub_self, abs_zero]; linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨q, hq1, hq2⟩ := rat_between hc
  have haq : ∀ n, a n ≤ q := by
    intro n
    have : (a n:Real) < (q:Real) := lt_of_le_of_lt (h n) hq1
    exact_mod_cast this.le
  have hle := LIM_mono hcauchy (Sequence.IsCauchy.const q) haq
  rw [← ratCast_def] at hle
  linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨q, hq1, hq2⟩ := rat_between hc
  have hqa : ∀ n, q ≤ a n := by
    intro n
    have : (q:Real) < (a n:Real) := lt_of_lt_of_le hq2 (h n)
    exact_mod_cast this.le
  have hge := LIM_mono (Sequence.IsCauchy.const q) hcauchy hqa
  rw [← ratCast_def] at hge
  linarith

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by rw [min_neg_neg, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by rw [max_neg_neg, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := _root_.max_comm x y

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := _root_.max_self x

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := _root_.max_add_add_right x y z

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  exact (max_mul_of_nonneg x y ((isPos_iff z).mp hz).le).symm
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := _root_.min_comm x y

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := _root_.min_self x

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := _root_.min_add_add_right x y z

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  exact (min_mul_of_nonneg x y ((isPos_iff z).mp hz).le).symm

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by sorry

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by sorry

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by sorry

end Chapter5
