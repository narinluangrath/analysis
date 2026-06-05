import Mathlib.Tactic
import Analysis.Section_8_4

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of `PartialOrder`, `LinearOrder`, and `WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib `PartialOrder` class. -/

example {X:Type} [PartialOrder X] (x:X) : x ≤ x := le_refl x
example {X:Type} [PartialOrder X] {x y:X} (h₁: x ≤ y) (h₂: y ≤ x) : x = y := antisymm h₁ h₂
example {X:Type} [PartialOrder X] {x y z:X} (h₁: x ≤ y) (h₂: y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X:Type} [PartialOrder X] (x y:X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

@[implicit_reducible] def PartialOrder.mk {X:Type} [LE X]
  (hrefl: ∀ x:X, x ≤ x)
  (hantisymm: ∀ x y:X, x ≤ y → y ≤ x → x = y)
  (htrans: ∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) : PartialOrder X :=
{
  le := (· ≤ ·)
  le_refl := hrefl
  le_antisymm := hantisymm
  le_trans := htrans
}

example {X:Type} : PartialOrder (Set X) := by infer_instance
example {X:Type} (A B: Set X) : A ≤ B ↔ A ⊆ B := by rfl

/-- Definition 8.5.3.  Here we just review the Mathlib `LinearOrder` class. -/
example {X:Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X:Type) [PartialOrder X] : Prop := ∀ x y:X, x ≤ y ∨ y ≤ x
example {X:Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
@[implicit_reducible] noncomputable def LinearOrder.mk {X:Type} [PartialOrder X]
  (htotal: IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Examples 8.5.4 -/
#check inferInstanceAs (LinearOrder ℕ)
#check inferInstanceAs (LinearOrder ℚ)
#check inferInstanceAs (LinearOrder ℝ)
#check inferInstanceAs (LinearOrder EReal)


@[implicit_reducible] noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
LinearOrder.mk (by
  intro ⟨x,hx⟩ ⟨y,hy⟩
  rcases le_total x y with h|h
  · left; exact h
  · right; exact h
  )

theorem IsTotal.subtype {X:Type} [PartialOrder X] {A: Set X} (hA: IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

theorem IsTotal.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) (hAB: B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by
  intro h
  rcases h ⟨{2}, by aesop⟩ ⟨{5}, by aesop⟩ with hle | hle <;>
    simp_all [Subtype.mk_le_mk, Set.subset_def]

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's `IsMax` and `IsMin`. -/
theorem IsMax.iff {X:Type} [PartialOrder X] (x:X) :
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

theorem IsMin.iff {X:Type} [PartialOrder X] (x:X) :
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Examples 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by
  rintro ⟨b, hb⟩ hle
  simp only [X_8_5_4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_def] at hle ⊢
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp_all

example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by
  rintro ⟨b, hb⟩ hle
  simp only [X_8_5_4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_def] at hle ⊢
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp_all

example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by
  rintro ⟨b, hb⟩ hle
  simp only [X_8_5_4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_def] at hle ⊢
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp_all

example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by
  constructor <;>
  · rintro ⟨b, hb⟩ hle
    simp only [X_8_5_4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_def] at hle ⊢
    rcases hb with rfl|rfl|rfl|rfl|rfl <;> simp_all

example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · intro h
    have := h (show (⟨{2}, by aesop⟩ : X_8_5_4) ≤ ⟨{2,3}, by aesop⟩ by
      simp [Subtype.mk_le_mk, Set.subset_def])
    simp_all [Subtype.mk_le_mk, Set.subset_def]
  · intro h
    have := h (show (⟨{2,3}, by aesop⟩ : X_8_5_4) ≤ ⟨{2,3,4}, by aesop⟩ by
      simp [Subtype.mk_le_mk, Set.subset_def])
    simp_all [Subtype.mk_le_mk, Set.subset_def]

/-- Example 8.5.7 -/
example : IsMin (0:ℕ) := by intro b _; exact Nat.zero_le b
example (n:ℕ) : ¬ IsMax n := by intro h; have := h (Nat.le_succ n); omega
example (n:ℤ): ¬ IsMin n ∧ ¬ IsMax n :=
  ⟨fun h => by have := h (show n-1 ≤ n by omega); omega,
   fun h => by have := h (show n ≤ n+1 by omega); omega⟩

/-- Definition 8.5.8.  We use `[LinearOrder X] [WellFoundedLT X]` to describe well-ordered sets. -/
theorem WellFoundedLT.iff (X:Type) [LinearOrder X] :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := by
  unfold WellFoundedLT IsMin
  rw [isWellFounded_iff, WellFounded.wellFounded_iff_has_min]
  peel with A hA; constructor
  . intro ⟨ x, hxA, h ⟩; use ⟨ x, hxA ⟩; intro ⟨ y, hy ⟩ this; specialize h y hy
    simp at *; order
  intro ⟨ ⟨ x, hx ⟩, h ⟩; refine ⟨ _, hx, ?_ ⟩; intro y hy; specialize h (b := ⟨ _, hy ⟩)
  simp at h; contrapose! h; simp [h]; order

theorem WellFoundedLT.iff' {X:Type} [PartialOrder X] (h: IsTotal X) :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := @iff X (LinearOrder.mk h)

/-- Example 8.5.9 -/
example : WellFoundedLT ℕ := by
  rw [WellFoundedLT.iff]
  intro A hA; use ⟨ _, (Nat.min_spec hA).1 ⟩
  simp [IsMin]; grind [Nat.min_spec]

/-- Exercise 8.1.2 -/
example : ¬ WellFoundedLT ℤ := by
  rw [WellFoundedLT.iff]; push_neg
  refine ⟨Set.univ, ⟨0, trivial⟩, ?_⟩
  rintro ⟨x, hx⟩; rw [IsMin.iff]; push_neg
  exact ⟨⟨x-1, trivial⟩, Subtype.mk_lt_mk.mpr (by omega)⟩
example : ¬ WellFoundedLT ℚ := by
  rw [WellFoundedLT.iff]; push_neg
  refine ⟨Set.univ, ⟨0, trivial⟩, ?_⟩
  rintro ⟨x, hx⟩; rw [IsMin.iff]; push_neg
  exact ⟨⟨x-1, trivial⟩, Subtype.mk_lt_mk.mpr (by linarith)⟩
example : ¬ WellFoundedLT ℝ := by
  rw [WellFoundedLT.iff]; push_neg
  refine ⟨Set.univ, ⟨0, trivial⟩, ?_⟩
  rintro ⟨x, hx⟩; rw [IsMin.iff]; push_neg
  exact ⟨⟨x-1, trivial⟩, Subtype.mk_lt_mk.mpr (by linarith)⟩

/-- Exercise 8.5.8 -/
theorem IsMax.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMax x := by
  obtain ⟨x, hx⟩ := Finite.exists_max (id : X → X)
  exact ⟨x, fun b _ => hx b⟩

theorem IsMin.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMin x := by
  obtain ⟨x, hx⟩ := Finite.exists_min (id : X → X)
  exact ⟨x, fun b _ => hx b⟩

/-- Exercise 8.5.8 -/
theorem WellFoundedLT.ofFinite {X:Type} [LinearOrder X] [Finite X] : WellFoundedLT X :=
  Finite.to_wellFoundedLT

example {X:Type} [LinearOrder X] [WellFoundedLT X] (A: Set X) : WellFoundedLT A :=
  Subtype.wellFoundedLT _

theorem WellFoundedLT.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) [hwell: WellFoundedLT A] (hAB: B ⊆ A) : WellFoundedLT B := by
  set hAlin : LinearOrder A := LinearOrder.mk hA
  set hBlin : LinearOrder B := LinearOrder.mk (hA.subset hAB)
  rw [iff' hA] at hwell; rw [iff' (hA.subset hAB)]; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]
  intro a ha_B ha_C
  apply hmin _ (hAB ha_B) <;> trivial

/-- Proposition 8.5.10 / Exercise 8.5.10 -/
theorem WellFoundedLT.strong_induction {X:Type} [LinearOrder X] [WellFoundedLT X] {P:X → Prop}
  (h: ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  intro n; exact wellFounded_lt.induction n h

/-- Definition 8.5.12 (Upper bounds and strict upper bounds) -/
abbrev IsUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  ∀ y ∈ A, y ≤ x

/-- Connection with Mathlib's `upperBounds` -/
theorem IsUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsUpperBound A x ↔ x ∈ upperBounds A := by simp [IsUpperBound, upperBounds]

abbrev IsStrictUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  IsUpperBound A x ∧ x ∉ A

theorem IsStrictUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ ∀ y ∈ A, y < x := by
  constructor
  · rintro ⟨hub, hni⟩ y hy
    exact lt_of_le_of_ne (hub y hy) (fun heq => hni (heq ▸ hy))
  · intro h
    exact ⟨fun y hy => (h y hy).le, fun hx => lt_irrefl x (h x hx)⟩

theorem IsStrictUpperBound.iff' {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2: Set ℝ) 2 := fun y hy => hy.2

example : ¬ IsStrictUpperBound (.Icc 1 2: Set ℝ) 2 := by
  rintro ⟨_, hni⟩; exact hni (by norm_num [Set.mem_Icc])

example : IsStrictUpperBound (.Icc 1 2: Set ℝ) 3 :=
  ⟨fun y hy => by simp only [Set.mem_Icc] at hy; linarith [hy.2], by norm_num [Set.mem_Icc]⟩

/-- A convenient way to simplify the notion of having `x₀` as a minimal element.-/
theorem IsMin.iff_lowerbound {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) (x₀ : X) : (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩:Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . rintro ⟨ hx₀, hmin ⟩; simp [IsMin, hx₀] at *
    peel hmin with x hx _; specialize hY ⟨ _, hx ⟩ ⟨ _, hx₀ ⟩; aesop
  intro h; use h.1; simp [IsMin]; aesop

theorem IsMin.iff_lowerbound' {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) : (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . intro ⟨ ⟨ x₀, hx₀ ⟩, hmin ⟩
    have : ∃ (hx₀ : x₀ ∈ Y), IsMin (⟨ _, hx₀ ⟩:Y) := by use hx₀
    rw [iff_lowerbound hY x₀] at this; use x₀
  intro ⟨ x₀, hx₀, hmin ⟩; choose hx₀ _ using (iff_lowerbound hY x₀).mpr ⟨ hx₀, hmin ⟩; use ⟨ _, hx₀ ⟩

/-- Exercise 8.5.11 -/
example {X:Type} [PartialOrder X] {Y Y':Set X} (hY: IsTotal Y) (hY': IsTotal Y') (hY_well: WellFoundedLT Y) (hY'_well: WellFoundedLT Y') (hYY': IsTotal (Y ∪ Y': Set X)) : WellFoundedLT (Y ∪ Y': Set X) := by
  have keyY : ∀ S : Set Y, S.Nonempty → ∃ y:Y, y ∈ S ∧ ∀ z ∈ S, y ≤ z := by
    rw [WellFoundedLT.iff' hY] at hY_well
    intro S hS; obtain ⟨⟨m, hmS⟩, hmin⟩ := hY_well S hS
    exact ⟨m, hmS, fun z hz => (hY m z).elim id (fun h => hmin (b := ⟨z,hz⟩) h)⟩
  have keyY' : ∀ S : Set Y', S.Nonempty → ∃ y:Y', y ∈ S ∧ ∀ z ∈ S, y ≤ z := by
    rw [WellFoundedLT.iff' hY'] at hY'_well
    intro S hS; obtain ⟨⟨m, hmS⟩, hmin⟩ := hY'_well S hS
    exact ⟨m, hmS, fun z hz => (hY' m z).elim id (fun h => hmin (b := ⟨z,hz⟩) h)⟩
  rw [WellFoundedLT.iff' hYY']
  intro A hA
  rw [IsMin.iff_lowerbound' (hYY'.subtype)]
  set B : Set X := { x | ∃ hx : x ∈ (Y ∪ Y':Set X), (⟨x,hx⟩ : (Y∪Y':Set X)) ∈ A } with hB
  obtain ⟨⟨a, ha⟩, haA⟩ := hA
  set BY : Set Y := { y | (y:X) ∈ B } with hBY
  set BY' : Set Y' := { y | (y:X) ∈ B } with hBY'
  by_cases hcaseY : BY.Nonempty <;> by_cases hcaseY' : BY'.Nonempty
  · obtain ⟨m, hmBY, hmmin⟩ := keyY BY hcaseY
    obtain ⟨m', hmBY', hmmin'⟩ := keyY' BY' hcaseY'
    have hmU : (m:X) ∈ (Y∪Y':Set X) := Or.inl m.2
    have hm'U : (m':X) ∈ (Y∪Y':Set X) := Or.inr m'.2
    obtain ⟨hmx, hmA⟩ := hmBY
    obtain ⟨hm'x, hm'A⟩ := hmBY'
    rcases hYY' ⟨_, hmU⟩ ⟨_, hm'U⟩ with hcmp|hcmp
    · refine ⟨⟨m, hmU⟩, hmA, ?_⟩
      rintro ⟨x, hx⟩ hxA
      have hxB : x ∈ B := ⟨hx, hxA⟩
      rcases hx with hxY|hxY'
      · exact hmmin ⟨x, hxY⟩ hxB
      · exact le_trans hcmp (hmmin' ⟨x, hxY'⟩ hxB)
    · refine ⟨⟨m', hm'U⟩, hm'A, ?_⟩
      rintro ⟨x, hx⟩ hxA
      have hxB : x ∈ B := ⟨hx, hxA⟩
      rcases hx with hxY|hxY'
      · exact le_trans hcmp (hmmin ⟨x, hxY⟩ hxB)
      · exact hmmin' ⟨x, hxY'⟩ hxB
  · obtain ⟨m, hmBY, hmmin⟩ := keyY BY hcaseY
    have hmU : (m:X) ∈ (Y∪Y':Set X) := Or.inl m.2
    obtain ⟨hmx, hmA⟩ := hmBY
    refine ⟨⟨m, hmU⟩, hmA, ?_⟩
    rintro ⟨x, hx⟩ hxA
    have hxB : x ∈ B := ⟨hx, hxA⟩
    rcases hx with hxY|hxY'
    · exact hmmin ⟨x, hxY⟩ hxB
    · exact absurd ⟨⟨x,hxY'⟩, hxB⟩ hcaseY'
  · obtain ⟨m', hmBY', hmmin'⟩ := keyY' BY' hcaseY'
    have hm'U : (m':X) ∈ (Y∪Y':Set X) := Or.inr m'.2
    obtain ⟨hm'x, hm'A⟩ := hmBY'
    refine ⟨⟨m', hm'U⟩, hm'A, ?_⟩
    rintro ⟨x, hx⟩ hxA
    have hxB : x ∈ B := ⟨hx, hxA⟩
    rcases hx with hxY|hxY'
    · exact absurd ⟨⟨x,hxY⟩, hxB⟩ hcaseY
    · exact hmmin' ⟨x, hxY'⟩ hxB
  · have haB : a ∈ B := ⟨ha, haA⟩
    rcases ha with haY|haY'
    · exact absurd ⟨⟨a,haY⟩, haB⟩ hcaseY
    · exact absurd ⟨⟨a,haY'⟩, haB⟩ hcaseY'

set_option maxHeartbeats 1000000 in
/-- Lemma 8.5.14-/
theorem WellFoundedLT.partialOrder {X:Type} [PartialOrder X] (x₀ : X) : ∃ Y : Set X, IsTotal Y ∧ WellFoundedLT Y ∧ (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩: Y)) ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
  -- This proof is based on the original text with some technical simplifications.

  -- The class of well-ordered subsets `Y` of `X` that contain `x₀` as a minimal element is not named in the text,
  -- but it is convenient to give it a name (`Ω₀`) for the formalization.  Here we use `IsMin.iff_lowerbound` to
  -- simplify the notion of minimality.
  let Ω₀ := { Y : Set X | IsTotal Y ∧ WellFoundedLT Y ∧ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x}
  suffices : ∃ Y ∈ Ω₀, ¬ ∃ x, IsStrictUpperBound Y x
  . have ⟨ Y, ⟨ hY, hY'⟩, hstrict ⟩ := this; use Y, hY
    rw [IsMin.iff_lowerbound hY x₀]; tauto
  by_contra! hs
  let s : Ω₀ → X := fun Y ↦ (hs Y Y.property).choose
  replace hs (Y:Ω₀) : IsStrictUpperBound Y (s Y) := (hs Y Y.property).choose_spec

  have hpt: {x₀} ∈ Ω₀ := by
    have htotal : IsTotal ({x₀}: Set X) := by simp [IsTotal]
    let _lin : LinearOrder ({x₀}: Set X) := LinearOrder.mk htotal
    simp [Ω₀, htotal]; apply WellFoundedLT.ofFinite
  let pt : Ω₀ := ⟨ _, hpt ⟩

  -- The operation of sending a set `Y` in `Ω₀` to the smaller set `{y ∈ Y.val | y < x}`, which is also
  -- in `Ω₀` if `x ∈ Y.val \ {x₀}`, is not named explicitly in the text, but we give it a name `F` for
  -- the formalization.
  have hF {Y:Set X} (hY: Y ∈ Ω₀) {x:X} (hxy : x ∈ Y \ {x₀}) : {y ∈ Y | y < x} ∈ Ω₀ := by
    simp [Ω₀, IsTotal] at hY ⊢; choose _ hmin using hY.2.2; simp_all
    split_ands
    . convert WellFoundedLT.subset (hwell := hY.2) (B := {y ∈ Y | y < x}) _ _
      . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩; simp; solve_by_elim [hY.1]
      intro _; simp; tauto
    have := hmin _ hxy.1; contrapose! hxy; order
  classical
  let F : Ω₀ → X → Ω₀ := fun Y x ↦ if hxy : x ∈ Y.val \ {x₀} then ⟨ {y ∈ (Y:Set X) | y < x}, hF Y.property hxy ⟩ else pt
  replace hF {Y : Ω₀} {x : X} (hxy : x ∈ (Y:Set X) \ {x₀}) : F Y x = { y ∈ (Y:Set X) | y < x } := by
    simp_all [F]

  -- The set `Ω` captures the notion of a `good set`.
  set Ω := { Y : Ω₀ | ∀ x ∈ (Y:Set X) \ {x₀}, x = s (F Y x) }
  have hΩ : pt ∈ Ω := by
    simp only [Ω, Set.mem_setOf_eq]
    intro x hx
    simp only [pt, Set.mem_diff, Set.mem_singleton_iff] at hx
    exact absurd hx.1 hx.2

  -- Exercise 8.5.13
  -- Generic facts about a good set `W : Ω`.
  -- The good-set recursion and the `F` description.
  have good_eq (W : Ω) {x:X} (hx : x ∈ (W:Set X) \ {x₀}) : x = s (F W.1 x) := W.2 x hx
  have Fdesc (W : Ω) {x:X} (hx : x ∈ (W:Set X) \ {x₀}) :
      (F W.1 x : Set X) = { y ∈ (W:Set X) | y < x } := by rw [hF hx]
  -- minimal-element extraction for a good set
  have memΩ₀ (W : Ω) : IsTotal (W:Set X) ∧ WellFoundedLT (W:Set X) ∧ x₀ ∈ (W:Set X) ∧ ∀ x ∈ (W:Set X), x₀ ≤ x := W.1.2
  have keyW (W : Ω) : ∀ T : Set (W:Set X), T.Nonempty → ∃ y:(W:Set X), y ∈ T ∧ ∀ z ∈ T, y ≤ z := by
    obtain ⟨htot, hwell, -, -⟩ := memΩ₀ W
    rw [WellFoundedLT.iff' htot] at hwell
    intro T hT; obtain ⟨⟨⟨m, hmW⟩, hmT⟩, hmin⟩ := hwell T hT
    exact ⟨⟨m, hmW⟩, hmT, fun z hz => (htot ⟨m,hmW⟩ z).elim id (fun h => hmin (b := ⟨z,hz⟩) h)⟩
  have wf_min (W : Ω) (S : Set X) (hS : S ⊆ (W:Set X)) (hne : S.Nonempty) :
      ∃ m ∈ S, ∀ z ∈ S, m ≤ z := by
    set T : Set (W:Set X) := { w | (w:X) ∈ S } with hT
    have hTne : T.Nonempty := by
      obtain ⟨a, haS⟩ := hne; exact ⟨⟨a, hS haS⟩, haS⟩
    obtain ⟨⟨m, hmW⟩, hmT, hmin⟩ := keyW W T hTne
    refine ⟨m, hmT, ?_⟩
    intro z hzS
    exact hmin ⟨z, hS hzS⟩ hzS
  -- `x₀` is the minimum of any good set
  have x0min (W : Ω) : ∀ z ∈ (W:Set X), x₀ ≤ z := (memΩ₀ W).2.2.2
  have x0mem (W : Ω) : x₀ ∈ (W:Set X) := (memΩ₀ W).2.2.1
  have x0total (W : Ω) : IsTotal (W:Set X) := (memΩ₀ W).1

  -- Exercise 8.5.13
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    -- The nesting predicate `Q p` for `p ∈ Y'`.
    set Q : X → Prop := fun p =>
      (p ∈ (Y:Set X) ∧ {y ∈ (Y':Set X) | y < p} = {y ∈ (Y:Set X) | y < p})
        ∨ IsStrictUpperBound (Y:Set X) p
      with hQdef
    -- Strong induction: every `p ∈ Y'` satisfies `Q p`.
    have hnest : ∀ p ∈ (Y':Set X), Q p := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨p0, hp0Y', hp0Q⟩ := hcon
      -- minimal `p ∈ Y'` with `¬ Q p`
      set S : Set X := {q ∈ (Y':Set X) | ¬ Q q} with hSdef
      have hSsub : S ⊆ (Y':Set X) := fun q hq => hq.1
      have hSne : S.Nonempty := ⟨p0, hp0Y', hp0Q⟩
      obtain ⟨p, ⟨hpY', hpQ⟩, hpmin⟩ := wf_min Y' S hSsub hSne
      -- IH: any `q ∈ Y'` with `q < p` satisfies `Q q`
      have IH : ∀ q ∈ (Y':Set X), q < p → Q q := by
        intro q hqY' hqp
        by_contra hq
        have : p ≤ q := hpmin q ⟨hqY', hq⟩
        order
      apply hpQ
      -- handle `p = x₀`
      by_cases hpx0 : p = x₀
      · left
        refine ⟨hpx0 ▸ x0mem Y, ?_⟩
        have hempty1 : {y ∈ (Y':Set X) | y < p} = (∅:Set X) := by
          ext y; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hyY', hyx0⟩
          have := x0min Y' y hyY'; rw [hpx0] at hyx0; order
        have hempty2 : {y ∈ (Y:Set X) | y < p} = (∅:Set X) := by
          ext y; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hyY, hyx0⟩
          have := x0min Y y hyY; rw [hpx0] at hyx0; order
        rw [hempty1, hempty2]
      -- `p ≠ x₀`, so `p ∈ Y' \ {x₀}` and `F Y' p = {y ∈ Y' | y < p}`.
      have hpdiff : p ∈ (Y':Set X) \ {x₀} := ⟨hpY', hpx0⟩
      have hAeq : (F Y'.1 p : Set X) = {y ∈ (Y':Set X) | y < p} := Fdesc Y' hpdiff
      set A : Set X := {y ∈ (Y':Set X) | y < p} with hA
      have hpeqsA : p = s (F Y'.1 p) := good_eq Y' hpdiff
      -- Case split : is some `m ∈ A` a strict upper bound of `Y`?
      by_cases hcase2 : ∃ m ∈ A, IsStrictUpperBound (Y:Set X) m
      · obtain ⟨m, hmA, hmSUB⟩ := hcase2
        have hmp : m < p := hmA.2
        right
        refine ⟨fun w hw => (lt_of_le_of_lt (hmSUB.1 w hw) hmp).le, ?_⟩
        intro hpY
        have := hmSUB.1 p hpY; order
      push_neg at hcase2
      -- From the IH, every `m ∈ A` lies in `Y` with matching initial segments.
      have hAprops : ∀ m ∈ A, m ∈ (Y:Set X) ∧
          {y ∈ (Y':Set X) | y < m} = {y ∈ (Y:Set X) | y < m} := by
        intro m hmA
        rcases IH m hmA.1 hmA.2 with hfirst | hSUB
        · exact hfirst
        · exact absurd hSUB (hcase2 m hmA)
      have hAsubY : A ⊆ (Y:Set X) := fun m hmA => (hAprops m hmA).1
      -- `A` is downward closed in `Y`.
      have hAdown : ∀ a ∈ A, ∀ b ∈ (Y:Set X), b < a → b ∈ A := by
        intro a haA b hbY hba
        obtain ⟨haY, hseg⟩ := hAprops a haA
        have hbseg : b ∈ {y ∈ (Y:Set X) | y < a} := ⟨hbY, hba⟩
        rw [← hseg] at hbseg
        obtain ⟨hbY', hba'⟩ := hbseg
        exact ⟨hbY', lt_trans hba' haA.2⟩
      -- decide whether `p` is a strict upper bound of `Y`.
      by_cases hYsubA : (Y:Set X) ⊆ A
      · -- then `p` is a strict upper bound of `Y`
        right
        refine ⟨fun w hw => (hYsubA hw).2.le, ?_⟩
        intro hpY
        exact absurd (hYsubA hpY).2 (lt_irrefl p)
      · -- `Y \ A` nonempty : take its minimum `n`.
        rw [Set.not_subset] at hYsubA
        obtain ⟨w0, hw0Y, hw0A⟩ := hYsubA
        set D : Set X := {y ∈ (Y:Set X) | y ∉ A} with hDdef
        have hDsub : D ⊆ (Y:Set X) := fun y hy => hy.1
        have hDne : D.Nonempty := ⟨w0, hw0Y, hw0A⟩
        obtain ⟨n, ⟨hnY, hnA⟩, hnmin⟩ := wf_min Y D hDsub hDne
        -- show `A = {y ∈ Y | y < n}`
        have hseg_n : A = {y ∈ (Y:Set X) | y < n} := by
          apply Set.eq_of_subset_of_subset
          · intro a haA
            refine ⟨hAsubY haA, ?_⟩
            -- `a < n` by totality of `Y`
            rcases x0total Y ⟨a, hAsubY haA⟩ ⟨n, hnY⟩ with hle | hle
            · rcases lt_or_eq_of_le (by simpa using hle) with h | h
              · exact h
              · exact absurd (h ▸ haA) hnA
            · -- `n ≤ a` impossible : would force `n ∈ A`
              have hna : n < a := by
                rcases lt_or_eq_of_le (by simpa using hle) with h | h
                · exact h
                · exact absurd (h ▸ haA) hnA
              exact absurd (hAdown a haA n hnY hna) hnA
          · intro c hc
            obtain ⟨hcY, hcn⟩ := hc
            by_contra hcA
            have : n ≤ c := hnmin c ⟨hcY, hcA⟩
            order
        -- `x₀ ∈ A`, hence `n ≠ x₀`.
        have hx0A : x₀ ∈ A := by
          refine ⟨x0mem Y', ?_⟩
          exact lt_of_le_of_ne (x0min Y' p hpY') (Ne.symm hpx0)
        have hnx0 : n ≠ x₀ := fun hn0 => hnA (hn0 ▸ hx0A)
        -- hence `n` is the `s`-successor of `A`, equal to `p`.
        have hndiff : n ∈ (Y:Set X) \ {x₀} := ⟨hnY, hnx0⟩
        have hFYn : (F Y.1 n : Set X) = {y ∈ (Y:Set X) | y < n} := Fdesc Y hndiff
        have hFeq : F Y.1 n = F Y'.1 p := by
          apply Subtype.ext
          rw [hFYn, hAeq, hseg_n]
        have hnp : n = p := by
          have := good_eq Y hndiff
          rw [hFeq, ← hpeqsA] at this
          exact this
        -- conclude the first disjunct
        left
        refine ⟨hnp ▸ hnY, ?_⟩
        rw [← hA, hseg_n, hnp]
    -- Apply the nesting result to the given `x`.
    obtain ⟨hxY', hxnY⟩ := h
    rcases hnest x hxY' with ⟨hxY, _⟩ | hSUB
    · exact absurd hxY hxnY
    · exact hSUB

  have : IsTotal Ω := by
    unfold IsTotal; by_contra!; obtain ⟨ ⟨ ⟨ Y, hY1 ⟩, hY2 ⟩, ⟨ ⟨ Y', hY'1⟩, hY'2 ⟩, h1, h2 ⟩ := this
    simp_all [Set.not_subset]
    choose x₁ hx₁ hx₁' using h1; choose x₂ hx₂ hx₂' using h2
    observe h1 : IsStrictUpperBound Y x₂
    observe h2 : IsStrictUpperBound Y' x₁
    simp [IsStrictUpperBound.iff] at h1 h2
    specialize h1 _ hx₁; specialize h2 _ hx₂; order
  set Y_infty : Set X := ⋃ Y:Ω, Y
  have hmem : x₀ ∈ Y_infty := by simp [Y_infty]; use pt; grind
  have hmin {x:X} (hx: x ∈ Y_infty) : x₀ ≤ x := by
    simp only [Y_infty, Set.mem_iUnion] at hx
    obtain ⟨Y, hxY⟩ := hx
    exact (Y.1.2).2.2.2 x hxY
  have htotal : IsTotal Y_infty := by
    intro ⟨ x, hx ⟩ ⟨ x', hx'⟩; simp [Y_infty] at hx hx'
    obtain ⟨ Y, ⟨ hYΩ₀, hYΩ ⟩, hxY ⟩ := hx; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx'
    specialize this ⟨ _, hYΩ ⟩ ⟨ _, hY'Ω ⟩; simp [Ω₀] at this ⊢ hYΩ₀ hY'Ω₀
    obtain this | this := this
    . replace hY'Ω₀ := hY'Ω₀.1 ⟨ _, this hxY ⟩ ⟨ _, hxY' ⟩; simpa using hY'Ω₀
    replace hYΩ₀ := hYΩ₀.1 ⟨ _, hxY ⟩ ⟨ _, this hxY' ⟩; simpa using hYΩ₀
  have hwell : WellFoundedLT Y_infty := by
    rw [iff' htotal]; intro A ⟨ ⟨a, ha⟩, haA ⟩
    simp [Y_infty] at ha; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, haY ⟩ := ha
    simp [Ω₀, iff' hYΩ₀.1] at hYΩ₀
    choose b hb hbY hbmin using hYΩ₀.2.1 {x:Y | ∃ x':A, (x:X) = x'} (by use ⟨ _, haY ⟩; simp [ha, haA])
    simp at hbY; choose hbY_infty hbA using hbY
    rw [IsMin.iff_lowerbound' (IsTotal.subtype htotal)]
    use ⟨ _, hbY_infty ⟩, hbA; intro ⟨ x, hx ⟩ hxA
    simp [Y_infty] at hx ⊢; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    by_cases hxinY : x ∈ Y
    · -- x ∈ Y, so x is in the restricted set; use minimality of b
      rcases hYΩ₀.1 ⟨b, hb⟩ ⟨x, hxinY⟩ with hbx | hxb
      · simpa using hbx
      · have := hbmin (b := ⟨⟨x, hxinY⟩, ⟨⟨x, hx⟩, hxA⟩, rfl⟩) hxb
        simpa using this
    · -- x ∈ Y' \ Y, use ex_8_5_13
      have hsub := ex_8_5_13 (Y := ⟨_, hYΩ⟩) (Y' := ⟨_, hY'Ω⟩) x ⟨hxY', hxinY⟩
      rw [IsStrictUpperBound.iff] at hsub
      exact (hsub b hb).le
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    exact ⟨htotal, hwell, hmem, fun x hx => hmin hx⟩
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    have hsub := hs ⟨ _, hY_inftyΩ₀ ⟩
    rw [IsStrictUpperBound.iff] at hsub
    rintro ⟨x, (hx|hx)⟩ ⟨y, (hy|hy)⟩
    · exact htotal ⟨x, hx⟩ ⟨y, hy⟩
    · simp only [Set.mem_singleton_iff] at hy; subst hy
      left; exact (hsub x hx).le
    · simp only [Set.mem_singleton_iff] at hx; subst hx
      right; exact (hsub y hy).le
    · simp only [Set.mem_singleton_iff] at hx hy; subst hx; subst hy
      left; exact le_refl _
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    have hsub := hs ⟨ _, hY_inftyΩ₀ ⟩
    rw [IsStrictUpperBound.iff] at hsub
    have keyInf : ∀ S : Set Y_infty, S.Nonempty → ∃ y:Y_infty, y ∈ S ∧ ∀ z ∈ S, y ≤ z := by
      have hwell' := hwell
      rw [WellFoundedLT.iff' htotal] at hwell'
      intro S hS; obtain ⟨⟨m, hmS⟩, hmm⟩ := hwell' S hS
      exact ⟨m, hmS, fun z hz => (htotal m z).elim id (fun h => hmm (b := ⟨z,hz⟩) h)⟩
    rw [WellFoundedLT.iff' hYs_total]
    intro A hA
    rw [IsMin.iff_lowerbound' (hYs_total.subtype)]
    -- project A to Y_infty
    set SInf : Set Y_infty := { y | ∃ hy : (y:X) ∈ (Y_infty ∪ {sY_infty}:Set X), (⟨(y:X), hy⟩ : (Y_infty ∪ {sY_infty}:Set X)) ∈ A } with hSInf
    by_cases hcase : SInf.Nonempty
    · obtain ⟨m, ⟨hmU, hmA⟩, hmmin⟩ := keyInf SInf hcase
      have hmU2 : (m:X) ∈ (Y_infty ∪ {sY_infty}:Set X) := Or.inl m.2
      refine ⟨⟨m, hmU2⟩, hmA, ?_⟩
      rintro ⟨x, hx⟩ hxA
      rcases hx with hxInf|hxS
      · exact hmmin ⟨x, hxInf⟩ ⟨Or.inl hxInf, hxA⟩
      · simp only [Set.mem_singleton_iff] at hxS; subst hxS
        exact (hsub m m.2).le
    · -- A must be {sY_infty}
      obtain ⟨⟨a, ha⟩, haA⟩ := hA
      have hasY : a = sY_infty := by
        rcases ha with haInf|haS
        · exact absurd ⟨⟨a,haInf⟩, Or.inl haInf, haA⟩ hcase
        · simpa using haS
      have hmU2 : a ∈ (Y_infty ∪ {sY_infty}:Set X) := ha
      refine ⟨⟨a, hmU2⟩, haA, ?_⟩
      rintro ⟨x, hx⟩ hxA
      rcases hx with hxInf|hxS
      · exact absurd ⟨⟨x,hxInf⟩, Or.inl hxInf, hxA⟩ hcase
      · simp only [Set.mem_singleton_iff] at hxS; subst hxS
        rw [Subtype.mk_le_mk, hasY]
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := Or.inl hmem
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by
    rintro x (hx | hx)
    · exact hmin hx
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      have hsub := hs ⟨ _, hY_inftyΩ₀ ⟩
      rw [IsStrictUpperBound.iff] at hsub
      exact (hsub x₀ hmem).le
  have hYs_Ω₀ : (Y_infty ∪ {sY_infty}) ∈ Ω₀ := by
    simpa [-Set.union_singleton, Ω₀, hYs_total, hYs_well, hYs_mem]
  specialize hs ⟨ _, hY_inftyΩ₀ ⟩
  simp [IsStrictUpperBound.iff] at hs
  have hYs_Ω : ⟨ _, hYs_Ω₀ ⟩ ∈ Ω := by
    simp [Ω, -Set.mem_insert_iff, -and_imp]
    intro x hx hxx₀
    rcases hx with rfl | hx
    . unfold sY_infty; congr 1
      symm; apply Subtype.val_injective; convert hF _
      . ext; simp; constructor
        . grind
        rintro ⟨ _ | _, _ ⟩
        . order
        assumption
      simp; specialize hs (y := x₀) (by simp [hmem]); order
    have hx' := hx; simp [Y_infty] at hx'; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, hxY ⟩ := hx'
    have hYΩ' := hYΩ; simp [Ω] at hYΩ
    convert hYΩ _ hxY hxx₀ using 2
    apply Subtype.val_injective
    rw [hF, hF]
    . ext y; simp [Y_infty]; intro hyx; constructor
      . rintro (rfl | ⟨ Y', ⟨hY'Ω₀, hY'Ω⟩, hyY' ⟩)
        . specialize hs _ hx; order
        by_contra!
        specialize ex_8_5_13 (Y := ⟨_, hYΩ'⟩) (Y' := ⟨_, hY'Ω⟩) y (by grind)
        rw [IsStrictUpperBound.iff] at ex_8_5_13
        specialize ex_8_5_13 x (by simp [hxY]); order
      grind
    all_goals simp [hxY, hx, hxx₀]
  have hs_mem : sY_infty ∈ Y_infty := Set.mem_iUnion_of_mem ⟨ _, hYs_Ω ⟩ (by simp)
  specialize hs _ hs_mem; order


/-- Lemma 8.5.15 (Zorn's lemma) / Exercise 8.5.14 -/
theorem Zorns_lemma {X:Type} [PartialOrder X] [Nonempty X]
  (hchain: ∀ Y:Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨Y, hYtot, hYwell, ⟨hx₀mem, hx₀min⟩, hnostrict⟩ := WellFoundedLT.partialOrder x₀
  have hYne : Y.Nonempty := ⟨x₀, hx₀mem⟩
  obtain ⟨x, hxub⟩ := hchain Y ⟨hYtot, hYne⟩
  refine ⟨x, ?_⟩
  rw [IsMax.iff]
  rintro ⟨y, hxy⟩
  apply hnostrict
  refine ⟨y, ?_, ?_⟩
  · intro z hz; exact le_trans (hxub z hz) hxy.le
  · intro hyY
    have hyx := hxub y hyY
    exact absurd (le_antisymm hyx hxy.le).symm (ne_of_lt hxy)

/-- Exercise 8.5.1 -/
def empty_set_partial_order [h₀: LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  apply isTrue
  refine ⟨{ le := h₀.le, lt := fun x => x.elim, le_refl := fun x => x.elim, le_antisymm := fun x => x.elim, le_trans := fun x => x.elim, lt_iff_le_not_ge := fun x => x.elim }, rfl⟩

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  apply isTrue
  refine ⟨{ le := h₀.le, lt := fun x => x.elim, le_refl := fun x => x.elim, le_antisymm := fun x => x.elim, le_trans := fun x => x.elim, lt_iff_le_not_ge := fun x => x.elim, le_total := fun x => x.elim, toDecidableLE := fun x => x.elim, min := fun x => x.elim, max := fun x => x.elim, min_def := fun x => x.elim, max_def := fun x => x.elim }, rfl⟩

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) := by
  apply isTrue
  exact ⟨⟨⟨fun x => x.elim⟩⟩⟩

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) :=
  ⟨Fin 3, ⟨fun x y => x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)⟩,
    fun _ => Or.inl rfl,
    fun x y hxy hyx => by
      rcases hxy with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact h
      · rcases hyx with h|⟨h,_⟩|⟨_,h⟩ <;> exact absurd h (by decide)
      · rcases hyx with h|⟨h,_⟩|⟨h,_⟩ <;> exact absurd h (by decide),
    by
      intro htrans
      have := htrans 0 1 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rcases this with h|⟨_,h⟩|⟨h,_⟩ <;> exact absurd h (by decide)⟩

example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) :=
  ⟨Fin 2, ⟨fun _ _ => True⟩, fun _ => trivial, fun _ _ _ _ _ => trivial,
    fun h => absurd (h 0 1 trivial trivial) (by decide)⟩

example : ∃ (X:Type) (h₀: LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) :=
  ⟨Fin 1, ⟨fun _ _ => False⟩, fun _ _ hxy _ => hxy.elim, fun _ _ _ hxy _ => hxy.elim,
    fun h => (h 0).elim⟩

/-- Exercise 8.5.3 -/
example : ∃ (h₀: PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  refine ⟨{ le := fun x y ↦ ∃ n, y = n * x
            lt := fun x y ↦ (∃ n, y = n * x) ∧ ¬ (∃ n, x = n * y)
            le_refl := fun x => ⟨1, by simp⟩
            le_trans := ?_
            le_antisymm := ?_
            lt_iff_le_not_ge := fun x y => Iff.rfl }, rfl⟩
  · rintro a b c ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨n*m, by rw [mul_assoc]⟩
  · rintro a b ⟨m, rfl⟩ ⟨n, hn⟩
    have key : (n*m) = 1 := by
      have h2 : a = (n*m)*a := by rw [mul_assoc, ← hn]
      have : (n*m)*a = 1*a := by rw [← h2, one_mul]
      exact mul_right_cancel this
    have hm : m = 1 := by
      have hmn : (n:ℕ) * (m:ℕ) = 1 := by exact_mod_cast key
      have : (m:ℕ) = 1 := Nat.eq_one_of_mul_eq_one_left hmn
      exact_mod_cast this
    rw [hm, one_mul]

example : ¬ ∃ (h₀: LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  rintro ⟨h₀, hle⟩
  have htot := h₀.le_total (2:PNat) (3:PNat)
  rw [hle] at htot
  simp only at htot
  rcases htot with ⟨n, hn⟩|⟨n, hn⟩
  · have : (3:ℕ) = (n:ℕ)*2 := by exact_mod_cast hn
    omega
  · have : (2:ℕ) = (n:ℕ)*3 := by exact_mod_cast hn
    omega

/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by
  rintro ⟨⟨x, hx⟩, hmin⟩
  have hx' : x > 0 := hx
  have hmem : x/2 ∈ {x:ℝ | x > 0} := by simp only [Set.mem_setOf_eq]; linarith
  have hle : (⟨x/2, hmem⟩ : {x:ℝ|x>0}) ≤ ⟨x, hx⟩ := by rw [Subtype.mk_le_mk]; linarith
  have := hmin hle
  rw [Subtype.mk_le_mk] at this
  linarith

/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  refine ⟨{ le := fun x y => f x < f y ∨ x = y
            le_refl := fun x => Or.inr rfl
            le_trans := ?_
            le_antisymm := ?_ }, rfl⟩
  · intro a b c hab hbc
    rcases hab with h1|rfl <;> rcases hbc with h2|rfl
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr rfl
  · intro a b hab hba
    rcases hab with h1|h
    · rcases hba with h2|h
      · exact absurd h1 (lt_asymm h2)
      · exact h.symm
    · exact h

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (h: LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  apply isFalse
  intro H
  obtain ⟨h₀, hle⟩ := H Bool Unit inferInstance (fun _ => ())
  have := h₀.le_total false true
  rw [hle] at this
  simp at this

-- Final part of Exercise 8.5.5; if the answer to the previous part is "no", modify the hypotheses to make it true.

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

noncomputable def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x := ⟨ .Iic x, by simp ⟩
  invFun S := S.property.choose
  left_inv := by
    intro x
    simp only
    have h := (⟨ Set.Iic x, by simp ⟩ : OrderIdeals X).property.choose_spec
    have : Set.Iic (Subtype.property (⟨ Set.Iic x, by simp ⟩ : OrderIdeals X)).choose = Set.Iic x := h.2
    exact (Set.Iic_injective this)
  right_inv := by
    intro ⟨S, hS⟩
    apply Subtype.ext
    exact hS.choose_spec.2
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Set.le_eq_subset, Set.Iic_subset_Iic]
  }

/-- Exercise 8.5.7 -/
example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  sorry

example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
 sorry

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by
  classical
  have minof : ∀ (Y : Set X), Y.Nonempty → ∃ m, m ∈ Y ∧ ∀ z ∈ Y, m ≤ z := by
    intro Y hY
    obtain ⟨⟨m, hmY⟩, hm⟩ := hmin Y hY
    refine ⟨m, hmY, ?_⟩
    intro z hz
    rcases le_total m z with h|h
    · exact h
    · exact hm (b := ⟨z, hz⟩) h
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  set U : X → Set X := fun x => {y | x < y} with hU
  set a0 := (minof Set.univ (Set.univ_nonempty)).choose with ha0
  set a : ℕ → X := fun n => Nat.rec a0 (fun _ prev =>
      if h : (U prev).Nonempty then (minof (U prev) h).choose else prev) n with ha
  have ha_zero : a 0 = a0 := rfl
  have ha_succ : ∀ n, a (n+1) = if h : (U (a n)).Nonempty then (minof (U (a n)) h).choose else a n := by
    intro n; rfl
  have key : ∀ n, {x | x ≤ a n}.Finite := by
    intro n
    induction n with
    | zero =>
      have : {x | x ≤ a 0} = {a 0} := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hy
          have hmin0 := (minof Set.univ Set.univ_nonempty).choose_spec
          rw [← ha0] at hmin0
          have := hmin0.2 y (Set.mem_univ y)
          rw [ha_zero] at *
          exact le_antisymm hy this
        · rintro rfl; exact le_refl _
      rw [this]; exact Set.finite_singleton _
    | succ n ih =>
      have hUne : (U (a n)).Nonempty := by
        by_contra he
        rw [Set.not_nonempty_iff_eq_empty] at he
        have : (Set.univ : Set X) = {x | x ≤ a n} := by
          ext y; simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
          by_contra hy
          rw [not_le] at hy
          exact (Set.eq_empty_iff_forall_notMem.mp he y) hy
        have : (Set.univ : Set X).Finite := this ▸ ih
        exact hinf.not_finite (Set.finite_univ_iff.mp this)
      have hspec := (minof (U (a n)) hUne).choose_spec
      have han1 : a (n+1) = (minof (U (a n)) hUne).choose := by
        rw [ha_succ]; rw [dif_pos hUne]
      have hbetween : {x | x ≤ a (n+1)} = {x | x ≤ a n} ∪ {a (n+1)} := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro hy
          rcases le_or_gt y (a n) with h|h
          · exact Or.inl h
          · have hyU : y ∈ U (a n) := h
            have := hspec.2 y hyU
            rw [← han1] at this
            exact Or.inr (le_antisymm hy this)
        · rintro (h|rfl)
          · have : a n < a (n+1) := by rw [han1]; exact hspec.1
            exact le_trans h this.le
          · exact le_refl _
      rw [hbetween]
      exact Set.Finite.union ih (Set.finite_singleton _)
  have hincr : ∀ n, a n < a (n+1) := by
    intro n
    have hUne : (U (a n)).Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      have heq : (Set.univ : Set X) = {x | x ≤ a n} := by
        ext y; simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
        by_contra hy
        rw [not_le] at hy
        exact (Set.eq_empty_iff_forall_notMem.mp he y) hy
      have : (Set.univ : Set X).Finite := heq ▸ key n
      exact hinf.not_finite (Set.finite_univ_iff.mp this)
    have hspec := (minof (U (a n)) hUne).choose_spec
    have han1 : a (n+1) = (minof (U (a n)) hUne).choose := by
      rw [ha_succ]; rw [dif_pos hUne]
    rw [han1]; exact hspec.1
  have hmono : StrictMono a := strictMono_nat_of_lt_succ hincr
  obtain ⟨⟨M, hMrange⟩, hMmax⟩ := hmax (Set.range a) ⟨a 0, Set.mem_range_self 0⟩
  obtain ⟨k, hk⟩ := hMrange
  have hMlt : M < a (k+1) := by rw [← hk]; exact hincr k
  have hle := hMmax (b := ⟨a (k+1), Set.mem_range_self (k+1)⟩) (by rw [Subtype.mk_le_mk]; exact hMlt.le)
  rw [Subtype.mk_le_mk] at hle
  exact absurd hMlt (not_lt.mpr hle)


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's `Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by rintro ⟨x,y⟩; right; exact ⟨rfl, le_refl y⟩
  le_antisymm := by
    rintro ⟨x,y⟩ ⟨x',y'⟩ (h|⟨rfl,h⟩) (h2|⟨h3,h4⟩)
    · exact absurd h (lt_asymm h2)
    · exact absurd h3.symm (ne_of_lt h)
    · exact absurd rfl (ne_of_lt h2)
    · exact congrArg (Prod.mk x) (le_antisymm h h4)
  le_trans := by
    rintro ⟨x,y⟩ ⟨x',y'⟩ ⟨x'',y''⟩ (h|⟨rfl,h⟩) (h2|⟨rfl,h2⟩)
    · left; exact lt_trans h h2
    · left; exact h
    · left; exact h2
    · right; exact ⟨rfl, le_trans h h2⟩
}

noncomputable instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) :=
  LinearOrder.mk (by
    rintro ⟨x,y⟩ ⟨x',y'⟩
    rcases lt_trichotomy x x' with h|rfl|h
    · left; left; exact h
    · rcases le_total y y' with hy|hy
      · left; right; exact ⟨rfl, hy⟩
      · right; right; exact ⟨rfl, hy⟩
    · right; left; exact h)

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
  WellFoundedLT (Lex' (X × Y)) := by
  constructor
  rw [WellFounded.wellFounded_iff_has_min]
  intro S hS
  obtain ⟨a, ha⟩ := hS
  let S1 : Set X := {x | ∃ y, (⟨x,y⟩ : X × Y) ∈ S}
  have hS1 : S1.Nonempty := ⟨a.1, a.2, by cases a; exact ha⟩
  obtain ⟨x0, ⟨y00, hx0mem⟩, hx0min⟩ := (wellFounded_lt (α := X)).has_min S1 hS1
  let S2 : Set Y := {y | (⟨x0,y⟩ : X × Y) ∈ S}
  have hS2 : S2.Nonempty := ⟨y00, hx0mem⟩
  obtain ⟨y0, hy0mem, hy0min⟩ := (wellFounded_lt (α := Y)).has_min S2 hS2
  refine ⟨(⟨x0,y0⟩ : X × Y), hy0mem, ?_⟩
  rintro ⟨x',y'⟩ hmem hlt
  obtain ⟨hle, hnle⟩ := hlt
  have hle' : (x' < x0) ∨ (x' = x0 ∧ y' ≤ y0) := hle
  rcases hle' with hlt'|⟨rfl,hle2⟩
  · exact hx0min x' ⟨y', hmem⟩ hlt'
  · refine hy0min y' hmem (lt_of_le_of_ne hle2 ?_)
    rintro rfl; exact hnle (Or.inr ⟨rfl, le_refl _⟩)


end Chapter8
