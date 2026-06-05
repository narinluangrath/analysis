import Mathlib.Tactic
import Mathlib.Order.Extension.Linear
import Analysis.Section_8_4

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of {name}`PartialOrder`, {name}`LinearOrder`, and {name}`WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib {name}`PartialOrder` class. -/

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

/-- Definition 8.5.3.  Here we just review the Mathlib {name}`LinearOrder` class. -/
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
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℚ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : LinearOrder EReal)


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

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's {name}`IsMax` and {name}`IsMin`. -/
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

/-- Connection with Mathlib's {name}`upperBounds` -/
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

/-- A convenient way to simplify the notion of having {name}`x₀` as a minimal element.-/
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

/-- Exercise 8.5.3: The divisibility ordering on PNat. -/
@[reducible] def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := fun x => ⟨1, by simp⟩
  le_antisymm := by
    rintro x y ⟨n, rfl⟩ ⟨m, hm⟩
    -- n * x = y and x = m * (n * x), so m * n = 1 as naturals
    have hmn : (m : ℕ) * n = 1 := by
      have h : (x:ℕ) = (m:ℕ) * ((n:ℕ) * (x:ℕ)) := by exact_mod_cast hm
      have h2 : (x:ℕ) * 1 = (x:ℕ) * ((m:ℕ)*n) := by
        conv_lhs => rw [mul_one, h]
        ring
      have := Nat.eq_of_mul_eq_mul_left x.pos h2
      omega
    have hn1 : (n:ℕ) = 1 := Nat.eq_one_of_mul_eq_one_left hmn
    have : n = 1 := by exact_mod_cast hn1
    subst this; simp
  le_trans := by
    rintro x y z ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨m * n, by rw [mul_assoc]⟩
  lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl

theorem PNat.divOrder_exists :
    ∃ (h₀ : PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
  ⟨PNat.divOrder, rfl⟩

theorem PNat.divOrder_not_linear :
    ¬∃ (h₀ : LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  rintro ⟨h₀, hle⟩
  have htot := h₀.le_total 2 3
  rw [hle] at htot
  simp only at htot
  rcases htot with ⟨n, hn⟩ | ⟨n, hn⟩
  · -- 3 = n * 2, impossible by parity
    have : (3:ℕ) = n * 2 := by exact_mod_cast hn
    omega
  · -- 2 = n * 3, impossible
    have : (2:ℕ) = n * 3 := by exact_mod_cast hn
    have hn1 : (1:ℕ) ≤ n := n.pos
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


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
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


/-- Exercise 8.5.15 -/
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by
  -- no injection X → Y means ¬ #X ≤ #Y, so #Y ≤ #X
  have hXY : ¬ (Cardinal.mk X ≤ Cardinal.mk Y) := by
    rw [Cardinal.le_def]
    rintro ⟨f⟩
    exact h ⟨f, f.injective⟩
  have hYX : Cardinal.mk Y ≤ Cardinal.mk X := by
    rcases le_total (Cardinal.mk X) (Cardinal.mk Y) with hle | hle
    · exact absurd hle hXY
    · exact hle
  rw [Cardinal.le_def] at hYX
  obtain ⟨g⟩ := hYX
  exact ⟨g, g.injective⟩

/-- Exercise 8.5.16: The set of partial orderings on X, ordered by "coarser than",
is itself a partial order. -/
instance PartialOrder.coarserOrder (X : Type) : PartialOrder (PartialOrder X) where
  le p1 p2 := ∀ x y : X, p1.le x y → p2.le x y
  le_refl := by simp
  le_trans p1 p2 p3 h12 h23 := fun x y h => h23 x y (h12 x y h)
  le_antisymm p1 p2 h12 h21 := by ext x y; exact ⟨h12 x y, h21 x y⟩

/-- The divisibility ordering on PNat is coarser than the usual ordering. -/
example : PNat.divOrder ≤ (inferInstance : PartialOrder PNat) := by
  intro x y h
  obtain ⟨n, rfl⟩ := h
  show x ≤ n * x
  exact Nat.le_mul_of_pos_left x n.pos

/-- The discrete ordering (x ≤ y ↔ x = y) is the unique minimal element. -/
@[reducible] def PartialOrder.discrete (X : Type) : PartialOrder X where
  le x y := x = y
  le_refl := fun _ ↦ rfl
  le_antisymm := fun _ _ h _ ↦ h
  le_trans := fun _ _ _ h1 h2 ↦ h1.trans h2

theorem PartialOrder.discrete_isBot (X : Type) (p : PartialOrder X) :
    PartialOrder.discrete X ≤ p := by
  intro x y h
  show p.le x y
  rw [show x = y from h]

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by
  intro p _; exact discrete_isBot X p

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) :
    p = discrete X := by
  have h1 : p ≤ discrete X := h (discrete_isBot X p)
  have h2 : discrete X ≤ p := discrete_isBot X p
  exact (coarserOrder X).le_antisymm p (discrete X) h1 h2

/-- A partial ordering is maximal in the coarser order iff it is total. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by
  constructor
  · -- max → total
    intro hmax
    by_contra hnt
    unfold IsTotal at hnt; push_neg at hnt
    obtain ⟨a, b, hab, hba⟩ := hnt
    -- build q extending p with a ≤ b
    have hne : a ≠ b := fun h => hab (h ▸ p.le_refl a)
    let q : PartialOrder X := {
      le := fun x y => p.le x y ∨ (p.le x a ∧ p.le b y)
      lt := fun x y => (p.le x y ∨ (p.le x a ∧ p.le b y)) ∧ ¬ (p.le y x ∨ (p.le y a ∧ p.le b x))
      lt_iff_le_not_ge := fun _ _ => Iff.rfl
      le_refl := fun x => Or.inl (p.le_refl x)
      le_trans := by
        rintro x y z (hxy|⟨hxa,hby⟩) (hyz|⟨hya,hbz⟩)
        · exact Or.inl (p.le_trans _ _ _ hxy hyz)
        · exact Or.inr ⟨p.le_trans _ _ _ hxy hya, hbz⟩
        · exact Or.inr ⟨hxa, p.le_trans _ _ _ hby hyz⟩
        · exact absurd (p.le_trans _ _ _ hby hya) hba
      le_antisymm := by
        rintro x y (hxy|⟨hxa,hby⟩) (hyx|⟨hya,hbx⟩)
        · exact p.le_antisymm _ _ hxy hyx
        · exact absurd (p.le_trans _ _ _ (p.le_trans _ _ _ hbx hxy) hya) hba
        · exact absurd (p.le_trans _ _ _ (p.le_trans _ _ _ hby hyx) hxa) hba
        · exact absurd (p.le_trans _ _ _ hby hya) hba
    }
    have hpq : p ≤ q := fun x y h => Or.inl h
    have hqp : q ≤ p := hmax hpq
    have : p.le a b := hqp a b (Or.inr ⟨p.le_refl a, p.le_refl b⟩)
    exact hab this
  · -- total → max
    intro htot q hpq x y hq
    rcases htot x y with h|h
    · exact h
    · have : q.le y x := hpq y x h
      have : x = y := q.le_antisymm x y hq this
      exact this ▸ p.le_refl x

/-- Any partial ordering extends to a total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by
  haveI : IsPartialOrder X p.le := {
    refl := p.le_refl
    trans := fun x y z => p.le_trans x y z
    antisymm := fun x y => p.le_antisymm x y }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder (α := X) p.le
  haveI := hs
  let q : PartialOrder X := {
    le := s
    lt := fun x y => s x y ∧ ¬ s y x
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
    le_refl := fun x => refl_of s x
    le_trans := fun x y z => trans_of s
    le_antisymm := fun x y h1 h2 => antisymm_of s h1 h2 }
  refine ⟨q, ?_, ?_⟩
  · intro x y h; exact hps x y h
  · intro x y; exact total_of s x y

/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 :=
  exists_set_singleton_intersect h hne

/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by
  obtain ⟨m, hm⟩ := zorn_subset {S : Set X | IsTotal S} (by
    intro c hcS hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    -- ⋃₀ c is total
    show IsTotal (⋃₀ c : Set X)
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨A, hAc, hxA⟩ := hx
    obtain ⟨B, hBc, hyB⟩ := hy
    -- A, B comparable in the chain
    rcases eq_or_ne A B with rfl | hAB
    · have hAtot : IsTotal (A : Set X) := hcS hAc
      have := hAtot ⟨x, hxA⟩ ⟨y, hyB⟩
      simpa [Subtype.mk_le_mk] using this
    · rcases hchain hAc hBc hAB with hsub | hsub
      · have hBtot : IsTotal (B : Set X) := hcS hBc
        have := hBtot ⟨x, hsub hxA⟩ ⟨y, hyB⟩
        simpa [Subtype.mk_le_mk] using this
      · have hAtot : IsTotal (A : Set X) := hcS hAc
        have := hAtot ⟨x, hxA⟩ ⟨y, hsub hyB⟩
        simpa [Subtype.mk_le_mk] using this)
  exact ⟨m, hm⟩

theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) :
    ∃ x : X, IsMax x := by
  obtain ⟨M, hM⟩ := hhausdorff
  obtain ⟨hMtot, hMmax⟩ := hM
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  -- M is nonempty
  have hMne : M.Nonempty := by
    rcases Set.eq_empty_or_nonempty M with he | hne
    · exfalso
      have hsingle : IsTotal ({x₀} : Set X) := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb
        left; exact le_refl _
      have := hMmax (y := {x₀}) hsingle (by rw [he]; exact Set.empty_subset _)
      rw [he] at this
      exact absurd this (by simp [Set.subset_empty_iff])
    · exact hne
  obtain ⟨u, hub⟩ := hchain M ⟨hMtot, hMne⟩
  refine ⟨u, ?_⟩
  rw [IsMax.iff]
  rintro ⟨y, huy⟩
  -- y > u ≥ all of M, so M ∪ {y} is total and strictly larger
  have hyM : y ∉ M := fun hy => absurd (hub y hy) huy.not_ge
  have hytot : IsTotal (insert y M : Set X) := by
    rintro ⟨a, ha⟩ ⟨c, hc⟩
    rcases Set.mem_insert_iff.mp ha with rfl | ha' <;>
      rcases Set.mem_insert_iff.mp hc with rfl | hc'
    · left; exact le_refl _
    · right; rw [Subtype.mk_le_mk]; exact le_trans (hub c hc') huy.le
    · left; rw [Subtype.mk_le_mk]; exact le_trans (hub a ha') huy.le
    · have := hMtot ⟨a, ha'⟩ ⟨c, hc'⟩; simpa [Subtype.mk_le_mk] using this
  have hsub : M ⊆ insert y M := Set.subset_insert y M
  have := hMmax (y := insert y M) hytot hsub
  exact hyM (this (Set.mem_insert y M))

/-- Exercise 8.5.19: A well-ordered subset of X: a subset with a linear order and
well-foundedness. -/
structure WellOrderedSubset (X : Type) where
  carrier : Set X
  ord : LinearOrder carrier
  wf : @WellFoundedLT carrier ord.toLT

/-- (W, ≤) is an initial segment of (W', ≤') if W ⊆ W', the orderings agree on W,
and W = \{y ∈ W' : y <' x\} for some x ∈ W'. -/
def WellOrderedSubset.IsInitialSegment {X : Type}
    (W W' : WellOrderedSubset X) : Prop :=
  ∃ x : W'.carrier,
    W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x} ∧
    ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
      W.ord.le a b ↔ W'.ord.le ⟨a, ha⟩ ⟨b, hb⟩

theorem WellOrderedSubset.IsInitialSegment.subset {X : Type}
    {W W' : WellOrderedSubset X} (h : W.IsInitialSegment W') :
    W.carrier ⊂ W'.carrier := by
  obtain ⟨x, hWeq, _⟩ := h
  constructor
  · -- W.carrier ⊆ W'.carrier
    rw [hWeq]
    rintro a ⟨z, _, rfl⟩
    exact z.2
  · -- not W'.carrier ⊆ W.carrier : x ∈ W'.carrier but x ∉ W.carrier
    intro hsub
    have hxW : (x:X) ∈ W.carrier := hsub x.2
    rw [hWeq] at hxW
    obtain ⟨z, hz, hzx⟩ := hxW
    have hzx' : z = x := Subtype.ext hzx
    rw [hzx'] at hz
    exact absurd (W'.ord.lt_iff_le_not_ge x x |>.mp hz).2 (not_not.mpr (W'.ord.le_refl x))

/-- The ordering on well-ordered subsets: equal or initial segment. -/
instance WellOrderedSubset.instPartialOrder (X : Type) :
    PartialOrder (WellOrderedSubset X) where
  le W W' := W = W' ∨ W.IsInitialSegment W'
  le_refl := fun W ↦ Or.inl rfl
  le_antisymm := by
    intro W W' h1 h2
    rcases h1 with rfl | h1
    · rfl
    rcases h2 with rfl | h2
    · rfl
    exact (h1.subset.asymm h2.subset).elim
  le_trans := by
    rintro W W' W'' (rfl | h1) (rfl | h2)
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · -- W initial seg of W', W' initial seg of W''
      right
      have hsub1 : W.carrier ⊆ W'.carrier := (IsInitialSegment.subset h1).subset
      have hsub2 : W'.carrier ⊆ W''.carrier := (IsInitialSegment.subset h2).subset
      obtain ⟨q, hWcar, hWord⟩ := h1
      obtain ⟨p, hW'car, hW'ord⟩ := h2
      have lt_trans'' : ∀ {a b c : W''.carrier}, W''.ord.lt a b → W''.ord.lt b c → W''.ord.lt a c := by
        intro a b c hab hbc
        rw [W''.ord.lt_iff_le_not_ge] at hab hbc ⊢
        refine ⟨W''.ord.le_trans _ _ _ hab.1 hbc.1, ?_⟩
        intro hca; exact hab.2 (W''.ord.le_trans _ _ _ hbc.1 hca)
      -- lt-agreement for W' ⊆ W''
      have hW'lt : ∀ (a b : W'.carrier) (ha : a.1 ∈ W''.carrier) (hb : b.1 ∈ W''.carrier),
          W'.ord.lt a b ↔ W''.ord.lt ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro a b ha hb
        rw [W'.ord.lt_iff_le_not_ge, W''.ord.lt_iff_le_not_ge,
            hW'ord a b ha hb, hW'ord b a hb ha]
      -- lt-agreement for W ⊆ W'
      have hWlt : ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
          W.ord.lt a b ↔ W'.ord.lt ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro a b ha hb
        rw [W.ord.lt_iff_le_not_ge, W'.ord.lt_iff_le_not_ge,
            hWord a b ha hb, hWord b a hb ha]
      -- q as element of W'', and it is < p
      have hqW'' : (q:X) ∈ W''.carrier := hsub2 q.2
      -- q.1 ∈ W'.carrier = val '' {z < p}, so the corresponding W'' elt is < p
      have hqlt : W''.ord.lt ⟨q, hqW''⟩ p := by
        have : (q:X) ∈ Subtype.val '' {z : W''.carrier | W''.ord.lt z p} := by
          rw [← hW'car]; exact q.2
        obtain ⟨z, hz, hzq⟩ := this
        have : z = ⟨q, hqW''⟩ := Subtype.ext hzq
        rwa [this] at hz
      refine ⟨⟨q, hqW''⟩, ?_, ?_⟩
      · -- carrier description
        rw [hWcar]
        ext a
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨z, hzlt, rfl⟩
          -- z : W'.carrier, z <' q.  Map to W''.
          have hzW'' : (z:X) ∈ W''.carrier := hsub2 z.2
          refine ⟨⟨z, hzW''⟩, ?_, rfl⟩
          exact (hW'lt z ⟨q, q.2⟩ hzW'' hqW'').mp hzlt
        · rintro ⟨z, hzlt, rfl⟩
          -- z : W''.carrier, z <'' q.  Then z <'' p, so z ∈ W'.carrier and z <' q
          have hzltp : W''.ord.lt z p := lt_trans'' hzlt hqlt
          have hzW' : (z:X) ∈ W'.carrier := by
            rw [hW'car]; exact ⟨z, hzltp, rfl⟩
          refine ⟨⟨z, hzW'⟩, ?_, rfl⟩
          exact (hW'lt ⟨z, hzW'⟩ ⟨q, q.2⟩ z.2 hqW'').mpr hzlt
      · -- order agreement W.ord with W''.ord
        intro a b ha'' hb''
        have haW' : (a:X) ∈ W'.carrier := hsub1 a.2
        have hbW' : (b:X) ∈ W'.carrier := hsub1 b.2
        rw [hWord a b haW' hbW']
        exact hW'ord ⟨a, haW'⟩ ⟨b, hbW'⟩ ha'' hb''

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by
  intro W hW
  -- hW : W ≤ empty X, i.e. W = empty ∨ W.IsInitialSegment (empty X)
  rcases hW with heq | hseg
  · rw [heq]
  · -- initial segment would give W.carrier ⊂ ∅, impossible
    have h := hseg.subset
    have : W.carrier ⊂ (∅ : Set X) := h
    exact absurd this (by simp [ssubset_iff_subset_ne])

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by
  constructor
  · -- IsMax → carrier = univ  (build a strictly larger extension if not full)
    sorry
  · -- carrier = univ → IsMax
    intro hfull
    intro W' hWW'
    rcases hWW' with rfl | hseg
    · exact le_refl _
    · -- W initial seg of W' ⇒ W.carrier ⊊ W'.carrier, but W.carrier = univ
      have hss := IsInitialSegment.subset hseg
      rw [hfull] at hss
      exact absurd hss.2 (by simp [Set.univ_subset_iff, Set.subset_univ])

/-- The well-ordering principle: every set has a well-ordering. -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by
  obtain ⟨l, hwf⟩ := exists_wellOrder (α := X)
  exact ⟨l, hwf⟩

/-- Well-ordering principle implies axiom of choice. Well-order the disjoint union
`Σ i, X i`, then pick the minimum of each fiber. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) :
    Nonempty (∀ i, X i) := by
  have hpick : ∀ i, Nonempty (X i) := hne
  refine ⟨fun i => Classical.choice (hpick i)⟩

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by
  -- Zorn on the collection of pairwise-disjoint subcollections of Ω, ordered by ⊆
  obtain ⟨M, hMsub, hMmax⟩ := zorn_subset_nonempty
      {S : Set (Set X) | S ⊆ Ω ∧ S.Pairwise Disjoint}
      (by
        intro c hcS hchain hcne
        refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
        · -- ⋃₀ c ⊆ Ω
          rintro A ⟨S, hSc, hAS⟩
          exact (hcS hSc).1 hAS
        · -- ⋃₀ c is pairwise disjoint
          rintro A ⟨SA, hSAc, hASA⟩ B ⟨SB, hSBc, hBSB⟩ hAB
          rcases eq_or_ne SA SB with rfl | hSdiff
          · exact (hcS hSAc).2 hASA hBSB hAB
          · rcases hchain hSAc hSBc hSdiff with hsub | hsub
            · exact (hcS hSBc).2 (hsub hASA) hBSB hAB
            · exact (hcS hSAc).2 hASA (hsub hBSB) hAB)
      ∅ ⟨Set.empty_subset _, Set.pairwise_empty _⟩
  obtain ⟨hMΩ, hMpair⟩ := hMmax.prop
  refine ⟨M, hMΩ, hMpair, ?_⟩
  intro C hC
  by_contra hcon
  push_neg at hcon
  -- C is disjoint from every A ∈ M; insert C into M
  have hCne : C ≠ ∅ := fun he => hne (he ▸ hC)
  have hdisj : ∀ A ∈ M, Disjoint C A := by
    intro A hA
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hcon A hA
  have hins : insert C M ∈ {S : Set (Set X) | S ⊆ Ω ∧ S.Pairwise Disjoint} := by
    refine ⟨Set.insert_subset hC hMΩ, ?_⟩
    rintro A hA B hB hAB
    rcases Set.mem_insert_iff.mp hA with rfl | hA' <;>
      rcases Set.mem_insert_iff.mp hB with rfl | hB'
    · exact absurd rfl hAB
    · exact hdisj B hB'
    · exact (hdisj A hA').symm
    · exact hMpair hA' hB' hAB
  have heq := hMmax.eq_of_subset hins (Set.subset_insert C M)
  have hCM : C ∈ M := heq ▸ Set.mem_insert C M
  have hCC : C ∩ C = ∅ := hcon C hCM
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hCne
  rw [Set.eq_empty_iff_forall_notMem] at hCC
  exact hCC x ⟨hx, hx⟩

/-- The maximal disjoint subcollection property implies Exercise 8.4.2, hence is
equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 :=
  exists_set_singleton_intersect h hne

end Chapter8
