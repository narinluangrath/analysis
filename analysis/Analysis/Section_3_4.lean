import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  apply ext; intro y
  rw [mem_image, specification_axiom'']
  constructor
  · rintro ⟨x, hxS, rfl⟩
    exact ⟨(f x).property, x, hxS, rfl⟩
  · rintro ⟨h, x, hxS, hfx⟩
    exact ⟨x, hxS, by rw [hfx]⟩

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  intro h
  exact (mem_image _ _ _).mpr ⟨x, h, rfl⟩

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
  use {0,1}, {0}
  set f : ({0,1}:Set) → ({0}:Set) := fun _ => ⟨0, by simp⟩ with hf
  refine ⟨f, {0}, ⟨1, by simp⟩, ?_⟩
  intro h
  have himg : (f ⟨1, by simp⟩).val ∈ image f {0} :=
    mem_image_of_eval f {0} ⟨0, by simp⟩ (by simp)
  have hbad := h himg
  simp at hbad

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  intro h
  have h1 : ((1:ℕ):Object) ∈ image f_3_4_2 (preimage f_3_4_2 {1,2,3}) := by
    rw [h]; simp [mem_triple]
  rw [mem_image] at h1
  obtain ⟨x, hx, hfx⟩ := h1
  simp only [f_3_4_2] at hfx
  have key : (2 * nat_equiv.symm x : ℕ) = 1 := by
    have e1 : ((2 * nat_equiv.symm x : ℕ) : Object) = ((1:ℕ):Object) := hfx
    exact nat_coe_eq_iff.mp e1
  omega

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  intro h
  have h2 : (-2:ℤ) ∈ (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) := by
    simp only [Set.mem_preimage, Set.mem_image]
    exact ⟨2, by simp, by norm_num⟩
  rw [h] at h2
  norm_num [Set.mem_insert, Set.mem_singleton_iff] at h2

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

open Classical in
/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace
    (P := fun F y ↦ ∃ f : X → ({0,1}:Set), (f:Object) = F.val ∧ y = (preimage f {1} : Set))
    (by
      rintro F y y' ⟨⟨f, hf, hfy⟩, ⟨g, hg, hgy⟩⟩
      have : (f:Object) = (g:Object) := by rw [hf, hg]
      rw [coe_of_fun_inj] at this; rw [hfy, hgy, this])

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  rw [powerset, replacement_axiom]
  constructor
  · rintro ⟨F, f, hf, rfl⟩
    exact ⟨preimage f {1}, rfl, preimage_in_domain f {1}⟩
  · rintro ⟨Y, rfl, hYX⟩
    set f : X → ({0,1}:Set) := fun x ↦ if x.val ∈ Y then ⟨1, by simp⟩ else ⟨0, by simp⟩ with hfdef
    have hFmem : (f:Object) ∈ ({0,1}^X : Set) := by rw [powerset_axiom]; exact ⟨f, rfl⟩
    refine ⟨⟨(f:Object), hFmem⟩, f, rfl, ?_⟩
    rw [coe_eq_iff]
    apply ext; intro z
    rw [mem_preimage']
    constructor
    · intro hz
      have hzX : z ∈ X := hYX z hz
      refine ⟨⟨z, hzX⟩, rfl, ?_⟩
      simp only [hfdef, mem_singleton]
      rw [if_pos hz]
    · rintro ⟨z', rfl, hz'⟩
      rw [mem_singleton] at hz'
      simp only [hfdef] at hz'
      by_cases hzY : z'.val ∈ Y
      · exact hzY
      · rw [if_neg hzY] at hz'
        simp only [] at hz'
        exact absurd hz' (by simp)

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  apply ext; intro x
  simp only [union_axiom, mem_triple, coe_eq_iff]
  constructor
  · rintro ⟨S, hxS, rfl | rfl | rfl⟩ <;>
      simp only [mem_pair, mem_triple] at hxS <;>
      simp only [mem_insert, mem_singleton, mem_pair] <;> tauto
  · intro hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨{2,3}, by simp [mem_pair], Or.inl rfl⟩
    · exact ⟨{2,3}, by simp [mem_pair], Or.inl rfl⟩
    · exact ⟨{3,4}, by simp [mem_pair], Or.inr (Or.inl rfl)⟩
    · exact ⟨{4,5}, by simp [mem_pair], Or.inr (Or.inr rfl)⟩

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  apply ext; intro x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, _⟩; exact absurd i.property (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty _)

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  simp only [iInter, iInter', specification_axiom'']
  constructor
  · rintro ⟨_, hP⟩; exact hP
  · intro hP; exact ⟨hP _, hP⟩

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
  obtain ⟨hL, hR⟩ := hf
  apply ext; intro z
  rw [mem_image, mem_preimage']
  constructor
  · rintro ⟨y, hyV, rfl⟩
    refine ⟨f_inv y, rfl, ?_⟩
    rw [hR y]; exact hyV
  · rintro ⟨x, rfl, hfx⟩
    exact ⟨f x, hfx, by rw [hL x]⟩

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
-- theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : sorry := by sorry

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
-- theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
-- theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  intro y hy
  rw [mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_inter] at hx
  exact (mem_inter _ _ _).mpr ⟨(mem_image _ _ _).mpr ⟨x, hx.1, rfl⟩,
    (mem_image _ _ _).mpr ⟨x, hx.2, rfl⟩⟩

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro y hy
  rw [mem_sdiff] at hy
  obtain ⟨hyA, hyB⟩ := hy
  rw [mem_image] at hyA
  obtain ⟨x, hxA, rfl⟩ := hyA
  refine (mem_image _ _ _).mpr ⟨x, (mem_sdiff _ _ _).mpr ⟨hxA, ?_⟩, rfl⟩
  intro hxB
  exact hyB ((mem_image _ _ _).mpr ⟨x, hxB, rfl⟩)

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  apply ext; intro y
  simp only [mem_union, mem_image]
  constructor
  · rintro ⟨x, h, rfl⟩
    rcases h with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨x, h, rfl⟩
  · rintro (⟨x, h, rfl⟩ | ⟨x, h, rfl⟩)
    · exact ⟨x, Or.inl h, rfl⟩
    · exact ⟨x, Or.inr h, rfl⟩

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  refine ⟨{0,1}, {0}, fun _ => ⟨0, by simp⟩, {0}, {1}, ?_⟩
  intro h
  have : ((0:Object)) ∈ image (fun _ : ({0,1}:Set) => (⟨0, by simp⟩ : ({0}:Set))) ({0} ∩ {1}) := by
    rw [h, mem_inter]
    refine ⟨?_, ?_⟩ <;> rw [mem_image]
    · exact ⟨⟨0, by simp⟩, by simp, rfl⟩
    · exact ⟨⟨1, by simp⟩, by simp, rfl⟩
  rw [mem_image] at this
  obtain ⟨x, hx, _⟩ := this
  rw [mem_inter, mem_singleton, mem_singleton] at hx
  obtain ⟨h0, h1⟩ := hx
  rw [h0] at h1
  exact absurd h1 (by norm_num)

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  refine ⟨{0,1}, {0}, fun _ => ⟨0, by simp⟩, {0}, {1}, ?_⟩
  intro h
  have hmem : ((0:Object)) ∈ image (fun _ : ({0,1}:Set) => (⟨0, by simp⟩ : ({0}:Set))) ({0} \ {1}) := by
    rw [mem_image]
    refine ⟨⟨0, by simp⟩, ?_, rfl⟩
    rw [mem_sdiff]
    refine ⟨by simp, ?_⟩
    simp only [mem_singleton]; norm_num
  rw [h, mem_sdiff] at hmem
  apply hmem.2
  rw [mem_image]
  exact ⟨⟨1, by simp⟩, by simp, rfl⟩

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
  apply ext; intro x
  simp only [mem_inter, mem_preimage']
  constructor
  · rintro ⟨x', rfl, hfx'⟩
    exact ⟨⟨x', rfl, hfx'.1⟩, ⟨x', rfl, hfx'.2⟩⟩
  · rintro ⟨⟨x', rfl, hA⟩, ⟨x'', hx'', hB⟩⟩
    rw [show x'' = x' from Subtype.val_injective hx''] at hB
    exact ⟨x', rfl, hA, hB⟩

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
  apply ext; intro x
  simp only [mem_union, mem_preimage']
  constructor
  · rintro ⟨x', rfl, h⟩
    rcases h with h | h
    · exact Or.inl ⟨x', rfl, h⟩
    · exact Or.inr ⟨x', rfl, h⟩
  · rintro (⟨x', rfl, h⟩ | ⟨x', rfl, h⟩)
    · exact ⟨x', rfl, Or.inl h⟩
    · exact ⟨x', rfl, Or.inr h⟩

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
  apply ext; intro x
  simp only [mem_sdiff, mem_preimage']
  constructor
  · rintro ⟨x', rfl, hfx'⟩
    refine ⟨⟨x', rfl, hfx'.1⟩, ?_⟩
    rintro ⟨x'', hx'', hB⟩
    rw [show x'' = x' from Subtype.val_injective hx''] at hB
    exact hfx'.2 hB
  · rintro ⟨⟨x', rfl, hA⟩, hB⟩
    refine ⟨x', rfl, hA, ?_⟩
    intro hxB; exact hB ⟨x', rfl, hxB⟩

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor
  · intro h y
    have hS : ({y.val} : Set) ⊆ Y := by
      intro z hz; rw [mem_singleton] at hz; rw [hz]; exact y.property
    have hmem : y.val ∈ image f (preimage f {y.val}) := by
      rw [h {y.val} hS]; exact (mem_singleton _ _).mpr rfl
    rw [mem_image] at hmem
    obtain ⟨x, _, hfx⟩ := hmem
    exact ⟨x, Subtype.val_injective hfx⟩
  · intro hsurj S hS
    apply ext; intro z
    rw [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mem_preimage] at hx
    · intro hz
      obtain ⟨x, hfx⟩ := hsurj ⟨z, hS z hz⟩
      exact ⟨x, by rw [mem_preimage, hfx]; exact hz, by rw [hfx]⟩

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor
  · intro h x1 x2 hf
    have hS : ({x1.val}:Set) ⊆ X := by
      intro z hz; rw [mem_singleton] at hz; rw [hz]; exact x1.property
    have hmem : x2.val ∈ preimage f (image f {x1.val}) := by
      rw [mem_preimage, mem_image]
      exact ⟨x1, (mem_singleton _ _).mpr rfl, by rw [hf]⟩
    rw [h {x1.val} hS, mem_singleton] at hmem
    exact (Subtype.val_injective hmem).symm
  · intro hinj S hS
    apply ext; intro z
    rw [mem_preimage']
    constructor
    · rintro ⟨x, rfl, hfx⟩
      rw [mem_image] at hfx
      obtain ⟨x', hx'S, hfx'⟩ := hfx
      have hxx : x' = x := hinj (Subtype.val_injective hfx')
      rw [← hxx]; exact hx'S
    · intro hz
      exact ⟨⟨z, hS z hz⟩, rfl, mem_image_of_eval f S ⟨z, hS z hz⟩ hz⟩

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
  classical
  refine ⟨union (X.powerset.replace
    (P := fun X' W ↦ ∃ X'' : Set, (X'.val) = (X'' : Object) ∧
      W = union (Y.powerset.replace
        (P := fun Y' U ↦ ∃ Y'' : Set, (Y'.val) = (Y'' : Object) ∧ U = ((Y'' ^ X'' : Set):Object))
        (by
          rintro Y' U U' ⟨⟨a, ha, hU⟩, ⟨b, hb, hU'⟩⟩
          have hab : (a:Object) = (b:Object) := by rw [← ha, hb]
          rw [coe_eq_iff] at hab; rw [hU, hU', hab])))
    (by
      rintro X' W W' ⟨⟨a, ha, hW⟩, ⟨b, hb, hW'⟩⟩
      have hab : (a:Object) = (b:Object) := by rw [← ha, hb]
      rw [coe_eq_iff] at hab; rw [hW, hW', hab])), ?_⟩
  intro F
  rw [mem_union_powerset_replace_iff]
  constructor
  · rintro ⟨X'sub, U, ⟨X'', hX'', hU⟩, hFU⟩
    rw [coe_eq_iff] at hU
    rw [hU] at hFU
    rw [mem_union_powerset_replace_iff] at hFU
    obtain ⟨Y'sub, V, ⟨Y'', hY'', hV⟩, hFV⟩ := hFU
    rw [coe_eq_iff] at hV
    rw [hV] at hFV
    rw [powerset_axiom] at hFV
    obtain ⟨f, hf⟩ := hFV
    have hX'subX : X'' ⊆ X := by
      have hp := X'sub.property
      rw [mem_powerset] at hp
      obtain ⟨W, hW1, hW2⟩ := hp
      have : (X'' : Object) = (W : Object) := by rw [← hX'', hW1]
      rw [coe_eq_iff] at this; rw [this]; exact hW2
    have hY'subY : Y'' ⊆ Y := by
      have hp := Y'sub.property
      rw [mem_powerset] at hp
      obtain ⟨W, hW1, hW2⟩ := hp
      have : (Y'' : Object) = (W : Object) := by rw [← hY'', hW1]
      rw [coe_eq_iff] at this; rw [this]; exact hW2
    exact ⟨X'', Y'', hX'subX, hY'subY, f, hf.symm⟩
  · rintro ⟨X', Y', hX', hY', f, rfl⟩
    have hX'mem : (X':Object) ∈ X.powerset := by rw [mem_powerset']; exact hX'
    have hY'mem : (Y':Object) ∈ Y.powerset := by rw [mem_powerset']; exact hY'
    refine ⟨⟨(X':Object), hX'mem⟩, _, ⟨X', rfl, rfl⟩, ?_⟩
    rw [mem_union_powerset_replace_iff]
    refine ⟨⟨(Y':Object), hY'mem⟩, _, ⟨Y', rfl, rfl⟩, ?_⟩
    rw [powerset_axiom]
    exact ⟨f, rfl⟩

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) :=
  ⟨X ∪ Y, fun x => mem_union x X Y⟩

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
  apply ext; intro x
  simp only [iInter', specification_axiom'']
  constructor
  · rintro ⟨_, hP⟩; exact ⟨hP β', hP⟩
  · rintro ⟨_, hP⟩; exact ⟨hP β, hP⟩

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
  apply ext; intro x
  rw [mem_union, mem_iUnion, mem_iUnion, mem_iUnion]
  constructor
  · rintro (⟨α, hα⟩ | ⟨α, hα⟩)
    · exact ⟨⟨α.val, by simp [α.property]⟩, hα⟩
    · exact ⟨⟨α.val, by simp [α.property]⟩, hα⟩
  · rintro ⟨α, hα⟩
    rcases (mem_union α.val I J).mp α.property with h | h
    · exact Or.inl ⟨⟨α.val, h⟩, hα⟩
    · exact Or.inr ⟨⟨α.val, h⟩, hα⟩

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  obtain ⟨x, hx⟩ := nonempty_def hI
  intro h
  have : x ∈ I ∪ J := (mem_union x I J).mpr (Or.inl hx)
  rw [h] at this
  exact not_mem_empty x this

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  apply ext; intro x
  rw [mem_inter, mem_iInter, mem_iInter, mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩ α
    rcases (mem_union α.val I J).mp α.property with h | h
    · exact h1 ⟨α.val, h⟩
    · exact h2 ⟨α.val, h⟩
  · intro h
    exact ⟨fun α ↦ h ⟨α.val, by simp [α.property]⟩, fun α ↦ h ⟨α.val, by simp [α.property]⟩⟩

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  apply ext; intro x
  rw [mem_sdiff, mem_iUnion, mem_iInter]
  constructor
  · rintro ⟨hX, hnot⟩ α
    rw [mem_sdiff]
    exact ⟨hX, fun h ↦ hnot ⟨α, h⟩⟩
  · intro h
    have := (mem_sdiff _ _ _).mp (h (nonempty_choose hI))
    refine ⟨this.1, ?_⟩
    rintro ⟨α, hα⟩
    exact ((mem_sdiff _ _ _).mp (h α)).2 hα

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  apply ext; intro x
  rw [mem_sdiff, mem_iInter, mem_iUnion]
  constructor
  · rintro ⟨hX, hnot⟩
    by_contra hc
    push_neg at hc
    apply hnot
    intro α
    by_contra hα
    exact hc α ((mem_sdiff _ _ _).mpr ⟨hX, hα⟩)
  · rintro ⟨α, hα⟩
    rw [mem_sdiff] at hα
    exact ⟨hα.1, fun h ↦ hα.2 (h α)⟩

end Chapter3
