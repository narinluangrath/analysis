import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as {name}`Set.pi` and {name}`Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used {lean}`Object × Object` to
define {name}`OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  constructor
  · intro h
    have ha : a ∈ ({a,b}:Set) := by simp
    have hb : b ∈ ({a,b}:Set) := by simp
    rw [h] at ha hb; simp at ha hb; exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩; apply ext; intro x; simp

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro p q h
    simp only at h
    rw [SetTheory.Set.coe_eq_iff] at h
    have key := SetTheory.Set.pair_eq_pair h
    simp only [SetTheory.Set.coe_eq_iff] at key
    have hsingle : ∀ {a c:Object}, ({a}:Set) = {c} → a = c := by
      intro a c hac
      have : a ∈ ({c}:Set) := hac ▸ (SetTheory.Set.mem_singleton a a).mpr rfl
      exact (SetTheory.Set.mem_singleton a c).mp this
    have hfst : p.fst = q.fst := by
      rcases key with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hsingle h1
      · exact (SetTheory.Set.pair_eq_singleton_iff.mp h1.symm).1.symm
    have hsnd : p.snd = q.snd := by
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hsingle h1] at h2
        rcases SetTheory.Set.pair_eq_pair h2 with ⟨_, hh⟩ | ⟨hh1, hh2⟩
        · exact hh
        · rw [hh2, hh1]
      · have hq := SetTheory.Set.pair_eq_singleton_iff.mp h1.symm
        have hp := SetTheory.Set.pair_eq_singleton_iff.mp h2
        rw [hp.2, hq.1, ← hq.2]
    ext
    · exact hfst
    · exact hsnd

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object $`x` and a set $`Y` to a set $`{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an {name}`OrderedPair` with proofs that $`x ∈ X` and $`y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  {given -show}`x : X, y : Y`
  Connections with the Mathlib set product, which consists of Lean pairs like {lean}`(x, y)`
  equipped with a proof that {name}`x` is in the left set, and {name}`y` is in the right set.
  Lean pairs like {lean}`(x, y)` are similar to our {name}`OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between {lean}`X ×ˢ Y` and {lean}`Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun z := mk_cartesian (snd z) (fst z)
  invFun z := mk_cartesian (snd z) (fst z)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by ext; simp
  right_inv _ := by simp

/-- Definition 3.5.6.  The indexing set {name}`I` plays the role of $`{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  rw [tuple, tuple, coe_of_fun_inj]
  constructor
  · intro h
    funext i
    have := congrFun h i
    rw [Subtype.mk.injEq] at this
    exact Subtype.val_inj.mp this
  · rintro rfl; rfl

/-- Example 3.5.8. There is a bijection between {lean}`(X ×ˢ Y) ×ˢ Z` and {lean}`X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun t := ((mem_iProd _).mp t.property).choose ⟨i, by simp⟩
  invFun x := ⟨tuple (fun _ => x), by apply tuple_mem_iProd⟩
  left_inv t := by
    apply Subtype.val_inj.mp
    simp only
    conv_rhs => rw [((mem_iProd _).mp t.property).choose_spec]
    rw [tuple_inj]
    funext j
    have : j = ⟨i, by simp⟩ := by
      apply Subtype.val_inj.mp
      have := j.property; rw [mem_singleton] at this; exact this
    rw [this]
  right_inv x := by
    simp only
    generalize_proofs h1 h2
    have := h1.choose_spec
    rw [tuple_inj] at this
    rw [← this]

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨tuple (fun i => absurd i.property (not_mem_empty _)), by apply tuple_mem_iProd⟩
  left_inv t := by
    obtain ⟨x, hx⟩ := (mem_iProd _).mp t.property
    apply Subtype.val_inj.mp
    simp only
    rw [hx, tuple_inj]
    funext i
    exact absurd i.property (not_mem_empty _)
  right_inv _ := by simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _:I ↦ X) ≃ (I → X) where
  toFun t i := ((mem_iProd _).mp t.property).choose i
  invFun f := ⟨tuple (fun i => f i), by apply tuple_mem_iProd⟩
  left_inv t := by
    apply Subtype.val_inj.mp
    simp only
    rw [← ((mem_iProd _).mp t.property).choose_spec]
  right_inv f := by
    funext i
    simp only
    generalize_proofs h
    have := h.choose_spec
    rw [tuple_inj] at this
    rw [← this]

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun t := mk_cartesian
    (((mem_iProd _).mp t.property).choose ⟨0, by simp⟩)
    (((mem_iProd _).mp t.property).choose ⟨1, by simp⟩)
  invFun z := ⟨tuple (fun i => letI := Classical.propDecidable; if h : i.val = 0 then
      (by rw [show i = (⟨0, by simp⟩ : ({0,1}:Set)) from Subtype.val_inj.mp h]; exact fst z)
    else
      have h1 : i.val = 1 := by have := i.property; rw [mem_pair] at this; tauto
      (by rw [show i = (⟨1, by simp⟩ : ({0,1}:Set)) from Subtype.val_inj.mp h1]; exact snd z)),
    by apply tuple_mem_iProd⟩
  left_inv t := by
    apply Subtype.val_inj.mp
    simp only
    conv_rhs => rw [((mem_iProd _).mp t.property).choose_spec]
    rw [tuple_inj]
    funext j
    by_cases hj : j.val = 0
    · have hje : j = (⟨0, by simp⟩ : ({0,1}:Set)) := Subtype.val_inj.mp hj
      subst hje; simp [fst_of_mk_cartesian]
    · have hj1 : j.val = 1 := by have := j.property; rw [mem_pair] at this; tauto
      have hje : j = (⟨1, by simp⟩ : ({0,1}:Set)) := Subtype.val_inj.mp hj1
      subst hje; simp [hj, snd_of_mk_cartesian]
  right_inv z := by
    simp only
    generalize_proofs h1 h2 pa pb hex
    have hc := hex.choose_spec
    rw [tuple_inj] at hc
    have e0 := congrFun hc ⟨0, h1⟩
    have e1 := congrFun hc ⟨1, h2⟩
    simp only [eq_mpr_eq_cast, cast_eq, dif_pos, dif_neg,
      (by simp : ((0:Object) = 0) = True), (by simp : ((1:Object) = 0) = False)] at e0 e1
    simp only [dif_neg (not_false), reduceDIte] at e1
    rw [show hex.choose ⟨0, h1⟩ = fst z from e0.symm,
        show hex.choose ⟨1, h2⟩ = snd z from e1.symm]
    exact mk_cartesian_fst_snd_eq z

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun t := mk_cartesian
    (((mem_iProd _).mp t.property).choose ⟨0, by simp⟩)
    (mk_cartesian
      (((mem_iProd _).mp t.property).choose ⟨1, by simp⟩)
      (((mem_iProd _).mp t.property).choose ⟨2, by simp⟩))
  invFun z := ⟨tuple (fun i => letI := Classical.propDecidable;
    if h0 : i.val = 0 then
      (by rw [show i = (⟨0, by simp⟩ : ({0,1,2}:Set)) from Subtype.val_inj.mp h0]; exact fst z)
    else if h1 : i.val = 1 then
      (by rw [show i = (⟨1, by simp⟩ : ({0,1,2}:Set)) from Subtype.val_inj.mp h1]; exact fst (snd z))
    else
      have h2 : i.val = 2 := by have := i.property; rw [mem_triple] at this; tauto
      (by rw [show i = (⟨2, by simp⟩ : ({0,1,2}:Set)) from Subtype.val_inj.mp h2]; exact snd (snd z))),
    by apply tuple_mem_iProd⟩
  left_inv t := by
    apply Subtype.val_inj.mp
    simp only
    conv_rhs => rw [((mem_iProd _).mp t.property).choose_spec]
    rw [tuple_inj]
    funext j
    by_cases hj0 : j.val = 0
    · have hje : j = (⟨0, by simp⟩ : ({0,1,2}:Set)) := Subtype.val_inj.mp hj0
      subst hje; simp
    · by_cases hj1 : j.val = 1
      · have hje : j = (⟨1, by simp⟩ : ({0,1,2}:Set)) := Subtype.val_inj.mp hj1
        subst hje; simp [hj0]
      · have hj2 : j.val = 2 := by have := j.property; rw [mem_triple] at this; tauto
        have hje : j = (⟨2, by simp⟩ : ({0,1,2}:Set)) := Subtype.val_inj.mp hj2
        subst hje; simp [hj0, hj1]
  right_inv z := by
    simp only
    generalize_proofs h0 h1 h2 pa pb pc hex
    have hc := hex.choose_spec
    rw [tuple_inj] at hc
    have e0 := congrFun hc ⟨0, h0⟩
    have e1 := congrFun hc ⟨1, h1⟩
    have e2 := congrFun hc ⟨2, h2⟩
    simp only [eq_mpr_eq_cast, cast_eq, reduceDIte,
      (by simp : ((0:Object) = 0) = True), (by simp : ((1:Object) = 0) = False),
      (by simp : ((2:Object) = 0) = False), (by simp : ((1:Object) = 1) = True),
      (by simp : ((2:Object) = 1) = False)] at e0 e1 e2
    rw [show hex.choose ⟨0, h0⟩ = fst z from e0.symm,
        show hex.choose ⟨1, h1⟩ = fst (snd z) from e1.symm,
        show hex.choose ⟨2, h2⟩ = snd (snd z) from e2.symm]
    rw [mk_cartesian_fst_snd_eq, mk_cartesian_fst_snd_eq]

/-- Connections with Mathlib's {name}`Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib {lean}`Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's {lean}`Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro p q h
    simp only at h
    rw [SetTheory.Set.coe_eq_iff] at h
    have key := SetTheory.Set.pair_eq_pair h
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- good case
      rw [SetTheory.Set.coe_eq_iff] at h2
      have hsnd : p.snd = q.snd := by
        rw [h1] at h2
        rcases SetTheory.Set.pair_eq_pair h2 with ⟨_, hh⟩ | ⟨hh1, hh2⟩
        · exact hh
        · rw [hh2, hh1]
      ext
      · exact h1
      · exact hsnd
    · -- bad case ruled out by regularity
      exfalso
      set P : SetTheory.Set := {p.fst, p.snd}
      set Q : SetTheory.Set := {q.fst, q.snd}
      -- h1 : p.fst = (Q:Object), h2 : (P:Object) = q.fst
      have hQinP : (Q:Object) ∈ P := by
        rw [← h1]; exact (SetTheory.Set.mem_pair _ _ _).mpr (Or.inl rfl)
      have hPinQ : (P:Object) ∈ Q := by
        rw [h2]; exact (SetTheory.Set.mem_pair _ _ _).mpr (Or.inl rfl)
      rcases SetTheory.Set.not_mem_mem P Q with hc | hc
      · exact hc hPinQ
      · exact hc hQinP

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing {attr}`@[ext]` on the structure would generate a lemma requiring proof of {lit}`t.x = t'.x`,
  but these functions have different types when {lean}`t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor
  · rintro rfl _; rfl
  · intro h
    apply Tuple.ext _ h
    apply SetTheory.Set.ext
    intro y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := t.surj ⟨y, hy⟩
      have hh := h i
      rw [hi] at hh
      simp only at hh
      rw [hh]
      exact (t'.x i).property
    · intro hy
      obtain ⟨i, hi⟩ := t'.surj ⟨y, hy⟩
      have hh := h i
      rw [hi] at hh
      simp only at hh
      rw [← hh]
      exact (t.x i).property

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun t :=
    let f := ((mem_iProd _).mp t.property).choose
    ⟨{ X := (Fin n).replace (P := fun i y => y = (f i).val) (by rintro i y y' ⟨rfl, h⟩; exact h.symm)
       x := fun i => ⟨(f i).val, by rw [replacement_axiom]; exact ⟨i, rfl⟩⟩
       surj := by
         rintro ⟨s, hs⟩
         rw [replacement_axiom] at hs
         obtain ⟨i, hi⟩ := hs
         exact ⟨i, by apply Subtype.val_inj.mp; exact hi.symm⟩ },
     by intro i; simp only; rw [show (f i).val = ((f i:X i):Object) from rfl]; exact (f i).property⟩
  invFun p := ⟨tuple (fun i => ⟨(p.val.x i).val, p.property i⟩), by apply tuple_mem_iProd⟩
  left_inv t := by
    apply Subtype.val_inj.mp
    simp only
    conv_rhs => rw [((mem_iProd _).mp t.property).choose_spec]
  right_inv p := by
    obtain ⟨t, ht⟩ := p
    apply Subtype.val_inj.mp
    simp only
    generalize_proofs g1 g2 g3 hex
    have hc := g1.choose_spec
    rw [tuple_inj] at hc
    have key : ∀ i, (t.x i).val = (g1.choose i).val :=
      fun i => congrArg Subtype.val (congrFun hc i)
    apply Tuple.ext
    · apply ext
      intro y
      rw [replacement_axiom]
      constructor
      · rintro ⟨i, rfl⟩
        rw [← key i]
        exact (t.x i).property
      · intro hy
        obtain ⟨i, hi⟩ := t.surj ⟨y, hy⟩
        refine ⟨i, ?_⟩
        rw [← key i, hi]
    · intro i
      simp only
      rw [← key i]

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use {name}`OrderedPair.eq` or {name}`SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by rfl

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor <;> exact Eq.symm

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := hpq.trans hqr

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := rfl

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  constructor <;> exact Eq.symm

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := hab.trans hbc

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_union]
  constructor
  · rintro ⟨x, y, rfl⟩
    rcases (mem_union _ _ _).mp y.property with h | h
    · left; exact ⟨x, ⟨y, h⟩, rfl⟩
    · right; exact ⟨x, ⟨y, h⟩, rfl⟩
  · rintro (⟨x, y, rfl⟩ | ⟨x, y, rfl⟩)
    · exact ⟨x, ⟨y, by rw [mem_union]; left; exact y.property⟩, rfl⟩
    · exact ⟨x, ⟨y, by rw [mem_union]; right; exact y.property⟩, rfl⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_inter]
  constructor
  · rintro ⟨x, y, rfl⟩
    have := (mem_inter _ _ _).mp y.property
    exact ⟨⟨x, ⟨y, this.1⟩, rfl⟩, ⟨x, ⟨y, this.2⟩, rfl⟩⟩
  · rintro ⟨⟨x, y, rfl⟩, x', y', heq⟩
    refine ⟨x, ⟨y, ?_⟩, rfl⟩
    rw [mem_inter]
    refine ⟨y.property, ?_⟩
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    rw [heq.2]; exact y'.property

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_sdiff]
  constructor
  · rintro ⟨x, y, rfl⟩
    have := (mem_sdiff _ _ _).mp y.property
    refine ⟨⟨x, ⟨y, this.1⟩, rfl⟩, ?_⟩
    rintro ⟨x', y', heq⟩
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    apply this.2; rw [heq.2]; exact y'.property
  · rintro ⟨⟨x, y, rfl⟩, hni⟩
    refine ⟨x, ⟨y, ?_⟩, rfl⟩
    rw [mem_sdiff]
    refine ⟨y.property, ?_⟩
    intro hc
    exact hni ⟨x, ⟨y, hc⟩, rfl⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_union]
  constructor
  · rintro ⟨x, y, rfl⟩
    rcases (mem_union _ _ _).mp x.property with h | h
    · left; exact ⟨⟨x, h⟩, y, rfl⟩
    · right; exact ⟨⟨x, h⟩, y, rfl⟩
  · rintro (⟨x, y, rfl⟩ | ⟨x, y, rfl⟩)
    · exact ⟨⟨x, by rw [mem_union]; left; exact x.property⟩, y, rfl⟩
    · exact ⟨⟨x, by rw [mem_union]; right; exact x.property⟩, y, rfl⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_inter]
  constructor
  · rintro ⟨x, y, rfl⟩
    have := (mem_inter _ _ _).mp x.property
    exact ⟨⟨⟨x, this.1⟩, y, rfl⟩, ⟨x, this.2⟩, y, rfl⟩
  · rintro ⟨⟨x, y, rfl⟩, x', y', heq⟩
    refine ⟨⟨x, ?_⟩, y, rfl⟩
    rw [mem_inter]
    refine ⟨x.property, ?_⟩
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    rw [heq.1]; exact x'.property

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  apply ext; intro z; simp only [mem_cartesian, mem_sdiff]
  constructor
  · rintro ⟨x, y, rfl⟩
    have := (mem_sdiff _ _ _).mp x.property
    refine ⟨⟨⟨x, this.1⟩, y, rfl⟩, ?_⟩
    rintro ⟨x', y', heq⟩
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    apply this.2; rw [heq.1]; exact x'.property
  · rintro ⟨⟨x, y, rfl⟩, hni⟩
    refine ⟨⟨x, ?_⟩, y, rfl⟩
    rw [mem_sdiff]
    refine ⟨x.property, ?_⟩
    intro hc
    exact hni ⟨⟨x, hc⟩, y, rfl⟩

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  apply ext; intro z; simp only [mem_cartesian, mem_inter]
  constructor
  · rintro ⟨⟨x, y, rfl⟩, x', y', heq⟩
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    refine ⟨⟨x, by rw [mem_inter]; exact ⟨x.property, by rw [heq.1]; exact x'.property⟩⟩,
      ⟨y, by rw [mem_inter]; exact ⟨y.property, by rw [heq.2]; exact y'.property⟩⟩, rfl⟩
  · rintro ⟨x, y, rfl⟩
    have hx := (mem_inter _ _ _).mp x.property
    have hy := (mem_inter _ _ _).mp y.property
    exact ⟨⟨⟨x, hx.1⟩, ⟨y, hy.1⟩, rfl⟩, ⟨x, hx.2⟩, ⟨y, hy.2⟩, rfl⟩

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  apply isFalse
  intro h
  have key := h {(0:Object)} {(0:Object)} {(1:Object)} {(1:Object)}
  have hRHS : ((⟨(0:Object),(1:Object)⟩:OrderedPair):Object) ∈ ({(0:Object)}∪{(1:Object)}:Set) ×ˢ ({(0:Object)}∪{(1:Object)}:Set) := by
    rw [mem_cartesian]
    refine ⟨⟨0, by rw [mem_union]; left; simp⟩, ⟨1, by rw [mem_union]; right; simp⟩, rfl⟩
  rw [←key, mem_union] at hRHS
  rcases hRHS with h1 | h1
  · rw [mem_cartesian] at h1; obtain ⟨a, b, heq⟩ := h1
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    have hp := b.property; rw [← heq.2] at hp; simp at hp
  · rw [mem_cartesian] at h1; obtain ⟨a, b, heq⟩ := h1
    rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
    have hp := a.property; rw [← heq.1] at hp; simp at hp

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  apply isFalse
  intro h
  have key := h {(0:Object)} {(0:Object)} {(0:Object)} ∅
  have hLHS : ((⟨(0:Object),(0:Object)⟩:OrderedPair):Object) ∈ ({(0:Object)}:Set) ×ˢ ({(0:Object)}:Set) \ (({(0:Object)}:Set) ×ˢ (∅:Set)) := by
    rw [mem_sdiff]
    refine ⟨by rw [mem_cartesian]; exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩, rfl⟩, ?_⟩
    rintro hc; rw [mem_cartesian] at hc; obtain ⟨_, b, _⟩ := hc
    exact absurd b.property (not_mem_empty _)
  rw [key, mem_cartesian] at hLHS
  obtain ⟨a, _, _⟩ := hLHS
  have hp := a.property; rw [mem_sdiff] at hp
  exact hp.2 (by simpa using hp.1)

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  constructor
  · intro h
    obtain ⟨b0, hb0⟩ := nonempty_def hB
    obtain ⟨a0, ha0⟩ := nonempty_def hA
    refine ⟨?_, ?_⟩
    · intro a ha
      have : ((⟨a, b0⟩:OrderedPair):Object) ∈ A ×ˢ B := by
        rw [mem_cartesian]; exact ⟨⟨a, ha⟩, ⟨b0, hb0⟩, rfl⟩
      have := h _ this
      rw [mem_cartesian] at this
      obtain ⟨c, d, heq⟩ := this
      rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
      rw [heq.1]; exact c.property
    · intro b hb
      have : ((⟨a0, b⟩:OrderedPair):Object) ∈ A ×ˢ B := by
        rw [mem_cartesian]; exact ⟨⟨a0, ha0⟩, ⟨b, hb⟩, rfl⟩
      have := h _ this
      rw [mem_cartesian] at this
      obtain ⟨c, d, heq⟩ := this
      rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at heq
      rw [heq.2]; exact d.property
  · rintro ⟨hac, hbd⟩ z hz
    rw [mem_cartesian] at hz ⊢
    obtain ⟨a, b, rfl⟩ := hz
    exact ⟨⟨a, hac _ a.property⟩, ⟨b, hbd _ b.property⟩, rfl⟩

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  apply isFalse
  intro h
  have empty_prod_eq : ∀ B:Set, (∅:Set) ×ˢ B = ∅ := by
    intro B; apply ext; intro z; simp only [mem_cartesian]
    constructor
    · rintro ⟨a, _, _⟩; exact absurd a.property (not_mem_empty _)
    · intro h; exact absurd h (not_mem_empty _)
  have key := (h ∅ {(0:Object)} {(0:Object)} ∅).mp
  rw [empty_prod_eq] at key
  have hsub : (∅:Set) ⊆ ({(0:Object)}:Set) ×ˢ (∅:Set) := empty_subset _
  obtain ⟨_, hBD⟩ := key hsub
  have h0 : (0:Object) ∈ ({(0:Object)}:Set) := by simp
  exact absurd (hBD _ h0) (not_mem_empty _)

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  apply existsUnique_of_exists_of_unique
  · use fun z => mk_cartesian (f z) (g z)
    constructor <;> funext z <;> simp
  · intro h1 h2 ⟨hf1, hs1⟩ ⟨hf2, hs2⟩
    funext z
    have e1 : fst (h1 z) = fst (h2 z) := by
      have := congrFun hf1 z; have := congrFun hf2 z; simp_all
    have e2 : snd (h1 z) = snd (h2 z) := by
      have := congrFun hs1 z; have := congrFun hs2 z; simp_all
    rw [← mk_cartesian_fst_snd_eq (h1 z), ← mk_cartesian_fst_snd_eq (h2 z), e1, e2]

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact finite_choice hcon h
  · rintro ⟨i, hi⟩
    by_contra hcon
    obtain ⟨t, ht⟩ := nonempty_def hcon
    rw [mem_iProd] at ht
    obtain ⟨x, rfl⟩ := ht
    rw [eq_empty_iff_forall_notMem] at hi
    exact hi _ (x i).property

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  apply ext; intro z
  rw [mem_inter]
  rw [mem_iUnion A, mem_iUnion B, mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨mk_cartesian i j, ?_⟩
    rw [mem_inter]
    simp only [fst_of_mk_cartesian, snd_of_mk_cartesian]
    exact ⟨hi, hj⟩
  · rintro ⟨p, hp⟩
    rw [mem_inter] at hp
    exact ⟨⟨fst p, hp.1⟩, ⟨snd p, hp.2⟩⟩

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
  constructor
  · intro h
    funext x
    have hmem : ((mk_cartesian x (f x)):Object) ∈ graph f := by
      rw [graph, specification_axiom'']
      refine ⟨(mk_cartesian x (f x)).property, ?_⟩
      simp
    rw [h, graph, specification_axiom''] at hmem
    obtain ⟨hp, heq⟩ := hmem
    simp at heq
    exact heq.symm
  · rintro rfl; rfl

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
  have memg : ∀ (f:X→Y) (x:X) (y:Y), ((⟨x,y⟩:OrderedPair):Object) ∈ graph f ↔ f x = y := by
    intro f x y
    rw [graph, specification_axiom'']
    constructor
    · rintro ⟨hp, he⟩
      have key : (⟨((⟨x,y⟩:OrderedPair):Object), hp⟩ : (X ×ˢ Y)) = mk_cartesian x y := rfl
      rw [key] at he
      simp only [fst_of_mk_cartesian, snd_of_mk_cartesian] at he
      exact he
    · intro he
      refine ⟨by rw [mem_cartesian]; exact ⟨x, y, rfl⟩, ?_⟩
      show f (fst (mk_cartesian x y)) = snd (mk_cartesian x y)
      simp only [fst_of_mk_cartesian, snd_of_mk_cartesian]
      exact he
  apply existsUnique_of_exists_of_unique
  · use fun x => (hvert x).choose
    apply ext; intro z
    constructor
    · intro hz
      obtain ⟨x, y, rfl⟩ := (mem_cartesian _ _ _).mp (hG _ hz)
      rw [memg]
      exact ((hvert x).choose_spec.2 y hz).symm
    · intro hz
      rw [graph, specification_axiom''] at hz
      obtain ⟨hp, he⟩ := hz
      obtain ⟨x, y, hxy⟩ := (mem_cartesian _ _ _).mp hp
      have hmemG : ((⟨x,y⟩:OrderedPair):Object) ∈ graph (fun x => (hvert x).choose) := by
        rw [graph, specification_axiom'']; rw [← hxy]; exact ⟨hp, he⟩
      rw [memg] at hmemG
      rw [hxy, ← hmemG]
      exact (hvert x).choose_spec.1
  · intro f1 f2 hf1 hf2
    have : graph f1 = graph f2 := by rw [← hf1, ← hf2]
    exact (graph_inj f1 f2).mp this

/--
  Exercise 3.5.11. This trivially follows from {name}`SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from {name}`SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  apply existsUnique_of_exists_of_unique
  · exact ⟨X ^ Y, fun F => powerset_axiom F⟩
  · intro S S' hS hS'
    apply ext
    intro z
    rw [hS z, hS' z]

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  classical
  let g : ℕ → X := fun k => Nat.rec c (fun j prev => f (j:Nat) prev) k
  have g0 : g 0 = c := rfl
  have gsucc : ∀ k:ℕ, g (k+1) = f (k:Nat) (g k) := fun k => rfl
  apply existsUnique_of_exists_of_unique
  · refine ⟨fun m => g (m:ℕ), ?_, ?_⟩
    · show g ((0:Nat):ℕ) = c
      rw [show ((0:Nat):ℕ) = 0 from by simp, g0]
    · intro n
      simp only
      rw [show ((((n:ℕ) + 1 : ℕ):Nat):ℕ) = (n:ℕ) + 1 from by simp, gsucc]
      congr 2
      simp
  · rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    funext m
    obtain ⟨k, rfl⟩ : ∃ k:ℕ, m = (k:Nat) := ⟨(m:ℕ), by simp⟩
    induction k with
    | zero =>
      have : ((0:ℕ):Nat) = (0:Nat) := rfl
      rw [this, ha0, hb0]
    | succ j ih =>
      have haj := ha (j:Nat)
      have hbj := hb (j:Nat)
      simp only [nat_equiv_coe_of_coe] at haj hbj
      rw [haj, hbj, ih]

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, ⟨hf0, hfs0⟩, _⟩ := recursion nat' (fun _ prev => succ prev) zero
  -- f 0 = zero, f (n+1) = succ (f n)
  have hfs : ∀ n:ℕ, f ((n+1:ℕ):Nat) = succ (f (n:Nat)) := hfs0
  -- the iff condition
  have hiff : ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
    intro n n'
    have key : f (n+1:ℕ) = succ (f n) := by
      have := hfs (n:ℕ); simpa [nat_equiv_coe_of_coe] using this
    rw [key]
    constructor
    · intro h; rw [h]
    · intro h; by_contra hne
      exact succ_of_ne _ _ hne h
  -- surjectivity onto nat' via induction principle
  have hsurj : Function.Surjective f := by
    have : ∀ y:nat', ∃ n:nat, f n = y := by
      apply ind
      · exact ⟨0, hf0⟩
      · rintro y ⟨n, hn⟩
        refine ⟨(n+1:ℕ), ?_⟩
        have := hfs (n:ℕ)
        simpa [nat_equiv_coe_of_coe, hn] using this
    exact this
  -- injectivity
  have hinj : Function.Injective f := by
    intro x1 x2 heq
    obtain ⟨k1, rfl⟩ : ∃ k:ℕ, x1 = (k:Nat) := ⟨(x1:ℕ), by simp⟩
    obtain ⟨k2, rfl⟩ : ∃ k:ℕ, x2 = (k:Nat) := ⟨(x2:ℕ), by simp⟩
    -- f (k:Nat) determines k; prove by showing f is "strictly" via succ_ne
    rw [nat_equiv_inj]
    by_contra hne
    -- WLOG k1 < k2 or k2 < k1
    -- prove ∀ a b:ℕ, a < b → f (a:Nat) ≠ f (b:Nat)
    have hmono : ∀ a b:ℕ, a < b → f (a:Nat) ≠ f (b:Nat) := by
      intro a b hab
      obtain ⟨d, rfl⟩ : ∃ d:ℕ, b = a + d + 1 := ⟨b - a - 1, by omega⟩
      -- f (a+d+1) = succ^(d+1) applied... use induction on a
      clear hne heq hab
      induction a generalizing d with
      | zero =>
        intro hcon
        -- f 0 = zero, f (d+1) = succ (...), so zero = succ(...) contradiction
        rw [show ((0:ℕ):Nat) = (0:Nat) from rfl, hf0] at hcon
        have hd : f ((d+1:ℕ):Nat) = succ (f (d:Nat)) := hfs d
        rw [show ((0+d+1:ℕ):Nat) = ((d+1:ℕ):Nat) from by congr 1; omega, hd] at hcon
        exact succ_ne _ hcon.symm
      | succ a iha =>
        intro hcon
        have e1 : f ((a+1:ℕ):Nat) = succ (f (a:Nat)) := hfs a
        have e2 : f ((a+d+1+1:ℕ):Nat) = succ (f ((a+d+1:ℕ):Nat)) := hfs (a+d+1)
        rw [e1] at hcon
        rw [show ((a+1+d+1:ℕ):Nat) = ((a+d+1+1:ℕ):Nat) from by congr 1; omega, e2] at hcon
        have := succ_of_ne _ _ (iha d)
        exact this hcon
    rcases Nat.lt_or_ge k1 k2 with h | h
    · exact hmono k1 k2 h heq
    · rcases Nat.lt_or_ge k2 k1 with h2 | h2
      · exact hmono k2 k1 h2 heq.symm
      · exact hne (by omega)
  have key : ∀ g : nat → nat', (Function.Bijective g ∧ g 0 = zero
      ∧ ∀ (n:nat) (n':nat'), g n = n' ↔ g (n+1:ℕ) = succ n') → g = f := by
    rintro g ⟨_, hg0, hgiff⟩
    funext m
    obtain ⟨k, rfl⟩ : ∃ k:ℕ, m = (k:Nat) := ⟨(m:ℕ), by simp⟩
    induction k with
    | zero => rw [show ((0:ℕ):Nat) = (0:Nat) from rfl, hf0, hg0]
    | succ j ih =>
      have hfj : f ((j+1:ℕ):Nat) = succ (f (j:Nat)) := hfs j
      have hgj : g ((j+1:ℕ):Nat) = succ (g (j:Nat)) := by
        have := (hgiff (j:Nat) (g (j:Nat))).mp rfl
        simpa [nat_equiv_coe_of_coe] using this
      rw [hfj, hgj, ih]
  apply existsUnique_of_exists_of_unique
  · exact ⟨f, ⟨hinj, hsurj⟩, hf0, hiff⟩
  · intro a b ha hb
    rw [key a ha, key b hb]


end Chapter3
