import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals {name}`EReal`, particularly with regard to the supremum
  operation {name}`sSup` and infimum operation {name}`sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp <;> tauto

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by rw [lt_iff]; exact ⟨le_top, real_neq_infty 3⟩


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := bot_lt_top


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := le_refl x

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := lt_trichotomy x y

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  rintro ⟨h1, rfl⟩; exact lt_irrefl _ h1

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  rintro ⟨h1, rfl⟩; exact lt_irrefl _ h1

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := fun ⟨h1, h2⟩ => lt_asymm h1 h2

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := le_trans hxy hyz

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  rw [EReal.neg_le_neg_iff]; exact hxy

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  erw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . exact absurd hb (lt_irrefl _)
  exact ⟨↑hnon.choose, Set.mem_image_of_mem _ hnon.choose_spec, bot_lt_coe _⟩

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨Or.inl ⟨0, by norm_num⟩, by decide⟩
  · rintro x ⟨hx, hx'⟩
    rcases hx with ⟨n, rfl⟩ | rfl
    · have hb : (1:EReal) ≤ (n:EReal) + 1 := by
        have : (0:EReal) ≤ (n:EReal) := by positivity
        calc (1:EReal) = 0 + 1 := by norm_num
          _ ≤ (n:EReal) + 1 := by gcongr
      rw [show (-1:EReal) = -(1:EReal) from rfl, EReal.neg_le_neg_iff]
      exact hb
    · simp at hx'

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  have htop : (⊤:EReal) ∈ -Example_6_2_7 := by
    rw [Set.mem_neg, EReal.neg_top]
    simp [Example_6_2_7]
  rw [EReal.sup_of_infty_mem htop, EReal.neg_top]

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨0, ?_⟩
    norm_num
  · rintro x ⟨n, rfl⟩
    rw [EReal.coe_le_coe_iff]
    have h1 : (10:ℝ)^(-(n:ℤ)-1) ≤ (10:ℝ)^(-1:ℤ) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    have : (10:ℝ)^(-1:ℤ) = 0.1 := by norm_num
    rw [this] at h1
    norm_num
    linarith

example : sSup Example_6_2_8 = 1 := by
  refine IsLUB.csSup_eq ⟨?_, ?_⟩ ⟨_, 0, rfl⟩
  · rintro x ⟨n, rfl⟩
    rw [show (1:EReal) = ((1:ℝ):EReal) from rfl, EReal.coe_le_coe_iff]
    have : (0:ℝ) < (10:ℝ)^(-(n:ℤ)-1) := by positivity
    linarith
  · intro b hb
    by_contra hlt
    push_neg at hlt
    have h09 : ((0.9:ℝ):EReal) ≤ b := hb ⟨0, by norm_num⟩
    obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
    · rw [show (1:EReal) = ((1:ℝ):EReal) from rfl, EReal.coe_lt_coe_iff] at hlt
      have hpos : (0:ℝ) < 1 - y := by linarith
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1:ℝ)/10 < 1)
      have hub : (1 - (10:ℝ)^(-(n:ℤ)-1)) ≤ y := by
        have := hb ⟨n, rfl⟩; rwa [EReal.coe_le_coe_iff] at this
      have hz : (10:ℝ)^(-(n:ℤ)-1) ≤ (1/10:ℝ)^n := by
        have e : (1/10:ℝ)^n = (10:ℝ)^(-(n:ℤ)) := by
          rw [div_pow, one_pow, one_div, ← zpow_natCast (10:ℝ) n, ← zpow_neg]
        rw [e]
        apply zpow_le_zpow_right₀ (by norm_num)
        omega
      linarith
    · exact not_top_lt hlt
    · simp at h09

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨0, by norm_num⟩
  · rintro x ⟨n, rfl⟩
    have : (0:EReal) ≤ (n:EReal) := by positivity
    calc (1:EReal) = 0 + 1 := by norm_num
      _ ≤ (n:EReal) + 1 := by gcongr

example : sSup Example_6_2_9 = ⊤ := by
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def b
  · obtain ⟨n, hn⟩ := exists_nat_gt y
    refine ⟨n+1, ⟨n, rfl⟩, ?_⟩
    push_cast
    exact_mod_cast lt_trans (by exact_mod_cast hn) (by norm_num)
  · exact absurd hb (lt_irrefl _)
  · exact ⟨1, ⟨0, by norm_num⟩, bot_lt_iff_ne_bot.mpr (by decide)⟩

example : sInf (∅ : Set EReal) = ⊤ := sInf_empty

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  · intro h
    by_contra hne
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hne
    obtain ⟨x, hx⟩ := hne
    exact absurd (lt_of_le_of_lt (le_sSup hx) (lt_of_lt_of_le h (sInf_le hx))) (lt_irrefl x)
  · rintro rfl
    rw [sSup_empty, sInf_empty]
    exact bot_lt_top

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := le_sSup hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x := sInf_le hx

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := sSup_le hM

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_lower (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := le_sInf hM

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib {name}`EReal`.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro a b hab
  cases a <;> cases b <;>
    simp only [toEReal, EReal.coe_eq_coe_iff] at hab <;>
    first
      | rfl
      | rw [Real.equivR.injective hab]
      | exact absurd hab bot_ne_top
      | exact absurd hab top_ne_bot
      | exact absurd hab (EReal.coe_ne_bot _)
      | exact absurd hab (EReal.coe_ne_top _)
      | exact absurd hab.symm (EReal.coe_ne_bot _)
      | exact absurd hab.symm (EReal.coe_ne_top _)

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro x
  induction x using EReal.rec with
  | bot => exact ⟨neg_infty, rfl⟩
  | coe y =>
      refine ⟨real (Real.equivR.symm y), ?_⟩
      show ((Real.equivR (Real.equivR.symm y) : ℝ) : EReal) = (y : EReal)
      rw [Equiv.apply_symm_apply]
  | top => exact ⟨infty, rfl⟩

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal :=
  Equiv.ofBijective toEReal ⟨coe_inj, coe_surj⟩
