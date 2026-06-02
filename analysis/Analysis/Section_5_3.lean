import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
  rw [Sequence.equiv_iff] at *
  intro ε hε
  obtain ⟨N1, hN1⟩ := hab (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := hbc (ε/2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := hN1 n (le_trans (le_max_left _ _) hn)
  have e2 := hN2 n (le_trans (le_max_right _ _) hn)
  calc |a n - c n| ≤ |a n - b n| + |b n - c n| := abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := fun a => by
       rw [Sequence.equiv_iff]; intro ε hε
       exact ⟨0, fun n _ => by rw [sub_self, abs_zero]; linarith⟩
     symm := fun {a b} hab => by
       rw [Sequence.equiv_iff] at *; intro ε hε
       obtain ⟨N, hN⟩ := hab ε hε
       exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩
     trans := fun {a b c} hab hbc => Sequence.equiv_trans hab hbc
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  exact ⟨0, fun j _ k _ => by rw [Section_4_3.dist_eq, sub_self, abs_zero]; linarith⟩

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind


/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  obtain ⟨Ma, hMa, hBa⟩ := Sequence.isBounded_of_isCauchy ha
  obtain ⟨Mb, hMb, hBb⟩ := Sequence.isBounded_of_isCauchy hb
  have hba : ∀ j:ℕ, |a j| ≤ Ma := fun j => by
    have h := hBa (j:ℤ)
    rwa [Sequence.eval_coe_at_int, if_pos (by positivity), Int.toNat_natCast] at h
  have hbb : ∀ j:ℕ, |b j| ≤ Mb := fun j => by
    have h := hBb (j:ℤ)
    rwa [Sequence.eval_coe_at_int, if_pos (by positivity), Int.toNat_natCast] at h
  rw [Sequence.IsCauchy.coe] at ha hb ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := ha (ε/(2*(Mb+1))) (by positivity)
  obtain ⟨N2, hN2⟩ := hb (ε/(2*(Ma+1))) (by positivity)
  refine ⟨max N1 N2, fun j hj k hk => ?_⟩
  have ea := hN1 j (le_trans (le_max_left _ _) hj) k (le_trans (le_max_left _ _) hk)
  have eb := hN2 j (le_trans (le_max_right _ _) hj) k (le_trans (le_max_right _ _) hk)
  rw [Section_4_3.dist_eq] at ea eb ⊢
  simp only [Pi.mul_apply]
  have t1 : |a j * b j - a k * b k| ≤ |a j| * |b j - b k| + |b k| * |a j - a k| := by
    calc |a j * b j - a k * b k| = |a j * (b j - b k) + (a j - a k) * b k| := by congr 1; ring
      _ ≤ |a j * (b j - b k)| + |(a j - a k) * b k| := abs_add_le _ _
      _ = |a j| * |b j - b k| + |b k| * |a j - a k| := by rw [abs_mul, abs_mul]; ring
  have h1 : |a j| * |b j - b k| ≤ Ma * (ε/(2*(Ma+1))) := mul_le_mul (hba j) eb (abs_nonneg _) hMa
  have h2 : |b k| * |a j - a k| ≤ Mb * (ε/(2*(Mb+1))) := mul_le_mul (hbb k) ea (abs_nonneg _) hMb
  have h3 : Ma * (ε/(2*(Ma+1))) ≤ ε/2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [hMa, hε]
  have h4 : Mb * (ε/(2*(Mb+1))) ≤ ε/2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [hMb, hε]
  linarith [t1, h1, h2, h3, h4]

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  obtain ⟨Mb, hMb, hBb⟩ := Sequence.isBounded_of_isCauchy hb
  have hbb : ∀ j:ℕ, |b j| ≤ Mb := fun j => by
    have h := hBb (j:ℤ)
    rwa [Sequence.eval_coe_at_int, if_pos (by positivity), Int.toNat_natCast] at h
  rw [Sequence.equiv_iff] at *
  intro ε hε
  obtain ⟨N, hN⟩ := haa' (ε/(Mb+1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have e := hN n hn
  simp only [Pi.mul_apply]
  rw [show a n * b n - a' n * b n = (a n - a' n) * b n by ring, abs_mul, mul_comm]
  calc |b n| * |a n - a' n| ≤ Mb * (ε/(Mb+1)) := mul_le_mul (hbb n) e (abs_nonneg _) hMb
    _ ≤ ε := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [hMb, hε]

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  rw [ratCast_def, ratCast_def,
    Real.LIM_eq_LIM (Sequence.IsCauchy.const q) (Sequence.IsCauchy.const r), Sequence.equiv_iff]
  constructor
  · intro h
    by_contra hne
    have hpos : |q - r| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨N, hN⟩ := h (|q-r|/2) (by linarith)
    have hc := hN N (le_refl N)
    simp only at hc
    linarith
  · intro h; subst h; intro ε hε; exact ⟨0, fun n _ => by simp; linarith⟩

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  rw [ratCast_def a, ratCast_def b, ratCast_def (a+b),
    Real.LIM_add (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  congr 1

/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  rw [ratCast_def a, ratCast_def b, ratCast_def (a*b),
    Real.LIM_mul (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  congr 1

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  show ((-1:ℚ):Real) * (a:Real) = ((-a:ℚ):Real)
  rw [ratCast_mul]; congr 1; ring

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  show ((-1:ℚ):Real) * LIM a = LIM (-a)
  rw [ratCast_def, Real.LIM_mul (Sequence.IsCauchy.const (-1)) ha]
  congr 1; ext n; simp only [Pi.mul_apply, Pi.neg_apply]; ring

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at ha ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun j hj k hk => ?_⟩
  have h := hN j hj k hk
  rw [Section_4_3.dist_eq] at h ⊢
  simp only [Pi.neg_apply]
  rw [show -a j - -a k = -(a j - a k) by ring, abs_neg]
  exact h

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  have h : (a - b) = a + (-b) := by ext n; simp [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring
  rw [h]
  exact Sequence.IsCauchy.add ha (Sequence.IsCauchy.neg b hb)

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  rw [Real.sub_eq_add_neg, Real.neg_LIM b hb, Real.LIM_add ha (Sequence.IsCauchy.neg b hb)]
  congr 1; ext n; simp [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [Real.sub_eq_add_neg, neg_ratCast, ratCast_add]; congr 1; ring

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro x y
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    rw [Real.LIM_add ha hb, Real.LIM_add hb ha]
    congr 1; ext n; simp [Pi.add_apply]; ring

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro x y
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    rw [Real.LIM_mul ha hb, Real.LIM_mul hb ha]
    congr 1; ext n; simp [Pi.mul_apply]; ring
  mul_assoc := by
    intro x y z
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    obtain ⟨c, hc, rfl⟩ := Real.eq_lim z
    rw [Real.LIM_mul ha hb, Real.LIM_mul (Sequence.IsCauchy.mul ha hb) hc,
      Real.LIM_mul hb hc, Real.LIM_mul ha (Sequence.IsCauchy.mul hb hc)]
    congr 1; ext n; simp [Pi.mul_apply]; ring
  one_mul := by
    intro x
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    show ((1:ℚ):Real) * LIM a = LIM a
    rw [ratCast_def, Real.LIM_mul (Sequence.IsCauchy.const 1) ha]
    congr 1; ext n; simp [Pi.mul_apply]
  mul_one := by
    intro x
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    show LIM a * ((1:ℚ):Real) = LIM a
    rw [ratCast_def, Real.LIM_mul ha (Sequence.IsCauchy.const 1)]
    congr 1; ext n; simp [Pi.mul_apply]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by
    intro x y z
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    obtain ⟨c, hc, rfl⟩ := Real.eq_lim z
    rw [Real.LIM_add hb hc, Real.LIM_mul ha (Sequence.IsCauchy.add hb hc),
      Real.LIM_mul ha hb, Real.LIM_mul ha hc,
      Real.LIM_add (Sequence.IsCauchy.mul ha hb) (Sequence.IsCauchy.mul ha hc)]
    congr 1; ext n; simp [Pi.mul_apply, Pi.add_apply]; ring
  right_distrib := by
    intro x y z
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    obtain ⟨c, hc, rfl⟩ := Real.eq_lim z
    rw [Real.LIM_add ha hb, Real.LIM_mul (Sequence.IsCauchy.add ha hb) hc,
      Real.LIM_mul ha hc, Real.LIM_mul hb hc,
      Real.LIM_add (Sequence.IsCauchy.mul ha hc) (Sequence.IsCauchy.mul hb hc)]
    congr 1; ext n; simp [Pi.mul_apply, Pi.add_apply]; ring
  zero_mul := by
    intro x
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    rw [← Real.LIM.zero, Real.LIM_mul (Sequence.IsCauchy.const 0) ha]
    congr 1; ext n; simp [Pi.mul_apply]
  mul_zero := by
    intro x
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    rw [← Real.LIM.zero, Real.LIM_mul ha (Sequence.IsCauchy.const 0)]
    congr 1; ext n; simp [Pi.mul_apply]
  mul_assoc := by
    intro x y z
    obtain ⟨a, ha, rfl⟩ := Real.eq_lim x
    obtain ⟨b, hb, rfl⟩ := Real.eq_lim y
    obtain ⟨c, hc, rfl⟩ := Real.eq_lim z
    rw [Real.LIM_mul ha hb, Real.LIM_mul (Sequence.IsCauchy.mul ha hb) hc,
      Real.LIM_mul hb hc, Real.LIM_mul ha (Sequence.IsCauchy.mul hb hc)]
    congr 1; ext n; simp [Pi.mul_apply]; ring
  natCast_succ := fun n => by
    show (((n+1:ℕ):ℚ):Real) = (((n:ℕ):ℚ):Real) + 1
    rw [Nat.cast_add_one, show (1:Real) = ((1:ℚ):Real) from rfl, ← Real.ratCast_add]
  intCast_negSucc := fun n => by
    show (((Int.negSucc n:ℤ):ℚ):Real) = -(((n+1:ℕ):ℚ):Real)
    rw [Int.cast_negSucc, ← Real.neg_ratCast]

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by show ((0:ℚ):Real) = 0; rw [ratCast_def]; exact Real.LIM.zero
  map_one' := by show ((1:ℚ):Real) = 1; rfl
  map_add' := fun a b => (Real.ratCast_add a b).symm
  map_mul' := fun a b => (Real.ratCast_mul a b).symm

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  rw [bounded_away_zero_def]; push_neg
  intro c hc
  obtain ⟨m, hm⟩ := exists_nat_gt (1/c)
  refine ⟨m, ?_⟩
  rw [abs_of_pos (by positivity), show (10:ℚ)^(-(m:ℤ)-1) = 1/(10:ℚ)^(m+1) from by
    rw [one_div, ← zpow_natCast (10:ℚ) (m+1), ← zpow_neg]; congr 1; omega,
    div_lt_iff₀ (by positivity)]
  have hpow : (m:ℚ)+1 ≤ (10:ℚ)^(m+1) := by
    have key := one_add_mul_le_pow (show (-2:ℚ) ≤ 9 by norm_num) (m+1)
    norm_num at key
    have hmnn : (0:ℚ) ≤ (m:ℚ) := by positivity
    push_cast at key
    nlinarith [key, hmnn]
  rw [div_lt_iff₀ hc] at hm
  nlinarith [hm, hpow, hc, mul_le_mul_of_nonneg_left hpow hc.le]

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  rw [bounded_away_zero_def]; push_neg
  intro c hc
  refine ⟨0, ?_⟩
  have h0 : |(1:ℚ) - 10^(-((0:ℕ):ℤ))| = 0 := by norm_num
  rw [h0]; exact hc

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  rintro ⟨M, hM, hB⟩
  obtain ⟨m, hm⟩ := exists_nat_gt M
  have hb := hB (m:ℤ)
  rw [Sequence.eval_coe_at_int, if_pos (by positivity), Int.toNat_natCast,
    abs_of_pos (by positivity)] at hb
  have hpow : (m:ℚ) + 1 ≤ (10:ℚ)^(m+1) := by
    have key := one_add_mul_le_pow (show (-2:ℚ) ≤ 9 by norm_num) (m+1)
    norm_num at key
    have hmnn : (0:ℚ) ≤ (m:ℚ) := by positivity
    push_cast at key
    nlinarith [key, hmnn]
  linarith

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj
    have hd := hb' j hj n₀ hn₀
    rw [Section_4_3.dist_eq, abs_sub_comm] at hd
    have htri := abs_sub_abs_le_abs_sub (b n₀) (b j)
    linarith [hx, hd, htri]
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro δ hδ
    refine ⟨n₀, fun n hn => ?_⟩
    have hab : a n = b n := by simp only [a]; rw [if_neg (by omega)]
    rw [hab, sub_self, abs_zero]
    linarith
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  obtain ⟨c, hc, hca⟩ := ha
  rw [← Real.LIM.zero, Ne, Real.LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const 0),
    Sequence.equiv_iff]
  push_neg
  refine ⟨c/2, by linarith, fun N => ⟨N, le_refl N, ?_⟩⟩
  simp only [sub_zero]
  have := hca N
  linarith

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by
        congr; simp only [Pi.inv_apply]; field_simp [ha' m, ha' n]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [Inv.inv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  sorry

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

theorem Real.zero_ne_one' : (0:Real) ≠ 1 := by
  rw [show (0:Real) = ((0:ℚ):Real) from rfl, show (1:Real) = ((1:ℚ):Real) from rfl, Ne,
    Real.ratCast_inj]
  norm_num

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := ⟨0, 1, Real.zero_ne_one'⟩
  mul_inv_cancel := by sorry
  inv_zero := Real.inv_zero
  ratCast_def := by sorry
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by sorry

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  push_neg
  exact ⟨0, 1, 0, rfl, by simp, Real.zero_ne_one'⟩

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded :=
  (Sequence.isBounded_of_eventuallyClose (hab 1 (by norm_num))).mp ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  have hcau : ((fun n:ℕ ↦ 1/((n:ℚ)+1)):Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (1/ε)
    refine ⟨m, fun j hj k hk => ?_⟩
    rw [Section_4_3.dist_eq]
    have h1m : 1/((m:ℚ)+1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hε] at hm; nlinarith [hm, hε]
    have hbjm : 1/((j:ℚ)+1) ≤ 1/((m:ℚ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); have : (m:ℚ) ≤ j := by exact_mod_cast hj
      linarith
    have hbkm : 1/((k:ℚ)+1) ≤ 1/((m:ℚ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); have : (m:ℚ) ≤ k := by exact_mod_cast hk
      linarith
    have hbj : (0:ℚ) < 1/((j:ℚ)+1) := by positivity
    have hbk : (0:ℚ) < 1/((k:ℚ)+1) := by positivity
    rw [abs_le]
    constructor <;> linarith
  rw [← Real.LIM.zero, Real.LIM_eq_LIM hcau (Sequence.IsCauchy.const 0), Sequence.equiv_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1/ε)
  refine ⟨m, fun n hn => ?_⟩
  simp only [sub_zero]
  rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hm
  have hnm : (m:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
  nlinarith [hm, hnm, hε]

end Chapter5
