import Analysis.MeasureTheory.Section_1_4_2

/-!
# Introduction to Measure Theory, Section 1.4.3: Countably additive measures and measure spaces

A companion to (the introduction to) Section 1.4.3 of the book "An introduction to Measure Theory".

Note: initially this section will use custom-notions of concrete sigma algebras and countably additive measures, but will transition to the Mathlib notions of {name}`Measurable` and {name}`MeasureTheory.Measure`, which will be in use going forward. In particular, exercises past this point will be easier
to solve using the Mathlib library for measure theory than the custom results defined here.
-/

/-- Definition 1.4.19 (Finitely additive measure) -/
class FinitelyAdditiveMeasure {X:Type*} (B: ConcreteBooleanAlgebra X) where
  measure : Set X → EReal
  measure_pos : ∀ A : Set X, B.measurable A → 0 ≤ measure A
  measure_empty : measure ∅ = 0
  measure_finite_additive : ∀ E F : Set X, B.measurable E → B.measurable F → Disjoint E F →
    measure (E ∪ F) = measure E + measure F

theorem FinitelyAdditiveMeasure.ext {X:Type*} {B: ConcreteBooleanAlgebra X} {μ ν : FinitelyAdditiveMeasure B}
    (h : ∀ A, μ.measure A = ν.measure A) : μ = ν := by
  cases μ; cases ν
  congr 1
  ext A
  exact h A

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.lebesgue (d:ℕ) : FinitelyAdditiveMeasure (LebesgueMeasurable.boolean_algebra d) :=
  {
    measure A := Lebesgue_measure A
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.21 -/
def FinitelyAdditiveMeasure.restrict_alg {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {B':ConcreteBooleanAlgebra X} (hBB': B' ≤ B) : FinitelyAdditiveMeasure B' :=
  {
    measure := μ.measure
    measure_pos := fun A hA => μ.measure_pos A (hBB' A hA)
    measure_empty := μ.measure_empty
    measure_finite_additive := fun E F hE hF hdisj =>
      μ.measure_finite_additive E F (hBB' E hE) (hBB' F hF) hdisj
  }

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.jordan (d:ℕ) : FinitelyAdditiveMeasure (JordanMeasurable.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (LebesgueMeasurable.gt_jordan_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.null (d:ℕ) : FinitelyAdditiveMeasure (IsNull.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (IsNull.lt_lebesgue_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.elem (d:ℕ) : FinitelyAdditiveMeasure (EuclideanSpace'.elementary_boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (by sorry)

open Classical in
/-- Example 1.4.22 (Dirac measure) -/
noncomputable def FinitelyAdditiveMeasure.dirac {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : FinitelyAdditiveMeasure B :=
  {
    measure := fun A => if x₀ ∈ A then 1 else 0
    measure_pos := by intro A _; split <;> norm_num
    measure_empty := by simp
    measure_finite_additive := by
      intro E F _ _ hdisj
      by_cases hE : x₀ ∈ E
      · have hF : x₀ ∉ F := fun h => (Set.disjoint_left.mp hdisj) hE h
        simp [hE, hF, Set.mem_union]
      · by_cases hF : x₀ ∈ F
        · simp [hE, hF, Set.mem_union]
        · simp [hE, hF, Set.mem_union]
  }

/-- Example 1.4.23 (Zero measure) -/
noncomputable instance FinitelyAdditiveMeasure.instZero {X:Type*} (B: ConcreteBooleanAlgebra X) : Zero (FinitelyAdditiveMeasure B) :=
  {
    zero := {
      measure := fun A => 0
      measure_pos := by intro A _; rfl
      measure_empty := by rfl
      measure_finite_additive := by intro E F _ _ _; simp
    }
  }

/-- Example 1.4.24 (linear combinations of measures) -/
noncomputable instance FinitelyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteBooleanAlgebra X} : Add (FinitelyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        measure := fun A => μ.measure A + ν.measure A
        measure_pos := by
          intro A hA
          exact add_nonneg (μ.measure_pos A hA) (ν.measure_pos A hA)
        measure_empty := by simp [μ.measure_empty, ν.measure_empty]
        measure_finite_additive := by
          intro E F hE hF hdisj
          rw [μ.measure_finite_additive E F hE hF hdisj,
              ν.measure_finite_additive E F hE hF hdisj]
          rw [add_add_add_comm]
      }
  }

noncomputable instance FinitelyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteBooleanAlgebra X} : SMul ENNReal (FinitelyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        measure := fun A => c * μ.measure A
        measure_pos := by
          intro A hA
          exact mul_nonneg (by positivity) (μ.measure_pos A hA)
        measure_empty := by simp [μ.measure_empty]
        measure_finite_additive := by
          intro E F hE hF hdisj
          rw [μ.measure_finite_additive E F hE hF hdisj]
          exact EReal.left_distrib_of_nonneg (μ.measure_pos E hE) (μ.measure_pos F hF)
        }
}

noncomputable instance FinitelyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteBooleanAlgebra X} : AddCommMonoid (FinitelyAdditiveMeasure B) :=
{
  add_assoc := by intro a b c; apply FinitelyAdditiveMeasure.ext; intro A; exact add_assoc _ _ _
  zero_add := by intro a; apply FinitelyAdditiveMeasure.ext; intro A; exact zero_add _
  add_zero := by intro a; apply FinitelyAdditiveMeasure.ext; intro A; exact add_zero _
  add_comm := by intro a b; apply FinitelyAdditiveMeasure.ext; intro A; exact add_comm _ _
  nsmul := nsmulRec
}

noncomputable instance FinitelyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteBooleanAlgebra X} : DistribMulAction ENNReal (FinitelyAdditiveMeasure B) :=
{
  smul_zero := by intro c; apply FinitelyAdditiveMeasure.ext; intro A; show (c:EReal) * (0:EReal) = 0; exact mul_zero _
  smul_add := by sorry
  one_smul := by intro a; apply FinitelyAdditiveMeasure.ext; intro A; show ((1:ENNReal):EReal) * a.measure A = a.measure A; rw [EReal.coe_ennreal_one]; exact one_mul _
  mul_smul := by intro c d a; apply FinitelyAdditiveMeasure.ext; intro A; show ((c*d:ENNReal):EReal) * a.measure A = (c:EReal) * ((d:EReal) * a.measure A); rw [EReal.coe_ennreal_mul]; exact mul_assoc _ _ _
}

/-- Example 1.4.25 (Restriction of a measure) -/
def FinitelyAdditiveMeasure.restrict {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : FinitelyAdditiveMeasure (B.restrict A) :=
  {
    measure := fun E => μ.measure E
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.26 (Counting a measure) -/
noncomputable def FinitelyAdditiveMeasure.counting (X:Type*) : FinitelyAdditiveMeasure (⊤  : ConcreteBooleanAlgebra X) :=
  {
    measure := fun E => ENat.card E
    measure_pos := by
      intro A _
      positivity
    measure_empty := by
      show ((∅ : Set X).encard : EReal) = 0
      simp
    measure_finite_additive := by
      intro E F _ _ hdisj
      show (((E ∪ F : Set X).encard : EReal)) = ((E.encard : EReal)) + ((F.encard : EReal))
      rw [Set.encard_union_eq hdisj]
      push_cast
      rfl
  }

/-- Exercise 1.4.20(i) -/
theorem FinitelyAdditiveMeasure.mono {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X} (hE : B.measurable E) (hF : B.measurable F) (hsub : E ⊆ F) : μ.measure E ≤ μ.measure F :=
by
  have hdiff : B.measurable (F \ E) := by
    have : F \ E = (Fᶜ ∪ E)ᶜ := by ext x; simp [Set.mem_diff]
    rw [this]
    exact B.compl_mem _ (B.union_mem _ _ (B.compl_mem _ hF) hE)
  have hdisj : Disjoint E (F \ E) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx
  have hunion : E ∪ (F \ E) = F := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; constructor
    · rintro (h | h); exact hsub h; exact h.1
    · intro h; by_cases hxE : x ∈ E; exact Or.inl hxE; exact Or.inr ⟨h, hxE⟩
  have := μ.measure_finite_additive E (F \ E) hE hdiff hdisj
  rw [hunion] at this
  rw [this]
  have hpos := μ.measure_pos (F \ E) hdiff
  exact le_add_of_nonneg_right hpos

theorem ConcreteBooleanAlgebra.biUnion_mem {X J:Type*} {B: ConcreteBooleanAlgebra X} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) (I: Finset J) : B.measurable (⋃ j ∈ I, E j) := by
  classical
  induction I using Finset.induction with
  | empty => simpa using B.empty_mem
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact B.union_mem _ _ (hE a) ih

/-- Exercise 1.4.20(ii) -/
theorem FinitelyAdditiveMeasure.finite_additivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) (hdisj: Set.univ.PairwiseDisjoint E) :
  μ.measure (⋃ j ∈ I, E j) = ∑ j ∈ I, μ.measure (E j) := by
  classical
  induction I using Finset.induction with
  | empty => simp [μ.measure_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hdisj_as : Disjoint (E a) (⋃ j ∈ s, E j) := by
      rw [Set.disjoint_iUnion_right]; intro i; rw [Set.disjoint_iUnion_right]; intro his
      have hia : i ≠ a := fun h => ha (h ▸ his)
      exact (hdisj (Set.mem_univ a) (Set.mem_univ i) (Ne.symm hia))
    rw [μ.measure_finite_additive (E a) (⋃ j ∈ s, E j) (hE a) (ConcreteBooleanAlgebra.biUnion_mem hE s) hdisj_as, ih]

/-- Exercise 1.4.20(iii) -/
theorem FinitelyAdditiveMeasure.subadd_two {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X} (hE: B.measurable E) (hF: B.measurable F) :
  μ.measure (E ∪ F) ≤ μ.measure E + μ.measure F := by
  have hFE : B.measurable (F \ E) := by
    have : F \ E = (Fᶜ ∪ E)ᶜ := by ext x; simp [Set.mem_diff]
    rw [this]; exact B.compl_mem _ (B.union_mem _ _ (B.compl_mem _ hF) hE)
  have hdisj : Disjoint E (F \ E) := by rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx
  have heq : E ∪ F = E ∪ (F \ E) := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; constructor
    · rintro (h | h); exact Or.inl h; by_cases hxE : x ∈ E; exact Or.inl hxE; exact Or.inr ⟨h, hxE⟩
    · rintro (h | h); exact Or.inl h; exact Or.inr h.1
  rw [heq, μ.measure_finite_additive E (F \ E) hE hFE hdisj]
  exact add_le_add (le_refl _) (μ.mono hFE hF Set.diff_subset)

theorem FinitelyAdditiveMeasure.finite_subadditivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) :
  μ.measure (⋃ j ∈ I, E j) ≤ ∑ j ∈ I, μ.measure (E j) := by
  classical
  induction I using Finset.induction with
  | empty => simp [μ.measure_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    refine le_trans (μ.subadd_two (hE a) (ConcreteBooleanAlgebra.biUnion_mem hE s)) ?_
    exact add_le_add (le_refl _) ih

/-- Exercise 1.4.20(iv) -/
theorem FinitelyAdditiveMeasure.mes_union_add_mes_inter {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X}
    (hE: B.measurable E) (hF: B.measurable F) :
  μ.measure (E ∪ F) + μ.measure (E ∩ F) = μ.measure E + μ.measure F := by
  have hcompl : ∀ {S : Set X}, B.measurable S → ∀ {T : Set X}, B.measurable T → B.measurable (S \ T) := by
    intro S hS T hT
    have : S \ T = (Sᶜ ∪ T)ᶜ := by ext x; simp [Set.mem_diff]
    rw [this]; exact B.compl_mem _ (B.union_mem _ _ (B.compl_mem _ hS) hT)
  have hinter : ∀ {S T : Set X}, B.measurable S → B.measurable T → B.measurable (S ∩ T) := by
    intro S T hS hT
    have : S ∩ T = (Sᶜ ∪ Tᶜ)ᶜ := by ext x; simp [Set.mem_inter_iff]
    rw [this]; exact B.compl_mem _ (B.union_mem _ _ (B.compl_mem _ hS) (B.compl_mem _ hT))
  have hFE : B.measurable (F \ E) := hcompl hF hE
  have hEF : B.measurable (E ∩ F) := hinter hE hF
  -- E ∪ F = E ∪ (F \ E), disjoint
  have hUdisj : Disjoint E (F \ E) := by rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx
  have hUeq : E ∪ F = E ∪ (F \ E) := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; constructor
    · rintro (h | h); exact Or.inl h; by_cases hxE : x ∈ E; exact Or.inl hxE; exact Or.inr ⟨h, hxE⟩
    · rintro (h | h); exact Or.inl h; exact Or.inr h.1
  have hU := μ.measure_finite_additive E (F \ E) hE hFE hUdisj
  rw [← hUeq] at hU
  -- F = (E ∩ F) ∪ (F \ E), disjoint
  have hFdisj : Disjoint (E ∩ F) (F \ E) := by
    rw [Set.disjoint_left]; rintro x ⟨hxE, _⟩ ⟨_, hxE'⟩; exact hxE' hxE
  have hFeq : (E ∩ F) ∪ (F \ E) = F := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩); exact h; exact h
    · intro h; by_cases hxE : x ∈ E; exact Or.inl ⟨hxE, h⟩; exact Or.inr ⟨h, hxE⟩
  have hFdecomp := μ.measure_finite_additive (E ∩ F) (F \ E) hEF hFE hFdisj
  rw [hFeq] at hFdecomp
  rw [hU, hFdecomp]
  rw [add_assoc, add_comm (μ.measure (F \ E)) (μ.measure (E ∩ F)), ← add_assoc]

open Classical in
/-- Exercise 1.4.21 -/
theorem FinitelyAdditiveMeasure.finite_atomic_eq {I X: Type*} [Fintype I] {atoms: I → Set X} (h_part: IsPartition atoms) (μ : FinitelyAdditiveMeasure h_part.to_ConcreteBooleanAlgebra) : ∃! c : I → ENNReal, ∀ E, h_part.to_ConcreteBooleanAlgebra.measurable E → μ.measure E = ∑ i ∈ Finset.univ.filter (fun i => atoms i ⊆ E), c i := by sorry

/-- Definition 1.4.27 (Countably additive measure) -/
class CountablyAdditiveMeasure {X:Type*} (B: ConcreteSigmaAlgebra X) extends FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra where
  measure_countable_additive : ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    measure (⋃ n, E n) = ∑' n, (measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) : Prop :=
  B.isSigmaAlgebra ∧ ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    μ.measure (⋃ n, E n) = ∑' n, (μ.measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive.toCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (h: μ.isCountablyAdditive) : CountablyAdditiveMeasure h.1.toSigmaAlgebra :=
  {
    measure := μ.measure
    measure_pos := μ.measure_pos
    measure_empty := μ.measure_empty
    measure_finite_additive := μ.measure_finite_additive
    measure_countable_additive := h.2
  }

/-- Example 1.4.28-/
theorem FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive (d:ℕ) : (FinitelyAdditiveMeasure.lebesgue d).isCountablyAdditive :=
  by sorry

theorem FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB': B' ≤ B) : (μ.toFinitelyAdditiveMeasure.restrict_alg hBB').isCountablyAdditive := by
  refine ⟨B'.isSigmaAlgebra, ?_⟩
  intro E hE hdisj
  exact μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj

def CountablyAdditiveMeasure.restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB' : B' ≤ B) : CountablyAdditiveMeasure B' :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict_alg hBB',
    measure_countable_additive := by
      intro E hE hdisj
      exact μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj
  }

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.dirac_isCountablyAdditive {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : (FinitelyAdditiveMeasure.dirac x₀ B).isCountablyAdditive :=
  by sorry

/-- Example 1.4.29-/
theorem FinitelyAdditiveMeasure.counting_isCountablyAdditive {X:Type*} : (FinitelyAdditiveMeasure.counting X).isCountablyAdditive :=
  by sorry

/-- Example 1.4.30 -/
def CountablyAdditiveMeasure.restrict {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : CountablyAdditiveMeasure (B.restrict A) :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict A hA,
    measure_countable_additive := by sorry
  }

noncomputable instance CountablyAdditiveMeasure.instZero {X:Type*} (B: ConcreteSigmaAlgebra X) : Zero (CountablyAdditiveMeasure B) :=
  {
    zero := {
      toFinitelyAdditiveMeasure := 0
      measure_countable_additive := by
        intro E _ _
        show (0:EReal) = ∑' n, (0:EReal)
        simp
    }
  }

noncomputable instance CountablyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteSigmaAlgebra X} : Add (CountablyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure + ν.toFinitelyAdditiveMeasure
        measure_countable_additive := by sorry
      }
  }

theorem CountablyAdditiveMeasure.ext {X:Type*} {B: ConcreteSigmaAlgebra X} {μ ν : CountablyAdditiveMeasure B}
    (h : μ.toFinitelyAdditiveMeasure = ν.toFinitelyAdditiveMeasure) : μ = ν := by
  cases μ; cases ν; congr 1

noncomputable instance CountablyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteSigmaAlgebra X} : AddCommMonoid (CountablyAdditiveMeasure B) :=
{
  add_assoc := by intro a b c; apply CountablyAdditiveMeasure.ext; show (a.toFinitelyAdditiveMeasure + b.toFinitelyAdditiveMeasure) + c.toFinitelyAdditiveMeasure = a.toFinitelyAdditiveMeasure + (b.toFinitelyAdditiveMeasure + c.toFinitelyAdditiveMeasure); exact add_assoc _ _ _
  zero_add := by intro a; apply CountablyAdditiveMeasure.ext; show (0:FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra) + a.toFinitelyAdditiveMeasure = a.toFinitelyAdditiveMeasure; exact zero_add _
  add_zero := by intro a; apply CountablyAdditiveMeasure.ext; show a.toFinitelyAdditiveMeasure + (0:FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra) = a.toFinitelyAdditiveMeasure; exact add_zero _
  add_comm := by intro a b; apply CountablyAdditiveMeasure.ext; show a.toFinitelyAdditiveMeasure + b.toFinitelyAdditiveMeasure = b.toFinitelyAdditiveMeasure + a.toFinitelyAdditiveMeasure; exact add_comm _ _
  nsmul := nsmulRec
}

/-- Exercise 1.4.22(i) -/
noncomputable instance CountablyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteSigmaAlgebra X} : SMul ENNReal (CountablyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        toFinitelyAdditiveMeasure := c • μ.toFinitelyAdditiveMeasure
        measure_countable_additive := by sorry
        }
}

noncomputable instance CountablyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteSigmaAlgebra X} : DistribMulAction ENNReal (CountablyAdditiveMeasure B) :=
{
  smul_zero := by intro c; apply CountablyAdditiveMeasure.ext; show c • (0:FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra) = 0; exact smul_zero c
  smul_add := by sorry
  one_smul := by intro a; apply CountablyAdditiveMeasure.ext; show (1:ENNReal) • a.toFinitelyAdditiveMeasure = a.toFinitelyAdditiveMeasure; exact one_smul _ _
  mul_smul := by intro c d a; apply CountablyAdditiveMeasure.ext; show (c*d) • a.toFinitelyAdditiveMeasure = c • (d • a.toFinitelyAdditiveMeasure); exact mul_smul _ _ _
}

/-- Exercise 1.4.22(ii) -/
noncomputable def CountablyAdditiveMeasure.sum {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: ℕ → CountablyAdditiveMeasure B) : CountablyAdditiveMeasure B :=
  {
    toFinitelyAdditiveMeasure := {
      measure := fun A => ∑' n, (μ n).toFinitelyAdditiveMeasure.measure A
      measure_pos := by
        intro A hA
        apply tsum_nonneg
        intro n
        exact (μ n).toFinitelyAdditiveMeasure.measure_pos A hA
      measure_empty := by
        show ∑' n, (μ n).toFinitelyAdditiveMeasure.measure ∅ = 0
        simp only [(μ _).toFinitelyAdditiveMeasure.measure_empty]
        simp
      measure_finite_additive := by sorry
    }
    measure_countable_additive := by sorry
  }

open MeasureTheory

noncomputable def CountablyAdditiveMeasure.toMeasure {X:Type*} {B: ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) :
  @Measure X B.measurableSpace :=
  let _measurable := B.measurableSpace
  {
      measureOf E := (μ.measure E).toENNReal
      empty := by show (μ.measure ∅).toENNReal = 0; rw [μ.measure_empty]; simp
      mono := by sorry
      iUnion_nat := by sorry
      m_iUnion := by sorry
      trim_le := by sorry
  }

noncomputable def FinitelyAdditiveMeasure.isCountablyAdditive.toMeasure {X:Type*} {B: ConcreteBooleanAlgebra X} {μ: FinitelyAdditiveMeasure B} (h: μ.isCountablyAdditive) :
  @Measure X h.1.toSigmaAlgebra.measurableSpace := h.toCountablyAdditive.toMeasure

def Measure.toCountablyAdditiveMeasure {X:Type*} [M : MeasurableSpace X] (μ: Measure X) : CountablyAdditiveMeasure M.sigmaAlgebra :=
  {
    toFinitelyAdditiveMeasure := {
      measure E := μ.measureOf E
      measure_pos := by intro A _; positivity
      measure_empty := by show ((μ.measureOf ∅ : ENNReal) : EReal) = 0; simp
      measure_finite_additive := by sorry
    }
    measure_countable_additive := by sorry
  }

/-- Exercise 1.4.23(i) -/
theorem Measure.countable_subadditivity {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n)) :
  μ.measureOf (⋃ n, E n) ≤ ∑' n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.23(ii) -/
theorem Measure.upwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  (hmono : Monotone E) : μ (⋃ n, E n) = ⨆ n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.23(iii) -/
theorem Measure.downwards_mono {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E) (hfin : ∃ n, μ (E n) < ⊤) : μ (⋂ n, E n) = ⨅ n, μ.measureOf (E n) := by sorry

theorem Measure.downwards_mono_counter : ∃ (X:Type) (M: MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (hmono : Antitone E), μ (⋂ n, E n) ≠ ⨅ n, μ.measureOf (E n) := by sorry

/-- Exercise 1.4.24 (i) (Dominated convergence for sets) -/
theorem Measure.measurable_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' : Set X} (hlim : PointwiseConvergesTo E E') : Measurable E := by sorry

/-- Exercise 1.4.24 (ii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim {X:Type*} [MeasurableSpace X] (μ: Measure X) {E : ℕ → Set X} (hE: ∀ n, Measurable (E n))
  {E' F : Set X} (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hfin : μ F < ⊤) (hcon : ∀ n, E n ⊆ F) :
  Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.24 (iii) (Dominated convergence for sets) -/
theorem Measure.measure_of_lim_counter : ∃ (X:Type) (M:MeasurableSpace X) (μ: Measure X) (E : ℕ → Set X) (hE: ∀ n, Measurable (E n))
  (E' F : Set X) (hlim : PointwiseConvergesTo E E') (hF : Measurable F) (hcon : ∀ n, E n ⊆ F),
  ¬ Filter.atTop.Tendsto (fun n ↦ μ (E n)) (nhds (μ E')) := by sorry

/-- Exercise 1.4.25 -/
theorem Measure.on_countable {X:Type*} [Countable X] [M: MeasurableSpace X] (hM: M = ⊤) (μ: Measure X) :
  ∃! c : X → ENNReal, ∀ E : Set X, μ E = ∑' x : E, c x := by sorry

-- Definition 1.4.31
#check Measure.IsComplete

#check NullMeasurableSpace

#check Measure.completion

/-- Exercise 1.4.26 (Completion) -/
theorem Measure.completion_lt {X:Type*} [M : MeasurableSpace X] (μ: Measure X) (M' : MeasurableSpace X) (μ' : @Measure X M')
  (hMM' : M ≤ M') (hμ : ∀ E, M.MeasurableSet' E → μ E = μ' E) : ∀ E : Set X, @NullMeasurableSet X M E μ → (M'.MeasurableSet' E ∧ μ' E = μ.completion E)
   := by sorry

noncomputable def EuclideanSpace'.lebesgueMeasure (d:ℕ) := (FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toMeasure

noncomputable def EuclideanSpace'.borelMeasure (d:ℕ) := ((FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toCountablyAdditive.restrict_alg (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d)).toMeasure

def Measure.equiv {X:Type*} {M M' : MeasurableSpace X} (μ: @Measure X M) (μ': @Measure X M') : Prop := M = M' ∧ ∀ E, M.MeasurableSet' E → μ E = μ' E

/-- Exercise 1.4.27 -/
theorem EuclideanSpace'.borel_completion_eq_lebesgue {d:ℕ} :
  Measure.equiv (EuclideanSpace'.borelMeasure d).completion (EuclideanSpace'.lebesgueMeasure d) := by sorry

/-- Exercise 1.4.28(i) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hfin: μ Set.univ < ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry

/-- Exercise 1.4.28(ii) (Approximation by an algebra) -/
theorem BooleanAlgebra.approx_sigma_finite {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: @Measure X (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurableSpace) (hσfin: ∃ A : ℕ → Set X, (∀ n, B.measurable (A n) ∧ μ (A n) < ⊤) ∧ ⋃ n, A n = ⊤) : ∀ (ε : ℝ) (hε: ε>0) (E : Set X) (hE: (ConcreteSigmaAlgebra.generated_by B.measurableSets).measurable E),
  ∃ F : Set X, B.measurable F ∧ μ (symmDiff E F) < ENNReal.ofReal ε := by sorry
