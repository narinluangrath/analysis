import Mathlib.SetTheory.Cardinal.Aleph
import Analysis.MeasureTheory.Section_1_4_1
/-!
# Introduction to Measure Theory, Section 1.4.2: $\sigma$-algebras and measurable spaces

A companion to (the introduction to) Section 1.4.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.12 (Sigma algebra) -/
class ConcreteSigmaAlgebra (X:Type*) extends ConcreteBooleanAlgebra X where
  countable_union_mem : ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X := {
  MeasurableSet' := B.measurable
  measurableSet_empty := B.empty_mem
  measurableSet_compl := B.compl_mem
  measurableSet_iUnion := B.countable_union_mem
}

def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X := {
  measurable := M.MeasurableSet'
  empty_mem := M.measurableSet_empty
  compl_mem := M.measurableSet_compl
  union_mem := fun E F hE hF => @MeasurableSet.union X M E F hE hF
  countable_union_mem := M.measurableSet_iUnion
}

def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop := ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

theorem ConcreteSigmaAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteSigmaAlgebra X) : B.isSigmaAlgebra := B.countable_union_mem

def ConcreteBooleanAlgebra.isSigmaAlgebra.toSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isSigmaAlgebra) : ConcreteSigmaAlgebra X :=
  { countable_union_mem := h }

/-- Exercise 1.4.10 -/
def ConcreteBooleanAlgebra.isAtomic.isSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isAtomic) : B.isSigmaAlgebra :=
  by
  obtain ⟨I, parts, hI, rfl⟩ := h
  intro E hE
  choose J hJ using hE
  refine ⟨⋃ n, J n, ?_⟩
  rw [Set.iUnion_congr hJ]
  ext x
  simp only [Set.mem_iUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨n, i, hiJ, hx⟩
    exact ⟨i, ⟨n, hiJ⟩, hx⟩
  · rintro ⟨i, ⟨n, hiJ⟩, hx⟩
    exact ⟨n, i, hiJ, hx⟩

/-- Exercise 1.4.11 -/
theorem LebesgueMeasurable.boolean_algebra.isSigmaAlgebra (d:ℕ) : (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by
  intro E hE
  exact LebesgueMeasurable.countable_union hE

def LebesgueMeasurable.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

private theorem IsNull.iUnion {d:ℕ} {E : ℕ → Set (EuclideanSpace' d)} (hE : ∀ n, IsNull (E n)) :
    IsNull (⋃ n, E n) := by
  have hle := Lebesgue_outer_measure.union_le E
  have hsum : (∑' i, Lebesgue_outer_measure (E i)) = 0 := by
    simp only [hE, tsum_zero]
  rw [hsum] at hle
  exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)

theorem IsNull.boolean_algebra.isSigmaAlgebra (d:ℕ) : (IsNull.boolean_algebra d).isSigmaAlgebra :=
  by
  intro E hE
  show IsNull (⋃ n, E n) ∨ IsNull (⋃ n, E n)ᶜ
  by_cases h : ∃ k, IsNull (E k)ᶜ
  · obtain ⟨k, hk⟩ := h
    right
    apply IsNull.subset hk
    rw [Set.compl_iUnion]
    exact Set.iInter_subset (fun n => (E n)ᶜ) k
  · push_neg at h
    left
    apply IsNull.iUnion
    intro n
    rcases hE n with h' | h'
    · exact h'
    · exact absurd h' (h n)

def IsNull.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (IsNull.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem JordanMeasurable.boolean_algebra.not_isSigmaAlgebra (d:ℕ) : ¬ (JordanMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by sorry

/-- Exercise 1.4.12 -/
theorem ConcreteSigmaAlgebra.restrict_is_sigma {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X): (B.restrict A).isSigmaAlgebra := by
  intro E hE
  choose E' hE'meas hE'eq using hE
  refine ⟨⋃ n, E' n, ?_, ?_⟩
  · have : (Subtype.val '' ⋃ n, E n) = ⋃ n, Subtype.val '' E n := by
      rw [Set.image_iUnion]
    rw [this]
    exact B.countable_union_mem (fun n => Subtype.val '' E n) hE'meas
  · rw [Set.image_iUnion, Set.iUnion_inter]
    apply Set.iUnion_congr
    intro n
    exact hE'eq n

def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra

instance ConcreteSigmaAlgebra.instLE (X:Type*) : LE (ConcreteSigmaAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteSigmaAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteSigmaAlgebra X) :=
  {
    le_refl := fun B E h => h
    le_trans := fun B1 B2 B3 h12 h23 E hE => h23 E (h12 E hE)
    le_antisymm := by
      intro B1 B2 h12 h21
      suffices h : B1.toConcreteBooleanAlgebra = B2.toConcreteBooleanAlgebra by
        cases B1; cases B2
        cases h
        rfl
      apply le_antisymm <;> intro E hE
      · exact h12 E hE
      · exact h21 E hE
  }

instance ConcreteSigmaAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteSigmaAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
      countable_union_mem := fun _ _ => trivial
    }
    le_top := fun B E _ => trivial
  }

instance ConcreteSigmaAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteSigmaAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
      countable_union_mem := fun E hE => by
        by_cases h : ∃ n, E n = Set.univ
        · right
          obtain ⟨n, hn⟩ := h
          apply Set.eq_univ_of_univ_subset
          rw [← hn]
          exact Set.subset_iUnion E n
        · left
          push_neg at h
          rw [Set.iUnion_eq_empty]
          intro n
          rcases hE n with h' | h'
          · exact h'
          · exact absurd h' (h n)
    }
    bot_le := fun B E hE => by
      rcases hE with h | h
      · rw [h]; exact B.empty_mem
      · rw [h, ← Set.compl_empty]; exact B.compl_mem _ B.empty_mem
  }

/-- Exercise 1.4.13 (Intersection of sigma-algebras) -/
instance ConcreteSigmaAlgebra.instInfSet {X:Type*} : InfSet (ConcreteSigmaAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := fun B _ => B.empty_mem
          compl_mem := fun E hE B hB => B.compl_mem E (hE B hB)
          union_mem := fun E F hE hF B hB => B.union_mem E F (hE B hB) (hF B hB)
          countable_union_mem := fun E hE B hB => B.countable_union_mem E (fun n => hE n B hB)
        }
  }

def ConcreteSigmaAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteSigmaAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

/-- Definition 1.4.10 (Generation of algebras) -/
instance ConcreteSigmaAlgebra.instSupSet {X:Type*} : SupSet (ConcreteSigmaAlgebra X) :=
  {
      sSup S := ConcreteSigmaAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

instance ConcreteSigmaAlgebra.instCompleteLattice {X:Type*} : CompleteLattice (ConcreteSigmaAlgebra X) :=
  {
    toLattice := sorry
    toSupSet := ConcreteSigmaAlgebra.instSupSet
    toInfSet := ConcreteSigmaAlgebra.instInfSet
    toBoundedOrder := sorry
    isLUB_sSup := sorry
    isGLB_sInf := sorry
  }

theorem ConcreteSigmaAlgebra.generated_by_le {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by
  intro E hE
  intro B' hB'
  exact hE B'.toConcreteBooleanAlgebra hB'

example : ∃ (X:Type*) (F: Set (Set X)), ConcreteBooleanAlgebra.generated_by F ≠ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by sorry

/-- Remark 1.4.15 -/
theorem ConcreteSigmaAlgebra.induction {X:Type*} {F: Set (Set X)} {P: Set X → Prop}
  (h1: P ∅) (h2: ∀ E ∈ F, P E) (h3: ∀ E, P E → P Eᶜ)
  (h4: ∀ (E : ℕ → Set X), (∀ n, P (E n)) → P (⋃ n, E n)) : ∀ E, (ConcreteSigmaAlgebra.generated_by F).measurable E → P E :=
  by
  have hunion : ∀ E F : Set X, P E → P F → P (E ∪ F) := by
    intro E G hE hG
    have : (⋃ n, (fun n => if n = 0 then E else G) n) = E ∪ G := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨n, hn⟩
        by_cases h : n = 0
        · simp [h] at hn; exact Or.inl hn
        · simp [h] at hn; exact Or.inr hn
      · rintro (h | h)
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩
    rw [← this]
    exact h4 _ (fun n => by by_cases h : n = 0 <;> simp [h, hE, hG])
  let BP : ConcreteSigmaAlgebra X := {
    measurable := P
    empty_mem := h1
    compl_mem := h3
    union_mem := hunion
    countable_union_mem := h4
  }
  intro E hE
  exact hE BP (fun G hG => h2 G hG)

private theorem ConcreteSigmaAlgebra.countable_iUnion_mem {X:Type*} (B: ConcreteSigmaAlgebra X)
    {ι : Type*} [Countable ι] (E : ι → Set X) (hE : ∀ i, B.measurable (E i)) :
    B.measurable (⋃ i, E i) := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [Set.iUnion_of_empty]
    exact B.empty_mem
  · obtain ⟨f, hf⟩ := exists_surjective_nat ι
    have : (⋃ i, E i) = ⋃ n : ℕ, E (f n) := by
      apply le_antisymm
      · apply Set.iUnion_subset
        intro i
        obtain ⟨n, rfl⟩ := hf i
        exact Set.subset_iUnion (fun n => E (f n)) n
      · apply Set.iUnion_subset
        intro n
        exact Set.subset_iUnion E (f n)
    rw [this]
    exact B.countable_union_mem (fun n => E (f n)) (fun n => hE (f n))

private theorem ConcreteSigmaAlgebra.subset_generated_by {X:Type*} (F: Set (Set X)) :
    ∀ E ∈ F, (ConcreteSigmaAlgebra.generated_by F).measurable E := by
  intro E hE B hB
  exact hB E hE

private theorem ConcreteSigmaAlgebra.generated_by_le_of {X:Type*} {F: Set (Set X)} {B: ConcreteSigmaAlgebra X}
    (h: ∀ E ∈ F, B.measurable E) : ∀ E, (ConcreteSigmaAlgebra.generated_by F).measurable E → B.measurable E := by
  intro E hE
  exact hE B h

/-- If each generating family lies in the σ-algebra generated by the other, the σ-algebras agree. -/
private theorem ConcreteSigmaAlgebra.generated_by_eq_of {X:Type*} {F G: Set (Set X)}
    (hFG: ∀ E ∈ F, (ConcreteSigmaAlgebra.generated_by G).measurable E)
    (hGF: ∀ E ∈ G, (ConcreteSigmaAlgebra.generated_by F).measurable E) :
    ConcreteSigmaAlgebra.generated_by F = ConcreteSigmaAlgebra.generated_by G := by
  apply le_antisymm
  · exact ConcreteSigmaAlgebra.generated_by_le_of hFG
  · exact ConcreteSigmaAlgebra.generated_by_le_of hGF

/-- Definition 1.4.16 (Borel σ-algebra) -/
def BorelSigmaAlgebra (X:Type*) [TopologicalSpace X] : ConcreteSigmaAlgebra X :=
  ConcreteSigmaAlgebra.generated_by { U : Set X | IsOpen U }

/-- Exercise 1.4.14 (i) -/
theorem BorelSigmaAlgebra.generated_by_open (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } := rfl

/-- Exercise 1.4.14 (ii) -/
theorem BorelSigmaAlgebra.generated_by_closed (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { F : Set (EuclideanSpace' d) | IsClosed F } := by
  apply ConcreteSigmaAlgebra.generated_by_eq_of
  · intro U hU
    rw [Set.mem_setOf_eq] at hU
    have : (ConcreteSigmaAlgebra.generated_by { F : Set (EuclideanSpace' d) | IsClosed F }).measurable Uᶜ := by
      apply ConcreteSigmaAlgebra.subset_generated_by
      rw [Set.mem_setOf_eq]
      exact hU.isClosed_compl
    have h2 := (ConcreteSigmaAlgebra.generated_by { F : Set (EuclideanSpace' d) | IsClosed F }).compl_mem _ this
    rwa [compl_compl] at h2
  · intro C hC
    rw [Set.mem_setOf_eq] at hC
    have : (ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U }).measurable Cᶜ := by
      apply ConcreteSigmaAlgebra.subset_generated_by
      rw [Set.mem_setOf_eq]
      exact hC.isOpen_compl
    have h2 := (ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U }).compl_mem _ this
    rwa [compl_compl] at h2

/-- Exercise 1.4.14 (iii) -/
theorem BorelSigmaAlgebra.generated_by_compact (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K } := by
  rw [BorelSigmaAlgebra.generated_by_closed]
  apply ConcreteSigmaAlgebra.generated_by_eq_of
  · -- closed C lies in σ-algebra generated by compacts
    intro C hC
    rw [Set.mem_setOf_eq] at hC
    have hcov : C = ⋃ n : ℕ, (C ∩ Metric.closedBall (0 : EuclideanSpace' d) n) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        exact ⟨n, hx, hn⟩
      · rintro ⟨n, hx, _⟩
        exact hx
    rw [hcov]
    apply (ConcreteSigmaAlgebra.generated_by { K : Set (EuclideanSpace' d) | IsCompact K }).countable_union_mem
    intro n
    apply ConcreteSigmaAlgebra.subset_generated_by
    rw [Set.mem_setOf_eq]
    exact (isCompact_closedBall (0 : EuclideanSpace' d) n).inter_left hC
  · -- compact K is closed, hence in σ-algebra generated by closed sets
    intro K hK
    rw [Set.mem_setOf_eq] at hK
    apply ConcreteSigmaAlgebra.subset_generated_by
    rw [Set.mem_setOf_eq]
    exact hK.isClosed

/-- Exercise 1.4.15 (iv) -/
theorem BorelSigmaAlgebra.generated_by_open_balls (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { B : Set (EuclideanSpace' d) | ∃ x₀ r, B = Metric.ball x₀ r } := by
  apply ConcreteSigmaAlgebra.generated_by_eq_of
  · -- open U lies in σ-algebra generated by balls
    intro U hU
    rw [Set.mem_setOf_eq] at hU
    set I := { p : EuclideanSpace' d × ℝ | Metric.ball p.1 p.2 ⊆ U } with hI
    have hcov : U = ⋃ p : I, Metric.ball (p:EuclideanSpace' d × ℝ).1 (p:EuclideanSpace' d × ℝ).2 := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · intro hx
        rw [Metric.isOpen_iff] at hU
        obtain ⟨r, hr, hsub⟩ := hU x hx
        exact ⟨⟨(x, r), hsub⟩, Metric.mem_ball_self hr⟩
      · rintro ⟨p, hp⟩
        exact p.2 hp
    obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun p : I => Metric.ball (p:EuclideanSpace' d × ℝ).1 (p:EuclideanSpace' d × ℝ).2)
      (fun p => Metric.isOpen_ball)
    rw [hcov, ← hTeq, Set.biUnion_eq_iUnion]
    have hTcount : Countable T := hTc.to_subtype
    apply ConcreteSigmaAlgebra.countable_iUnion_mem
    rintro ⟨p, hp⟩
    apply ConcreteSigmaAlgebra.subset_generated_by
    exact ⟨(p:EuclideanSpace' d × ℝ).1, (p:EuclideanSpace' d × ℝ).2, rfl⟩
  · -- each ball is open
    intro B hB
    obtain ⟨x₀, r, rfl⟩ := hB
    apply ConcreteSigmaAlgebra.subset_generated_by
    rw [Set.mem_setOf_eq]
    exact Metric.isOpen_ball

/-- Exercise 1.4.14 (v) -/
theorem BorelSigmaAlgebra.generated_by_boxes (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by (Box.toSet '' Set.univ) := by sorry

/-- Exercise 1.4.14 (vi) -/
theorem BorelSigmaAlgebra.generated_by_elementary (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { E : Set (EuclideanSpace' d) | IsElementary E }  := by sorry

open Ordinal in
/-- Exercise 1.4.15 (Recursive definition of generated sigma-algebra)-/
def ConcreteSigmaAlgebra.generated_by_eq {X:Type*} (F: Set (Set X)) :
  (ConcreteSigmaAlgebra.generated_by F).measurableSets =
  ⋃ α < ω₁,
  Ordinal.limitRecOn (motive := fun _ ↦ Set (Set X)) α F (fun n G ↦ { E: Set X | (∃ S: Set G, Countable S ∧ E = ⋃ (H:S), H) ∨ (∃ S: Set G, Countable S ∧ E = (⋃ (H:S), H))ᶜ }) (fun α _ G ↦ ⋃ (β : Ordinal) (h : β < α), G β h) := by sorry

open Cardinal in
/-- Exercise 1.4.16 -/
theorem ConcreteSigmaAlgebra.card_of_generated_by {X:Type*} {F: Set (Set X)} [Infinite F] :
  Cardinal.mk (ConcreteSigmaAlgebra.generated_by F).measurableSets ≤ (Cardinal.mk F) ^ ℵ₀ :=
  by sorry

open Cardinal in
theorem BorelSigmaAlgebra.card (d:ℕ) : Cardinal.mk (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ≤ 2 ^ ℵ₀ :=
  by sorry

theorem JordanMeasurable.not_borel {d:ℕ} (hd: d ≥ 1) : ∃ E: Set (EuclideanSpace' d), JordanMeasurable E ∧ ¬ (BorelSigmaAlgebra (EuclideanSpace' d)).measurable E :=
  by sorry

/-- Exercise 1.4.17 -/
theorem BorelSigmaAlgebra.prod {d₁ d₂:ℕ} {E : Set (EuclideanSpace' d₁)} {F : Set (EuclideanSpace' d₂)}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable E)
  (hF: (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable F) :
  (BorelSigmaAlgebra (EuclideanSpace' (d₁ + d₂))).measurable ((EuclideanSpace'.prod_equiv d₁ d₂).symm '' (E ×ˢ F))
  :=
  by sorry

/-- Exercise 1.4.18(i) -/
theorem BorelSigmaAlgebra.slice_fst {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₂ : EuclideanSpace' d₂ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₁)).measurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by sorry

/-- Exercise 1.4.18(i) -/
theorem BorelSigmaAlgebra.slice_snd {d₁ d₂:ℕ} {E : Set (EuclideanSpace' (d₁+d₂))}
  (hE: (BorelSigmaAlgebra (EuclideanSpace' (d₁+d₂))).measurable E)
  (x₁ : EuclideanSpace' d₁ ) :
  (BorelSigmaAlgebra (EuclideanSpace' d₂)).measurable { x₂ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E }
  :=
  by sorry

/-- Exercise 1.4.18(ii) -/
example (d₁ d₂ :ℕ) (E : Set (EuclideanSpace' (d₁+d₂)))
  (hE: LebesgueMeasurable E)
  (x₂ : EuclideanSpace' d₂ ) :
  ¬ LebesgueMeasurable { x₁ | (EuclideanSpace'.prod_equiv d₁ d₂).symm ⟨ x₁, x₂ ⟩ ∈ E } := by sorry

/-- Exercise 1.4.19 -/
theorem LebesgueMeasurable.sigmaAlgebra_generated_by {d:ℕ} :
  LebesgueMeasurable.sigmaAlgebra d = ConcreteSigmaAlgebra.generated_by ( (BorelSigmaAlgebra (EuclideanSpace' d)).measurableSets ∪ (IsNull.sigmaAlgebra d).measurableSets) :=
  by sorry

def ConcreteSigmaAlgebra.measurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X := {
  MeasurableSet' := B.measurable
  measurableSet_empty := B.empty_mem
  measurableSet_compl := B.compl_mem
  measurableSet_iUnion := B.countable_union_mem
}

def MeasurableSpace.sigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X := {
  measurable := M.MeasurableSet'
  empty_mem := M.measurableSet_empty
  compl_mem := M.measurableSet_compl
  union_mem := fun E F hE hF => @MeasurableSet.union X M E F hE hF
  countable_union_mem := M.measurableSet_iUnion
}

theorem BorelSigmaAlgebra.le_LebesgueSigmaAlgebra (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) ≤ LebesgueMeasurable.sigmaAlgebra d := by
  intro E hE
  exact hE (LebesgueMeasurable.sigmaAlgebra d) (fun U hU => IsOpen.measurable hU)
