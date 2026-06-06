import Analysis.MeasureTheory.Section_1_3_2

/-!
# Introduction to Measure Theory, Section 1.3.3: Unsigned Lebesgue integrals

A companion to (the introduction to) Section 1.3.3 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.3.12 (Lower unsigned Lebesgue integral) -/
noncomputable def LowerUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ}

/-- Definition 1.3.12 (Upper unsigned Lebesgue integral) -/
noncomputable def UpperUnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal) : EReal :=
  sInf { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, ∀ x, g x ≥ f x ∧ R = hg.integ}

theorem LowerUnsignedLebesgueIntegral.eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf : ∀ x, 0 ≤ f x) : LowerUnsignedLebesgueIntegral f =
  sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, (AlmostAlways (fun x ↦ g x ≤ f x)) ∧ R = hg.integ} := by
  -- Both sides are suprema over sets of integrals of simple functions g bounded by f.
  -- LHS: pointwise everywhere g ≤ f; RHS: almost everywhere g ≤ f.
  -- Equality follows since the simple integral is invariant under modification on null sets.
  unfold LowerUnsignedLebesgueIntegral
  -- First, simplify the weird definition: ∀ x, g x ≤ f x ∧ R = hg.integ is equivalent to
  -- (∀ x, g x ≤ f x) ∧ R = hg.integ (since R = hg.integ is constant in x)
  congr 1
  ext R
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨g, hg, hcond⟩
    -- Extract the pointwise bound and the equality
    have hle : ∀ x, g x ≤ f x := fun x ↦ (hcond x).1
    have hReq : R = hg.integ := by
      -- hcond gives us R = hg.integ for any x, so pick any x
      -- EuclideanSpace' d is always nonempty
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond (Classical.arbitrary _)).2
    exact ⟨g, hg, AlmostAlways.ofAlways hle, hReq⟩
  · intro ⟨g, hg, hae, hReq⟩
    -- Need to find g' with g' ≤ f everywhere and same integral
    -- Let N = {x | g x > f x} be the null set where g exceeds f
    let N := {x | ¬(g x ≤ f x)}
    have hN_null : IsNull N := hae
    have hN_meas : LebesgueMeasurable N := IsNull.measurable hN_null
    -- Define g' = g * indicator(Nᶜ) = g where g ≤ f, 0 elsewhere
    let g' := fun x => g x * (EReal.indicator Nᶜ x)
    -- g' is a simple function (product of simple function with indicator of measurable set)
    have hg'_simple : UnsignedSimpleFunction g' := by
      -- This follows from the definition of simple functions as linear combinations of indicators
      -- g = ∑ c_i • indicator(E_i), so g' = ∑ c_i • indicator(E_i ∩ Nᶜ)
      obtain ⟨k, c, E, ⟨hcE, hg_eq⟩⟩ := hg
      use k, c, fun i => E i ∩ Nᶜ
      constructor
      · intro i
        constructor
        · exact LebesgueMeasurable.inter (hcE i).1 (LebesgueMeasurable.complement hN_meas)
        · exact (hcE i).2
      · -- Prove g' = ∑ c_i • indicator(E_i ∩ Nᶜ) pointwise
        funext x
        simp only [g', hg_eq, EReal.indicator, Real.EReal_fun]
        -- Use Finset.sum_fn to convert (∑ i, f i) x to ∑ i, f i x
        conv_lhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        conv_rhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        by_cases hx : x ∈ Nᶜ
        · -- x ∈ Nᶜ: multiply by 1, and E_i ∩ Nᶜ membership reduces to E_i membership
          rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Real.EReal_fun]
          by_cases hEi : x ∈ E i
          · rw [Set.indicator'_of_mem hEi, Set.indicator'_of_mem (Set.mem_inter hEi hx)]
          · have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hEi (Set.mem_of_mem_inter_left h)
            rw [Set.indicator'_of_notMem hEi, Set.indicator'_of_notMem hnotinter]
        · -- x ∉ Nᶜ: multiply by 0, and E_i ∩ Nᶜ is empty at x
          rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
          symm
          apply Finset.sum_eq_zero
          intro i _
          have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hx (Set.mem_of_mem_inter_right h)
          simp only [Real.EReal_fun, Set.indicator'_of_notMem hnotinter, EReal.coe_zero, smul_zero]
    -- g' ≤ f everywhere
    have hg'_le_f : ∀ x, g' x ≤ f x := by
      intro x
      by_cases hx : x ∈ N
      · -- On N: g' x = g x * 0 = 0 ≤ f x (using hf)
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hnotmem : x ∉ Nᶜ := by simp only [Set.mem_compl_iff, not_not]; exact hx
        rw [Set.indicator'_of_notMem hnotmem, EReal.coe_zero, mul_zero]
        exact hf x
      · -- On Nᶜ: g' x = g x * 1 = g x ≤ f x (by definition of N)
        simp only [N, Set.mem_setOf_eq] at hx
        push_neg at hx
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq, hx, not_true_eq_false, not_false_eq_true]
        rw [Set.indicator'_of_mem hmem, EReal.coe_one, mul_one]
        exact hx
    -- g' = g almost everywhere (they differ only on N which is null)
    have hg'_ae : AlmostEverywhereEqual g' g := by
      unfold AlmostEverywhereEqual AlmostAlways IsNull
      -- {x | g' x ≠ g x} ⊆ N, and N is null
      have hsub : {x | g' x ≠ g x} ⊆ N := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        by_contra hxN
        -- If x ∉ N, then g' x = g x * 1 = g x
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq]; exact hxN
        simp only [g', EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hmem,
                   EReal.coe_one, mul_one] at hx
        exact hx rfl
      have hle : Lebesgue_outer_measure {x | g' x ≠ g x} ≤ 0 :=
        calc Lebesgue_outer_measure {x | g' x ≠ g x}
            ≤ Lebesgue_outer_measure N := Lebesgue_outer_measure.mono hsub
          _ = 0 := hN_null
      exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
    -- By Exercise 1.3.1(iv), same integral
    have hinteg_eq : hg'_simple.integ = hg.integ :=
      UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hg'_simple hg hg'_ae
    -- Now construct the witness
    use g', hg'_simple
    intro x
    constructor
    · exact hg'_le_f x
    · rw [hReq, ← hinteg_eq]

/-- Exercise 1.3.10(i) (Compatibility with the simple integral) -/
theorem LowerUnsignedLebesgueIntegral.eq_simpleIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
    LowerUnsignedLebesgueIntegral f = hf.integ := by
  unfold LowerUnsignedLebesgueIntegral
  apply le_antisymm
  · apply sSup_le
    rintro R ⟨g, hg, hcond⟩
    haveI : Nonempty (EuclideanSpace' d) := inferInstance
    have hReq : R = hg.integ := (hcond (Classical.arbitrary _)).2
    rw [hReq]
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hf
      (AlmostAlways.ofAlways (fun x ↦ (hcond x).1))
  · apply le_sSup
    exact ⟨f, hf, fun x ↦ ⟨le_refl _, rfl⟩⟩

/-- Exercise 1.3.10(ii) (Monotonicity) -/
theorem LowerUnsignedLebesgueIntegral.mono {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: AlmostAlways (fun x ↦ f x ≤ g x)) :
    LowerUnsignedLebesgueIntegral f ≤ LowerUnsignedLebesgueIntegral g := by
  rw [LowerUnsignedLebesgueIntegral.eq hf.1, LowerUnsignedLebesgueIntegral.eq hg.1]
  apply sSup_le
  rintro R ⟨h, hh, hae, hReq⟩
  apply le_sSup
  refine ⟨h, hh, ?_, hReq⟩
  have hboth : AlmostAlways (fun x ↦ ∀ i : Fin 2, (if i = 0 then h x ≤ f x else f x ≤ g x)) :=
    AlmostAlways.countable (fun i => by fin_cases i <;> simpa using (by assumption : AlmostAlways _))
  exact hboth.mp (fun x hx => le_trans (by simpa using hx 0) (by simpa using hx 1))

/-- The zero function is an unsigned simple function. -/
private lemma UnsignedSimpleFunction.zero {d:ℕ} : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0:EReal)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_⟩
  funext x; simp

/-- The simple integral of an unsigned simple function is nonnegative. -/
private lemma UnsignedSimpleFunction.integ_nonneg {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf: UnsignedSimpleFunction f) : 0 ≤ hf.integ := by
  unfold UnsignedSimpleFunction.integ
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hf.choose_spec.choose_spec.choose_spec.1 i).2
    (Lebesgue_outer_measure.nonneg _)

/-- The simple integral of the zero function is `0`. -/
private lemma UnsignedSimpleFunction.zero_integ {d:ℕ} :
    (UnsignedSimpleFunction.zero (d := d)).integ = 0 := by
  rw [(UnsignedSimpleFunction.zero (d := d)).integral_eq (k := 0) (c := Fin.elim0)
    (E := fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (by funext y; simp)]
  simp

/-- The lower integral of an unsigned function is nonnegative. -/
private lemma LowerUnsignedLebesgueIntegral.nonneg {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf: Unsigned f) : 0 ≤ LowerUnsignedLebesgueIntegral f := by
  apply le_sSup
  refine ⟨(fun _ => (0:EReal)), UnsignedSimpleFunction.zero, fun x => ⟨hf x, ?_⟩⟩
  exact (UnsignedSimpleFunction.zero_integ (d := d)).symm

/-- The lower integral of the zero function is `0`. -/
private lemma LowerUnsignedLebesgueIntegral.zero {d:ℕ} :
    LowerUnsignedLebesgueIntegral (fun _ : EuclideanSpace' d => (0:EReal)) = 0 := by
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (UnsignedSimpleFunction.zero (d := d))]
  exact UnsignedSimpleFunction.zero_integ

/-- For a positive EReal scalar, multiplication commutes with `sSup`. -/
private lemma EReal.mul_sSup_of_pos {b : EReal} (hb : 0 < b) (hbt : b ≠ ⊤) (S : Set EReal) :
    b * sSup S = sSup ((fun x => b * x) '' S) := by
  apply le_antisymm
  · -- b * sSup S ≤ sSup (b·S): show sSup S ≤ sSup(b·S)/b, then rearrange.
    rw [mul_comm, ← EReal.le_div_iff_mul_le hb hbt]
    apply sSup_le
    intro s hs
    rw [EReal.le_div_iff_mul_le hb hbt, mul_comm]
    exact le_sSup ⟨s, hs, rfl⟩
  · -- sSup (b·S) ≤ b * sSup S: each b·s ≤ b·sSup S by monotonicity.
    apply sSup_le
    rintro _ ⟨s, hs, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_sSup hs) hb.le

/-- Exercise 1.3.10(iii) (Homogeneity) -/
theorem LowerUnsignedLebesgueIntegral.hom {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {c: ℝ} (hc: 0 ≤ c) :
    LowerUnsignedLebesgueIntegral ((c:EReal) • f) = c * LowerUnsignedLebesgueIntegral f := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- c = 0: both sides are 0.
    subst hc0
    have hfun : ((0:ℝ):EReal) • f = (fun _ => (0:EReal)) := by
      funext x; simp
    rw [hfun]
    rw [show ((0:ℝ):EReal) = (0:EReal) from rfl, zero_mul]
    -- lower of the zero function is 0.
    rw [show (fun _ : EuclideanSpace' d => (0:EReal)) = (fun _ => (0:EReal)) from rfl]
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral (UnsignedSimpleFunction.zero (d := d))]
    -- integral of the zero function is 0, via the empty representation.
    rw [(UnsignedSimpleFunction.zero (d := d)).integral_eq (k := 0) (c := Fin.elim0)
      (E := fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (by funext x; simp)]
    simp
  · -- c > 0: scaling bijection on the defining set.
    have hcE : (0:EReal) < (c:EReal) := by exact_mod_cast hcpos
    have hcEt : (c:EReal) ≠ ⊤ := by simp
    unfold LowerUnsignedLebesgueIntegral
    rw [EReal.mul_sSup_of_pos hcE hcEt]
    congr 1
    ext R
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, hcond⟩
      -- g ≤ c•f simple. Let h = c⁻¹ • g ≤ f. Then integ g = c * integ h.
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      have hRg : R = hg.integ := (hcond (Classical.arbitrary _)).2
      have hcinv_nonneg : ((c⁻¹ : ℝ) : EReal) ≥ 0 := by
        exact_mod_cast le_of_lt (inv_pos.mpr hcpos)
      refine ⟨hg.integ / (c:EReal), ⟨((c⁻¹:ℝ):EReal) • g, hg.smul hcinv_nonneg, ?_⟩, ?_⟩
      · intro x
        refine ⟨?_, ?_⟩
        · -- c⁻¹ • g x ≤ f x  from  g x ≤ c * f x
          have hgle : g x ≤ (c:EReal) * f x := by
            have := (hcond x).1; simpa using this
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [EReal.coe_inv c, ← EReal.div_eq_inv_mul, EReal.div_le_iff_le_mul hcE hcEt]
          exact hgle
        · -- integ(c⁻¹•g) = c⁻¹ * integ g  = integ g / c
          rw [UnsignedSimpleFunction.integral_smul hg hcinv_nonneg]
          rw [EReal.coe_inv c, ← EReal.div_eq_inv_mul]
      · -- R = c * (integ g / c)
        rw [hRg]
        exact EReal.mul_div_cancel (by simp) (by simp) (ne_of_gt hcE)
    · rintro ⟨S, ⟨g, hg, hcond⟩, hRS⟩
      -- g ≤ f simple. Then c•g ≤ c•f simple, integ(c•g) = c*integ g.
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      have hcnonneg : ((c:ℝ):EReal) ≥ 0 := hcE.le
      have hSg : S = hg.integ := (hcond (Classical.arbitrary _)).2
      refine ⟨(c:EReal) • g, hg.smul hcnonneg, ?_⟩
      intro x
      refine ⟨?_, ?_⟩
      · -- c • g x ≤ (c•f) x
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using (hcond x).1) hcE.le
      · -- R = c * integ g = integ (c • g)
        rw [hSg] at hRS
        rw [UnsignedSimpleFunction.integral_smul hg hcnonneg]
        exact hRS.symm

/-- Exercise 1.3.10(iv) (Equivalence) -/
theorem LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (heq: AlmostEverywhereEqual f g) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · exact LowerUnsignedLebesgueIntegral.mono hf hg (heq.mp (fun x hx => le_of_eq hx))
  · exact LowerUnsignedLebesgueIntegral.mono hg hf (heq.mp (fun x hx => le_of_eq hx.symm))


/-- Exercise 1.3.10(v) (Superadditivity) -/
theorem LowerUnsignedLebesgueIntegral.superadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) :
    LowerUnsignedLebesgueIntegral (f + g) ≥ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  -- It suffices to show `lower(f) + lower(g) ≤ lower(f+g)`.
  -- Key tool: `EReal.add_le_of_forall_lt`, which avoids EReal-addition discontinuity:
  -- to bound `lower(f) + lower(g)`, bound `a' + b'` for every `a' < lower(f)`, `b' < lower(g)`.
  rw [ge_iff_le]
  set Sf := { R | ∃ g' : EuclideanSpace' d → EReal, ∃ hg' : UnsignedSimpleFunction g',
      ∀ x, g' x ≤ f x ∧ R = hg'.integ } with hSf
  set Sg := { R | ∃ g' : EuclideanSpace' d → EReal, ∃ hg' : UnsignedSimpleFunction g',
      ∀ x, g' x ≤ g x ∧ R = hg'.integ } with hSg
  have hLf : LowerUnsignedLebesgueIntegral f = sSup Sf := rfl
  have hLg : LowerUnsignedLebesgueIntegral g = sSup Sg := rfl
  rw [hLf, hLg]
  apply EReal.add_le_of_forall_lt
  intro a' ha' b' hb'
  -- `a' < lower(f)` gives a simple `s ≤ f` with `a' < s.integ`; similarly for `g`.
  obtain ⟨a, ⟨gs, hgs, hcond_s⟩, ha'a⟩ := exists_lt_of_lt_csSup
    (s := Sf) ⟨_, _, UnsignedSimpleFunction.zero, fun x => ⟨hf.1 x, rfl⟩⟩ ha'
  obtain ⟨b, ⟨gt, hgt, hcond_t⟩, hb'b⟩ := exists_lt_of_lt_csSup
    (s := Sg) ⟨_, _, UnsignedSimpleFunction.zero, fun x => ⟨hg.1 x, rfl⟩⟩ hb'
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  have hgs_le : ∀ x, gs x ≤ f x := fun x => (hcond_s x).1
  have hgt_le : ∀ x, gt x ≤ g x := fun x => (hcond_t x).1
  have haR : a = hgs.integ := (hcond_s (Classical.arbitrary _)).2
  have hbR : b = hgt.integ := (hcond_t (Classical.arbitrary _)).2
  -- `gs + gt` is simple, ≤ f + g, with integral a + b.
  have hsum_le : ∀ x, (gs + gt) x ≤ (f + g) x := by
    intro x; simp only [Pi.add_apply]; exact add_le_add (hgs_le x) (hgt_le x)
  have hsum_integ : (hgs.add hgt).integ = a + b := by
    rw [UnsignedSimpleFunction.integral_add, haR, hbR]
  -- `a + b` is in the set defining `lower(f+g)`, hence ≤ lower(f+g).
  have hmem : (hgs.add hgt).integ ∈ { R | ∃ g' : EuclideanSpace' d → EReal,
      ∃ hg' : UnsignedSimpleFunction g', ∀ x, g' x ≤ (f + g) x ∧ R = hg'.integ } :=
    ⟨gs + gt, hgs.add hgt, fun x => ⟨hsum_le x, rfl⟩⟩
  calc a' + b' ≤ a + b := add_le_add ha'a.le hb'b.le
    _ = (hgs.add hgt).integ := hsum_integ.symm
    _ ≤ LowerUnsignedLebesgueIntegral (f + g) := le_sSup hmem

/-- The constant `⊤` function is an unsigned simple function dominating any function. -/
private lemma UnsignedSimpleFunction.top {d:ℕ} : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (⊤:EReal)) := by
  have huniv : LebesgueMeasurable (Set.univ : Set (EuclideanSpace' d)) := by
    have := (LebesgueMeasurable.empty (d := d)).complement
    rwa [Set.compl_empty] at this
  refine ⟨1, fun _ => ⊤, fun _ => Set.univ, fun _ => ⟨huniv, le_top⟩, ?_⟩
  funext x
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem (Set.mem_univ x)]
  simp

/-- The defining set of the upper integral is bounded below by `0`, hence the integral is `≥ 0`. -/
private lemma UpperUnsignedLebesgueIntegral.nonneg {d:ℕ} {f: EuclideanSpace' d → EReal} :
    0 ≤ UpperUnsignedLebesgueIntegral f := by
  unfold UpperUnsignedLebesgueIntegral
  apply le_csInf
  · exact ⟨_, _, UnsignedSimpleFunction.top, fun x => ⟨le_top, rfl⟩⟩
  · rintro R ⟨h, hh, hcond⟩
    haveI : Nonempty (EuclideanSpace' d) := inferInstance
    rw [(hcond (Classical.arbitrary _)).2]
    exact UnsignedSimpleFunction.integ_nonneg hh

/-- Exercise 1.3.10(vi) (Subadditivity of upper integral)-/
theorem UpperUnsignedLebesgueIntegral.subadditive {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) :
    UpperUnsignedLebesgueIntegral (f + g) ≤ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g := by
  set Sf := { R | ∃ g' : EuclideanSpace' d → EReal, ∃ hg' : UnsignedSimpleFunction g',
      ∀ x, g' x ≥ f x ∧ R = hg'.integ } with hSf
  set Sg := { R | ∃ g' : EuclideanSpace' d → EReal, ∃ hg' : UnsignedSimpleFunction g',
      ∀ x, g' x ≥ g x ∧ R = hg'.integ } with hSg
  have hUf : UpperUnsignedLebesgueIntegral f = sInf Sf := rfl
  have hUg : UpperUnsignedLebesgueIntegral g = sInf Sg := rfl
  rw [hUf, hUg]
  -- Side conditions for `le_add_of_forall_gt`: both upper integrals are `≥ 0`, hence `≠ ⊥`.
  have hbot_f : sInf Sf ≠ ⊥ := by
    have := @UpperUnsignedLebesgueIntegral.nonneg d f; rw [hUf] at this
    exact fun h => by rw [h] at this; exact (not_le.mpr (by decide : (⊥:EReal) < 0)) this
  have hbot_g : sInf Sg ≠ ⊥ := by
    have := @UpperUnsignedLebesgueIntegral.nonneg d g; rw [hUg] at this
    exact fun h => by rw [h] at this; exact (not_le.mpr (by decide : (⊥:EReal) < 0)) this
  apply EReal.le_add_of_forall_gt (Or.inl hbot_f) (Or.inr hbot_g)
  intro a' ha' b' hb'
  -- `a' > upper(f)` gives a simple `s ≥ f` with `s.integ < a'`; similarly for `g`.
  obtain ⟨a, ⟨gs, hgs, hcond_s⟩, hsa'⟩ := exists_lt_of_csInf_lt
    (s := Sf) ⟨_, _, UnsignedSimpleFunction.top, fun x => ⟨le_top, rfl⟩⟩ ha'
  obtain ⟨b, ⟨gt, hgt, hcond_t⟩, htb'⟩ := exists_lt_of_csInf_lt
    (s := Sg) ⟨_, _, UnsignedSimpleFunction.top, fun x => ⟨le_top, rfl⟩⟩ hb'
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  have hgs_ge : ∀ x, gs x ≥ f x := fun x => (hcond_s x).1
  have hgt_ge : ∀ x, gt x ≥ g x := fun x => (hcond_t x).1
  have haR : a = hgs.integ := (hcond_s (Classical.arbitrary _)).2
  have hbR : b = hgt.integ := (hcond_t (Classical.arbitrary _)).2
  have hsum_ge : ∀ x, (gs + gt) x ≥ (f + g) x := by
    intro x; simp only [Pi.add_apply]; exact add_le_add (hgs_ge x) (hgt_ge x)
  have hsum_integ : (hgs.add hgt).integ = a + b := by
    rw [UnsignedSimpleFunction.integral_add, haR, hbR]
  have hmem : (hgs.add hgt).integ ∈ { R | ∃ g' : EuclideanSpace' d → EReal,
      ∃ hg' : UnsignedSimpleFunction g', ∀ x, g' x ≥ (f + g) x ∧ R = hg'.integ } :=
    ⟨gs + gt, hgs.add hgt, fun x => ⟨hsum_ge x, rfl⟩⟩
  calc UpperUnsignedLebesgueIntegral (f + g) ≤ (hgs.add hgt).integ := csInf_le ⟨0, by
        rintro R ⟨h, hh, hc⟩; rw [(hc (Classical.arbitrary _)).2]
        exact UnsignedSimpleFunction.integ_nonneg hh⟩ hmem
    _ = a + b := hsum_integ
    _ ≤ a' + b' := add_le_add hsa'.le htb'.le

/-- Exercise 1.3.10(vii) (Divisibility) -/
theorem LowerUnsignedLebesgueIntegral.eq_add {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {E: Set (EuclideanSpace' d)} (hE: MeasurableSet E) :
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ E.indicator') +
      LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ Eᶜ.indicator') := by sorry

/-- Exercise 1.3.10(viii) (Vertical truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(ix) (Horizontal truncation)-/
theorem LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n:ℕ ↦ LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_horiz_trunc : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 1.3.10(x) (Reflection) -/
theorem LowerUnsignedLebesgueIntegral.sum_of_reflect_eq {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedSimpleFunction (f+g)) (hbound: EReal.BoundedFunction (f + g)) (hsupport: FiniteMeasureSupport (f + g)) :
    hfg.integ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Definition 1.3.13 (Unsigned Lebesgue integral).  For Lean purposes it is convenient to assign a "junk" value to this integral when f is not unsigned measurable. -/
noncomputable def UnsignedLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → EReal): EReal := LowerUnsignedLebesgueIntegral f

noncomputable def UnsignedMeasurable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedMeasurable f) : EReal := UnsignedLebesgueIntegral f

/-- The lower integral never exceeds the upper integral: any simple minorant is `≤` any
    simple majorant (a.e.), and these dominate the lower/upper integrals respectively. -/
private lemma LowerUnsignedLebesgueIntegral.le_upper {d:ℕ} (f: EuclideanSpace' d → EReal) :
    LowerUnsignedLebesgueIntegral f ≤ UpperUnsignedLebesgueIntegral f := by
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  unfold LowerUnsignedLebesgueIntegral UpperUnsignedLebesgueIntegral
  apply sSup_le
  rintro R ⟨g, hg, hcond⟩
  apply le_csInf
  · exact ⟨_, _, UnsignedSimpleFunction.top, fun x => ⟨le_top, rfl⟩⟩
  · rintro S ⟨h, hh, hcond'⟩
    have hRg : R = hg.integ := (hcond (Classical.arbitrary _)).2
    have hSh : S = hh.integ := (hcond' (Classical.arbitrary _)).2
    rw [hRg, hSh]
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hh
      (AlmostAlways.ofAlways (fun x => le_trans (hcond x).1 (hcond' x).1))

/-- Extract a real, nonnegative pointwise bound from `EReal.BoundedFunction` for an unsigned function. -/
private lemma EReal.BoundedFunction.exists_real_bound {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hbound: EReal.BoundedFunction f) : ∃ M:ℝ, 0 ≤ M ∧ ∀ x, f x ≤ (M:EReal) := by
  obtain ⟨M, hM⟩ := hbound
  refine ⟨(M:ℝ), M.2, fun x => ?_⟩
  have h := hM x
  rcases lt_or_ge (f x) ⊤ with hfin | htop
  · by_cases hbot' : f x = ⊥
    · exfalso; rw [hbot', EReal.abs_bot] at h; simp at h
    · have hr := EReal.coe_toReal (ne_of_lt hfin) hbot'
      rw [← hr] at h ⊢
      rw [EReal.abs_def] at h
      rw [EReal.coe_le_coe_iff]
      have hle : |(f x).toReal| ≤ (M:ℝ) := by exact_mod_cast h
      calc (f x).toReal ≤ |(f x).toReal| := le_abs_self _
        _ ≤ (M:ℝ) := hle
  · exfalso
    have : f x = ⊤ := le_antisymm le_top htop
    rw [this, EReal.abs_top] at h
    simp at h

open scoped Classical in
/-- A constant times `card` of a filtered `Fin n` set, written through real coercion. -/
private lemma EReal.nsmul_coe (m:ℕ) (wr:ℝ) : m • ((wr:ℝ):EReal) = (((m:ℝ)*wr : ℝ):EReal) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih, ← EReal.coe_add]
    congr 1; push_cast; ring

open scoped Classical in
/-- The "band" minorant for slicing `[0,M]` into `n` equal pieces. For a fixed point `x` with
    value `v=f x ∈ [0,M]`, the value of the minorant simple function is `(c·M/n)` where `c` counts
    the crossed thresholds; it satisfies `minorant ≤ f ≤ minorant + M/n` pointwise. -/
private lemma LowerUnsignedLebesgueIntegral.band_sandwich {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f) (hsupp: FiniteMeasureSupport f)
    (M:ℝ) (hMpos : 0 < M) (hMle : ∀ x, f x ≤ (M:EReal))
    (hfin : ∀ x, f x ≠ ⊤) (n:ℕ) (hn : 0 < n) :
    UpperUnsignedLebesgueIntegral f ≤
      LowerUnsignedLebesgueIntegral f + (((M/n * (Lebesgue_measure (Support f)).toReal : ℝ)):EReal) := by
  set w : ℝ := M / n with hwdef
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have hwnn : (0:EReal) ≤ ((w:ℝ):EReal) := by exact_mod_cast hwpos.le
  set S : Set (EuclideanSpace' d) := Support f with hSdef
  have hμS_fin : Lebesgue_measure S < ⊤ := hsupp
  have hμS_ne : Lebesgue_measure S ≠ ⊤ := ne_of_lt hμS_fin
  -- Level-set measurability via TFAE (i) ↔ (vi): {f ≥ t} measurable for all t.
  have hge_iff : UnsignedMeasurable f ↔ ∀ t, LebesgueMeasurable {x | f x ≥ t} :=
    (UnsignedMeasurable.TFAE hf.1).out 0 5
  have hge : ∀ t:EReal, LebesgueMeasurable {x : EuclideanSpace' d | f x ≥ t} := hge_iff.mp hf
  -- Threshold sets E i = {f ≥ (i+1)w}, i ∈ Fin n.
  set E : Fin n → Set (EuclideanSpace' d) := fun i => {x | f x ≥ ((((i:ℝ)+1)*w : ℝ):EReal)} with hEdef
  have hEmeas : ∀ i, LebesgueMeasurable (E i) := fun i => hge _
  -- For i, E i ⊆ S (threshold (i+1)w > 0), so measure E i ≤ measure S, finite.
  have hEsubS : ∀ i, E i ⊆ S := by
    intro i x hx
    simp only [hEdef, Set.mem_setOf_eq] at hx
    simp only [hSdef, Support, Set.mem_setOf_eq]
    have hthr : (0:EReal) < ((((i:ℝ)+1)*w : ℝ):EReal) := by
      have : (0:ℝ) < ((i:ℝ)+1)*w := by positivity
      exact_mod_cast this
    exact ne_of_gt (lt_of_lt_of_le hthr hx)
  have hEmeas_le : ∀ i, Lebesgue_measure (E i) ≤ Lebesgue_measure S :=
    fun i => Lebesgue_outer_measure.mono (hEsubS i)
  have hE_fin : ∀ i, Lebesgue_measure (E i) ≠ ⊤ :=
    fun i => ne_of_lt (lt_of_le_of_lt (hEmeas_le i) hμS_fin)
  -- The minorant simple function φ = ∑ i, w • 1_{E i}.
  set φ : EuclideanSpace' d → EReal := ∑ i, ((w:ℝ):EReal) • (EReal.indicator (E i)) with hφdef
  have hφ_simple : UnsignedSimpleFunction φ :=
    ⟨n, fun _ => ((w:ℝ):EReal), E, fun i => ⟨hEmeas i, hwnn⟩, rfl⟩
  -- The majorant ψ = φ + w • 1_S.
  have hSmeas : LebesgueMeasurable S := by
    have hgt_iff : UnsignedMeasurable f ↔ ∀ t, LebesgueMeasurable {x | f x > t} :=
      (UnsignedMeasurable.TFAE hf.1).out 0 4
    have hgt : LebesgueMeasurable {x : EuclideanSpace' d | f x > (0:EReal)} :=
      hgt_iff.mp hf 0
    have heq : S = {x : EuclideanSpace' d | f x > (0:EReal)} := by
      ext x; simp only [hSdef, Support, Set.mem_setOf_eq]
      exact ⟨fun h => lt_of_le_of_ne (hf.1 x) (Ne.symm h), fun h => ne_of_gt h⟩
    rw [heq]; exact hgt
  have hS_simple : UnsignedSimpleFunction (Real.toEReal ∘ S.indicator') :=
    UnsignedSimpleFunction.indicator hSmeas
  -- Pointwise value of φ: φ x = (card · w) where card counts crossed thresholds at x.
  have hφ_val : ∀ x, φ x = (((Finset.univ.filter (fun i => x ∈ E i)).card * w : ℝ):EReal) := by
    intro x
    rw [hφdef, Finset.sum_apply]
    have hstep : (∑ i, (((w:ℝ):EReal) • EReal.indicator (E i)) x)
        = ∑ i ∈ Finset.univ.filter (fun i => x ∈ E i), ((w:ℝ):EReal) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ E i
      · rw [EReal.indicator_of_mem hx, if_pos hx, mul_one]
      · rw [EReal.indicator_of_notMem hx, if_neg hx, mul_zero]
    rw [hstep, Finset.sum_const, EReal.nsmul_coe]
  -- For each x, the count equals ⌊t/w⌋₊ where t = (f x).toReal.
  have hcard_eq : ∀ x, (Finset.univ.filter (fun i => x ∈ E i)).card = ⌊(f x).toReal / w⌋₊ := by
    intro x
    set t : ℝ := (f x).toReal with htdef
    have hvbot : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf.1 x))
    have hvr : ((t:ℝ):EReal) = f x := EReal.coe_toReal (hfin x) hvbot
    have ht0 : 0 ≤ t := by rw [htdef]; exact EReal.toReal_nonneg (hf.1 x)
    have htM : t ≤ M := by rw [← EReal.coe_le_coe_iff, hvr]; exact hMle x
    -- membership iff (i+1) ≤ t/w
    have hmem_iff : ∀ i : Fin n, (x ∈ E i) ↔ ((i:ℝ)+1 ≤ t / w) := by
      intro i
      simp only [hEdef, Set.mem_setOf_eq, ge_iff_le]
      rw [← hvr, EReal.coe_le_coe_iff, le_div_iff₀ hwpos, mul_comm]
    have hcond : ∀ i : Fin n, (x ∈ E i) ↔ (i:ℕ) < ⌊t/w⌋₊ := by
      intro i; rw [hmem_iff i, Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity)]
      push_cast; tauto
    have hfilter_eq : (Finset.univ.filter (fun i : Fin n => x ∈ E i))
        = (Finset.univ.filter (fun i : Fin n => (i:ℕ) < ⌊t/w⌋₊)) := by
      apply Finset.filter_congr; intro i _; rw [hcond i]
    rw [hfilter_eq]
    -- card of {i : Fin n | i < ⌊t/w⌋₊} = ⌊t/w⌋₊ since ⌊t/w⌋₊ ≤ n.
    have hsn : t / w ≤ (n:ℝ) := by
      rw [div_le_iff₀ hwpos]
      have hnw : (n:ℝ) * w = M := by rw [hwdef]; field_simp
      rw [hnw]; exact htM
    have hfloor_le : ⌊t/w⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hsn)
    rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i < ⌊t/w⌋₊ then 1 else 0) n,
        ← Finset.card_filter (fun i => i < ⌊t/w⌋₊) (Finset.range n)]
    have : ((Finset.range n).filter (fun i => i < ⌊t/w⌋₊)) = Finset.range ⌊t/w⌋₊ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  -- The pointwise EReal sandwich:  φ x ≤ f x  and  f x ≤ φ x + w.
  have hsand : ∀ x, φ x ≤ f x ∧ f x ≤ φ x + ((w:ℝ):EReal) := by
    intro x
    rw [hφ_val x, hcard_eq x]
    set t : ℝ := (f x).toReal with htdef
    set c : ℕ := ⌊t / w⌋₊ with hcdef
    have hvbot : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf.1 x))
    have hvr : ((t:ℝ):EReal) = f x := EReal.coe_toReal (hfin x) hvbot
    have ht0 : 0 ≤ t := by rw [htdef]; exact EReal.toReal_nonneg (hf.1 x)
    have hfl1 : (c:ℝ) * w ≤ t := by
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ t/w)
      rw [le_div_iff₀ hwpos] at this; rw [hcdef]; linarith [this]
    have hfl2 : t ≤ ((c:ℝ)+1) * w := by
      have := Nat.lt_floor_add_one (t / w)
      rw [div_lt_iff₀ hwpos] at this; rw [hcdef]; nlinarith [this]
    constructor
    · rw [← hvr, EReal.coe_le_coe_iff]; exact hfl1
    · rw [← hvr, ← EReal.coe_add, EReal.coe_le_coe_iff]; nlinarith [hfl2]
  have hφ_le_f : ∀ x, φ x ≤ f x := fun x => (hsand x).1
  -- The majorant ψ = φ + w • 1_S.
  set ψ : EuclideanSpace' d → EReal := φ + ((w:ℝ):EReal) • (Real.toEReal ∘ S.indicator') with hψdef
  have hψ_simple : UnsignedSimpleFunction ψ := hφ_simple.add (hS_simple.smul hwnn)
  -- f ≤ ψ everywhere.
  have hf_le_ψ : ∀ x, f x ≤ ψ x := by
    intro x
    rw [hψdef]
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    by_cases hx : x ∈ S
    · rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
      exact (hsand x).2
    · -- x ∉ S: f x = 0 and φ x = 0.
      rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero, add_zero]
      have hfx0 : f x = 0 := by
        by_contra h; exact hx (by simp only [hSdef, Support, Set.mem_setOf_eq]; exact h)
      rw [hfx0, hφ_val x]
      have : (0:ℝ) ≤ (Finset.univ.filter (fun i => x ∈ E i)).card * w := by positivity
      exact_mod_cast this
  -- Integrals.
  have hφ_integ_lower : hφ_simple.integ ≤ LowerUnsignedLebesgueIntegral f :=
    le_sSup ⟨φ, hφ_simple, fun x => ⟨hφ_le_f x, rfl⟩⟩
  have hψ_integ_upper : UpperUnsignedLebesgueIntegral f ≤ hψ_simple.integ := by
    apply csInf_le
    · exact ⟨0, by rintro R ⟨h, hh, hc⟩
                   haveI : Nonempty (EuclideanSpace' d) := inferInstance
                   rw [(hc (Classical.arbitrary _)).2]; exact UnsignedSimpleFunction.integ_nonneg hh⟩
    · exact ⟨ψ, hψ_simple, fun x => ⟨hf_le_ψ x, rfl⟩⟩
  -- integ ψ = integ φ + w · μS.
  have hψ_integ : hψ_simple.integ = hφ_simple.integ + ((w:ℝ):EReal) * Lebesgue_measure S := by
    have h1 : hψ_simple.integ = hφ_simple.integ + (hS_simple.smul hwnn).integ :=
      UnsignedSimpleFunction.integral_add hφ_simple (hS_simple.smul hwnn)
    rw [h1]
    congr 1
    rw [UnsignedSimpleFunction.integral_smul hS_simple hwnn,
        UnsignedSimpleFunction.integral_indicator hSmeas]
  -- Combine:  Upper ≤ integ ψ = integ φ + w·μS ≤ Lower + w·μS.
  have hμS_eq : ((w:ℝ):EReal) * Lebesgue_measure S = (((M/n * (Lebesgue_measure S).toReal : ℝ)):EReal) := by
    have hμSr : ((Lebesgue_measure S).toReal : EReal) = Lebesgue_measure S :=
      EReal.coe_toReal hμS_ne (by
        have := Lebesgue_outer_measure.nonneg S
        exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero this))
    rw [← hμSr, ← EReal.coe_mul]; norm_cast
  calc UpperUnsignedLebesgueIntegral f ≤ hψ_simple.integ := hψ_integ_upper
    _ = hφ_simple.integ + ((w:ℝ):EReal) * Lebesgue_measure S := hψ_integ
    _ ≤ LowerUnsignedLebesgueIntegral f + ((w:ℝ):EReal) * Lebesgue_measure S := by
        gcongr
    _ = LowerUnsignedLebesgueIntegral f + (((M/n * (Lebesgue_measure (Support f)).toReal : ℝ)):EReal) := by
        rw [hμS_eq, hSdef]

/-- Exercise 1.3.11 -/
theorem LowerUnsignedLebesgueIntegral.eq_upperIntegral {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f) (hsupp: FiniteMeasureSupport f) :
    LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f := by
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  obtain ⟨M, hM0, hMle⟩ := hbound.exists_real_bound
  have hfin : ∀ x, f x ≠ ⊤ := fun x => ne_of_lt (lt_of_le_of_lt (hMle x) (by simp))
  -- It always holds that Lower ≤ Upper.
  refine le_antisymm (LowerUnsignedLebesgueIntegral.le_upper f) ?_
  rcases eq_or_lt_of_le hM0 with hM0' | hMpos
  · -- M = 0 ⟹ f ≡ 0.
    have hf0 : f = (fun _ => (0:EReal)) := by
      funext x
      exact le_antisymm (by have := hMle x; rwa [← hM0', EReal.coe_zero] at this) (hf.1 x)
    rw [hf0]
    -- Upper(0) ≤ Lower(0): Lower(0)=0, Upper(0)≤0 via zero majorant.
    rw [LowerUnsignedLebesgueIntegral.zero]
    apply csInf_le
    · exact ⟨0, by rintro R ⟨h, hh, hc⟩
                   rw [(hc (Classical.arbitrary _)).2]; exact UnsignedSimpleFunction.integ_nonneg hh⟩
    · exact ⟨(fun _ => (0:EReal)), UnsignedSimpleFunction.zero,
        fun x => ⟨le_refl _, (UnsignedSimpleFunction.zero_integ (d := d)).symm⟩⟩
  · -- M > 0: take the band-slicing limit.
    set μSr : ℝ := (Lebesgue_measure (Support f)).toReal with hμSrdef
    have hμSr_nn : 0 ≤ μSr := by rw [hμSrdef]; exact EReal.toReal_nonneg (Lebesgue_outer_measure.nonneg _)
    -- Lower is finite (0 ≤ Lower ≤ Upper ≤ Lower + M·μSr from band with n=1, but just need ≠ ⊤,⊥).
    have hLow_nn : (0:EReal) ≤ LowerUnsignedLebesgueIntegral f :=
      LowerUnsignedLebesgueIntegral.nonneg hf.1
    have hLow_ne_bot : LowerUnsignedLebesgueIntegral f ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hLow_nn)
    have hband : ∀ n:ℕ, 0 < n → UpperUnsignedLebesgueIntegral f ≤
        LowerUnsignedLebesgueIntegral f + (((M/n * μSr : ℝ)):EReal) :=
      fun n hn => LowerUnsignedLebesgueIntegral.band_sandwich hf hbound hsupp M hMpos hMle hfin n hn
    -- The bounding sequence  r n = Lower + (M/n · μSr)  tends to Lower.
    have hseq : Filter.atTop.Tendsto (fun n:ℕ => (((M/n * μSr : ℝ)):EReal)) (nhds 0) := by
      have hr : Filter.atTop.Tendsto (fun n:ℕ => (M/n * μSr : ℝ)) (nhds 0) := by
        have hM' : Filter.atTop.Tendsto (fun n:ℕ => (M/n : ℝ)) (nhds 0) := by
          simpa using (tendsto_const_div_atTop_nhds_zero_nat M)
        simpa using hM'.mul_const μSr
      have h0 : ((0:ℝ):EReal) = 0 := by norm_num
      rw [← h0]
      exact (continuous_coe_real_ereal.tendsto 0).comp hr
    have hlim : Filter.atTop.Tendsto
        (fun n:ℕ => LowerUnsignedLebesgueIntegral f + (((M/n * μSr : ℝ)):EReal))
        (nhds (LowerUnsignedLebesgueIntegral f)) := by
      have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          (LowerUnsignedLebesgueIntegral f, 0) :=
        EReal.continuousAt_add (by right; simp) (by right; simp)
      have := hc.tendsto.comp (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hseq)
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hband n hn

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hsupp: FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hbound: EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Multiplying an unsigned measurable function by a ball indicator preserves measurability.
    This is a key helper for the horizontal truncation argument in Corollary 1.3.14. -/
lemma UnsignedMeasurable.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (n : ℕ) :
    UnsignedMeasurable (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- The indicator of a ball is measurable (balls are open, hence measurable)
  -- Multiplication of measurable functions is measurable
  -- The product of nonnegative functions is nonnegative
  set h := f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator' with hhdef
  -- First: h is unsigned (nonnegative).
  have hunsigned : Unsigned h := by
    intro x
    simp only [hhdef, Pi.mul_apply, Function.comp_apply]
    apply mul_nonneg (hf.1 x)
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
    · simp [Set.indicator'_of_mem hx]
    · simp [Set.indicator'_of_notMem hx]
  -- Pointwise value of h: f x on the ball, 0 off the ball.
  have hval_in : ∀ x, x ∈ Metric.ball (0 : EuclideanSpace' d) n → h x = f x := by
    intro x hx
    simp only [hhdef, Pi.mul_apply, Function.comp_apply]
    rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
  have hval_out : ∀ x, x ∉ Metric.ball (0 : EuclideanSpace' d) n → h x = 0 := by
    intro x hx
    simp only [hhdef, Pi.mul_apply, Function.comp_apply]
    rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
  -- Use the level-set characterization: it suffices that every super-level set {h > s} is measurable.
  rw [show UnsignedMeasurable h ↔ ∀ s, LebesgueMeasurable {x | h x > s} from
    (UnsignedMeasurable.TFAE hunsigned).out 0 4]
  have hball_meas : LebesgueMeasurable (Metric.ball (0 : EuclideanSpace' d) n) :=
    IsOpen.measurable Metric.isOpen_ball
  have hf_gt : ∀ s, LebesgueMeasurable {x | f x > s} :=
    ((UnsignedMeasurable.TFAE hf.1).out 0 4).mp hf
  intro s
  rcases lt_or_ge s 0 with hs | hs
  · -- s < 0: {h > s} = univ since h ≥ 0 > s.
    have : {x : EuclideanSpace' d | h x > s} = Set.univ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hs (hunsigned x)
    rw [this]
    have := (LebesgueMeasurable.empty (d := d)).complement
    rwa [Set.compl_empty] at this
  · -- s ≥ 0: {h > s} = {f > s} ∩ ball.
    have heq : {x : EuclideanSpace' d | h x > s} = {x | f x > s} ∩ Metric.ball 0 n := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · rw [hval_in x hx]; simp [hx]
      · rw [hval_out x hx]
        simp only [hx, and_false, iff_false, not_lt]
        exact hs
    rw [heq]
    exact LebesgueMeasurable.inter (hf_gt s) hball_meas

/-- Helper: horizontal truncation produces functions with finite measure support. -/
lemma FiniteMeasureSupport.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (n : ℕ) : FiniteMeasureSupport (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  unfold FiniteMeasureSupport
  have h_support_sub : Support (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator')
      ⊆ {x | ‖x‖ ≤ (n:ℝ)} := by
    intro x hx
    simp only [Support, Set.mem_setOf_eq, Pi.mul_apply, Function.comp_apply] at hx
    by_contra h
    simp only [Set.mem_setOf_eq, not_le] at h
    have hnotin : x ∉ Metric.ball (0 : EuclideanSpace' d) n := by
      simp only [Metric.mem_ball, dist_zero_right, not_lt]; exact le_of_lt h
    rw [Set.indicator'_of_notMem hnotin] at hx
    simp at hx
  have h_ball_eq : {x : EuclideanSpace' d | ‖x‖ ≤ (n:ℝ)} = Metric.closedBall 0 n := by
    ext x; simp [Metric.closedBall, dist_zero_right]
  have h_compact : IsCompact (Metric.closedBall (0 : EuclideanSpace' d) n) :=
    isCompact_closedBall 0 n
  have h_finite : Lebesgue_outer_measure (Metric.closedBall (0 : EuclideanSpace' d) n) ≠ ⊤ :=
    Lebesgue_outer_measure.finite_of_compact h_compact
  calc Lebesgue_measure (Support (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'))
      ≤ Lebesgue_measure {x | ‖x‖ ≤ (n:ℝ)} := Lebesgue_outer_measure.mono h_support_sub
    _ = Lebesgue_measure (Metric.closedBall 0 n) := by rw [h_ball_eq]
    _ < ⊤ := lt_top_iff_ne_top.mpr h_finite

/-- Additivity of lower integral for finite-support functions.
    This is the key step where we can apply {name}`eq_upperIntegral` and use the sandwich argument. -/
lemma LowerUnsignedLebesgueIntegral.add_of_finiteSupport {d : ℕ}
    {f g : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g))
    (hf_supp : FiniteMeasureSupport f) (hg_supp : FiniteMeasureSupport g) :
    LowerUnsignedLebesgueIntegral (f + g) =
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  -- For finite-support functions, use vertical truncation to reduce to bounded case,
  -- then apply eq_upperIntegral to show Lower = Upper, then sandwich:
  --   Lower(f+g) ≥ Lower(f) + Lower(g)  [superadditive]
  --   Lower(f+g) = Upper(f+g) ≤ Upper(f) + Upper(g) = Lower(f) + Lower(g)  [eq_upperIntegral + subadditive]
  apply le_antisymm
  · -- ≤ direction: use vertical truncation + eq_upperIntegral + subadditive
    -- For bounded finite-support: Lower = Upper by eq_upperIntegral
    -- Then Upper(f+g) ≤ Upper(f) + Upper(g) by subadditive
    -- Take vertical truncation limit to handle unbounded case
    sorry
  · -- ≥ direction: direct from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Corollary 1.3.14 (Finite additivity of Lebesgue integral )-/
theorem LowerUnsignedLebesgueIntegral.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g)
    (hfg: UnsignedMeasurable (f + g)) :
    LowerUnsignedLebesgueIntegral (f + g) = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · -- ≤: horizontal truncation → finite support → additivity → limit
    let f_h := fun n : ℕ ↦ f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let g_h := fun n : ℕ ↦ g * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let fg_h := fun n : ℕ ↦ (f + g) * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'

    have hfg_lim := eq_lim_horiz_trunc hfg

    -- (f+g) * ind = f * ind + g * ind by right_distrib for nonneg
    have heq : ∀ n, fg_h n = f_h n + g_h n := by
      intro n; funext x
      simp only [f_h, g_h, fg_h, Pi.add_apply, Pi.mul_apply]
      exact EReal.right_distrib_of_nonneg (hf.1 x) (hg.1 x)

    -- Additivity for finite-support truncations
    have heq_integ : ∀ n, LowerUnsignedLebesgueIntegral (fg_h n) =
        LowerUnsignedLebesgueIntegral (f_h n) + LowerUnsignedLebesgueIntegral (g_h n) := by
      intro n
      rw [heq n]
      apply LowerUnsignedLebesgueIntegral.add_of_finiteSupport
      · exact UnsignedMeasurable.mul_indicator_ball hf n
      · exact UnsignedMeasurable.mul_indicator_ball hg n
      · exact UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator_ball hf n)
            (UnsignedMeasurable.mul_indicator_ball hg n)
      · exact FiniteMeasureSupport.mul_indicator_ball n
      · exact FiniteMeasureSupport.mul_indicator_ball n

    conv at hfg_lim => arg 1; ext n; rw [heq_integ n]

    -- Use le_of_tendsto': Lower(f_h n) + Lower(g_h n) → Lower(f+g) and each term ≤ limit
    apply le_of_tendsto' hfg_lim
    intro n
    apply add_le_add
    · -- Lower(f_h n) ≤ Lower(f) by monotonicity (f_h n ≤ f pointwise)
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hf n) hf
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hf.1 x
    · -- Lower(g_h n) ≤ Lower(g) by monotonicity
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hg n) hg
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hg.1 x
  · -- ≥: from superadditivity
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Exercise 1.3.12 (Upper Lebesgue integral and outer measure)-/
theorem UpperUnsignedLebesgueIntegral.eq_outer_measure_integral {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: MeasurableSet E) :
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ E.indicator') = Lebesgue_outer_measure E := by sorry

theorem LowerUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (LowerUnsignedLebesgueIntegral (f + g) ≠ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g) := by
    sorry

theorem UpperUnsignedLebesgueIntegral.not_additive : ∃ (d:ℕ) (f g: EuclideanSpace' d → EReal) (hf: Unsigned f) (hg: Unsigned g), (UpperUnsignedLebesgueIntegral (f + g) ≠ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g) := by
    sorry

/-- Exercise 1.3.13 (Area interpretation of integral)-/
theorem LowerUnsignedLebesgueIntegral.eq_area {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
    LowerUnsignedLebesgueIntegral f = Lebesgue_measure { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-- Exercise 1.3.14 (Uniqueness) -/
theorem UnsignedLebesgueIntegral.unique {d:ℕ} (integ: (EuclideanSpace' d → EReal) → EReal)
  (hsimple : ∀ f (hf: UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd: ∀ f g (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz: ∀ f (hf: UnsignedMeasurable f), Filter.atTop.Tendsto (fun n:ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  : ∀ f, UnsignedMeasurable f → integ f = UnsignedLebesgueIntegral f := by sorry

/-- Exercise 1.3.15 (Translation invariance)-/
theorem UnsignedLebesgueIntegral.trans {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (a: EuclideanSpace' d) :
    UnsignedLebesgueIntegral (fun x ↦ f (x + a)) = hf.integ := by sorry

/-- Exercise 1.3.16 (Linear change of variables)-/
theorem UnsignedLebesgueIntegral.comp_linear {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d) (hA: A.det ≠ 0) :
    UnsignedLebesgueIntegral (fun x ↦ f (A x)) = |A.det|⁻¹ * hf.integ := by sorry

/-- Exercise 1.3.17 (Compatibility with the Riemann integral)-/
theorem RiemannIntegral.eq_UnsignedLebesgueIntegral {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    (riemannIntegral f I : EReal) = UnsignedLebesgueIntegral (Real.toEReal ∘ (fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

/-- Lemma 1.3.15 (Markov's inequality) -/
theorem UnsignedLebesgueIntegral.markov_inequality {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {t:ℝ} (ht: 0 < t) :
    Lebesgue_measure { x | f x ≥ t } ≤ hf.integ / (t:EReal) := by
  -- E = {x | f x ≥ t} is Lebesgue measurable (super-level set of a measurable function).
  set E := { x : EuclideanSpace' d | f x ≥ (t:EReal) } with hEdef
  have hge_iff : UnsignedMeasurable f ↔ ∀ t, LebesgueMeasurable {x | f x ≥ t} :=
    (UnsignedMeasurable.TFAE hf.1).out 0 5
  have hEmeas : LebesgueMeasurable E := hge_iff.mp hf t
  have htE : (0:EReal) < (t:EReal) := by exact_mod_cast ht
  have htEt : (t:EReal) ≠ ⊤ := by simp
  have htnn : (t:EReal) ≥ 0 := htE.le
  -- s = t • 1_E is a simple function with s ≤ f and s.integ = t * measure(E).
  have hind_simple : UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') :=
    UnsignedSimpleFunction.indicator hEmeas
  set s := (t:EReal) • (Real.toEReal ∘ E.indicator') with hsdef
  have hs_simple : UnsignedSimpleFunction s := hind_simple.smul htnn
  have hs_le : ∀ x, s x ≤ f x := by
    intro x
    simp only [hsdef, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    by_cases hx : x ∈ E
    · rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
      exact hx
    · rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
      exact hf.1 x
  have hs_integ : hs_simple.integ = (t:EReal) * Lebesgue_measure E := by
    rw [UnsignedSimpleFunction.integral_smul hind_simple htnn,
      UnsignedSimpleFunction.integral_indicator hEmeas]
  -- s.integ ≤ LowerUnsignedLebesgueIntegral f = hf.integ.
  have hle : hs_simple.integ ≤ LowerUnsignedLebesgueIntegral f :=
    le_sSup ⟨s, hs_simple, fun x => ⟨hs_le x, rfl⟩⟩
  -- Conclude: measure(E) * t ≤ lower(f), hence measure(E) ≤ lower(f)/t.
  show Lebesgue_measure E ≤ hf.integ / (t:EReal)
  have hfint : (hf.integ : EReal) = LowerUnsignedLebesgueIntegral f := rfl
  rw [hfint, EReal.le_div_iff_mul_le htE htEt, mul_comm]
  calc (t:EReal) * Lebesgue_measure E = hs_simple.integ := hs_integ.symm
    _ ≤ LowerUnsignedLebesgueIntegral f := hle

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.ae_finite {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hfin: UnsignedLebesgueIntegral f < ⊤) :
    AlmostAlways (fun x ↦ f x < ⊤) := by
  -- AlmostAlways (f x < ⊤) means {x | f x = ⊤} is null.
  -- {f = ⊤} ⊆ {f ≥ t} for every real t, and by Markov measure{f≥t} ≤ ∫f/t → 0.
  unfold AlmostAlways IsNull
  -- The bad set {x | ¬ f x < ⊤} = {x | f x = ⊤}.
  set B := {x : EuclideanSpace' d | ¬ f x < ⊤} with hBdef
  -- ∫f is a nonnegative finite real value v.
  have hint_nonneg : (0:EReal) ≤ UnsignedLebesgueIntegral f :=
    LowerUnsignedLebesgueIntegral.nonneg hf.1
  have hint_ne_top : UnsignedLebesgueIntegral f ≠ ⊤ := ne_of_lt hfin
  have hint_ne_bot : UnsignedLebesgueIntegral f ≠ ⊥ := by
    intro h; rw [h] at hint_nonneg
    exact absurd (lt_of_le_of_lt hint_nonneg EReal.bot_lt_zero) (lt_irrefl _)
  set v := (UnsignedLebesgueIntegral f).toReal with hvdef
  have hv_eq : (v:EReal) = UnsignedLebesgueIntegral f := EReal.coe_toReal hint_ne_top hint_ne_bot
  have hv_nonneg : 0 ≤ v := by rw [hvdef]; exact EReal.toReal_nonneg hint_nonneg
  -- {f = ⊤} ⊆ {f ≥ t} for all real t, giving measure(B) ≤ ∫f / t by Markov.
  have hmarkov : ∀ t : ℝ, 0 < t → Lebesgue_outer_measure B ≤ UnsignedLebesgueIntegral f / (t:EReal) := by
    intro t ht
    have hsub : B ⊆ {x | f x ≥ (t:EReal)} := by
      intro x hx
      simp only [hBdef, Set.mem_setOf_eq, not_lt] at hx
      -- hx : ⊤ ≤ f x, so f x ≥ ⊤ ≥ t.
      exact le_trans le_top hx
    calc Lebesgue_outer_measure B ≤ Lebesgue_outer_measure {x | f x ≥ (t:EReal)} :=
          Lebesgue_outer_measure.mono hsub
      _ = Lebesgue_measure {x | f x ≥ (t:EReal)} := rfl
      _ ≤ hf.integ / (t:EReal) := UnsignedLebesgueIntegral.markov_inequality hf ht
  -- Conclude measure(B) ≤ z for every real z > 0, hence measure(B) ≤ 0, hence = 0.
  have hle_all : ∀ z : ℝ, (0:EReal) < z → Lebesgue_outer_measure B ≤ (z:EReal) := by
    intro z hz
    have hzr : 0 < z := by exact_mod_cast hz
    rcases eq_or_lt_of_le hv_nonneg with hv0 | hvpos
    · -- v = 0: ∫f = 0, so measure(B) ≤ 0/t = 0 ≤ z.
      have := hmarkov 1 (by norm_num)
      rw [← hv_eq, ← hv0] at this
      simp only [EReal.coe_zero, EReal.zero_div] at this
      exact le_trans this hz.le
    · -- v > 0: pick t = v/z so that ∫f/t = z.
      have ht : (0:ℝ) < v / z := div_pos hvpos hzr
      have := hmarkov (v / z) ht
      rw [← hv_eq, ← EReal.coe_div] at this
      rw [show v / (v / z) = z by field_simp] at this
      exact this
  -- measure(B) ≤ 0 by le_of_forall_lt_iff_le; with nonneg gives = 0.
  have hle0 : Lebesgue_outer_measure B ≤ 0 := by
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    exact hle_all z hz
  exact le_antisymm hle0 (Lebesgue_outer_measure.nonneg B)

theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d:ℕ) (f: EuclideanSpace' d → EReal) (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by sorry

/-- Exercise 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.eq_zero_aeZero {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) :
     hf.integ = 0 ↔ AlmostAlways (fun x ↦ f x = 0) := by
  have hzero_meas : UnsignedMeasurable (fun _ : EuclideanSpace' d => (0:EReal)) :=
    UnsignedSimpleFunction.zero.unsignedMeasurable
  constructor
  · -- integ = 0 ⟹ ae f = 0.  {f ≠ 0} = {f > 0} = ⋃ₙ {f ≥ 1/(n+1)}, each null by Markov.
    intro hint0
    show AlmostAlways (fun x ↦ f x = 0)
    unfold AlmostAlways IsNull
    -- The bad set {x | f x ≠ 0}.
    have hsub : {x : EuclideanSpace' d | ¬ f x = 0}
        ⊆ ⋃ n : ℕ, {x | f x ≥ ((1/(n+1) : ℝ) : EReal)} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      -- f x > 0 since f x ≥ 0 and f x ≠ 0.
      have hpos : (0:EReal) < f x := lt_of_le_of_ne (hf.1 x) (Ne.symm hx)
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      -- Archimedean: ∃ n, 1/(n+1) ≤ f x.
      rcases lt_or_ge (f x) ⊤ with hfin | hinf
      · -- f x is a positive finite EReal: use its toReal.
        have hxbot : f x ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hpos)
        have hxr : ((f x).toReal : EReal) = f x := EReal.coe_toReal (ne_of_lt hfin) hxbot
        have hxrpos : 0 < (f x).toReal := by
          rw [← EReal.coe_lt_coe_iff, hxr, EReal.coe_zero]; exact hpos
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (f x).toReal)
        refine ⟨n, ?_⟩
        rw [ge_iff_le, ← hxr, EReal.coe_le_coe_iff, div_le_iff₀ (by positivity)]
        have hn' : 1 / (f x).toReal < (n:ℝ) + 1 := lt_trans hn (by linarith)
        rw [div_lt_iff₀ hxrpos] at hn'
        linarith [hn']
      · -- f x = ⊤ ≥ anything.
        exact ⟨0, le_trans le_top hinf⟩
    have hnull : ∀ n : ℕ, Lebesgue_outer_measure {x : EuclideanSpace' d | f x ≥ ((1/(n+1):ℝ):EReal)} = 0 := by
      intro n
      have htpos : (0:ℝ) < 1/(n+1) := by positivity
      have hmk := UnsignedLebesgueIntegral.markov_inequality hf htpos
      rw [hint0, EReal.zero_div] at hmk
      exact le_antisymm hmk (Lebesgue_outer_measure.nonneg _)
    -- Countable union of null sets is null.
    set Efam : ℕ → Set (EuclideanSpace' d) :=
      fun n => {x | f x ≥ ((1/(n+1):ℝ):EReal)} with hEfam
    have huninull : Lebesgue_outer_measure (⋃ n : ℕ, Efam n) = 0 := by
      apply le_antisymm _ (Lebesgue_outer_measure.nonneg _)
      have hbound := Lebesgue_outer_measure.union_le Efam
      have hsum : ∑' n, Lebesgue_outer_measure (Efam n) = 0 := by
        simp only [hEfam, hnull, tsum_zero]
      rwa [hsum] at hbound
    have hsub' : {x : EuclideanSpace' d | ¬ f x = 0} ⊆ ⋃ n : ℕ, Efam n := hsub
    exact le_antisymm (le_trans (Lebesgue_outer_measure.mono hsub') (le_of_eq huninull))
      (Lebesgue_outer_measure.nonneg _)
  · -- ae f = 0 ⟹ integ = 0.
    intro hae
    have heq : AlmostEverywhereEqual f (fun _ => 0) := hae
    have : LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (fun _ : EuclideanSpace' d => (0:EReal)) :=
      LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual hf hzero_meas heq
    show LowerUnsignedLebesgueIntegral f = 0
    rw [this, LowerUnsignedLebesgueIntegral.zero]
