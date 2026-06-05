import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_3
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.10: Consequences of the fundamental theorems

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval Chapter9 Chapter10

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
    set I := Icc a b
    set F' := derivWithin F I
    set G' := derivWithin G I
    have hF_cts : ContinuousOn F I := hF.continuousOn
    have hG_cts : ContinuousOn G I := hG.continuousOn
    have hbdd_of_cts : ∀ {H:ℝ→ℝ}, ContinuousOn H I → BddOn H I := by
      intro H hH
      have hcpt : IsCompact (I:Set ℝ) := by
        rw [BoundedInterval.set_Icc]; exact isCompact_Icc
      obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hH
      exact ⟨M, fun x hx => hM x hx⟩
    have hF_bdd : BddOn F I := hbdd_of_cts hF_cts
    have hG_bdd : BddOn G I := hbdd_of_cts hG_cts
    have hF_int : IntegrableOn F I := integ_of_bdd_cts hF_bdd hF_cts
    have hG_int : IntegrableOn G I := integ_of_bdd_cts hG_bdd hG_cts
    have hFG' : IntegrableOn (F * G') I := integ_of_mul hF_int hG'
    have hGF' : IntegrableOn (G * F') I := integ_of_mul hG_int hF'
    have hsum : IntegrableOn (F * G' + G * F') I := (hFG'.add hGF').1
    have hanti : AntiderivOn (F * G) (F * G' + G * F') I := by
      refine ⟨ hF.mul hG, ?_ ⟩
      intro x hx
      have hdF : HasDerivWithinAt F (F' x) I x := (hF x hx).hasDerivWithinAt
      have hdG : HasDerivWithinAt G (G' x) I x := (hG x hx).hasDerivWithinAt
      have := hdF.mul hdG
      simp only [Pi.add_apply, Pi.mul_apply]
      convert this using 1
      ring
    have hftc := integ_eq_antideriv_sub hab hsum hanti
    rw [(hFG'.add hGF').2] at hftc
    simp only [Pi.mul_apply] at hftc
    linarith

/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on {name}`α_length` -/
theorem PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ}
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hf_integ: IntegrableOn f (Icc a b) := (integ_of_piecewise_const hf).1
  observe hfα'_integ: IntegrableOn (f * α') (Icc a b)
  refine ⟨ hfα'_integ, ?_ ⟩
  choose P hP using hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, hfα'_integ.split P]
  apply Finset.sum_congr rfl; intro J hJ
  calc
    _ = Chapter11.integ ((constant_value_on f (J:Set ℝ)) • α') J := by
      apply Chapter11.integ_congr; intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      exact (hP J hJ).eq hx
    _ = constant_value_on f (J:Set ℝ) * Chapter11.integ α' J := ((hα'.mono' (P.contains _ hJ)).smul _).2
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) :=
        (subset_Icc J).trans (by simp [subset_iff, Set.Icc_subset_Ioo_iff hJab])
      obtain hJab | hJab := le_iff_eq_or_lt.mp (length_nonneg J)
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab; obtain hJab | hJab := hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts _ _ _ (hJsub _) hαcont.continuousOn] <;> grind
      simp [length] at hJab
      rw [α_length_of_cts ?_ ?_ ?_ (hJsub ?_) hαcont.continuousOn ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := closure_mono $ (subset_iff _ _).mp $ (Ioo_subset J).trans $ P.contains _ hJ
          simpa [closure_Ioo (show J.a ≠ J.b by linarith), subset_iff] using this
        calc
          _ = Chapter11.integ α' (Icc J.a J.b) := (hα'.mono' this).eq (subset_Icc J) rfl rfl
          _ = _ := by
            convert integ_eq_antideriv_sub (by order) (hα'.mono' this) _
            apply AntiderivOn.mono ⟨ hα_diff, _ ⟩ this
            intros; solve_by_elim [DifferentiableWithinAt.hasDerivWithinAt]
      all_goals linarith

private lemma lower_integral_mono {p q:ℝ → ℝ} {I:BoundedInterval} (hp: BddOn p I) (hq: BddOn q I)
    (h: MinorizesOn p q I) :
    lower_integral p I ≤ lower_integral q I := by
  apply csSup_le_csSup (integral_bound_above hq) (integral_bound_lower_nonempty hp)
  rintro v ⟨g, ⟨hg1, hg2⟩, rfl⟩
  exact ⟨g, ⟨fun x hx => le_trans (hg1 x hx) (h x hx), hg2⟩, rfl⟩

private lemma upper_integral_mono {p q:ℝ → ℝ} {I:BoundedInterval} (hp: BddOn p I) (hq: BddOn q I)
    (h: MajorizesOn p q I) :
    upper_integral q I ≤ upper_integral p I := by
  apply csInf_le_csInf (integral_bound_below hq) (integral_bound_upper_nonempty hp)
  rintro v ⟨g, ⟨hg1, hg2⟩, rfl⟩
  exact ⟨g, ⟨fun x hx => le_trans (h x hx) (hg1 x hx), hg2⟩, rfl⟩

/-- Corollary 11.10.3 -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} (hab: a < b) {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: RS_IntegrableOn f (Icc a b) α) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hfα'_bound: BddOn (f * α') (Icc a b) := by
    have ⟨ M, hM ⟩ := hf.1; have ⟨ N, hN ⟩ := hα'.1
    use M * N; intro x hx; specialize hM _ hx; specialize hN _ hx
    simp [abs_mul]; gcongr; linarith [abs_nonneg (f x)]
  have hα'_nonneg : MajorizesOn α' 0 (Icc a b) := by
    intro x hx
    convert ge_iff_le.mp (derivative_of_monotone _ _ hα (hα_diff x hx))
    rw [←mem_closure_iff_clusterPt]
    simp at hx
    obtain h | h := le_iff_lt_or_eq.mp hx.1
    . apply closure_mono (s := .Ico a x) _
      . simp [closure_Ico (show a ≠ x by linarith), hx.1]
      intro _ _; simp_all; grind
    apply closure_mono (s := .Ioc x b) _
    . simp [closure_Ioc (show x ≠ b by linarith), hx.2]
    intro _ _; simp_all
  have h0 := hf.2
  have h1 : RS_integ f (Icc a b) α ≤ lower_integral (f * α') (Icc a b) := by
    apply le_of_forall_sub_le; intro ε hε
    have ⟨ h, hhminor, hhconst, hh ⟩ :=
      gt_of_lt_lower_RS_integral hf.1 hα (show RS_integ f (Icc a b) α - ε < lower_RS_integral f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    have hbdd_hα' : BddOn (h * α') (Icc a b) := this.1.1
    rw [←this.2] at hh
    replace : lower_integral (h * α') (Icc a b) = integ (h * α') (Icc a b) := this.1.2
    have why : lower_integral (h * α') (Icc a b) ≤ lower_integral (f * α') (Icc a b) := by
      apply lower_integral_mono hbdd_hα' hfα'_bound
      intro x hx
      simp only [Pi.mul_apply]
      exact mul_le_mul_of_nonneg_right (hhminor x hx) (hα'_nonneg x hx)
    linarith
  have h2 : upper_integral (f * α') (Icc a b) ≤ RS_integ f (Icc a b) α := by
    apply le_of_forall_pos_le_add; intro ε hε
    have ⟨ h, hhmajor, hhconst, hh ⟩ :=
      lt_of_gt_upper_RS_integral hf.1 hα (show upper_RS_integral f (Icc a b) α + ε > RS_integ f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    have why : upper_integral (f * α') (Icc a b) ≤ upper_integral (h * α') (Icc a b) := by
      apply upper_integral_mono this.1.1 hfα'_bound
      intro x hx
      simp only [Pi.mul_apply]
      exact mul_le_mul_of_nonneg_right (hhmajor x hx) (hα'_nonneg x hx)
    linarith
  have h3 : lower_integral (f * α') (Icc a b) ≤
    upper_integral (f * α') (Icc a b) := lower_integral_le_upper hfα'_bound
  refine ⟨ ⟨ hfα'_bound, ?_ ⟩, ?_ ⟩ <;> linarith

private theorem cv_csInf_eq_a {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) : sInf (I:Set ℝ) = I.a := by
  cases I with
  | Icc a b => simp only [BoundedInterval.set_Icc] at h ⊢; exact csInf_Icc (Set.nonempty_Icc.mp h)
  | Ico a b => simp only [BoundedInterval.set_Ico] at h ⊢; exact csInf_Ico (Set.nonempty_Ico.mp h)
  | Ioc a b => simp only [BoundedInterval.set_Ioc] at h ⊢; exact csInf_Ioc (Set.nonempty_Ioc.mp h)
  | Ioo a b => simp only [BoundedInterval.set_Ioo] at h ⊢; exact csInf_Ioo (Set.nonempty_Ioo.mp h)

private theorem cv_csSup_eq_b {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) : sSup (I:Set ℝ) = I.b := by
  cases I with
  | Icc a b => simp only [BoundedInterval.set_Icc] at h ⊢; exact csSup_Icc (Set.nonempty_Icc.mp h)
  | Ico a b => simp only [BoundedInterval.set_Ico] at h ⊢; exact csSup_Ico (Set.nonempty_Ico.mp h)
  | Ioc a b => simp only [BoundedInterval.set_Ioc] at h ⊢; exact csSup_Ioc (Set.nonempty_Ioc.mp h)
  | Ioo a b => simp only [BoundedInterval.set_Ioo] at h ⊢; exact csSup_Ioo (Set.nonempty_Ioo.mp h)

/-- φ maps the inf of the preimage of `J` to the left endpoint of `J`. -/
private theorem cv_phi_inf {a b:ℝ} (hab: a < b) {φ:ℝ → ℝ}
    (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) {J : BoundedInterval}
    (hJne : (J:Set ℝ).Nonempty)
    (hJsub : (J:Set ℝ) ⊆ Set.Icc (φ a) (φ b)) :
    let S := {x : ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ)}
    φ (sInf S) = J.a ∧ φ (sSup S) = J.b ∧ sInf S ∈ Set.Icc a b ∧ sSup S ∈ Set.Icc a b
    ∧ S.Nonempty := by
  intro S
  -- S is nonempty
  have hSne : S.Nonempty := by
    obtain ⟨p, hp⟩ := hJne
    have hpsub : p ∈ Set.Icc (φ a) (φ b) := hJsub hp
    obtain ⟨x, hx, hxp⟩ := intermediate_value_Icc hab.le hφ_cont.continuousOn hpsub
    exact ⟨x, hx, by rw [hxp]; exact hp⟩
  have hSsub : S ⊆ Set.Icc a b := fun x hx => hx.1
  have hbddB : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hbddA : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  -- the closed interval Icc a b contains inf and sup of S
  have hinfmem : sInf S ∈ Set.Icc a b := by
    constructor
    · exact le_csInf hSne (fun x hx => hx.1.1)
    · obtain ⟨x, hx⟩ := hSne; exact le_trans (csInf_le hbddB hx) hx.1.2
  have hsupmem : sSup S ∈ Set.Icc a b := by
    constructor
    · obtain ⟨x, hx⟩ := hSne; exact le_trans hx.1.1 (le_csSup hbddA hx)
    · exact csSup_le hSne (fun x hx => hx.1.2)
  -- J ⊆ Icc J.a J.b and Ioo J.a J.b ⊆ J
  have hJab : (J:Set ℝ) ⊆ Set.Icc J.a J.b := by
    have := J.subset_Icc; rwa [BoundedInterval.subset_iff, BoundedInterval.set_Icc] at this
  have hJoo : Set.Ioo J.a J.b ⊆ (J:Set ℝ) := by
    have := J.Ioo_subset; rwa [BoundedInterval.subset_iff, BoundedInterval.set_Ioo] at this
  have hJle : J.a ≤ J.b := by
    obtain ⟨p, hp⟩ := hJne; have := hJab hp; rw [Set.mem_Icc] at this; linarith [this.1, this.2]
  refine ⟨?_, ?_, hinfmem, hsupmem, hSne⟩
  · -- φ (sInf S) = J.a
    apply le_antisymm
    · -- φ(inf) ≤ J.a : suppose not, find a J-value below φ(inf), contradiction
      by_contra hlt
      push_neg at hlt  -- J.a < φ (sInf S)
      -- pick y with J.a ≤ y < φ(sInf S) and y ∈ J
      -- y := max J.a (φ(sInf S) - something); use midpoint between J.a and φ inf if J.a < that
      set c := sInf S with hc
      -- there is a point of S, hence φ inf ≤ J.b (φ value at that point ≥ ... ) Actually use a J value
      -- Choose y := (J.a + min (φ c) J.b)/2? Simpler: y in [J.a, φc) ∩ J.
      -- Since J.a < φ c and J.a ≤ J.b, and J contains points arbitrarily close to J.a from above (Ioo J.a J.b ⊆ J) when J.a<J.b.
      rcases eq_or_lt_of_le hJle with hJeq | hJlt
      · -- J.a = J.b : J singleton {J.a}; then every φ x = J.a for x∈S, so φ c = J.a (limit) contradiction with hlt
        -- pick the witness point of S, its φ = J.a since J ⊆ {J.a}
        obtain ⟨x, hx⟩ := hSne
        have hxval : φ x = J.a := by
          have := hJab hx.2; rw [Set.mem_Icc, ← hJeq] at this; linarith [this.1, this.2]
        have hcx : c ≤ x := csInf_le hbddB hx
        have := hφ_mono hcx
        rw [hxval] at this; linarith
      · -- J.a < J.b
        set m := min (φ c) J.b with hm
        have hmc : m ≤ φ c := min_le_left _ _
        have hmb : m ≤ J.b := min_le_right _ _
        have hma : J.a < m := lt_min hlt hJlt
        set y := (J.a + m) / 2 with hy
        have hymem : y ∈ (J:Set ℝ) := by
          apply hJoo; rw [Set.mem_Ioo]; constructor <;> [skip; skip] <;> rw [hy] <;> linarith
        have hyImem : y ∈ Set.Icc (φ a) (φ b) := hJsub hymem
        obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab.le hφ_cont.continuousOn hyImem
        have hxS : x ∈ S := ⟨hx, by rw [hxy]; exact hymem⟩
        have hcx : c ≤ x := csInf_le hbddB hxS
        have hmono := hφ_mono hcx
        rw [hxy] at hmono
        have hylt : y < φ c := by rw [hy]; linarith
        linarith
    · -- J.a ≤ φ(inf): φ c is a limit of φ(x_n), x_n ∈ S → φ x_n ∈ J ⊆ ≥ J.a, and c = inf S
      -- For any x ∈ S, φ x ≥ J.a. φ c = lim from points of S decreasing to c. Use: c is adherent.
      -- Use sequential: there's x_n ∈ S with x_n → c. Then φ x_n → φ c, φ x_n ≥ J.a.
      set c := sInf S with hc
      have hcl : c ∈ closure S := by
        rw [hc]; exact csInf_mem_closure hSne hbddB
      have hmem : φ c ∈ closure (φ '' S) :=
        map_mem_closure hφ_cont hcl (fun x hx => Set.mem_image_of_mem φ hx)
      have hsub : φ '' S ⊆ Set.Ici J.a := by
        rintro z ⟨x, hx, rfl⟩
        have := hJab hx.2; rw [Set.mem_Icc] at this; exact this.1
      have : φ c ∈ Set.Ici J.a :=
        (closure_minimal hsub isClosed_Ici) hmem
      exact this
  · -- φ (sSup S) = J.b, symmetric
    apply le_antisymm
    · -- φ(sup) ≤ J.b
      set d := sSup S with hd
      have hcl : d ∈ closure S := by
        rw [hd]; exact csSup_mem_closure hSne hbddA
      have hmem : φ d ∈ closure (φ '' S) :=
        map_mem_closure hφ_cont hcl (fun x hx => Set.mem_image_of_mem φ hx)
      have hsub : φ '' S ⊆ Set.Iic J.b := by
        rintro z ⟨x, hx, rfl⟩
        have := hJab hx.2; rw [Set.mem_Icc] at this; exact this.2
      exact (closure_minimal hsub isClosed_Iic) hmem
    · -- J.b ≤ φ(sup)
      by_contra hlt
      push_neg at hlt  -- φ (sSup S) < J.b
      set d := sSup S with hd
      rcases eq_or_lt_of_le hJle with hJeq | hJlt
      · obtain ⟨x, hx⟩ := hSne
        have hxval : φ x = J.b := by
          have := hJab hx.2; rw [Set.mem_Icc, hJeq] at this; linarith [this.1, this.2]
        have hxd : x ≤ d := le_csSup hbddA hx
        have := hφ_mono hxd
        rw [hxval] at this; linarith
      · set m := max (φ d) J.a with hm
        have hmd : φ d ≤ m := le_max_left _ _
        have hma : J.a ≤ m := le_max_right _ _
        have hmb : m < J.b := max_lt hlt hJlt
        set y := (m + J.b) / 2 with hy
        have hymem : y ∈ (J:Set ℝ) := by
          apply hJoo; rw [Set.mem_Ioo]; constructor <;> [skip; skip] <;> rw [hy] <;> linarith
        have hyImem : y ∈ Set.Icc (φ a) (φ b) := hJsub hymem
        obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab.le hφ_cont.continuousOn hyImem
        have hxS : x ∈ S := ⟨hx, by rw [hxy]; exact hymem⟩
        have hxd : x ≤ d := le_csSup hbddA hxS
        have hmono := hφ_mono hxd
        rw [hxy] at hmono
        have hygt : φ d < y := by rw [hy]; linarith
        linarith

/-- For a globally continuous `φ`, the `φ`-length of an interval `K` with `K.a ≤ K.b`
    is `φ K.b - φ K.a`. -/
private theorem cv_alpha_length {φ:ℝ → ℝ} (hφ_cont: Continuous φ) {K:BoundedInterval}
    (hK: K.a ≤ K.b) : φ[K]ₗ = φ K.b - φ K.a := by
  have hll : ∀ z:ℝ, left_lim φ z = φ z := fun z =>
    left_lim_of_continuous ⟨1, one_pos, Set.subset_univ _⟩ hφ_cont.continuousWithinAt
  have hrl : ∀ z:ℝ, right_lim φ z = φ z := fun z =>
    right_lim_of_continuous ⟨1, one_pos, Set.subset_univ _⟩ hφ_cont.continuousWithinAt
  cases K with
  | Icc c d => simp only [α_length, BoundedInterval.a, BoundedInterval.b] at hK ⊢; rw [if_pos hK, hrl, hll]
  | Ico c d => simp only [α_length, BoundedInterval.a, BoundedInterval.b] at hK ⊢; rw [if_pos hK, hll, hll]
  | Ioc c d => simp only [α_length, BoundedInterval.a, BoundedInterval.b] at hK ⊢; rw [if_pos hK, hrl, hrl]
  | Ioo c d =>
    simp only [α_length, BoundedInterval.a, BoundedInterval.b] at hK ⊢
    rcases eq_or_lt_of_le hK with h | h
    · rw [if_neg (by linarith), h]; ring
    · rw [if_pos h, hll, hrl]

/-- Lemma 11.10.5 / Exercise 11.10.2-/
theorem PiecewiseConstantOn.RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f:ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: PiecewiseConstantOn f (Icc (φ a) (φ b))) :
  PiecewiseConstantOn (f ∘ φ) (Icc a b) ∧ RS_integ (f ∘ φ) (Icc a b) φ =
    integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  choose P' hf using hf
  set P := P'.remove_empty
  replace hf : PiecewiseConstantWith f P := by
    intro J hJ; simp [P, (· ∈ ·)] at hJ; exact hf J hJ.1
  rw [integ_def hf]
  unfold PiecewiseConstantWith.integ
  set φ_inv : P.intervals → Set ℝ := fun J ↦ { x:ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ) }
  have hφ_inv_bounded (J: P.intervals) : Bornology.IsBounded (φ_inv J) := by
    apply Bornology.IsBounded.subset (Icc_bounded a b); intro _; aesop
  have hφ_inv_connected (J: P.intervals) : (φ_inv J).OrdConnected := by
    have hJoc : (J:Set ℝ).OrdConnected :=
      ((BoundedInterval.ordConnected_iff _).mpr ⟨(J:BoundedInterval), rfl⟩).2
    rw [Set.ordConnected_def]
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ z hz
    refine ⟨⟨hx1.1.trans hz.1, hz.2.trans hy1.2⟩, ?_⟩
    exact hJoc.out hx2 hy2 ⟨hφ_mono hz.1, hφ_mono hz.2⟩
  set φ_inv' : P.intervals → BoundedInterval := fun J ↦ ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose
  have hφ_inv' (J:P.intervals) : φ_inv J = φ_inv' J :=
    ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose_spec
  have hφ_inv_nonempty (J:P.intervals) : (φ_inv J).Nonempty := by
    have hJne : (J:Set ℝ).Nonempty := by
      have := J.property; simp [P, (· ∈ ·)] at this; exact this.2
    obtain ⟨p, hp⟩ := hJne
    have hpsub : p ∈ Set.Icc (φ a) (φ b) := by
      have hc := P.contains _ J.property
      rw [BoundedInterval.subset_iff] at hc
      have hmem := hc hp
      rwa [BoundedInterval.set_Icc] at hmem
    obtain ⟨x, hx, hxp⟩ := intermediate_value_Icc hab.le hφ_cont.continuousOn hpsub
    exact ⟨x, hx, by rw [hxp]; exact hp⟩
  have hφ_inv_const {J:P.intervals} : ConstantOn (f ∘ φ) (φ_inv' J) ∧ constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
    have hfJ : ConstantOn f (J:Set ℝ) := hf J J.property
    have hval : ∀ x ∈ ((φ_inv' J : BoundedInterval) : Set ℝ), (f ∘ φ) x = constant_value_on f (J:Set ℝ) := by
      intro x hx
      rw [←hφ_inv' J] at hx
      simp only [φ_inv, Set.mem_setOf_eq] at hx
      exact hfJ.eq hx.2
    have hne : ((φ_inv' J : BoundedInterval) : Set ℝ).Nonempty := by
      rw [←hφ_inv' J]; exact hφ_inv_nonempty J
    exact ⟨ ConstantOn.of_const hval, ConstantOn.const_eq hne hval ⟩
  set Q : Partition (Icc a b) := {
    intervals := .image φ_inv' .univ
    exists_unique x := by
      intro hx
      rw [mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at hx
      have hφx : φ x ∈ Icc (φ a) (φ b) := by
        rw [mem_iff, BoundedInterval.set_Icc, Set.mem_Icc]; exact ⟨hφ_mono hx.1, hφ_mono hx.2⟩
      obtain ⟨J, ⟨hJmem, hJx⟩, hJuniq⟩ := P.exists_unique _ hφx
      refine ExistsUnique.intro (φ_inv' ⟨J, hJmem⟩) ?_ ?_
      · refine ⟨ ?_, ?_ ⟩
        · simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨⟨J, hJmem⟩, rfl⟩
        · rw [mem_iff, ←hφ_inv' ⟨J, hJmem⟩]
          simp only [φ_inv, Set.mem_setOf_eq]
          exact ⟨Set.mem_Icc.mpr hx, hJx⟩
      · intro K ⟨hKmem, hKx⟩
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hKmem
        obtain ⟨J', rfl⟩ := hKmem
        rw [mem_iff, ←hφ_inv' J'] at hKx
        simp only [φ_inv, Set.mem_setOf_eq] at hKx
        have : (J':BoundedInterval) = J := hJuniq _ ⟨J'.property, hKx.2⟩
        congr 1; exact Subtype.ext this
    contains K hK := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK
      obtain ⟨J, rfl⟩ := hK
      rw [subset_iff, ←hφ_inv' J]
      intro x hx
      simp only [φ_inv, Set.mem_setOf_eq] at hx
      rw [BoundedInterval.set_Icc]
      exact hx.1
  }
  have hfφ_piecewise : PiecewiseConstantWith (f ∘ φ) Q := by
    intro K hK
    have hK' : K ∈ Q.intervals := hK
    simp only [Q, Finset.mem_image, Finset.mem_univ, true_and] at hK'
    obtain ⟨J, rfl⟩ := hK'
    exact (hφ_inv_const (J := J)).1
  have hfφ_piecewise' : PiecewiseConstantOn (f ∘ φ) (Icc a b) := ⟨ Q, hfφ_piecewise ⟩
  refine ⟨ hfφ_piecewise' , ?_ ⟩
  rw [RS_integ_def hfφ_piecewise]
  unfold PiecewiseConstantWith.RS_integ
  rw [Finset.sum_image, ←Finset.sum_coe_sort (s := P.intervals)]
  . apply Finset.sum_congr rfl
    intro J _
    congr 1
    . exact hφ_inv_const.2
    -- goal: φ[φ_inv' J]ₗ = (↑J).length
    have hJne : ((J:BoundedInterval):Set ℝ).Nonempty := by
      have := J.property; simp [P, (· ∈ ·)] at this; exact this.2
    have hJsub : ((J:BoundedInterval):Set ℝ) ⊆ Set.Icc (φ a) (φ b) := by
      have hc := P.contains _ J.property
      rw [BoundedInterval.subset_iff, BoundedInterval.set_Icc] at hc
      exact hc
    -- S = φ_inv J as a set
    set S := {x : ℝ | x ∈ Set.Icc a b ∧ φ x ∈ ((J:BoundedInterval):Set ℝ)} with hSdef
    have hKS : ((φ_inv' J : BoundedInterval):Set ℝ) = S := by
      rw [← hφ_inv' J]
    have hSne : S.Nonempty := by
      have := cv_phi_inf hab hφ_cont hφ_mono hJne hJsub; exact this.2.2.2.2
    have hKne : ((φ_inv' J : BoundedInterval):Set ℝ).Nonempty := by rw [hKS]; exact hSne
    have hKa : (φ_inv' J : BoundedInterval).a = sInf S := by
      rw [← cv_csInf_eq_a hKne, hKS]
    have hKb : (φ_inv' J : BoundedInterval).b = sSup S := by
      rw [← cv_csSup_eq_b hKne, hKS]
    obtain ⟨hφinf, hφsup, _, _, _⟩ := cv_phi_inf hab hφ_cont hφ_mono hJne hJsub
    have hab' : (φ_inv' J : BoundedInterval).a ≤ (φ_inv' J : BoundedInterval).b := by
      rw [hKa, hKb]
      obtain ⟨x, hx⟩ := hSne
      exact le_trans (csInf_le ⟨a, fun y hy => hy.1.1⟩ hx) (le_csSup ⟨b, fun y hy => hy.1.2⟩ hx)
    have hJab : (J:BoundedInterval).a ≤ (J:BoundedInterval).b := by
      obtain ⟨p, hp⟩ := hJne
      have := (J:BoundedInterval).subset_Icc
      rw [BoundedInterval.subset_iff, BoundedInterval.set_Icc] at this
      have := this hp; rw [Set.mem_Icc] at this; linarith [this.1, this.2]
    rw [cv_alpha_length hφ_cont hab', hKa, hKb, hφinf, hφsup,
      BoundedInterval.length, max_eq_left (by linarith)]
  intro J _ K _ hJK
  set x := (hφ_inv_nonempty J).some
  have h1 : x ∈ φ_inv J := (hφ_inv_nonempty J).some_mem
  have h2 : x ∈ φ_inv K := by rwa [hφ_inv' J, hJK, ←hφ_inv' K] at h1
  simp [φ_inv] at h1 h2
  have h3 : φ x ∈ Icc (φ a) (φ b) := by
    have := P.contains _ J.property
    simp only [subset_iff, mem_iff] at this ⊢
    exact this h1.2
  ext; apply (P.exists_unique _ h3).unique <;> simp [J.property, K.property, mem_iff, h1, h2]

/-- Proposition 11.10.6 (Change of variables formula II)-/
theorem RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  RS_IntegrableOn (f ∘ φ) (Icc a b) φ ∧
  RS_integ (f ∘ φ) (Icc a b) φ = integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  have hf_bdd := hf.1
  have hfφ_bdd : BddOn (f ∘ φ) (Icc a b) := by
    obtain ⟨M, hM⟩ := hf_bdd
    refine ⟨M, ?_⟩
    intro x hx
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    apply hM
    rw [BoundedInterval.set_Icc, Set.mem_Icc]
    exact ⟨hφ_mono hx.1, hφ_mono hx.2⟩
  have heq : lower_integral f (Icc (φ a) (φ b)) = upper_integral f (Icc (φ a) (φ b)) := hf.2
  have hupper : upper_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_integral f (Icc (φ a) (φ b)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose f_up hf_upmajor hf_upconst hf_up using lt_of_gt_upper_integral hf.1 (show upper_integral f (Icc (φ a) (φ b)) + ε > integ f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_upconst
    rw [←hpc.2] at hf_up
    have : MajorizesOn (f_up ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_upmajor; aesop
    linarith [upper_RS_integral_le_integ hfφ_bdd this hpc.1 hφ_mono]
  have hlower : lower_integral f (Icc (φ a) (φ b)) ≤ lower_RS_integral (f ∘ φ) (Icc a b) φ := by
    apply le_of_forall_sub_le
    intro ε hε
    choose f_low hf_lowminor hf_lowconst hf_low using gt_of_lt_lower_integral hf.1 (show lower_integral f (Icc (φ a) (φ b)) - ε < lower_integral f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_lowconst
    rw [←hpc.2] at hf_low
    have : MinorizesOn (f_low ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_lowminor; aesop
    linarith [integ_le_lower_RS_integral hfφ_bdd this hpc.1 hφ_mono]
  have hle : lower_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_RS_integral (f ∘ φ) (Icc a b) φ :=
    lower_RS_integral_le_upper hfφ_bdd hφ_mono
  refine ⟨ ⟨ hfφ_bdd, ?_ ⟩, ?_ ⟩ <;> linarith

/-- Proposition 11.10.7 (Change of variables formula III)-/
theorem integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    integ f (Icc (φ a) (φ b)) := by
 have h1 := RS_integ_of_comp hab hφ_cont hφ_mono hf
 have h2 := RS_integ_eq_integ_of_mul_deriv hab hφ_mono hφ_diff hφ_cont hφ' h1.1
 refine ⟨ h2.1, by aesop ⟩

/-- Exercise 11.10.3-/
example {a b:ℝ} (hab: a < b) {f: ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
  integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = -integ f (Icc a b) := by
  sorry

/- Exercise 11.10.4: state and prove a version of `integ_of_comp` in which `φ` is `Antitone` rather than `Monotone`. -/

end Chapter11
