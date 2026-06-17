import Mathlib.Tactic
import Analysis.Section_9_9
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5: Riemann integrability of continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions.
- Riemann integrability of bounded continuous functions.

-/

namespace Chapter11
open BoundedInterval
open Chapter9

private theorem blen {I : BoundedInterval} (h : I.a ≤ I.b) : |I|ₗ = I.b - I.a := by
  simp only [BoundedInterval.length]; exact max_eq_left (by linarith)
private theorem bne {I : BoundedInterval} (h : I.a < I.b) : (I:Set ℝ).Nonempty := by
  refine ⟨(I.a+I.b)/2, ?_⟩
  have := BoundedInterval.Ioo_subset I; rw [subset_iff, set_Ioo] at this
  exact this (by rw [Set.mem_Ioo]; constructor <;> linarith)

theorem unif_gen : ∀ N : ℕ, 0 < N → ∀ (I : BoundedInterval), I.a < I.b →
    ∃ P : Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (I.b - I.a)/N := by
  intro N
  induction N with
  | zero => intro h0 _ _; exact absurd h0 (lt_irrefl 0)
  | succ n ih =>
    intro _ I hab
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨⊥, by rw [Partition.intervals_of_bot]; simp, ?_⟩
      intro J hJ; rw [Partition.intervals_of_bot, Finset.mem_singleton] at hJ; subst hJ
      rw [Nat.cast_one, div_one, blen hab.le]
    · have hn1 : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
      have hlt1 : (1:ℝ) < ((n+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < n+1)
      have hnR : ((n:ℕ):ℝ) ≠ 0 := by positivity
      have key : ∀ (I' F R : BoundedInterval), I'.joins F R → 0 < I'.b - I'.a →
          F.a = I'.a → F.b = I'.a + (I'.b-I'.a)/((n+1:ℕ):ℝ) →
          R.a = I'.a + (I'.b-I'.a)/((n+1:ℕ):ℝ) → R.b = I'.b →
          ∃ P : Partition I', P.intervals.card = n+1 ∧ ∀ J ∈ P.intervals, |J|ₗ = (I'.b-I'.a)/((n+1:ℕ):ℝ) := by
        intro I' F R hj hd' hFa hFb hRa hRb
        have hRab : R.a < R.b := by rw [hRa, hRb]; linarith [div_lt_self hd' hlt1]
        obtain ⟨PR, hPRcard, hPRlen⟩ := ih hnpos R hRab
        have hFab : F.a ≤ F.b := by rw [hFa, hFb]; have : (0:ℝ) ≤ (I'.b-I'.a)/((n+1:ℕ):ℝ) := by positivity
                                    linarith
        have hFlen : |F|ₗ = (I'.b-I'.a)/((n+1:ℕ):ℝ) := by rw [blen hFab, hFb, hFa]; ring
        have hFmem : F ∉ PR.intervals := by
          intro hmem
          have hsub := PR.contains _ hmem; rw [subset_iff] at hsub
          obtain ⟨x, hx⟩ := bne (by rw [hFa, hFb]; have : (0:ℝ) < (I'.b-I'.a)/((n+1:ℕ):ℝ) := by positivity
                                    linarith)
          have : x ∈ (F:Set ℝ) ∩ (R:Set ℝ) := ⟨hx, hsub hx⟩
          rw [hj.1] at this; exact this
        refine ⟨(⊥ : Partition F).join PR hj, ?_, ?_⟩
        · rw [Partition.intervals_of_join, Partition.intervals_of_bot,
            ← Finset.insert_eq, Finset.card_insert_of_notMem hFmem, hPRcard]
        · intro J hJ
          rw [Partition.intervals_of_join, Partition.intervals_of_bot, Finset.mem_union,
            Finset.mem_singleton] at hJ
          rcases hJ with hJ | hJ
          · subst hJ; exact hFlen
          · have harith : (R.b - R.a)/((n:ℕ):ℝ) = (I'.b-I'.a)/((n+1:ℕ):ℝ) := by
              rw [hRa, hRb, show ((n+1:ℕ):ℝ) = (n:ℝ)+1 by push_cast; ring]; field_simp; ring
            rw [hPRlen J hJ]; exact harith
      cases I with
      | Icc a b =>
        have hab' : a < b := hab
        exact key _ (Ico a (a+(b-a)/((n+1:ℕ):ℝ))) (Icc (a+(b-a)/((n+1:ℕ):ℝ)) b)
          (join_Ico_Icc (le_add_of_nonneg_right (div_nonneg (by linarith) hn1.le)) (by have := div_le_self (by linarith : (0:ℝ)≤b-a) hlt1.le; linarith))
          (by linarith) rfl rfl rfl rfl
      | Ico a b =>
        have hab' : a < b := hab
        exact key _ (Ico a (a+(b-a)/((n+1:ℕ):ℝ))) (Ico (a+(b-a)/((n+1:ℕ):ℝ)) b)
          (join_Ico_Ico (le_add_of_nonneg_right (div_nonneg (by linarith) hn1.le)) (by have := div_le_self (by linarith : (0:ℝ)≤b-a) hlt1.le; linarith))
          (by linarith) rfl rfl rfl rfl
      | Ioc a b =>
        have hab' : a < b := hab
        exact key _ (Ioc a (a+(b-a)/((n+1:ℕ):ℝ))) (Ioc (a+(b-a)/((n+1:ℕ):ℝ)) b)
          (join_Ioc_Ioc (le_add_of_nonneg_right (div_nonneg (by linarith) hn1.le)) (by have := div_le_self (by linarith : (0:ℝ)≤b-a) hlt1.le; linarith))
          (by linarith) rfl rfl rfl rfl
      | Ioo a b =>
        have hab' : a < b := hab
        exact key _ (Ioc a (a+(b-a)/((n+1:ℕ):ℝ))) (Ioo (a+(b-a)/((n+1:ℕ):ℝ)) b)
          (join_Ioc_Ioo (le_add_of_nonneg_right (div_nonneg (by linarith) hn1.le)) (by have := div_lt_self (by linarith : (0:ℝ)<b-a) hlt1; linarith))
          (by linarith) rfl rfl rfl rfl

/-- Theorem 11.5.1 -/
theorem integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I) :
  IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1.2
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ ε * (b-a) := by
    rw [UniformContinuousOn.iff] at hf
    choose δ hδ hf using hf ε hε; simp [Real.Close, Real.dist_eq] at hf
    choose N hN using exists_nat_gt ((b-a)/δ)
    have hNpos : 0 < N := by
      have : 0 < (b-a)/δ := by positivity
      rify; order
    have hN' : (b-a)/N < δ := by rwa [div_lt_comm₀] <;> positivity
    have : ∃ P: Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b-a) / N := by
      have hIab : I.a < I.b := by show a < b; linarith
      have := unif_gen N hNpos I hIab
      simpa only [a, b] using this
    choose P hcard hlength using this
    calc
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * |J|ₗ := by
        have h1 := upper_integ_le_upper_sum hfbound P
        have h2 := lower_integ_ge_lower_sum hfbound P
        simp [sub_mul, upper_riemann_sum, lower_riemann_sum] at *
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * |J|ₗ := by
        apply Finset.sum_le_sum; intro J hJ; gcongr
        have {x y:ℝ} (hx: x ∈ J) (hy: y ∈ J) : f x ≤ f y + ε := by
          have : J ⊆ I := P.contains _ hJ
          have : |f x - f y| ≤ ε := by
            apply hf y _ x _ _ <;> try solve_by_elim
            apply (BoundedInterval.dist_le_length hx hy).trans; grind
          grind [abs_le']
        have hJnon : (f '' J).Nonempty := by
          simp; by_contra! h
          replace h : Subsingleton (J:Set ℝ) := by simp [h]
          simp only [length_of_subsingleton, hlength J hJ] at h
          linarith [show 0 < (b-a) / N by positivity]
        replace (y:ℝ) (hy:y ∈ J) : sSup (f '' J) ≤ f y + ε := by
          apply csSup_le hJnon; rintro _ ⟨z, hz, rfl⟩; exact this hz hy
        replace : sSup (f '' J) - ε ≤ sInf (f '' J) := by
          apply le_csInf hJnon; grind [mem_iff]
        linarith
      _ = ∑ J ∈ P.intervals, ε * (b-a)/N := by grind [Finset.sum_congr]
      _ = _ := by simp [hcard]; field_simp
  have lower_le_upper : 0 ≤ upper_integral f I - lower_integral f I := by linarith [lower_integral_le_upper hfbound]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  . set ε := (upper_integral f I - lower_integral f I)/(2*(b-a))
    replace : upper_integral f I - lower_integral f I ≤ (upper_integral f I - lower_integral f I)/2 := by
      convert this ε (by positivity) using 1; grind
    linarith
  linarith

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by sorry

example : ¬ IntegrableOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by
  rintro ⟨⟨M, hM⟩, _⟩
  have hx : (1/(|M|+2):ℝ) ∈ ((Icc 0 1 : BoundedInterval):Set ℝ) := by
    rw [BoundedInterval.set_Icc, Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; have := abs_nonneg M; linarith
  have hbound := hM _ hx
  rw [show (fun x:ℝ ↦ 1/x) (1/(|M|+2)) = |M|+2 by simp [one_div_one_div],
    abs_of_pos (by positivity)] at hbound
  have := le_abs_self M
  linarith

open PiecewiseConstantOn ConstantOn in
set_option maxHeartbeats 300000 in
/-- Proposition 11.5.3-/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by by_contra!; rw [←BoundedInterval.length_of_subsingleton] at hsing; simp_all
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have ⟨ M, hM ⟩ := hbound
  have hMpos : 0 ≤ M := (abs_nonneg _).trans (hM hI.some hI.some_mem)
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . specialize this _ _ _ _ _ _ hM _ ((b-a)/3) _ _
        <;> first | assumption | linarith | apply this.trans; gcongr; linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by cases I <;> simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by cases I <;> simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => apply join_Ico_Icc <;> linarith
      case Ico _ _ => apply join_Ico_Icc <;> linarith
      case Ioc _ _ => apply join_Ioo_Icc <;> linarith
      case Ioo _ _ => apply join_Ioo_Icc <;> linarith
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => apply join_Icc_Ioc <;> linarith
      case Ico _ _ => apply join_Icc_Ioo <;> linarith
      case Ioc _ _ => apply join_Ioc_Ioc <;> linarith
      case Ioo _ _ => apply join_Ioc_Ioo <;> linarith
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts $ ContinuousOn.mono hf $ subset_trans _ $ (subset_iff _ _).mp $ Ioo_subset I
      intro _; simp; grind
    choose h hhmin hhconst hhint using lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [h',mem_iff]
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [h',mem_iff]
    have h'const : PiecewiseConstantOn h' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hhconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have h'maj : MajorizesOn h' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [h', hxI']; solve_by_elim; grind [abs_le']
    observe h'maj : upper_integral f I ≤ h'const.integ'
    have h'integ1 := h'const.integ_of_join hjoin2
    have h'integ2 := ((of_join hjoin2 _).mp h'const).1.integ_of_join hjoin1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    choose g hgmin hgconst hgint using gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [g', mem_iff]
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [g', mem_iff]
    have g'const : PiecewiseConstantOn g' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hgconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have g'maj : MinorizesOn g' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [g', hxI']; solve_by_elim; grind [abs_le']
    observe g'maj : g'const.integ' ≤ lower_integral f I
    have g'integ1 := g'const.integ_of_join hjoin2
    have g'integ2 := ((of_join hjoin2 _).mp g'const).1.integ_of_join hjoin1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    grind
  exact ⟨ hbound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

/-- Definition 11.5.4 -/
abbrev PiecewiseContinuousOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ P: Partition I, ∀ J ∈ P.intervals, ContinuousOn f J

/-- Example 11.5.5 -/
noncomputable abbrev f_11_5_5 : ℝ → ℝ := fun x ↦
  if x < 2 then x^2
  else if x = 2 then 7
  else x^3

example : ¬ ContinuousOn f_11_5_5 (Icc 1 3) := by
  intro h
  have h2mem : (2:ℝ) ∈ (↑(Icc 1 3):Set ℝ) := by rw [BoundedInterval.set_Icc, Set.mem_Icc]; norm_num
  have hsub : Set.Ico (1:ℝ) 2 ⊆ (↑(Icc 1 3):Set ℝ) := by
    rw [BoundedInterval.set_Icc]; intro x hx; rw [Set.mem_Ico] at hx; rw [Set.mem_Icc]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hc := (h.continuousWithinAt h2mem).mono hsub
  have hcont : Filter.Tendsto (fun x:ℝ => x^2) (nhdsWithin 2 (Set.Ico 1 2)) (nhds 4) := by
    have h4 : ((2:ℝ))^2 = 4 := by norm_num
    rw [← h4]; exact ((continuous_pow 2).tendsto 2).mono_left nhdsWithin_le_nhds
  have hcf : Filter.Tendsto f_11_5_5 (nhdsWithin 2 (Set.Ico 1 2)) (nhds 4) :=
    tendsto_nhdsWithin_congr (fun x hx => by rw [Set.mem_Ico] at hx; simp only [f_11_5_5, if_pos hx.2]) hcont
  haveI : (nhdsWithin (2:ℝ) (Set.Ico 1 2)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (by norm_num : (1:ℝ) ≠ 2)]
    exact Set.mem_Icc.mpr ⟨by norm_num, le_refl 2⟩
  have := tendsto_nhds_unique hc hcf
  rw [show f_11_5_5 2 = 7 from by simp [f_11_5_5]] at this
  norm_num at this

example : ContinuousOn f_11_5_5 (Ico 1 2) := by
  rw [BoundedInterval.set_Ico]
  apply (continuous_pow 2).continuousOn.congr
  intro x hx; simp only [Set.mem_Ico] at hx
  simp only [f_11_5_5, if_pos hx.2]

example : ContinuousOn f_11_5_5 (Icc 2 2) := by
  rw [BoundedInterval.set_Icc, Set.Icc_self]
  exact continuousOn_singleton f_11_5_5 2

example : ContinuousOn f_11_5_5 (Ioc 2 3) := by
  rw [BoundedInterval.set_Ioc]
  apply (continuous_pow 3).continuousOn.congr
  intro x hx; simp only [Set.mem_Ioc] at hx
  simp only [f_11_5_5, if_neg (by linarith [hx.1] : ¬ x < 2), if_neg (by linarith [hx.1] : x ≠ 2)]

example : PiecewiseContinuousOn f_11_5_5 (Icc 1 3) := by
  set P1 : Partition (Ico 1 2) := ⊥
  set P2 : Partition (Icc 1 2) := P1.join (⊥:Partition (Icc 2 2)) (join_Ico_Icc (by norm_num) (by norm_num))
  set P3 : Partition (Icc 1 3) := P2.join (⊥:Partition (Ioc 2 3)) (join_Icc_Ioc (by norm_num) (by norm_num))
  refine ⟨P3, fun J hJ => ?_⟩
  simp only [P3, P2, P1, Partition.intervals_of_join, Partition.intervals_of_bot,
    Finset.mem_union, Finset.mem_singleton] at hJ
  rcases hJ with (rfl | rfl) | rfl
  · rw [BoundedInterval.set_Ico]
    apply (continuous_pow 2).continuousOn.congr
    intro x hx; simp only [Set.mem_Ico] at hx; simp only [f_11_5_5, if_pos hx.2]
  · rw [BoundedInterval.set_Icc, Set.Icc_self]; exact continuousOn_singleton f_11_5_5 2
  · rw [BoundedInterval.set_Ioc]
    apply (continuous_pow 3).continuousOn.congr
    intro x hx; simp only [Set.mem_Ioc] at hx
    simp only [f_11_5_5, if_neg (by linarith [hx.1] : ¬ x < 2), if_neg (by linarith [hx.1] : x ≠ 2)]

/-- Proposition 11.5.6 / Exercise 11.5.1 -/
theorem integ_of_bdd_piecewise_cts {I: BoundedInterval} {f:ℝ → ℝ}
  (hbound: BddOn f I) (hf: PiecewiseContinuousOn f I) : IntegrableOn f I := by
  obtain ⟨P, hP⟩ := hf
  apply IntegrableOn.of_partition hbound P
  intro J hJ
  have hbJ : BddOn f J := by
    obtain ⟨M, hM⟩ := hbound
    refine ⟨M, fun x hx => hM x ?_⟩
    have := P.contains J hJ; rw [BoundedInterval.subset_iff] at this; exact this hx
  exact integ_of_bdd_cts hbJ (hP J hJ)

/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a < b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
    sorry

end Chapter11
