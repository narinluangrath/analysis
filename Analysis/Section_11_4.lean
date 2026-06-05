import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem IntegrableOn.add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  unfold IntegrableOn at hf hg
  have hbound : BddOn (f + g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M + M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.add_apply]; exact (abs_add_le _ _).trans (add_le_add hM hM')
  have hfu : integ f I = upper_integral f I := rfl
  have hgu : integ g I = upper_integral g I := rfl
  have hup : upper_integral (f + g) I ≤ integ f I + integ g I := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨f'', hf''maj, hf''const, hf''int⟩ := lt_of_gt_upper_integral hf.1 (X := integ f I + ε/2) (by rw [hfu]; linarith)
    obtain ⟨g'', hg''maj, hg''const, hg''int⟩ := lt_of_gt_upper_integral hg.1 (X := integ g I + ε/2) (by rw [hgu]; linarith)
    have hmaj : MajorizesOn (f'' + g'') (f + g) I := fun x hx => by
      simp only [Pi.add_apply]; exact add_le_add (hf''maj x hx) (hg''maj x hx)
    have hle := upper_integral_le_integ hbound hmaj (hf''const.add hg''const)
    rw [show (hf''const.add hg''const).integ' = PiecewiseConstantOn.integ (f'' + g'') I from rfl,
      PiecewiseConstantOn.integ_add hf''const hg''const] at hle
    linarith
  have hlow : integ f I + integ g I ≤ lower_integral (f + g) I := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨f', hf'min, hf'const, hf'int⟩ := gt_of_lt_lower_integral hf.1 (X := integ f I - ε/2) (by rw [hfu]; linarith [lower_integral_le_upper hf.1])
    obtain ⟨g', hg'min, hg'const, hg'int⟩ := gt_of_lt_lower_integral hg.1 (X := integ g I - ε/2) (by rw [hgu]; linarith [lower_integral_le_upper hg.1])
    have hmin : MinorizesOn (f' + g') (f + g) I := fun x hx => by
      simp only [Pi.add_apply]; exact add_le_add (hf'min x hx) (hg'min x hx)
    have hle := integ_le_lower_integral hbound hmin (hf'const.add hg'const)
    rw [show (hf'const.add hg'const).integ' = PiecewiseConstantOn.integ (f' + g') I from rfl,
      PiecewiseConstantOn.integ_add hf'const hg'const] at hle
    linarith
  have hlu := lower_integral_le_upper hbound
  refine ⟨⟨hbound, by linarith⟩, ?_⟩
  show upper_integral (f + g) I = integ f I + integ g I
  linarith

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem IntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  unfold IntegrableOn at hf
  have hbound : BddOn (c • f) I := by
    choose M hM using hf.1; use |c| * M; peel hM with x hx hM
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hM (abs_nonneg c)
  have hfu : integ f I = upper_integral f I := rfl
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- c < 0
    have hup : upper_integral (c • f) I ≤ c * integ f I := by
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨f', hf'min, hf'const, hf'int⟩ := gt_of_lt_lower_integral hf.1 (X := integ f I + ε/c) (by rw [hfu]; have : ε/c < 0 := div_neg_of_pos_of_neg hε hc; linarith [lower_integral_le_upper hf.1])
      have hmaj : MajorizesOn (c • f') (c • f) I := fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_le_mul_of_nonpos_left (hf'min x hx) hc.le
      have hle := upper_integral_le_integ hbound hmaj (hf'const.smul c)
      rw [show (hf'const.smul c).integ' = PiecewiseConstantOn.integ (c • f') I from rfl,
        PiecewiseConstantOn.integ_smul c hf'const] at hle
      have hkey : c * PiecewiseConstantOn.integ f' I ≤ c * integ f I + ε := by
        have := mul_le_mul_of_nonpos_left hf'int.le hc.le
        rw [mul_add, mul_div_cancel₀ ε (ne_of_lt hc)] at this; linarith
      linarith
    have hlow : c * integ f I ≤ lower_integral (c • f) I := by
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨f'', hf''maj, hf''const, hf''int⟩ := lt_of_gt_upper_integral hf.1 (X := integ f I - ε/c) (by rw [hfu]; have : ε/c < 0 := div_neg_of_pos_of_neg hε hc; linarith)
      have hmin : MinorizesOn (c • f'') (c • f) I := fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_le_mul_of_nonpos_left (hf''maj x hx) hc.le
      have hle := integ_le_lower_integral hbound hmin (hf''const.smul c)
      rw [show (hf''const.smul c).integ' = PiecewiseConstantOn.integ (c • f'') I from rfl,
        PiecewiseConstantOn.integ_smul c hf''const] at hle
      have hkey : c * integ f I - ε ≤ c * PiecewiseConstantOn.integ f'' I := by
        have := mul_le_mul_of_nonpos_left hf''int.le hc.le
        rw [mul_sub, mul_div_cancel₀ ε (ne_of_lt hc)] at this; linarith
      linarith
    have hlu := lower_integral_le_upper hbound
    exact ⟨⟨hbound, by linarith⟩, by show upper_integral (c • f) I = c * integ f I; linarith⟩
  · subst hc
    have hz : (0:ℝ) • f = (fun _ => (0:ℝ)) := by ext x; simp
    rw [hz, zero_mul]
    have hconst : ConstantOn (fun _:ℝ => (0:ℝ)) I := ConstantOn.of_const' 0 _
    obtain ⟨hint, heq⟩ := integ_of_piecewise_const hconst.piecewiseConstantOn
    refine ⟨hint, ?_⟩
    rw [heq, show hconst.piecewiseConstantOn.integ' = PiecewiseConstantOn.integ (fun _ => (0:ℝ)) I from rfl,
      PiecewiseConstantOn.integ_const 0 I, zero_mul]
  · -- c > 0
    have hup : upper_integral (c • f) I ≤ c * integ f I := by
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨f'', hf''maj, hf''const, hf''int⟩ := lt_of_gt_upper_integral hf.1 (X := integ f I + ε/c) (by rw [hfu]; have := div_pos hε hc; linarith)
      have hmaj : MajorizesOn (c • f'') (c • f) I := fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_le_mul_of_nonneg_left (hf''maj x hx) hc.le
      have hle := upper_integral_le_integ hbound hmaj (hf''const.smul c)
      rw [show (hf''const.smul c).integ' = PiecewiseConstantOn.integ (c • f'') I from rfl,
        PiecewiseConstantOn.integ_smul c hf''const] at hle
      have hkey : c * PiecewiseConstantOn.integ f'' I < c * integ f I + ε := by
        have := mul_lt_mul_of_pos_left hf''int hc
        rw [mul_add, mul_div_cancel₀ ε (ne_of_gt hc)] at this; linarith
      linarith
    have hlow : c * integ f I ≤ lower_integral (c • f) I := by
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨f', hf'min, hf'const, hf'int⟩ := gt_of_lt_lower_integral hf.1 (X := integ f I - ε/c) (by rw [hfu]; have := div_pos hε hc; linarith [lower_integral_le_upper hf.1])
      have hmin : MinorizesOn (c • f') (c • f) I := fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_le_mul_of_nonneg_left (hf'min x hx) hc.le
      have hle := integ_le_lower_integral hbound hmin (hf'const.smul c)
      rw [show (hf'const.smul c).integ' = PiecewiseConstantOn.integ (c • f') I from rfl,
        PiecewiseConstantOn.integ_smul c hf'const] at hle
      have hkey : c * integ f I - ε < c * PiecewiseConstantOn.integ f' I := by
        have := mul_lt_mul_of_pos_left hf'int hc
        rw [mul_sub, mul_div_cancel₀ ε (ne_of_gt hc)] at this; linarith
      linarith
    have hlu := lower_integral_le_upper hbound
    exact ⟨⟨hbound, by linarith⟩, by show upper_integral (c • f) I = c * integ f I; linarith⟩

theorem IntegrableOn.neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by have := IntegrableOn.smul (-1) hf; aesop

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem IntegrableOn.sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  unfold IntegrableOn at hf hg
  have hbound : BddOn (f - g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M + M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sub_apply]
    calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ M + M' := add_le_add hM hM'
  have hfu : integ f I = upper_integral f I := rfl
  have hgu : integ g I = upper_integral g I := rfl
  have hup : upper_integral (f - g) I ≤ integ f I - integ g I := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨f'', hf''maj, hf''const, hf''int⟩ := lt_of_gt_upper_integral hf.1 (X := integ f I + ε/2) (by rw [hfu]; linarith)
    obtain ⟨g', hg'min, hg'const, hg'int⟩ := gt_of_lt_lower_integral hg.1 (X := integ g I - ε/2) (by rw [hgu]; linarith [lower_integral_le_upper hg.1])
    have hmaj : MajorizesOn (f'' - g') (f - g) I := fun x hx => by
      simp only [Pi.sub_apply]; exact sub_le_sub (hf''maj x hx) (hg'min x hx)
    have hle := upper_integral_le_integ hbound hmaj (hf''const.sub hg'const)
    rw [show (hf''const.sub hg'const).integ' = PiecewiseConstantOn.integ (f'' - g') I from rfl,
      PiecewiseConstantOn.integ_sub hf''const hg'const] at hle
    linarith
  have hlow : integ f I - integ g I ≤ lower_integral (f - g) I := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨f', hf'min, hf'const, hf'int⟩ := gt_of_lt_lower_integral hf.1 (X := integ f I - ε/2) (by rw [hfu]; linarith [lower_integral_le_upper hf.1])
    obtain ⟨g'', hg''maj, hg''const, hg''int⟩ := lt_of_gt_upper_integral hg.1 (X := integ g I + ε/2) (by rw [hgu]; linarith)
    have hmin : MinorizesOn (f' - g'') (f - g) I := fun x hx => by
      simp only [Pi.sub_apply]; exact sub_le_sub (hf'min x hx) (hg''maj x hx)
    have hle := integ_le_lower_integral hbound hmin (hf'const.sub hg''const)
    rw [show (hf'const.sub hg''const).integ' = PiecewiseConstantOn.integ (f' - g'') I from rfl,
      PiecewiseConstantOn.integ_sub hf'const hg''const] at hle
    linarith
  have hlu := lower_integral_le_upper hbound
  refine ⟨⟨hbound, by linarith⟩, ?_⟩
  show upper_integral (f - g) I = integ f I - integ g I
  linarith

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem IntegrableOn.nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  apply le_csInf (integral_bound_upper_nonempty hf.1)
  rintro v ⟨φ, ⟨hφmaj, hφpc⟩, rfl⟩
  exact hφpc.integ_of_nonneg (fun x hx => le_trans (hf_nonneg x hx) (hφmaj x hx))

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem IntegrableOn.mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  apply csInf_le_csInf (integral_bound_below hf.1) (integral_bound_upper_nonempty hg.1)
  rintro v ⟨φ, ⟨hφmaj, hφpc⟩, rfl⟩
  exact ⟨φ, ⟨fun x hx => le_trans (h x hx) (hφmaj x hx), hφpc⟩, rfl⟩

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hc : ConstantOn (fun _:ℝ ↦ c) I := ConstantOn.of_const' c _
  obtain ⟨hint, heq⟩ := integ_of_piecewise_const hc.piecewiseConstantOn
  exact ⟨hint, heq.trans (PiecewiseConstantOn.integ_const c I)⟩

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  obtain ⟨hint, heq⟩ := integ_of_piecewise_const hf.piecewiseConstantOn
  exact ⟨hint, heq.trans (PiecewiseConstantOn.integ_const' hf)⟩


open Classical in
private theorem IntegrableOn.extend_bounds {I J: BoundedInterval} (hIJ: I ⊆ J)
    {f: ℝ → ℝ} (h: IntegrableOn f I) :
    BddOn (fun x ↦ if x ∈ I then f x else 0) J ∧
    upper_integral (fun x ↦ if x ∈ I then f x else 0) J ≤ integ f I ∧
    integ f I ≤ lower_integral (fun x ↦ if x ∈ I then f x else 0) J := by
  classical
  set g : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hgdef
  have hbg : BddOn g J := by
    obtain ⟨M, hM⟩ := h.1
    refine ⟨max M 0, fun x hx => ?_⟩
    simp only [hgdef]
    split_ifs with hxI
    · exact le_trans (hM x (by rw [BoundedInterval.mem_iff] at hxI; exact hxI)) (le_max_left _ _)
    · rw [abs_zero]; exact le_max_right _ _
  have hfuI : integ f I = upper_integral f I := rfl
  refine ⟨hbg, ?_, ?_⟩
  · apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨φ, hφmaj, hφpc, hφint⟩ := lt_of_gt_upper_integral h.1 (X := integ f I + ε)
      (by rw [hfuI]; linarith)
    have hφepc : PiecewiseConstantOn (fun x => if x ∈ I then φ x else 0) J :=
      PiecewiseConstantOn.of_extend hIJ hφpc
    have hφemaj : MajorizesOn (fun x => if x ∈ I then φ x else 0) g J := by
      intro x hx; simp only [hgdef]; split_ifs with hxI
      · exact hφmaj x (by rw [BoundedInterval.mem_iff] at hxI; exact hxI)
      · exact le_refl 0
    have hle := upper_integral_le_integ hbg hφemaj hφepc
    rw [show hφepc.integ' = PiecewiseConstantOn.integ (fun x => if x ∈ I then φ x else 0) J from rfl,
      PiecewiseConstantOn.integ_of_extend hIJ hφpc] at hle
    linarith [hφint]
  · apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨ψ, hψmin, hψpc, hψint⟩ := gt_of_lt_lower_integral h.1 (X := integ f I - ε)
      (by rw [hfuI]; linarith [h.2])
    have hψepc : PiecewiseConstantOn (fun x => if x ∈ I then ψ x else 0) J :=
      PiecewiseConstantOn.of_extend hIJ hψpc
    have hψemin : MinorizesOn (fun x => if x ∈ I then ψ x else 0) g J := by
      intro x hx; simp only [hgdef]; split_ifs with hxI
      · exact hψmin x (by rw [BoundedInterval.mem_iff] at hxI; exact hxI)
      · exact le_refl 0
    have hge := integ_le_lower_integral hbg hψemin hψepc
    rw [show hψepc.integ' = PiecewiseConstantOn.integ (fun x => if x ∈ I then ψ x else 0) J from rfl,
      PiecewiseConstantOn.integ_of_extend hIJ hψpc] at hge
    linarith [hψint]

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  obtain ⟨hbg, hup, hlow⟩ := IntegrableOn.extend_bounds hIJ h
  exact ⟨hbg, le_antisymm (lower_integral_le_upper hbg) (by linarith)⟩

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend' {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  obtain ⟨hbg, hup, hlow⟩ := IntegrableOn.extend_bounds hIJ h
  show upper_integral (fun x ↦ if x ∈ I then f x else 0) J = integ f I
  exact le_antisymm hup (le_trans hlow (lower_integral_le_upper hbg))

/-- A nonnegative piecewise constant function integrates to no more over a subinterval. -/
theorem PiecewiseConstantOn.integ_le_of_subset {I J: BoundedInterval} (hJI: J ⊆ I)
    {φ: ℝ → ℝ} (hφ: PiecewiseConstantOn φ I) (hnn: ∀ x ∈ I, 0 ≤ φ x) :
    integ φ J ≤ integ φ I := by
  classical
  obtain ⟨P, hP⟩ := hφ
  -- build the restriction partition Q of J: each piece L of P becomes L ∩ J
  have hQ : ∃ Q : Partition J, Q.intervals = P.intervals.image (fun L => L ∩ J) := by
    refine ⟨⟨P.intervals.image (fun L => L ∩ J), ?_, ?_⟩, rfl⟩
    · intro x hx
      have hxI : x ∈ (I:Set ℝ) := by
        have := hJI; rw [BoundedInterval.subset_iff] at this
        exact this ((BoundedInterval.mem_iff J x).mp hx)
      obtain ⟨L, ⟨hLmem, hxL⟩, hLuniq⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)
      refine ⟨L ∩ J, ⟨Finset.mem_image_of_mem _ hLmem, ?_⟩, ?_⟩
      · rw [BoundedInterval.mem_iff, BoundedInterval.inter_eq]
        exact ⟨(BoundedInterval.mem_iff L x).mp hxL, (BoundedInterval.mem_iff J x).mp hx⟩
      · rintro M ⟨hMmem, hxM⟩
        obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hMmem
        rw [BoundedInterval.mem_iff, BoundedInterval.inter_eq] at hxM
        rw [hLuniq L' ⟨hL'mem, (BoundedInterval.mem_iff L' x).mpr hxM.1⟩]
    · intro M hMmem
      obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hMmem
      rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      exact Set.inter_subset_right
  obtain ⟨Q, hQint⟩ := hQ
  have hQpc : PiecewiseConstantWith φ Q := by
    intro M hM
    rw [show (M ∈ Q) = (M ∈ Q.intervals) from rfl, hQint] at hM
    obtain ⟨L', hL'mem, rfl⟩ := Finset.mem_image.mp hM
    rw [BoundedInterval.inter_eq]
    exact ConstantOn.of_const (fun y hy => ConstantOn.eq (hP L' hL'mem) hy.1)
  -- value on a nonempty piece L ∩ J equals the value on L
  have hcval : ∀ L ∈ P.intervals, (↑(L ∩ J):Set ℝ).Nonempty →
      constant_value_on φ ↑(L ∩ J) = constant_value_on φ ↑L := by
    intro L hL hne
    obtain ⟨x, hx⟩ := hne
    rw [BoundedInterval.inter_eq] at hx
    have hcK : ConstantOn φ ↑(L ∩ J) :=
      ConstantOn.of_const (fun y hy => ConstantOn.eq (hP L hL)
        (by rw [BoundedInterval.inter_eq] at hy; exact hy.1))
    rw [← ConstantOn.eq hcK (by rw [BoundedInterval.inter_eq]; exact hx),
      ← ConstantOn.eq (hP L hL) hx.1]
  -- nonnegativity of each value
  have hval_nn : ∀ L ∈ P.intervals, (↑(L ∩ J):Set ℝ).Nonempty → 0 ≤ constant_value_on φ ↑(L ∩ J) := by
    intro L hL hne
    obtain ⟨x, hx⟩ := hne
    have hxI : x ∈ (I:Set ℝ) := by
      rw [BoundedInterval.inter_eq] at hx
      have := P.contains L hL; rw [BoundedInterval.subset_iff] at this; exact this hx.1
    rw [hcval L hL ⟨x, hx⟩, ← ConstantOn.eq (hP L hL)
      (by rw [BoundedInterval.inter_eq] at hx; exact hx.1)]
    exact hnn x hxI
  rw [PiecewiseConstantOn.integ_def hQpc, PiecewiseConstantOn.integ_def hP]
  simp only [PiecewiseConstantWith.integ, hQint]
  calc ∑ M ∈ P.intervals.image (fun L => L ∩ J), constant_value_on φ ↑M * |M|ₗ
      ≤ ∑ L ∈ P.intervals, constant_value_on φ ↑(L ∩ J) * |L ∩ J|ₗ := by
        apply Finset.sum_image_le_of_nonneg
        intro u hu
        obtain ⟨L, hLmem, rfl⟩ := Finset.mem_image.mp hu
        rcases eq_or_ne (↑(L ∩ J):Set ℝ) ∅ with he | hne
        · rw [BoundedInterval.length_of_empty he, mul_zero]
        · exact mul_nonneg (hval_nn L hLmem (Set.nonempty_iff_ne_empty.mpr hne))
            (BoundedInterval.length_nonneg _)
    _ ≤ ∑ L ∈ P.intervals, constant_value_on φ ↑L * |L|ₗ := by
        apply Finset.sum_le_sum
        intro L hL
        rcases eq_or_ne (↑(L ∩ J):Set ℝ) ∅ with he | hne
        · rw [BoundedInterval.length_of_empty he, mul_zero]
          rcases eq_or_ne (↑L:Set ℝ) ∅ with heL | hneL
          · rw [BoundedInterval.length_of_empty heL, mul_zero]
          · have hxL : (↑L:Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hneL
            obtain ⟨x, hx⟩ := hxL
            have hxI : x ∈ (I:Set ℝ) := by
              have := P.contains L hL; rw [BoundedInterval.subset_iff] at this; exact this hx
            apply mul_nonneg _ (BoundedInterval.length_nonneg _)
            rw [← ConstantOn.eq (hP L hL) hx]; exact hnn x hxI
        · have hneU : (↑(L ∩ J):Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
          rw [hcval L hL hneU]
          have hLJ : (↑(L ∩ J):Set ℝ) ⊆ ↑L := by
            rw [BoundedInterval.inter_eq]; exact Set.inter_subset_left
          apply mul_le_mul_of_nonneg_left (BoundedInterval.length_mono hLJ)
          obtain ⟨x, hx⟩ := hneU
          have hxI : x ∈ (I:Set ℝ) := by
            rw [BoundedInterval.inter_eq] at hx
            have := P.contains L hL; rw [BoundedInterval.subset_iff] at this; exact this hx.1
          rw [← ConstantOn.eq (hP L hL) (by rw [BoundedInterval.inter_eq] at hx; exact hx.1)]
          exact hnn x hxI

/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  obtain ⟨hbddI, heqI⟩ := h
  -- f is bounded on J since J ⊆ I
  have hbddJ : BddOn f J := by
    obtain ⟨M, hM⟩ := hbddI
    refine ⟨M, fun x hx => hM x ?_⟩
    have hs := hIJ; rw [BoundedInterval.subset_iff] at hs; exact hs hx
  refine ⟨hbddJ, ?_⟩
  -- show upper_integral f J ≤ lower_integral f J via epsilon of room
  have hlu := lower_integral_le_upper hbddJ
  rcases eq_or_lt_of_le hlu with heq | hlt
  · exact heq
  exfalso
  set ε := upper_integral f J - lower_integral f J with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- pc majorant g of f on I with integ g I close to upper = integ f I
  have hfuI : integ f I = upper_integral f I := rfl
  obtain ⟨g, hgmaj, hgpc, hgint⟩ := lt_of_gt_upper_integral hbddI (X := integ f I + ε/3)
    (by rw [hfuI]; linarith)
  obtain ⟨k, hkmin, hkpc, hkint⟩ := gt_of_lt_lower_integral hbddI (X := integ f I - ε/3)
    (by rw [hfuI]; linarith [lower_integral_le_upper hbddI])
  -- g - k is nonnegative pc on I; restrict to J
  have hsubnn : ∀ x ∈ I, 0 ≤ (g - k) x := by
    intro x hx; simp only [Pi.sub_apply]
    linarith [hgmaj x hx, hkmin x hx]
  have hgkpc : PiecewiseConstantOn (g - k) I := hgpc.sub hkpc
  -- integ (g-k) J ≤ integ (g-k) I
  have hle := PiecewiseConstantOn.integ_le_of_subset hIJ hgkpc hsubnn
  rw [PiecewiseConstantOn.integ_sub hgpc hkpc] at hle
  -- restrict g, k to J as majorant / minorant of f on J
  have hgpcJ : PiecewiseConstantOn g J := hgpc.restrict hIJ
  have hkpcJ : PiecewiseConstantOn k J := hkpc.restrict hIJ
  have hgmajJ : MajorizesOn g f J := fun x hx => hgmaj x (by
    have hs := hIJ; rw [BoundedInterval.subset_iff] at hs; exact hs hx)
  have hkminJ : MinorizesOn k f J := fun x hx => hkmin x (by
    have hs := hIJ; rw [BoundedInterval.subset_iff] at hs; exact hs hx)
  have hupJ : upper_integral f J ≤ PiecewiseConstantOn.integ g J :=
    upper_integral_le_integ hbddJ hgmajJ hgpcJ
  have hlowJ : PiecewiseConstantOn.integ k J ≤ lower_integral f J :=
    integ_le_lower_integral hbddJ hkminJ hkpcJ
  -- combine: ε = upper_J - lower_J ≤ integ g J - integ k J = integ (g-k) J ≤ integ (g-k) I < ε
  have hgkI : PiecewiseConstantOn.integ (g - k) I < ε := by
    rw [PiecewiseConstantOn.integ_sub hgpc hkpc]
    linarith [hgint, hkint]
  have hgkJ : PiecewiseConstantOn.integ (g - k) J =
      PiecewiseConstantOn.integ g J - PiecewiseConstantOn.integ k J :=
    PiecewiseConstantOn.integ_sub hgpcJ hkpcJ
  linarith [hupJ, hlowJ, hle, hgkI, hgkJ]

open Classical in
/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem IntegrableOn.join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  have hIK : I ⊆ K := by
    rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by
    rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  have hI : IntegrableOn f I := h.mono' hIK
  have hJ : IntegrableOn f J := h.mono' hJK
  refine ⟨hI, hJ, ?_⟩
  have hfuK : integ f K = upper_integral f K := rfl
  have hfuI : integ f I = upper_integral f I := rfl
  have hfuJ : integ f J = upper_integral f J := rfl
  -- membership in K splits into I or J
  have hmemK : ∀ x ∈ (K:Set ℝ), x ∈ (I:Set ℝ) ∨ x ∈ (J:Set ℝ) := by
    intro x hx; rw [hIJK.2.1] at hx; exact hx
  have hdisj : ∀ x ∈ (J:Set ℝ), x ∉ (I:Set ℝ) := by
    intro x hxJ hxI
    have : x ∈ (I:Set ℝ) ∩ (J:Set ℝ) := ⟨hxI, hxJ⟩
    rw [hIJK.1] at this; exact this
  -- upper: integ f K ≤ integ f I + integ f J
  have hup : integ f K ≤ integ f I + integ f J := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨gI, hgImaj, hgIpc, hgIint⟩ := lt_of_gt_upper_integral hI.1 (X := integ f I + ε/2)
      (by rw [hfuI]; linarith)
    obtain ⟨gJ, hgJmaj, hgJpc, hgJint⟩ := lt_of_gt_upper_integral hJ.1 (X := integ f J + ε/2)
      (by rw [hfuJ]; linarith)
    set g := fun x => if x ∈ (I:Set ℝ) then gI x else gJ x with hgdef
    have hgI_eq : ∀ x ∈ (I:Set ℝ), g x = gI x := fun x hx => by simp only [hgdef, if_pos hx]
    have hgJ_eq : ∀ x ∈ (J:Set ℝ), g x = gJ x := fun x hx => by
      simp only [hgdef, if_neg (hdisj x hx)]
    have hgpcI : PiecewiseConstantOn g I := hgIpc.congr' (fun x hx => (hgI_eq x hx).symm)
    have hgpcJ : PiecewiseConstantOn g J := hgJpc.congr' (fun x hx => (hgJ_eq x hx).symm)
    have hgpcK : PiecewiseConstantOn g K := (PiecewiseConstantOn.of_join hIJK g).mpr ⟨hgpcI, hgpcJ⟩
    have hgmaj : MajorizesOn g f K := by
      intro x hx
      rcases hmemK x hx with hxI | hxJ
      · rw [hgI_eq x hxI]; exact hgImaj x hxI
      · rw [hgJ_eq x hxJ]; exact hgJmaj x hxJ
    have hKle := upper_integral_le_integ h.1 hgmaj hgpcK
    have hsplit := PiecewiseConstantOn.integ_of_join hIJK hgpcK
    have hcgI : PiecewiseConstantOn.integ g I = PiecewiseConstantOn.integ gI I :=
      PiecewiseConstantOn.integ_congr hgI_eq
    have hcgJ : PiecewiseConstantOn.integ g J = PiecewiseConstantOn.integ gJ J :=
      PiecewiseConstantOn.integ_congr hgJ_eq
    rw [show hgpcK.integ' = PiecewiseConstantOn.integ g K from rfl] at hKle
    rw [hsplit, hcgI, hcgJ] at hKle
    rw [hfuK]; linarith [hgIint, hgJint]
  -- lower: integ f I + integ f J ≤ integ f K
  have hlow : integ f I + integ f J ≤ integ f K := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨gI, hgImin, hgIpc, hgIint⟩ := gt_of_lt_lower_integral hI.1 (X := integ f I - ε/2)
      (by rw [hfuI]; linarith [hI.2])
    obtain ⟨gJ, hgJmin, hgJpc, hgJint⟩ := gt_of_lt_lower_integral hJ.1 (X := integ f J - ε/2)
      (by rw [hfuJ]; linarith [hJ.2])
    set g := fun x => if x ∈ (I:Set ℝ) then gI x else gJ x with hgdef
    have hgI_eq : ∀ x ∈ (I:Set ℝ), g x = gI x := fun x hx => by simp only [hgdef, if_pos hx]
    have hgJ_eq : ∀ x ∈ (J:Set ℝ), g x = gJ x := fun x hx => by
      simp only [hgdef, if_neg (hdisj x hx)]
    have hgpcI : PiecewiseConstantOn g I := hgIpc.congr' (fun x hx => (hgI_eq x hx).symm)
    have hgpcJ : PiecewiseConstantOn g J := hgJpc.congr' (fun x hx => (hgJ_eq x hx).symm)
    have hgpcK : PiecewiseConstantOn g K := (PiecewiseConstantOn.of_join hIJK g).mpr ⟨hgpcI, hgpcJ⟩
    have hgmin : MinorizesOn g f K := by
      intro x hx
      rcases hmemK x hx with hxI | hxJ
      · rw [hgI_eq x hxI]; exact hgImin x hxI
      · rw [hgJ_eq x hxJ]; exact hgJmin x hxJ
    have hKle := integ_le_lower_integral h.1 hgmin hgpcK
    have hsplit := PiecewiseConstantOn.integ_of_join hIJK hgpcK
    have hcgI : PiecewiseConstantOn.integ g I = PiecewiseConstantOn.integ gI I :=
      PiecewiseConstantOn.integ_congr hgI_eq
    have hcgJ : PiecewiseConstantOn.integ g J = PiecewiseConstantOn.integ gJ J :=
      PiecewiseConstantOn.integ_congr hgJ_eq
    rw [show hgpcK.integ' = PiecewiseConstantOn.integ g K from rfl] at hKle
    rw [hsplit, hcgI, hcgJ] at hKle
    have hluK : lower_integral f K ≤ upper_integral f K := lower_integral_le_upper h.1
    rw [hfuK]; linarith [hgIint, hgJint]
  linarith [hup, hlow]

/-- For a nondegenerate interval, the integral equals the integral over its open core
(the endpoints contribute zero). -/
theorem integ_eq_Ioo {I: BoundedInterval} (hlt: I.a < I.b) {f: ℝ → ℝ} (h: IntegrableOn f I) :
    integ f I = integ f (BoundedInterval.Ioo I.a I.b) := by
  have hsingl : ∀ c:ℝ, integ f (BoundedInterval.Icc c c) = 0 :=
    fun c => (integ_on_subsingleton (by rw [BoundedInterval.length]; exact max_eq_right (by simp))).2
  cases I with
  | Ioo a b => rfl
  | Icc a b =>
    obtain ⟨_, hIoc, heq1⟩ := h.join (BoundedInterval.join_Icc_Ioc (le_refl a) hlt.le)
    obtain ⟨_, _, heq2⟩ := hIoc.join (BoundedInterval.join_Ioo_Icc hlt (le_refl b))
    rw [heq1, heq2, hsingl a, hsingl b]; ring
  | Ioc a b =>
    obtain ⟨_, _, heq⟩ := h.join (BoundedInterval.join_Ioo_Icc hlt (le_refl b))
    rw [heq, hsingl b]; ring
  | Ico a b =>
    obtain ⟨_, _, heq⟩ := h.join (BoundedInterval.join_Icc_Ioo (le_refl a) hlt)
    rw [heq, hsingl a]; ring

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  rcases lt_or_ge I.a I.b with hlt | hge
  · have hltJ : J.a < J.b := by rw [ha, hb]; exact hlt
    rw [integ_eq_Ioo hltJ (h.mono' hIJ), integ_eq_Ioo hlt h, ha, hb]
  · have hI0 : |I|ₗ = 0 := by rw [BoundedInterval.length]; exact max_eq_right (by linarith)
    have hJ0 : |J|ₗ = 0 := le_antisymm
      (by rw [← hI0]; exact BoundedInterval.length_mono (by
        have := hIJ; rwa [BoundedInterval.subset_iff] at this))
      (BoundedInterval.length_nonneg J)
    rw [(integ_on_subsingleton hJ0).2, (integ_on_subsingleton hI0).2]

/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) (by positivity); convert_to x ≤ x/2 at h; grind
    linarith
  specialize h 1 ?_ <;> grind

/-- Theorem 11.4.3 (Max and min preserve integrability)-/
theorem IntegrableOn.max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊔ g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (f ⊔ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    exact abs_max_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_IntegrableOn.eq := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊔ g'') (f ⊔ g) I := by
      intro x hx; simp only [Pi.sup_apply]
      exact max_le_max (hf''max x hx) (hg''max x hx)
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (f' ⊔ g') (f ⊔ g) I := by
      intro x hx; simp only [Pi.sup_apply]
      exact max_le_max (hf'min x hx) (hg'min x hx)
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (f'' ⊔ g'') (f' ⊔ g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; split_ands <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_IntegrableOn.eq.1
    rw [MinorizesOn.iff] at this
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above.-/
theorem IntegrableOn.min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊓ g) I  := by
  unfold IntegrableOn at hf hg
  have hmin_bound : BddOn (f ⊓ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.inf_apply]
    exact abs_min_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊓ g) I - lower_integral (f ⊓ g) I := by linarith [lower_integral_le_upper hmin_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊓ g) I - lower_integral (f ⊓ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_int := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.min hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊓ g'') (f ⊓ g) I := by
      intro x hx; simp only [Pi.inf_apply]
      exact min_le_min (hf''max x hx) (hg''max x hx)
    have hf'g'_const := hf'const.min hg'const
    have hf'g'_maj : MinorizesOn (f' ⊓ g') (f ⊓ g) I := by
      intro x hx; simp only [Pi.inf_apply]
      exact min_le_min (hf'min x hx) (hg'min x hx)
    have hff'g''_ge := upper_integral_le_integ hmin_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmin_bound hf'g'_maj hf'g'_const
    have hmin : MinorizesOn (f'' ⊓ g'') (f' ⊓ g' + h) I := by
      intro x hx
      specialize hf'min x hx; specialize hg'min x hx; specialize hf''max x hx; specialize hg''max x hx
      simp only [Pi.inf_apply, Pi.add_apply, h, Pi.sub_apply]
      rcases le_total (f' x) (g' x) with hle | hle
      · rw [inf_of_le_left hle]
        calc f'' x ⊓ g'' x ≤ f'' x := inf_le_left
          _ ≤ f' x + (f'' x - f' x + (g'' x - g' x)) := by linarith
      · rw [inf_of_le_right hle]
        calc f'' x ⊓ g'' x ≤ g'' x := inf_le_right
          _ ≤ g' x + (f'' x - f' x + (g'' x - g' x)) := by linarith
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_int.1
    rw [MinorizesOn.iff] at hmin
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 hmin]
  exact ⟨ hmin_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

/-- Corollary 11.4.4 -/
theorem IntegrableOn.abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (IntegrableOn.const 0 I).1
  convert ((hf.max this).sub (hf.min this)).1 using 1
  ext x; obtain h | h := (show f x ≤ 0 ∨ f x ≥ 0 by grind) <;> simp [h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case.-/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  choose M₁ hM₁ using hf.1
  choose M₂ hM₂ using hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . apply lt_of_lt_of_le hf'int (hf'const.integ_mono _ (hf'const.max hzero)); simp
      intro _; simp
    choose f' hf'min hf'const hf'int hf'_nonneg using this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono _ (hg'const.max hzero)); simp
      intro _; simp
    choose g' hg'min hg'const hg'int hg'_nonneg using this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := (ConstantOn.of_const' M₁ I).piecewiseConstantOn
      split_ands
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        simp [hf''maj _ hx, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        simp
      intro _; simp
    choose f'' hf''maj hf''const hf''int hf''bound using this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := (ConstantOn.of_const' M₂ I).piecewiseConstantOn
      split_ands
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        simp [hg''maj _ hx, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        simp
      intro _ _; simp
    choose g'' hg''maj hg''const hg''int hg''bound using this
    have hf'g'_const := hf'const.mul hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx;
      specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; apply mul_le_mul hf'min hg'min <;> grind
    have hf''g''_const := hf''const.mul hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; apply mul_le_mul hf''maj hg''maj <;> grind
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by gcongr <;> grind
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (IntegrableOn.const 0 I).1
  observe hfplus_integ : IntegrableOn fplus I
  observe hgplus_integ : IntegrableOn gplus I
  have hfminus_integ : IntegrableOn fminus I := (hf.min this).neg.1
  have hgminus_integ : IntegrableOn gminus I := (hg.min this).neg.1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  rw [show f = fplus - fminus by ext; simp [fplus, fminus],
      show g = gplus - gminus by ext; simp [gplus, gminus]]
  ring_nf
  exact ((hfplusgplus.add (hfplusgminus.neg.1.sub hfminusgplus).1).1.add hfminusgminus).1
open BoundedInterval

/-- Exercise 11.4.2 -/
theorem IntegrableOn.split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
  generalize hcard : P.intervals.card = n
  revert I
  induction' n with n hn <;> intro I hf P hcard
  · rw [Finset.card_eq_zero] at hcard
    have hIe : (I:Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x hx
      obtain ⟨J, ⟨hJ, _⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [hcard] at hJ; simp at hJ
    rw [hcard, Finset.sum_empty]
    exact (integ_on_subsingleton (BoundedInterval.length_of_empty hIe)).2
  · by_cases hss : Subsingleton (I:Set ℝ)
    · have hI0 : |I|ₗ = 0 := BoundedInterval.length_of_subsingleton.mp hss
      rw [(integ_on_subsingleton hI0).2]
      symm; apply Finset.sum_eq_zero; intro J hJ
      have hJss : Subsingleton (J:Set ℝ) := by
        rw [Set.subsingleton_coe] at hss ⊢
        have hsub := P.contains J hJ; rw [BoundedInterval.subset_iff] at hsub
        exact hss.anti hsub
      exact (integ_on_subsingleton (BoundedInterval.length_of_subsingleton.mp hJss)).2
    · have hlt : I.a < I.b := by
        simp [BoundedInterval.length_of_subsingleton, BoundedInterval.length,
          -Set.subsingleton_coe] at hss
        exact hss
      obtain ⟨K, L, P', hK, hjoin, hP'⟩ := P.exists_peel hlt
      obtain ⟨hIL, _, hjeq⟩ := hf.join hjoin
      have hcardL : P'.intervals.card = n := by
        rw [hP', Finset.card_erase_of_mem hK]; omega
      have hLsum := hn hIL P' hcardL
      rw [hjeq, hLsum, hP', add_comm]
      exact Finset.add_sum_erase _ _ hK

open Classical in
/-- The converse of `IntegrableOn.join`: integrability on the two pieces of a join,
together with boundedness, gives integrability on the whole. -/
theorem IntegrableOn.combine {L K I: BoundedInterval} (hIJK: I.joins L K)
    {f: ℝ → ℝ} (hbI: BddOn f I) (hL: IntegrableOn f L) (hK: IntegrableOn f K) :
    IntegrableOn f I := by
  refine ⟨hbI, ?_⟩
  have hmemI : ∀ x ∈ (I:Set ℝ), x ∈ (L:Set ℝ) ∨ x ∈ (K:Set ℝ) := by
    intro x hx; rw [hIJK.2.1] at hx; exact hx
  have hdisj : ∀ x ∈ (K:Set ℝ), x ∉ (L:Set ℝ) := by
    intro x hxK hxL
    have : x ∈ (L:Set ℝ) ∩ (K:Set ℝ) := ⟨hxL, hxK⟩
    rw [hIJK.1] at this; exact this
  have hfuL : integ f L = upper_integral f L := rfl
  have hfuK : integ f K = upper_integral f K := rfl
  have hle : upper_integral f I ≤ lower_integral f I := by
    apply le_of_forall_pos_le_add; intro ε hε
    obtain ⟨gL, hgLmaj, hgLpc, hgLint⟩ := lt_of_gt_upper_integral hL.1 (X := integ f L + ε/4)
      (by rw [hfuL]; linarith)
    obtain ⟨gK, hgKmaj, hgKpc, hgKint⟩ := lt_of_gt_upper_integral hK.1 (X := integ f K + ε/4)
      (by rw [hfuK]; linarith)
    obtain ⟨hL', hL'min, hL'pc, hL'int⟩ := gt_of_lt_lower_integral hL.1 (X := integ f L - ε/4)
      (by rw [hfuL]; linarith [hL.2])
    obtain ⟨hK', hK'min, hK'pc, hK'int⟩ := gt_of_lt_lower_integral hK.1 (X := integ f K - ε/4)
      (by rw [hfuK]; linarith [hK.2])
    set g := fun x => if x ∈ (L:Set ℝ) then gL x else gK x with hgdef
    set h := fun x => if x ∈ (L:Set ℝ) then hL' x else hK' x with hhdef
    have hgL_eq : ∀ x ∈ (L:Set ℝ), g x = gL x := fun x hx => by simp only [hgdef, if_pos hx]
    have hgK_eq : ∀ x ∈ (K:Set ℝ), g x = gK x := fun x hx => by simp only [hgdef, if_neg (hdisj x hx)]
    have hhL_eq : ∀ x ∈ (L:Set ℝ), h x = hL' x := fun x hx => by simp only [hhdef, if_pos hx]
    have hhK_eq : ∀ x ∈ (K:Set ℝ), h x = hK' x := fun x hx => by simp only [hhdef, if_neg (hdisj x hx)]
    have hgpcI : PiecewiseConstantOn g I := (PiecewiseConstantOn.of_join hIJK g).mpr
      ⟨hgLpc.congr' (fun x hx => (hgL_eq x hx).symm), hgKpc.congr' (fun x hx => (hgK_eq x hx).symm)⟩
    have hhpcI : PiecewiseConstantOn h I := (PiecewiseConstantOn.of_join hIJK h).mpr
      ⟨hL'pc.congr' (fun x hx => (hhL_eq x hx).symm), hK'pc.congr' (fun x hx => (hhK_eq x hx).symm)⟩
    have hgmaj : MajorizesOn g f I := by
      intro x hx; rcases hmemI x hx with hxL | hxK
      · rw [hgL_eq x hxL]; exact hgLmaj x hxL
      · rw [hgK_eq x hxK]; exact hgKmaj x hxK
    have hhmin : MinorizesOn h f I := by
      intro x hx; rcases hmemI x hx with hxL | hxK
      · rw [hhL_eq x hxL]; exact hL'min x hxL
      · rw [hhK_eq x hxK]; exact hK'min x hxK
    have hupI := upper_integral_le_integ hbI hgmaj hgpcI
    have hlowI := integ_le_lower_integral hbI hhmin hhpcI
    rw [show hgpcI.integ' = PiecewiseConstantOn.integ g I from rfl,
      PiecewiseConstantOn.integ_of_join hIJK hgpcI,
      PiecewiseConstantOn.integ_congr hgL_eq, PiecewiseConstantOn.integ_congr hgK_eq] at hupI
    rw [show hhpcI.integ' = PiecewiseConstantOn.integ h I from rfl,
      PiecewiseConstantOn.integ_of_join hIJK hhpcI,
      PiecewiseConstantOn.integ_congr hhL_eq, PiecewiseConstantOn.integ_congr hhK_eq] at hlowI
    linarith [hgLint, hgKint, hL'int, hK'int]
  exact le_antisymm (lower_integral_le_upper hbI) hle

/-- Integrability on every piece of a partition (plus boundedness) implies integrability
on the whole interval. -/
theorem IntegrableOn.of_partition {I: BoundedInterval} {f: ℝ → ℝ} (hbI: BddOn f I)
    (P: Partition I) (hpieces: ∀ J ∈ P.intervals, IntegrableOn f J) : IntegrableOn f I := by
  generalize hcard : P.intervals.card = n
  revert I
  induction' n with n hn <;> intro I hbI P hpieces hcard
  · rw [Finset.card_eq_zero] at hcard
    have hIe : (I:Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x hx
      obtain ⟨J, ⟨hJ, _⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [hcard] at hJ; simp at hJ
    exact (integ_on_subsingleton (BoundedInterval.length_of_empty hIe)).1
  · by_cases hss : Subsingleton (I:Set ℝ)
    · exact (integ_on_subsingleton (BoundedInterval.length_of_subsingleton.mp hss)).1
    · have hlt : I.a < I.b := by
        simp [BoundedInterval.length_of_subsingleton, BoundedInterval.length,
          -Set.subsingleton_coe] at hss
        exact hss
      obtain ⟨K, L, P', hK, hjoin, hP'⟩ := P.exists_peel hlt
      have hbL : BddOn f L := by
        obtain ⟨M, hM⟩ := hbI
        refine ⟨M, fun x hx => hM x ?_⟩
        have hLI : (L:Set ℝ) ⊆ (I:Set ℝ) := by rw [hjoin.2.1]; exact Set.subset_union_left
        exact hLI hx
      have hcardL : P'.intervals.card = n := by rw [hP', Finset.card_erase_of_mem hK]; omega
      have hpiecesL : ∀ J ∈ P'.intervals, IntegrableOn f J := by
        intro J hJ; rw [hP'] at hJ; exact hpieces J (Finset.mem_of_mem_erase hJ)
      exact IntegrableOn.combine hjoin hbI (hn hbL P' hpiecesL hcardL) (hpieces K hK)

end Chapter11
