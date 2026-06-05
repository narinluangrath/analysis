import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

open Filter Real EReal

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]; exact le_top
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
    set s : Series := (Series.mk' (m:=1) fun n ↦ 1 / ((n:ℤ):ℝ)^(1:ℝ)) with hs
    refine ⟨s, ?_, ?_⟩
    · have hg : atTop.Tendsto (fun x:ℝ ↦ (x^(1/x))⁻¹) (nhds 1) := by
        have := tendsto_rpow_div.inv₀ (by norm_num); simpa using this
      have hgz : atTop.Tendsto (fun n:ℤ ↦ ((n:ℝ)^(1/(n:ℝ)))⁻¹) (nhds 1) :=
        hg.comp tendsto_intCast_atTop_atTop
      apply hgz.congr'
      filter_upwards [eventually_ge_atTop (1:ℤ)] with n hn
      have h1 : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      have hpos : (0:ℝ) < n := by linarith
      have hseq : s.seq n = 1 / ((n:ℤ):ℝ)^(1:ℝ) := Series.eval_mk' _ hn
      simp only [hseq, Real.rpow_one, one_div]
      rw [abs_of_pos (by positivity), ← Real.inv_rpow (le_of_lt hpos)]
    · rw [Series.diverges, Series.converges_qseries 1 (by norm_num)]; norm_num

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
    set s : Series := (Series.mk' (m:=1) fun n ↦ 1 / ((n:ℤ):ℝ)^(2:ℝ)) with hs
    refine ⟨s, ?_, ?_⟩
    · have hg : atTop.Tendsto (fun x:ℝ ↦ ((x^(1/x))⁻¹)^(2:ℕ)) (nhds 1) := by
        have h0 : atTop.Tendsto (fun x:ℝ ↦ (x^(1/x))⁻¹) (nhds 1) := by
          have := tendsto_rpow_div.inv₀ (by norm_num); simpa using this
        have := h0.pow 2; simpa using this
      have hgz : atTop.Tendsto (fun n:ℤ ↦ (((n:ℝ)^(1/(n:ℝ)))⁻¹)^(2:ℕ)) (nhds 1) :=
        hg.comp tendsto_intCast_atTop_atTop
      apply hgz.congr'
      filter_upwards [eventually_ge_atTop (1:ℤ)] with n hn
      have h1 : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      have hpos : (0:ℝ) < n := by linarith
      have hseq : s.seq n = 1 / ((n:ℤ):ℝ)^(2:ℝ) := Series.eval_mk' _ hn
      simp only [hseq, one_div]
      have hn0 : (0:ℝ) ≤ (n:ℝ) := le_of_lt hpos
      rw [abs_of_pos (by positivity)]
      rw [← Real.rpow_natCast (((n:ℝ) ^ ((n:ℝ))⁻¹)⁻¹) 2]
      rw [Real.inv_rpow (by positivity), Real.inv_rpow (by positivity)]
      rw [← Real.rpow_mul hn0, ← Real.rpow_mul hn0]
      congr 1; push_cast; ring
    · have hconv : s.converges := (Series.converges_qseries 2 (by norm_num)).mpr (by norm_num)
      refine (Series.converges_of_le (s:=s) (t:=s) rfl ?_ hconv).1
      intro n hn
      have hm : s.m = 1 := rfl
      rw [hm] at hn
      rw [Series.eval_mk' _ hn, abs_of_nonneg (by positivity)]

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  · -- First conjunct: liminf (c(n+1)/cn) ≤ liminf (cn^(1/n))
    set M' := liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop with hM'def
    -- the root liminf is ≥ 0
    have hrootnn : (0:EReal) ≤ liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) .atTop := by
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [eventually_ge_atTop m] with n hn
      have := hpos n hn; positivity
    apply le_of_forall_lt_imp_le_of_dense
    intro z hz
    -- if z ≤ 0, done by nonnegativity
    rcases le_or_gt z 0 with hz0 | hz0
    · exact le_trans (by exact_mod_cast hz0) hrootnn
    -- now 0 < z < M', and z is a real (z ≠ ⊤ since z < M' ≤ ⊤... but z could be ⊥? no, z>0)
    have hztop : z ≠ ⊤ := by
      intro h; rw [h] at hz; exact absurd hz (not_top_lt)
    have hzbot : z ≠ ⊥ := by intro h; rw [h] at hz0; exact absurd hz0 (by simp)
    set y := z.toReal with hydef
    have hzy : z = (y:EReal) := (coe_toReal hztop hzbot).symm
    have hypos : 0 < y := by rw [hzy] at hz0; exact_mod_cast hz0
    rw [hzy] at hz ⊢
    -- eventually c(n+1)/cn > y
    have hevent := eventually_lt_of_lt_liminf hz (by isBoundedDefault)
    rw [eventually_atTop] at hevent; choose N' hN using hevent
    set N := max N' (max m 1) with hNdef
    have hge (n:ℤ) (hn: n ≥ N) : y ≤ c (n+1) / c n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this; norm_cast at hN; order
    set B := c N * y^(-N) with hBdef
    have hB : 0 < B := by have := hpos N (by omega); positivity
    have hlow (n:ℤ) (hn: n ≥ N) : B * y^n ≤ c n := by
      induction n, hn using Int.le_induction with
      | base =>
          have : B * y^N = c N := by
            rw [hBdef, mul_assoc, ← zpow_add₀ (ne_of_gt hypos)]; simp
          rw [this]
      | succ k hk ih =>
        have hck : 0 < c k := hpos k (by omega)
        have hstep := hge k (by omega)
        rw [le_div_iff₀ hck] at hstep
        calc B * y^(k+1) = (B * y^k) * y := by rw [zpow_add_one₀ (ne_of_gt hypos), ← mul_assoc]
          _ ≤ c k * y := by apply mul_le_mul_of_nonneg_right ih (le_of_lt hypos)
          _ ≤ c (k+1) := by linarith
    have hlow_root (n:ℤ) (hn: n ≥ N) : ((B^(1/(n:ℝ)) * y:ℝ):EReal) ≤ (((c n)^(1/(n:ℝ)):ℝ):EReal) := by
      rw [EReal.coe_le_coe_iff]
      have hn' : n > 0 := by omega
      calc B^(1/(n:ℝ)) * y = B^(1/(n:ℝ)) * ((y^n)^(1/(n:ℝ))) := by
              congr 1
              rw [←rpow_intCast, ←rpow_mul (by positivity)]
              symm; convert rpow_one _; field_simp
        _ = (B * y^n)^(1/(n:ℝ)) := (mul_rpow (by positivity) (by positivity)).symm
        _ ≤ ((c n)^(1/(n:ℝ))) := by
            apply rpow_le_rpow (by positivity) (hlow n hn) (by positivity)
    -- take liminf
    calc (y:EReal)
        = (atTop.liminf (fun n:ℤ ↦ ((B^(1/(n:ℝ)):ℝ):EReal))) * (atTop.liminf (fun n:ℤ ↦ ((y:ℝ):EReal))) := by
          have h1 : atTop.liminf (fun n:ℤ ↦ ((B^(1/(n:ℝ)):ℝ):EReal)) = 1 := by
            apply Tendsto.liminf_eq
            have hr : atTop.Tendsto (fun n:ℤ ↦ (B^(1/(n:ℝ)):ℝ)) (nhds 1) := by
              have hbase : Tendsto (fun x:ℝ ↦ B^x) (nhds (0:ℝ)) (nhds (B^(0:ℝ))) :=
                (continuous_const_rpow (ne_of_gt hB)).tendsto 0
              rw [Real.rpow_zero] at hbase
              have hz : atTop.Tendsto (fun n:ℤ ↦ (1/(n:ℝ))) (nhds 0) := by
                simpa [one_div] using tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop
              exact hbase.comp hz
            have := (continuous_coe_real_ereal.tendsto (1:ℝ)).comp hr
            simpa using this
          have h2 : atTop.liminf (fun n:ℤ ↦ ((y:ℝ):EReal)) = (y:EReal) := liminf_const _
          rw [h1, h2, one_mul]
      _ ≤ atTop.liminf (fun n:ℤ ↦ ((B^(1/(n:ℝ)) * y:ℝ):EReal)) := by
          have hu : (fun _:ℤ ↦ (0:EReal)) ≤ᶠ[atTop] fun n:ℤ ↦ ((B^(1/(n:ℝ)):ℝ):EReal) := by
            apply Eventually.of_forall; intro n; simp; positivity
          have hv : (fun _:ℤ ↦ (0:EReal)) ≤ᶠ[atTop] fun n:ℤ ↦ ((y:ℝ):EReal) := by
            apply Eventually.of_forall; intro n; simp; positivity
          refine le_trans (EReal.le_liminf_mul hu hv) (le_of_eq ?_)
          apply liminf_congr
          apply Eventually.of_forall; intro n
          simp only [Pi.mul_apply]; rw [EReal.coe_mul]
      _ ≤ atTop.liminf (fun n:ℤ ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) := by
          apply liminf_le_liminf <;> try isBoundedDefault
          rw [eventually_atTop]; use N
  set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
  by_cases hL : L' = ⊤; · rw [hL]; exact le_top
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by
    intro h; rw [h] at hL'pos; exact absurd hL'pos (by simp)
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; · simp [hy']; exact le_top
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have hLε : 0 < L+ε := by linarith
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    induction n, hn using Int.le_induction with
    | base =>
        have : A * (L+ε)^N = c N := by
          simp [A]; field_simp
        rw [this]
    | succ k hk ih =>
      have hck : 0 < c k := hpos k (by omega)
      have hstep := this k (by omega)
      rw [div_le_iff₀ hck] at hstep
      calc c (k+1) ≤ c k * (L+ε) := by linarith
        _ ≤ (A * (L+ε)^k) * (L+ε) := by
            apply mul_le_mul_of_nonneg_right ih (le_of_lt hLε)
        _ = A * (L+ε)^(k+1) := by rw [mul_assoc, ←zpow_add_one₀ (ne_of_gt hLε)]
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp
  calc
    _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε:ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
    set s : Series := (Series.mk' (m:=1) fun n ↦ 1 / ((n:ℤ):ℝ)^(1:ℝ)) with hs
    have hm : s.m = 1 := rfl
    have hg : atTop.Tendsto (fun n:ℤ ↦ (n:ℝ)/((n:ℝ)+1)) (nhds 1) := by
      have hr : atTop.Tendsto (fun x:ℝ ↦ x/(x+1)) (nhds 1) := by
        have h2 : atTop.Tendsto (fun x:ℝ ↦ 1 - (x+1)⁻¹) (nhds (1-0)) := by
          apply Tendsto.const_sub
          apply Tendsto.comp tendsto_inv_atTop_zero
          apply tendsto_atTop_add_const_right _ 1 tendsto_id
        simp only [sub_zero] at h2
        apply h2.congr'
        filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        have : (0:ℝ) < x+1 := by linarith
        field_simp; ring
      exact hr.comp tendsto_intCast_atTop_atTop
    refine ⟨s, ?_, ?_, ?_⟩
    · intro n hn; rw [hm] at hn; rw [Series.eval_mk' _ hn, Real.rpow_one]
      have : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      positivity
    · apply hg.congr'
      filter_upwards [eventually_ge_atTop (1:ℤ)] with n hn
      have h1 : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      rw [Series.eval_mk' _ (by rw [hm]; omega : (n:ℤ)+1 ≥ s.m),
          Series.eval_mk' _ (by rw [hm]; omega : (n:ℤ) ≥ s.m)]
      push_cast
      rw [Real.rpow_one, Real.rpow_one]
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      have : (0:ℝ) < (n:ℝ) := by linarith
      have : (0:ℝ) < (n:ℝ)+1 := by linarith
      field_simp
    · rw [Series.diverges, Series.converges_qseries 1 (by norm_num)]; norm_num

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
    set s : Series := (Series.mk' (m:=1) fun n ↦ 1 / ((n:ℤ):ℝ)^(2:ℝ)) with hs
    have hm : s.m = 1 := rfl
    have hg : atTop.Tendsto (fun n:ℤ ↦ ((n:ℝ)/((n:ℝ)+1))^(2:ℕ)) (nhds 1) := by
      have hr : atTop.Tendsto (fun x:ℝ ↦ x/(x+1)) (nhds 1) := by
        have h2 : atTop.Tendsto (fun x:ℝ ↦ 1 - (x+1)⁻¹) (nhds (1-0)) := by
          apply Tendsto.const_sub
          apply Tendsto.comp tendsto_inv_atTop_zero
          apply tendsto_atTop_add_const_right _ 1 tendsto_id
        simp only [sub_zero] at h2
        apply h2.congr'
        filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        have : (0:ℝ) < x+1 := by linarith
        field_simp; ring
      have := (hr.comp tendsto_intCast_atTop_atTop).pow 2
      simpa using this
    refine ⟨s, ?_, ?_, ?_⟩
    · intro n hn; rw [hm] at hn; rw [Series.eval_mk' _ hn]
      have : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      positivity
    · apply hg.congr'
      filter_upwards [eventually_ge_atTop (1:ℤ)] with n hn
      have h1 : (n:ℝ) ≥ 1 := by exact_mod_cast hn
      rw [Series.eval_mk' _ (by rw [hm]; omega : (n:ℤ)+1 ≥ s.m),
          Series.eval_mk' _ (by rw [hm]; omega : (n:ℤ) ≥ s.m)]
      push_cast
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hn1 : (0:ℝ) < (n:ℝ)+1 := by linarith
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      rw [Real.rpow_two, Real.rpow_two]
      field_simp
    · have hconv : s.converges := (Series.converges_qseries 2 (by norm_num)).mpr (by norm_num)
      refine (Series.converges_of_le (s:=s) (t:=s) rfl ?_ hconv).1
      intro n hn
      rw [hm] at hn
      rw [Series.eval_mk' _ hn, abs_of_nonneg (by positivity)]

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) :=
  tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

private theorem root_aux (x:ℝ)(q:ℝ)(k:ℕ)(hk:(0:ℝ)<(k:ℝ)) :
    |(k:ℝ)^q * x^k|^(1/(k:ℝ)) = (k:ℝ)^(q/(k:ℝ)) * |x| := by
  rw [show |(k:ℝ)^q * x^k| = (k:ℝ)^q * |x|^k by
        rw [_root_.abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)^q), _root_.abs_pow]]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  · rw [← Real.rpow_mul (le_of_lt hk)]; congr 1; field_simp
  · rw [← Real.rpow_natCast (|x|) k, ← Real.rpow_mul (abs_nonneg x)]
    rw [show (k:ℝ) * (1/(k:ℝ)) = 1 by field_simp, Real.rpow_one]

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  set s : Series := (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series) with hsdef
  have hsm : s.m = 0 := rfl
  -- The root function n ↦ |s.seq n|^(1/n) tends to |x| over ℤ
  have htend_root : atTop.Tendsto (fun n:ℤ ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ))) (nhds |x|) := by
    -- compute n^(q/n) → 1
    have hroot1 : atTop.Tendsto (fun n:ℤ ↦ ((n:ℝ)^(q/(n:ℝ)))) (nhds 1) := by
      have := tendsto_rpow_div_mul_add q 1 0 zero_ne_one
      have h2 : atTop.Tendsto (fun x:ℝ ↦ x^(q/x)) (nhds 1) := by
        apply this.congr; intro x; congr 1; ring
      exact h2.comp tendsto_intCast_atTop_atTop
    have hlim : atTop.Tendsto (fun n:ℤ ↦ ((n:ℝ)^(q/(n:ℝ)) * |x|)) (nhds (1 * |x|)) :=
      hroot1.mul_const _
    rw [one_mul] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1:ℤ)] with n hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have hseq : s.seq n = (n.toNat:ℝ)^q * x^(n.toNat) := by
      simp only [hsdef]; simp [show (0:ℤ) ≤ n by omega]
    have htn : ((n.toNat:ℝ)) = (n:ℝ) := by
      rw [show ((n.toNat:ℝ)) = (((n.toNat:ℤ)):ℝ) by push_cast; ring, Int.toNat_of_nonneg (by omega)]
    rw [hseq, ← htn, root_aux x q n.toNat (by rw [htn]; exact hnpos)]
  -- absConverges via root test
  have habs : s.absConverges := by
    apply Series.root_test_pos
    have htE : atTop.Tendsto (fun n:ℤ ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) (nhds ((|x|:ℝ):EReal)) :=
      (continuous_coe_real_ereal.tendsto (|x|:ℝ)).comp htend_root
    rw [htE.limsup_eq]
    rw [show (1:EReal) = ((1:ℝ):EReal) by simp, EReal.coe_lt_coe_iff]
    exact hx
  refine ⟨ converges_of_absConverges habs, ?_ ⟩
  have hdecay := decay_of_converges (converges_of_absConverges habs)
  have := hdecay.comp tendsto_natCast_atTop_atTop
  apply this.congr
  intro n; simp [hsdef]

end Chapter7
