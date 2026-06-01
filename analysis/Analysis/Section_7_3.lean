import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Analysis.Section_6_1
import Analysis.Section_6_epilogue
import Analysis.Section_7_2

/-!
# Analysis I, Section 7.3: Sums of non-negative numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Equivalent characterizations of convergence of nonnegative series.
- Cauchy condensation test.

-/

namespace Chapter7

open Real

abbrev Series.nonneg (s: Series) : Prop := ∀ n, s.seq n ≥ 0

abbrev Series.partial_of_nonneg {s: Series} (h: s.nonneg) : Monotone s.partial := by
  intro N₁ N₂ hN
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hN)
  intro i _ _
  exact h i

/-- Proposition 7.3.1 -/
theorem Series.converges_of_nonneg_iff {s: Series} (h: s.nonneg) : s.converges ↔ ∃ M, ∀ N, s.partial N ≤ M := by
  -- This broadly follows the argument in the text, though for one direction I choose to use Mathlib routines rather than Chapter6 results.
  constructor
  . intro hconv
    set S : Chapter6.Sequence := ⟨ s.m, s.partial, by intro n hn; simp [Series.partial, hn] ⟩
    have : S.IsBounded := by
      apply S.bounded_of_convergent
      rw [Chapter6.Sequence.converges_iff_Tendsto']
      grind
    choose M hpos hM using this
    use M; peel hM with N hM
    exact (le_abs_self _).trans hM
  intro hbound
  obtain hinfin | hfin := tendsto_atTop_of_monotone (partial_of_nonneg h)
  . choose M hM using hbound
    choose N hN using (hinfin.eventually_gt_atTop M).exists
    grind
  assumption

theorem Series.sum_of_nonneg_lt {s: Series} (h: s.nonneg) {M:ℝ} (hM: ∀ N, s.partial N ≤ M) : s.sum ≤ M := by
  have : ∃ M, ∀ N, s.partial N ≤ M  := by use M
  rw [←converges_of_nonneg_iff h] at this; simp [sum, this]
  have hconv := this.choose_spec; simp [convergesTo] at hconv; exact le_of_tendsto' hconv hM

theorem Series.partial_le_sum_of_nonneg {s: Series} (hnon: s.nonneg) (hconv: s.converges) (N : ℤ) :
  s.partial N ≤ s.sum := by
  apply (partial_of_nonneg hnon).ge_of_tendsto
  simp [sum, hconv]; exact hconv.choose_spec

/-- Some useful nonnegativity lemmas for later applications. -/
theorem Series.partial_nonneg {s: Series} (hnon: s.nonneg) (N : ℤ) : 0 ≤ s.partial N := by
  simp [Series.partial]; apply Finset.sum_nonneg; aesop

theorem Series.sum_of_nonneg {s:Series} (hnon: s.nonneg) : 0 ≤ s.sum := by
  by_cases h: s.converges <;> simp [Series.sum, h]
  exact ge_of_tendsto' h.choose_spec (partial_nonneg hnon)

/-- Corollary 7.3.2 (Comparison test) / Exercise 7.3.1 -/
theorem Series.converges_of_le {s t: Series} (hm: s.m = t.m) (hcomp: ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hconv : t.converges) : s.absConverges ∧ |s.sum| ≤ s.abs.sum ∧ s.abs.sum ≤ t.sum := by
  have habsm : s.abs.m = s.m := rfl
  have htnn : t.nonneg := by
    intro n
    rcases le_or_gt s.m n with hn | hn
    · exact le_trans (abs_nonneg _) (hcomp n hn)
    · rw [t.vanish n (by rw [← hm]; exact hn)]
  have habsnn : s.abs.nonneg := by
    intro n
    rcases le_or_gt s.m n with hn | hn
    · rw [show s.abs.seq n = |s.seq n| from Series.eval_mk' _ hn]; positivity
    · rw [s.abs.vanish n (by rw [habsm]; exact hn)]
  have hpart : ∀ N:ℤ, s.abs.partial N ≤ t.partial N := by
    intro N
    unfold Series.partial
    rw [habsm, hm]
    apply Finset.sum_le_sum
    intro n hn; simp only [Finset.mem_Icc] at hn
    rw [show s.abs.seq n = |s.seq n| from Series.eval_mk' _ (by omega)]
    exact hcomp n (by omega)
  have hbound : ∀ N:ℤ, s.abs.partial N ≤ t.sum := fun N =>
    le_trans (hpart N) (partial_le_sum_of_nonneg htnn hconv N)
  have habsconv : s.absConverges := (converges_of_nonneg_iff habsnn).mpr ⟨t.sum, hbound⟩
  exact ⟨habsconv, abs_le habsconv, sum_of_nonneg_lt habsnn hbound⟩

theorem Series.diverges_of_ge {s t: Series} (hm: s.m = t.m) (hcomp: ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hdiv: ¬ s.absConverges) : t.diverges := by
  intro hconv
  exact hdiv (converges_of_le hm hcomp hconv).1

theorem Series.partial_coe_eq_range {a:ℕ → ℝ} (N:ℤ) (hN: 0 ≤ N) :
    (a:Series).partial N = ∑ k ∈ Finset.range (N.toNat + 1), a k := by
  induction N, hN using Int.le_induction with
  | base =>
    rw [show (0:ℤ).toNat + 1 = 1 from rfl, Finset.sum_range_one]
    unfold Series.partial
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact Series.eval_coe a 0
  | succ N hN ih =>
    have hm : (a:Series).m = 0 := rfl
    have hseq : (a:Series).seq (N+1) = a (N.toNat+1) := by
      rw [show N+1 = ((N.toNat+1:ℕ):ℤ) by omega, Series.eval_coe]
    rw [Series.partial_succ (a:Series) (by rw [hm]; omega), ih,
        show (N+1).toNat = N.toNat + 1 by omega, hseq, Finset.sum_range_succ a (N.toNat+1)]

/-- Lemma 7.3.3 (Geometric series) / Exercise 7.3.2 -/
theorem Series.converges_geom {x: ℝ} (hx: |x| < 1) : (fun n ↦ x ^ n : Series).convergesTo (1 / (1 - x)) := by
  unfold Series.convergesTo
  have hsum : Filter.Tendsto (fun M:ℕ => ∑ k ∈ Finset.range M, x^k) Filter.atTop (nhds (1-x)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])).tendsto_sum_nat
  have hshift : Filter.Tendsto (fun M:ℕ => M+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hg : Filter.Tendsto (fun M:ℕ => ∑ k ∈ Finset.range (M+1), x^k) Filter.atTop (nhds (1/(1-x))) := by
    rw [one_div]; exact hsum.comp hshift
  have htn : Filter.Tendsto (Int.toNat) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨(b:ℤ), fun a ha => by omega⟩)
  apply (hg.comp htn).congr'
  filter_upwards [Filter.eventually_ge_atTop (0:ℤ)] with N hN
  exact (Series.partial_coe_eq_range N hN).symm

theorem Series.absConverges_geom {x: ℝ} (hx: |x| < 1) : (fun n ↦ x ^ n : Series).absConverges := by
  have hpe : (fun n ↦ x ^ n : Series).abs.partial = ((fun n:ℕ ↦ |x|^n):Series).partial := by
    funext N
    unfold Series.partial
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ≥ 0
    · simp [Series.abs, Series.mk', Series.instCoe, hn, abs_pow]
    · simp [Series.abs, Series.mk', Series.instCoe, hn]
  refine ⟨1/(1-|x|), ?_⟩
  unfold Series.convergesTo
  rw [hpe]
  exact converges_geom (show |(|x|)| < 1 by rw [abs_abs]; exact hx)

theorem Series.diverges_geom {x: ℝ} (hx: |x| ≥ 1) : (fun n ↦ x ^ n : Series).diverges := by
  apply Series.diverges_of_nodecay
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have key := hN (max N 0) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero,
      show (max N 0:ℤ) = (((max N 0).toNat:ℕ):ℤ) by omega, Series.eval_coe, abs_pow] at key
  have : (1:ℝ) ≤ |x|^(max N 0).toNat := one_le_pow₀ hx
  linarith

theorem Series.converges_geom_iff (x: ℝ) : (fun n ↦ x ^ n : Series).converges ↔ |x| < 1 := by
  constructor
  · intro h
    by_contra hx
    push_neg at hx
    exact (diverges_geom hx) h
  · intro hx
    exact ⟨_, converges_geom hx⟩

/-- Proposition 7.3.4 (Cauchy criterion) -/
theorem Series.cauchy_criterion {s:Series} (hm: s.m = 1) (hs:s.nonneg) (hmono: ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n) : s.converges ↔ (fun k ↦ 2^k * s.seq (2^k): Series).converges := by
  -- This proof is written to follow the structure of the original text.
  set t := (fun k ↦ 2^k * s.seq (2^k):Series)
  have ht: t.nonneg := by intro n; by_cases h: n ≥ 0 <;> simp [t,h]; grind
  have hmono' : ∀ n ≥ 1, ∀ m ≥ n, s.seq m ≤ s.seq n := by
    intro n hn m hm; obtain ⟨ k, rfl ⟩ := Int.le.dest hm; clear hm
    induction' k with k hk; simp
    convert (hmono (n+k) (by grind)).trans hk using 2; grind
  have htm : t.m = 0 := by simp [t]
  rw [converges_of_nonneg_iff hs, converges_of_nonneg_iff ht]
  set S := s.partial
  set T := t.partial
  have Lemma_7_3_6 (K:ℕ) : S (2^(K+1) - 1) ≤ T K ∧ T K ≤ 2 * S (2^K) := by
    induction' K with K hK
    . simp [S,T,Series.partial, hm, t]; grind
    observe h2K : 1 ≤ 2^K; observe h2K' : 1 ≤ 2^(K+1)
    choose hK1 hK2 using hK
    have claim1 : T (K + 1) = T K + 2^(K+1) * s.seq (2^(K+1)) := by apply t.partial_succ; grind
    have claim2a : S (2^(K+1)) ≥ S (2^K) + 2^K * s.seq (2^(K+1)) := calc
      _ = S (2^K) + ∑ n ∈ .Ioc (2^K) (2^(K+1)), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^K)) (Finset.Ioc (2^K) (2^(K+1))) := by
          rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp at hx hy; linarith
        convert Finset.sum_union this
        ext x; simp; constructor
        . intro ⟨h1, h2⟩; simp [h1, h2, le_or_gt]
        rintro (⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩)
        . simp [h1,pow_succ']; linarith
        simp [h2, hm]; grind
      _ ≥ S (2^K) + ∑ n ∈ .Ioc ((2:ℤ)^K) (2^(K+1)), s.seq (2^(K+1)) := by
        gcongr with n hn; simp at hn; exact hmono' _ (by grind) _ hn.2
      _ = _ := by simp [pow_succ']; left; ring_nf; norm_cast
    have claim2 : 2 * S (2^(K+1)) ≥ 2 * S (2^K) + 2^(K+1) * s.seq (2^(K+1)) := by
      nth_rewrite 2 [pow_succ']; grind
    have claim3 : S (2^(K+1+1) - 1) ≤ S (2^(K+1)-1) + 2^(K+1) * s.seq (2^(K+1)) := calc
      _ = S (2^(K+1)-1) + ∑ n ∈ .Icc (2^(K+1)) (2^(K+1+1)-1), s.seq n := by
        have : Disjoint (Finset.Icc s.m (2^(K+1)-1)) (Finset.Icc (2^(K+1)) (2^(K+1+1)-1)) := by
          rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp at hx hy; linarith
        convert Finset.sum_union this
        ext; simp; constructor
        . intro ⟨h1, h2⟩; simp [h1, h2]; omega
        rintro (⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩)
        . simp [h1, pow_succ' _ (K+1)]; linarith
        simp [h2, hm]; linarith
      _ ≤ S (2^(K+1)-1) + ∑ n ∈ .Icc ((2:ℤ)^(K+1)) (2^(K+1+1)-1), s.seq (2^(K+1)) := by
        gcongr with n hn; simp at hn; apply hmono' _ _ _ hn.1; linarith
      _ = _ := by simp [pow_succ']; left; ring_nf; norm_cast
    simp; constructor <;> grind
  constructor
  . intro ⟨ M, hM ⟩; use 2*M; intro N; obtain hN | hN := lt_or_ge N 0
    . simp [T, Series.partial, htm, hN]; convert hM 0; simp [S, Series.partial, hm]
    rw [Int.eq_natCast_toNat.mpr hN]; apply (Lemma_7_3_6 N.toNat).2.trans; grind
  intro ⟨ M, hM ⟩; use M; intro K'; obtain hK' | hK' := lt_or_ge K' 1
  . simp [S, Series.partial, hm, hK']; convert hM (-1)
  set K := (K'-1).toNat; have hK : K' = K + 1 := by rw [Int.toNat_of_nonneg (by linarith)]; abel
  calc
    _ ≤ S (2 ^ (K+1) - 1) := by
      apply partial_of_nonneg hs; rw [hK]
      generalize K = n; induction' n with n hn; simp
      simp [pow_succ] at *; linarith
    _ ≤ T K := (Lemma_7_3_6 K).1
    _ ≤ M := hM K

/-- Corollary 7.3.7 -/
theorem Series.converges_qseries (q: ℝ) (hq: q > 0) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).converges ↔ (q>1) := by
  -- This proof is written to follow the structure of the original text.
  set s := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series)
  have hs : s.nonneg := by intro n; simp [s]; by_cases h : 1 ≤ n <;> simp [h]; positivity
  have hmono : ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n := by
    intro n hn
    have hn1 : n ≥ 0 := by positivity
    have hn3 : n.toNat > 0 := by omega
    simp [s, hn, hn1]
    apply_rules [inv_anti₀, rpow_le_rpow] <;> try positivity
    simp
  rw [cauchy_criterion (by simp [s]) hs hmono]
  have (n:ℕ) : 2^n * s.seq (2^n) = (2^(1-q))^n := by
    have : 1 ≤ (2:ℤ)^n := by norm_cast; exact Nat.one_le_two_pow
    simp [s, this]
    rw [←rpow_neg, mul_comm, ←rpow_add_one, rpow_pow_comm] <;> (try positivity); grind
  simp [this, converges_geom_iff]
  rw [abs_of_nonneg, rpow_lt_one_iff_of_pos] <;> try positivity
  simp

/-- Remark 7.3.8 -/
theorem Series.zeta_eq {q:ℝ} (hq: q > 1) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).sum = riemannZeta q := by
  -- `riemannZeta` is defined over the complex numbers, so some preliminary work is needed to specialize to the reals.
  set L := ∑' n:ℕ, 1 / (n+1:ℝ)^q
  have hL : L = riemannZeta q := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_cast)]
    convert Complex.ofReal_tsum _ with n
    simp [Complex.ofReal_cpow (x := n+1) (by positivity) _]
  rw [←hL]
  norm_cast; apply sum_of_converges
  have : Summable (fun (n : ℕ)↦ 1 / (n+1:ℝ) ^ q) := by
    convert (summable_one_div_nat_add_rpow 1 q).mpr hq using 4 with n
    rw [abs_of_nonneg]; positivity
  have tail (a: ℤ → ℝ) (L:ℝ) : Filter.atTop.Tendsto a (nhds L) ↔ Filter.atTop.Tendsto (fun n:ℕ ↦ a n) (nhds L) := by
    convert Filter.tendsto_map'_iff (g:= fun n:ℕ ↦ (n:ℤ) )
    simp
  unfold convergesTo
  rw [tail _ L]
  convert Summable.tendsto_sum_tsum_nat this with n
  simp [Series.partial]
  set e : ℕ ↪ ℤ := {
    toFun n := n+1
    inj' _ _ _ := by grind
  }
  convert Finset.sum_map _ e _ using 2 with n _ m hm
  . ext x; simp [e]; constructor
    . intro ⟨ _, _ ⟩; use (x-1).toNat; omega
    grind
  simp [e]

theorem Series.Basel_problem :  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ 2 : Series).sum = Real.pi ^ 2 / 6 := by
  have := zeta_eq (show 2 > 1 by norm_num)
  simp [Complex.ofReal_ofNat, riemannZeta_two] at this
  simpa [←Complex.ofReal_inj]

/-- Exercise 7.3.3 -/
theorem Series.nonneg_sum_zero {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges) : (a:Series).sum = 0 ↔ ∀ n, a n = 0 := by sorry


end Chapter7
