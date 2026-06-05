import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  intro ε hε
  set a : Sequence := ((fun (_:ℕ) ↦ c) : Sequence)
  refine ⟨0, le_refl _, ?_⟩
  intro n hn
  have hn' : n ≥ (0:ℤ) := by
    have : (a.from 0).m = max 0 0 := rfl
    omega
  show dist ((a.from 0) n) c ≤ ε
  rw [a.from_eval hn']
  simp only [a, Sequence.instCoeFun, Sequence.ofNatFun, hn']
  simp [dist_self]
  linarith

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha' using 1; rw [ih.2]; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h
    · simp
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
      convert Real.rpow_one _; field_simp; push_cast; ring
    · simp
  simp [lim_eq, ha', eq_zero_of_pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  have hmath := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
  rw [Metric.tendsto_atTop] at hmath
  obtain ⟨N, hN⟩ := hmath ε hε
  refine ⟨(N:ℤ), fun n hn => ?_⟩
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hn
  rw [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe]
  have hd := hN n.toNat (by omega)
  rw [Real.dist_eq, sub_zero] at hd
  rw [sub_zero]
  exact le_of_lt hd

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  subst hx; simp; exact lim_of_const 1

/-- A sequence whose absolute value diverges to `+∞` is divergent in the book's sense. -/
private theorem Sequence.divergent_of_abs_atTop {f:ℕ→ℝ}
    (h: Filter.Tendsto (fun n => |f n|) Filter.atTop Filter.atTop) :
    ((fun n => f n):Sequence).Divergent := by
  rw [Sequence.divergent_def]
  intro hconv
  obtain ⟨M, _, hbound⟩ := bounded_of_convergent hconv
  rw [Sequence.boundedBy_def] at hbound
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h (M+1)
  have hb := hbound ((N:ℤ))
  rw [Sequence.eval_coe] at hb
  have hf := hN N (le_refl N)
  linarith

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  rcases hx with rfl | hx
  · -- x = -1: the sequence oscillates between 1 and -1
    rw [Sequence.divergent_def]
    rintro ⟨L, hL⟩
    rw [Sequence.tendsTo_iff] at hL
    obtain ⟨N, hN⟩ := hL (1/2) (by norm_num)
    have e1 := hN (2 * (N.toNat:ℤ)) (by have := Int.self_le_toNat N; omega)
    have e2 := hN (2 * (N.toNat:ℤ) + 1) (by have := Int.self_le_toNat N; omega)
    rw [show (2 * (N.toNat:ℤ)) = ((2 * N.toNat:ℕ):ℤ) by push_cast; ring, Sequence.eval_coe] at e1
    rw [show (2 * (N.toNat:ℤ) + 1) = ((2 * N.toNat + 1:ℕ):ℤ) by push_cast; ring,
      Sequence.eval_coe] at e2
    rw [show ((-1:ℝ))^(2 * N.toNat) = 1 from (even_two_mul N.toNat).neg_one_pow] at e1
    rw [show ((-1:ℝ))^(2 * N.toNat + 1) = -1 from (odd_two_mul_add_one N.toNat).neg_one_pow] at e2
    rw [abs_le] at e1 e2
    linarith [e1.1, e1.2, e2.1, e2.2]
  · -- |x| > 1: the absolute values diverge to +∞
    apply Sequence.divergent_of_abs_atTop
    have hpow : Filter.Tendsto (fun n:ℕ => |x|^n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hx
    simpa [abs_pow] using hpow

/-- Bridge from Mathlib's `Filter.atTop` convergence to the book's `Sequence.TendsTo`. -/
private theorem Sequence.tendsTo_of_filter {f:ℕ→ℝ} {L:ℝ}
    (h: Filter.Tendsto f Filter.atTop (nhds L)) : ((fun n => f n):Sequence).TendsTo L := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨(N:ℤ), fun n hn => ?_⟩
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hn
  rw [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe]
  have hd := hN n.toNat (by omega)
  rw [Real.dist_eq] at hd
  exact le_of_lt hd

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  apply Sequence.tendsTo_of_filter
  have hexp : Filter.Tendsto (fun n:ℕ => 1/((n:ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousAt (fun y:ℝ => x^y) 0 := Real.continuousAt_const_rpow (ne_of_gt hx)
  have hcomp := hcont.tendsto.comp hexp
  rw [Real.rpow_zero] at hcomp
  exact hcomp

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  apply Sequence.tendsTo_of_filter
  have hbase : Filter.Tendsto (fun n:ℕ => ((n:ℝ)+1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun n:ℕ => ((n:ℝ)+1)^(q:ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by exact_mod_cast hq)).comp hbase
  have hinv := hpow.inv_tendsto_atTop
  simp only [← one_div] at hinv
  exact hinv

/-- A sequence diverging to `+∞` (in Mathlib's sense) is divergent in the book's sense. -/
private theorem Sequence.divergent_of_filter_atTop {f:ℕ→ℝ}
    (h: Filter.Tendsto f Filter.atTop Filter.atTop) : ((fun n => f n):Sequence).Divergent := by
  rw [Sequence.divergent_def]
  intro hconv
  obtain ⟨M, _, hbound⟩ := bounded_of_convergent hconv
  rw [Sequence.boundedBy_def] at hbound
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h (M+1)
  have hb := hbound ((N:ℤ))
  rw [Sequence.eval_coe] at hb
  have hf := hN N (le_refl N)
  have : f N ≤ M := le_trans (le_abs_self _) hb
  linarith

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  apply Sequence.divergent_of_filter_atTop
  have hbase : Filter.Tendsto (fun n:ℕ => ((n:ℝ)+1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_atTop (by exact_mod_cast hq)).comp hbase

end Chapter6
