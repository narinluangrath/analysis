import Mathlib.Tactic
import Analysis.Appendix_B_1

/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

An implementation of the decimal representation of Mathlib's real numbers {lean}`ℝ`.

This is separate from the way decimal numerals are already represented in Mathlib.  We also represent the integer part of the natural numbers just by {lean}`ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the {name}`AppendixB.Digit` class.
-/

namespace AppendixB

structure NNRealDecimal where
  intPart : ℕ
  fracPart : ℕ → Digit

open NNReal NNRealDecimal

#check mk

@[coe]
noncomputable def NNRealDecimal.toNNReal (d:NNRealDecimal) : NNReal :=
  d.intPart + ∑' i, (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ)

noncomputable instance NNRealDecimal.instCoeNNReal : Coe NNRealDecimal NNReal where
  coe := toNNReal

/-- Exercise B.2.1 -/
theorem NNRealDecimal.toNNReal_conv (d:NNRealDecimal) :
  Summable fun i ↦ (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ) := by
  rw [← NNReal.summable_coe]
  have hgeo : Summable (fun i:ℕ ↦ (9/10:ℝ) * (1/10)^i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hgeo
  push_cast [NNReal.coe_rpow]
  have h9 : ((d.fracPart i : ℕ):ℝ) ≤ 9 := by
    have hlt := (d.fracPart i).lt
    have : (d.fracPart i : ℕ) ≤ 9 := by omega
    exact_mod_cast this
  have hrw : (10:ℝ)^(-(i:ℝ)-1) = (1/10)^(i+1) := by
    rw [show -(i:ℝ)-1 = -((i+1:ℕ):ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
      Real.rpow_natCast, ← inv_pow, one_div]
  rw [hrw, pow_succ]
  have hpos : (0:ℝ) ≤ (1/10)^i := by positivity
  nlinarith [h9, hpos]

theorem NNRealDecimal.surj (x:NNReal) : ∃ d:NNRealDecimal, x = d := by
  -- This proof is written to follow the structure of the original text.
  by_cases h : x = 0
  . use mk 0 fun _ ↦ 0; simp [h, toNNReal]
  let s : ℕ → ℕ := fun n ↦ ⌊ x * 10^n ⌋₊
  have hs (n:ℕ) : s n ≤ x * 10^n := Nat.floor_le (by positivity)
  have hs' (n:ℕ) : x * 10^n < s n + 1 := Nat.lt_floor_add_one _
  have hdigit (n:ℕ) : ∃ a:Digit, s (n+1) = 10 * s n + (a:ℕ) := by
    have hl : (10:NNReal) * s n < s (n+1) + 1 := calc
      _ ≤ 10 * (x * 10^n) := by gcongr; grind
      _ = x * 10^(n+1) := by ring_nf
      _ < _ := hs' _
    have hu : s (n+1) < (10:NNReal) * s n + 10 := calc
      _ ≤ x * 10^(n+1) := hs (n+1)
      _ = 10 * (x * 10^n) := by ring_nf
      _ < 10 * (s n + 1) := by gcongr; grind
      _ = _ := by ring
    norm_cast at hl hu
    set d := s (n+1) - 10 * s n
    have hd : d < 10 := by omega
    have : s (n+1) = 10 * s n + d := by omega
    use Digit.mk hd
  choose a ha using hdigit
  set d := mk (s 0) a; use d
  have hsum (n:ℕ) : s n * (10:NNReal)^(-n:ℝ) = s 0 + ∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) := by
    induction' n with n hn; simp
    rw [ha n]; calc
      _ = s n * (10:NNReal)^(-n:ℝ) + a n * 10^(-n-1:ℝ) := by
        simp [add_mul]; ring_nf; congr 1
        rw [mul_assoc, ←rpow_add_one]; ring_nf; norm_num
      _ = s 0 + (∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) + a n * 10^(-n-1:ℝ)) := by grind
      _ = _ := by congr; symm; apply Finset.sum_range_succ
  have := (d.toNNReal_conv.tendsto_sum_tsum_nat).const_add (s 0:NNReal)
  convert_to Filter.atTop.Tendsto (fun n ↦ s n * (10:NNReal)^(-n:ℝ)) (nhds (d:NNReal)) at this
  . ext n; rw [hsum n]
  apply tendsto_nhds_unique _ this
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ x - (10:NNReal)^(-n:ℝ)) (h := fun _ ↦ x)
  . convert Filter.Tendsto.const_sub (c := 0) x _
    . simp
    convert tendsto_pow_atTop_nhds_zero_of_lt_one (?_:(1/10:NNReal) < 1) with n
    . rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]
    apply div_lt_one_of_lt; bound
  . exact tendsto_const_nhds
  . intro n; simp; calc
    _ = (x * 10^n) * (10:NNReal)^(-n:ℝ) := by
      rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num
    _ ≤ ((s n:NNReal) + 1)*(10:NNReal)^(-n:ℝ) := by gcongr; grind [le_of_lt]
    _ = _ := by ring
  intro n; simp; calc
    _ ≤ (x * 10^n) * (10:NNReal)^(-n:ℝ) := by gcongr; grind
    _ = x := by rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num

/-- Proposition B.2.2 -/
theorem NNRealDecimal.not_inj : (1:NNReal) = (mk 1 fun _ ↦ 0) ∧ (1:NNReal) = (mk 0 fun _ ↦ 9) := by
  -- This proof is written to follow the structure of the original text.
  simp [toNNReal]
  have := (mk 0 fun _ ↦ 9).toNNReal_conv.tendsto_sum_tsum_nat
  simp at this
  apply tendsto_nhds_unique _ this
  convert_to Filter.atTop.Tendsto (fun n:ℕ ↦ 1 - (10:NNReal)^(-n:ℝ)) (nhds 1) using 2 with n
  . induction' n with n hn
    . simp
    rw [Finset.sum_range_succ, hn, Nat.cast_add, Nat.cast_one, neg_add']
    have : (10:NNReal)^(-n:ℝ) = 10^(-n-1:ℝ) * 10 := by
      rw [←rpow_add_one]; simp; norm_num
    simp [this, ←coe_inj]
    rw [NNReal.coe_sub, NNReal.coe_sub]
    . suffices h : ∀ c a : ℝ, c = 9 → 1 - a * 10 + c * a = 1 - a by apply h; norm_cast
      grind
    . apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith
    rw [←rpow_add_one]
    apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith; norm_num
  convert Filter.Tendsto.const_sub (f := fun n:ℕ ↦ (10:NNReal)^(-n:ℝ)) (c := 0) 1 _; simp
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (show (1/10:NNReal) < 1 by bound) with n
  rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]

inductive RealDecimal where
  | pos : NNRealDecimal → RealDecimal
  | neg : NNRealDecimal → RealDecimal

noncomputable instance RealDecimal.instCoeReal : Coe RealDecimal ℝ where
  coe := fun d ↦ match d with
    | RealDecimal.pos d => d.toNNReal
    | RealDecimal.neg d => -(d.toNNReal:ℝ)

theorem RealDecimal.surj (x:ℝ) : ∃ d:RealDecimal, x = d := by
  obtain h | h := le_or_gt 0 x
  . choose d hd using NNRealDecimal.surj (x.toNNReal); use pos d; simp [←hd, h]
  . choose d hd using NNRealDecimal.surj ((-x).toNNReal); use neg d; simp [←hd, show 0 ≤ -x by linarith]

/-- The natural-number truncation of a decimal expansion to `n` fractional digits. -/
noncomputable def NNRealDecimal.trunc (e:NNRealDecimal) (n:ℕ) : ℕ :=
  e.intPart * 10^n + ∑ i ∈ Finset.range n, (e.fracPart i:ℕ) * 10^(n-1-i)

theorem NNRealDecimal.trunc_zero (e:NNRealDecimal) : e.trunc 0 = e.intPart := by simp [trunc]

theorem NNRealDecimal.trunc_succ (e:NNRealDecimal) (n:ℕ) :
    e.trunc (n+1) = 10 * e.trunc n + (e.fracPart n:ℕ) := by
  unfold trunc
  rw [Finset.sum_range_succ]
  have hsum : ∑ i ∈ Finset.range n, (e.fracPart i:ℕ)*10^(n+1-1-i)
            = 10 * ∑ i ∈ Finset.range n, (e.fracPart i:ℕ)*10^(n-1-i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi; simp only [Finset.mem_range] at hi
    rw [show n+1-1-i = (n-1-i)+1 by omega, pow_succ]; ring
  rw [hsum]
  have : n+1-1-n = 0 := by omega
  rw [this, pow_zero, mul_one]
  ring

private theorem NNRealDecimal.term_eq (e:NNRealDecimal) (n i:ℕ) (hi : i < n) :
    ((e.fracPart i:ℕ):NNReal)*(10:NNReal)^(-(i:ℝ)-1)
    = ((e.fracPart i:ℕ):NNReal) * (10:NNReal)^(n-1-i) * (10:NNReal)^(-(n:ℝ)) := by
  rw [mul_assoc]
  congr 1
  rw [← rpow_natCast (10:NNReal) (n-1-i), ← rpow_add (by norm_num)]
  rw [show ((n-1-i:ℕ):ℝ) + (-n) = -i-1 by
    have h1 : (1:ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub (by omega : i ≤ n-1), Nat.cast_sub h1]
    ring]

theorem NNRealDecimal.partial_eq (e:NNRealDecimal) (n:ℕ) :
    (e.intPart:NNReal) + ∑ i ∈ Finset.range n, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)
    = (e.trunc n : NNReal) * (10:NNReal)^(-n:ℝ) := by
  unfold trunc
  push_cast
  rw [add_mul, Finset.sum_congr rfl (fun i hi => term_eq e n i (Finset.mem_range.1 hi)),
    ← Finset.sum_mul]
  congr 1
  rw [mul_assoc, ← rpow_natCast (10:NNReal) n, ← rpow_add (by norm_num)]
  simp

theorem NNRealDecimal.partial_le (e:NNRealDecimal) (n:ℕ) :
    (e.intPart:NNReal) + ∑ i ∈ Finset.range n, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)
    ≤ e.toNNReal := by
  rw [toNNReal]
  gcongr
  exact e.toNNReal_conv.sum_le_tsum _ (fun i _ => zero_le _)

theorem NNRealDecimal.tail_le_one (e:NNRealDecimal) :
    (∑' i, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)) ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_tsum]
  have hconv := e.toNNReal_conv
  rw [← NNReal.summable_coe] at hconv
  have hgeo : Summable (fun i:ℕ ↦ (9/10:ℝ) * (1/10)^i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ i, ((((e.fracPart i:ℕ):NNReal):ℝ) * ((10:NNReal)^(-(i:ℝ)-1):NNReal)) ≤ (9/10:ℝ)*(1/10)^i := by
    intro i
    push_cast [NNReal.coe_rpow]
    have h9 : ((e.fracPart i : ℕ):ℝ) ≤ 9 := by
      have : (e.fracPart i : ℕ) ≤ 9 := by have := (e.fracPart i).lt; omega
      exact_mod_cast this
    have hrw : (10:ℝ)^(-(i:ℝ)-1) = (1/10)^(i+1) := by
      rw [show -(i:ℝ)-1 = -((i+1:ℕ):ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
        Real.rpow_natCast, ← inv_pow, one_div]
    rw [hrw, pow_succ]
    have hpos : (0:ℝ) ≤ (1/10)^i := by positivity
    nlinarith [h9, hpos]
  calc ∑' i, (((e.fracPart i:ℕ):NNReal):ℝ) * ((10:NNReal)^(-(i:ℝ)-1):NNReal)
      ≤ ∑' i, (9/10:ℝ)*(1/10)^i := hconv.tsum_le_tsum hle hgeo
    _ = 1 := by rw [_root_.tsum_mul_left, _root_.tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

theorem NNRealDecimal.tail_from_le (e:NNRealDecimal) (n:ℕ) :
    (∑' i, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ))
    ≤ (∑ i ∈ Finset.range n, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)) + (10:NNReal)^(-n:ℝ) := by
  have hconv : Summable (fun i => (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)) := e.toNNReal_conv
  have hsplit := (sum_add_tsum_nat_add n hconv).symm
  rw [← hsplit]
  gcongr
  set e' : NNRealDecimal := mk 0 (fun i => e.fracPart (i+n)) with he'
  have hfp : ∀ i, e'.fracPart i = e.fracPart (i+n) := fun i => rfl
  have h1 : (∑' i, (e.fracPart (i+n):NNReal)*(10:NNReal)^(-(↑(i+n):ℝ)-1))
          = (∑' i, ((e'.fracPart i:NNReal)*(10:NNReal)^(-(i:ℝ)-1))) * (10:NNReal)^(-n:ℝ) := by
    conv_rhs => rw [← NNReal.tsum_mul_right]
    apply tsum_congr; intro i
    rw [hfp, mul_assoc, ← rpow_add (by norm_num)]
    congr 2
    push_cast; ring
  rw [h1]
  calc (∑' i, ((e'.fracPart i:NNReal)*(10:NNReal)^(-(i:ℝ)-1))) * (10:NNReal)^(-n:ℝ)
      ≤ 1 * (10:NNReal)^(-n:ℝ) := by gcongr; exact tail_le_one e'
    _ = (10:NNReal)^(-n:ℝ) := one_mul _

theorem NNRealDecimal.trunc_bounds (e:NNRealDecimal) (n:ℕ) :
    (e.trunc n : NNReal) * (10:NNReal)^(-n:ℝ) ≤ e.toNNReal
    ∧ e.toNNReal ≤ (e.trunc n : NNReal) * (10:NNReal)^(-n:ℝ) + (10:NNReal)^(-n:ℝ) := by
  constructor
  · rw [← partial_eq]; exact partial_le e n
  · rw [toNNReal, ← partial_eq]
    calc (e.intPart:NNReal) + ∑' i, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)
        ≤ (e.intPart:NNReal) + ((∑ i ∈ Finset.range n, (e.fracPart i:NNReal)*(10:NNReal)^(-i-1:ℝ)) + (10:NNReal)^(-n:ℝ)) := by gcongr; exact tail_from_le e n
      _ = _ := by ring

/-- The truncation bounds expressed in `ℝ`, comparing `trunc n` with `y * 10^n`. -/
theorem NNRealDecimal.trunc_bounds_real (e:NNRealDecimal) {y:NNReal} (hx : e.toNNReal = y) (n:ℕ) :
    (e.trunc n : ℝ) ≤ (y:ℝ) * 10^n ∧ (y:ℝ) * 10^n ≤ (e.trunc n : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := trunc_bounds e n
  rw [hx] at h1 h2
  -- push down to ℝ
  rw [← NNReal.coe_le_coe] at h1 h2
  push_cast [NNReal.coe_rpow] at h1 h2
  have hpos : (0:ℝ) < (10:ℝ)^(-(n:ℝ)) := by positivity
  have hpown : (10:ℝ)^(-(n:ℝ)) * (10:ℝ)^(n:ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hpn : (10:ℝ)^(n:ℝ) = (10:ℝ)^n := by rw [Real.rpow_natCast]
  have hpos' : (0:ℝ) < (10:ℝ)^(n:ℝ) := by positivity
  constructor
  · have h := mul_le_mul_of_nonneg_right h1 hpos'.le
    rw [mul_assoc, hpown, mul_one, hpn] at h
    convert h using 2
  · have h := mul_le_mul_of_nonneg_right h2 hpos'.le
    rw [add_mul, mul_assoc, hpown, mul_one, hpn] at h
    convert h using 2

theorem NNRealDecimal.trunc_one (e:NNRealDecimal) (hx : e.toNNReal = 1) (n:ℕ) :
    e.trunc n ≤ 10^n ∧ 10^n ≤ e.trunc n + 1 := by
  obtain ⟨h1, h2⟩ := trunc_bounds e n
  rw [hx] at h1 h2
  have hpow : (10:NNReal)^(-n:ℝ) * (10:NNReal)^(n:ℝ) = 1 := by
    rw [← rpow_add (by norm_num)]; simp
  have hpn : (10:NNReal)^(n:ℝ) = (10^n : NNReal) := by rw [rpow_natCast]
  constructor
  · have hb : (e.trunc n : NNReal) ≤ 10^n := by
      have h := mul_le_mul_right' h1 ((10:NNReal)^(n:ℝ))
      rw [mul_assoc, hpow, mul_one, one_mul, hpn] at h
      exact h
    exact_mod_cast hb
  · have hb : (10^n : NNReal) ≤ (e.trunc n : NNReal) + 1 := by
      have h := mul_le_mul_right' h2 ((10:NNReal)^(n:ℝ))
      rw [add_mul, mul_assoc, hpow, mul_one, one_mul, hpn] at h
      exact h
    exact_mod_cast hb

theorem NNRealDecimal.toNNReal_eq_one_iff (e:NNRealDecimal) :
    e.toNNReal = 1 ↔ e = mk 1 (fun _ ↦ 0) ∨ e = mk 0 (fun _ ↦ 9) := by
  constructor
  · intro hx
    have hb := trunc_one e hx
    have h0 := hb 0
    rw [trunc_zero] at h0
    simp only [pow_zero] at h0
    have hub : e.intPart ≤ 1 := h0.1
    interval_cases hip : e.intPart
    · right
      have hall : ∀ n, e.trunc n = 10^n - 1 ∧ (e.fracPart n:ℕ) = 9 := by
        intro n
        induction n with
        | zero =>
          refine ⟨by rw [trunc_zero, hip]; simp, ?_⟩
          have h1 := hb 1
          rw [trunc_succ, trunc_zero, hip] at h1
          have hd : (e.fracPart 0:ℕ) < 10 := (e.fracPart 0).lt
          simp only [pow_one, mul_one, mul_zero, zero_add] at h1
          omega
        | succ k ih =>
          obtain ⟨iht, _⟩ := ih
          have hk2 := hb (k+2)
          have hp : (1:ℕ) ≤ 10^k := Nat.one_le_pow _ _ (by norm_num)
          have hpk1 : 10^(k+1) = 10*10^k := by rw [pow_succ]; ring
          have hp2 : 10^(k+2) = 10*10^(k+1) := by rw [pow_succ]; ring
          have hp1 : (1:ℕ) ≤ 10^(k+1) := Nat.one_le_pow _ _ (by norm_num)
          have hd : (e.fracPart k:ℕ) < 10 := (e.fracPart k).lt
          have hcur : e.trunc (k+1) = 10^(k+1)-1 := by
            have hk1 := hb (k+1); rw [trunc_succ, iht] at hk1; rw [trunc_succ, iht]; omega
          refine ⟨hcur, ?_⟩
          rw [trunc_succ, hcur] at hk2
          have hdk1 : (e.fracPart (k+1):ℕ) < 10 := (e.fracPart (k+1)).lt
          omega
      obtain ⟨ip, fp⟩ := e
      simp only at hip hall
      subst hip
      congr 1
      funext n; rw [Digit.inj, (hall n).2]; rfl
    · left
      have hall : ∀ n, e.trunc n = 10^n ∧ (e.fracPart n:ℕ) = 0 := by
        intro n
        induction n with
        | zero =>
          refine ⟨by rw [trunc_zero, hip]; simp, ?_⟩
          have h1 := hb 1
          rw [trunc_succ, trunc_zero, hip] at h1
          simp only [pow_one, mul_one] at h1
          have hd : (e.fracPart 0:ℕ) < 10 := (e.fracPart 0).lt
          omega
        | succ k ih =>
          obtain ⟨iht, _⟩ := ih
          have hk2 := hb (k+2)
          have hpk1 : 10^(k+1) = 10*10^k := by rw [pow_succ]; ring
          have hp2 : 10^(k+2) = 10*10^(k+1) := by rw [pow_succ]; ring
          have hcur : e.trunc (k+1) = 10^(k+1) := by
            have hk1 := hb (k+1); rw [trunc_succ, iht] at hk1; rw [trunc_succ, iht]
            have hd : (e.fracPart k:ℕ) < 10 := (e.fracPart k).lt; omega
          refine ⟨hcur, ?_⟩
          rw [trunc_succ, hcur] at hk2
          have hd : (e.fracPart (k+1):ℕ) < 10 := (e.fracPart (k+1)).lt
          omega
      obtain ⟨ip, fp⟩ := e
      simp only at hip hall
      subst hip
      congr 1
      funext n; rw [Digit.inj, (hall n).2]; rfl
  · rintro (rfl | rfl)
    · rw [← NNRealDecimal.not_inj.1]
    · rw [← NNRealDecimal.not_inj.2]

/-- A `NNRealDecimal` is determined by its sequence of truncations. -/
theorem NNRealDecimal.eq_of_trunc_eq {e f : NNRealDecimal}
    (h : ∀ n, e.trunc n = f.trunc n) : e = f := by
  obtain ⟨ip, fp⟩ := e
  obtain ⟨ip', fp'⟩ := f
  have hip : ip = ip' := by
    have := h 0; simp only [trunc_zero] at this; exact this
  subst hip
  congr 1
  funext n
  have hn := h (n+1)
  have hn0 := h n
  rw [trunc_succ, trunc_succ, hn0] at hn
  simp only at hn
  rw [Digit.inj]
  omega

/-- For a value `y`, the truncation `e.trunc n` lies within `1` of the floor of `y * 10^n`. -/
theorem NNRealDecimal.trunc_floor_bounds (e:NNRealDecimal) {y:NNReal} (hx : e.toNNReal = y) (n:ℕ) :
    e.trunc n ≤ ⌊(y:ℝ) * 10^n⌋₊ ∧ ⌊(y:ℝ) * 10^n⌋₊ ≤ e.trunc n + 1 := by
  obtain ⟨h1, h2⟩ := trunc_bounds_real e hx n
  have hyge : (0:ℝ) ≤ (y:ℝ) * 10^n := by positivity
  constructor
  · exact Nat.le_floor (by exact_mod_cast h1)
  · have : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) ≤ (y:ℝ) * 10^n := Nat.floor_le hyge
    have h3 : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) ≤ (e.trunc n : ℝ) + 1 := le_trans this h2
    exact_mod_cast h3

/-- If `y * 10^n` is never an integer, the truncation is forced to be the floor. -/
theorem NNRealDecimal.trunc_forced (e:NNRealDecimal) {y:NNReal} (hx : e.toNNReal = y) (n:ℕ)
    (hni : ¬ ∃ k:ℕ, (y:ℝ) * 10^n = k) : e.trunc n = ⌊(y:ℝ) * 10^n⌋₊ := by
  obtain ⟨h1, h2⟩ := trunc_bounds_real e hx n
  have hyge : (0:ℝ) ≤ (y:ℝ) * 10^n := by positivity
  have hfl : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) ≤ (y:ℝ) * 10^n := Nat.floor_le hyge
  -- strict: floor < value, since value is not an integer
  have hstrict : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) < (y:ℝ) * 10^n := by
    rcases lt_or_eq_of_le hfl with h | h
    · exact h
    · exact absurd ⟨_, h.symm⟩ hni
  have hlt : (y:ℝ) * 10^n < ⌊(y:ℝ) * 10^n⌋₊ + 1 := Nat.lt_floor_add_one _
  have hle1 : e.trunc n ≤ ⌊(y:ℝ) * 10^n⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  -- ⌊⌋ < trunc + 1 from hstrict and h2
  have : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) < (e.trunc n : ℝ) + 1 := lt_of_lt_of_le hstrict h2
  have hge1 : ⌊(y:ℝ) * 10^n⌋₊ ≤ e.trunc n := by
    have : (⌊(y:ℝ) * 10^n⌋₊ : ℝ) < (e.trunc n : ℝ) + 1 := this
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  omega

/-- Exercise B.2.2 -/
theorem RealDecimal.not_inj_one (d: RealDecimal) : (d:ℝ) = 1 ↔ (d = pos (mk 1 fun _ ↦ 0) ∨ d = pos (mk 0 fun _ ↦ 9)) := by
  constructor
  · intro hd
    cases d with
    | pos e =>
      have he : e.toNNReal = 1 := by
        have : ((e.toNNReal:ℝ)) = 1 := hd
        exact_mod_cast this
      rcases (NNRealDecimal.toNNReal_eq_one_iff e).1 he with h | h
      · left; rw [h]
      · right; rw [h]
    | neg e =>
      exfalso
      have : -(e.toNNReal:ℝ) = 1 := hd
      have hpos : (0:ℝ) ≤ (e.toNNReal:ℝ) := (e.toNNReal).coe_nonneg
      linarith
  · rintro (rfl | rfl)
    · show ((mk 1 (fun _ ↦ 0)).toNNReal:ℝ) = 1
      rw [← NNRealDecimal.not_inj.1]; norm_num
    · show ((mk 0 (fun _ ↦ 9)).toNNReal:ℝ) = 1
      rw [← NNRealDecimal.not_inj.2]; norm_num

/-- Exercise B.2.3 -/
abbrev TerminatingDecimal (x:ℝ) : Prop := ∃ (n:ℤ) (m:ℕ), x = n / (10:ℝ)^m

/-- If `(y:ℝ)` is not a terminating decimal, then `y * 10^n` is never a natural number. -/
theorem NNRealDecimal.not_int_of_nonterminating {y:NNReal} (hy : ¬ TerminatingDecimal (y:ℝ))
    (n:ℕ) : ¬ ∃ k:ℕ, (y:ℝ) * 10^n = k := by
  rintro ⟨k, hk⟩
  apply hy
  refine ⟨(k:ℤ), n, ?_⟩
  have hpow : (0:ℝ) < (10:ℝ)^n := by positivity
  rw [eq_div_iff (ne_of_gt hpow)]; push_cast [hk]; ring

/-- Uniqueness of the decimal representation of a non-terminating nonnegative value. -/
theorem NNRealDecimal.inj_of_nonterminating {e f : NNRealDecimal}
    (hy : ¬ TerminatingDecimal (e.toNNReal:ℝ)) (hef : e.toNNReal = f.toNNReal) : e = f := by
  apply eq_of_trunc_eq
  intro n
  have h1 := trunc_forced e (rfl : e.toNNReal = e.toNNReal) n (not_int_of_nonterminating hy n)
  have hyf : ¬ TerminatingDecimal (f.toNNReal:ℝ) := by rw [← hef]; exact hy
  have h2 := trunc_forced f (rfl : f.toNNReal = f.toNNReal) n (not_int_of_nonterminating hyf n)
  rw [h1, h2, hef]

theorem RealDecimal.inj_nonterminating {x:ℝ} (hx: ¬TerminatingDecimal x) : ∃! d:RealDecimal, d = x := by
  obtain ⟨d, hd⟩ := RealDecimal.surj x
  refine ⟨d, hd.symm, ?_⟩
  intro d' hd'
  -- x ≠ 0 since 0 is terminating
  have hx0 : x ≠ 0 := by rintro rfl; exact hx ⟨0, 0, by norm_num⟩
  -- both d and d' have the same sign as x
  have key : ∀ a : RealDecimal, (a:ℝ) = x → ∃ e:NNRealDecimal,
      a = (if 0 < x then RealDecimal.pos e else RealDecimal.neg e) ∧ (e.toNNReal : ℝ) = |x| := by
    intro a ha
    cases a with
    | pos e =>
      have hval : (e.toNNReal : ℝ) = x := ha
      have hxnn : 0 ≤ x := by rw [← hval]; exact (e.toNNReal).coe_nonneg
      rcases lt_or_eq_of_le hxnn with hlt | heq
      · exact ⟨e, by simp [hlt], by rw [hval, abs_of_pos hlt]⟩
      · exact absurd heq.symm hx0
    | neg e =>
      have hval : -(e.toNNReal : ℝ) = x := ha
      have hxnp : x ≤ 0 := by rw [← hval]; simp [(e.toNNReal).coe_nonneg]
      have hxlt : x < 0 := lt_of_le_of_ne hxnp hx0
      refine ⟨e, by simp [not_lt.mpr hxnp], ?_⟩
      rw [abs_of_neg hxlt, ← hval]; ring
  obtain ⟨e, hde, hev⟩ := key d hd.symm
  obtain ⟨e', hd'e, he'v⟩ := key d' hd'
  -- e and e' represent the same nonneg value |x|, which is non-terminating
  have hntabs : ¬ TerminatingDecimal (e.toNNReal:ℝ) := by
    rw [hev]
    rintro ⟨n, m, h⟩
    apply hx
    rcases abs_cases x with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ⟨n, m, by rw [← ha, h]⟩
    · exact ⟨-n, m, by rw [show x = -|x| by rw [ha]; ring, h]; push_cast; ring⟩
  have hee' : e.toNNReal = e'.toNNReal := by
    have : (e.toNNReal:ℝ) = (e'.toNNReal:ℝ) := by rw [hev, he'v]
    exact_mod_cast this
  have : e = e' := inj_of_nonterminating hntabs hee'
  rw [hde, hd'e, this]

/-- If the truncations of `e` bracket `y * 10^n` for every `n`, then `e.toNNReal = y`. -/
theorem NNRealDecimal.toNNReal_eq_of_bounds (e:NNRealDecimal) {y:NNReal}
    (h : ∀ n:ℕ, (e.trunc n : ℝ) ≤ (y:ℝ) * 10^n ∧ (y:ℝ) * 10^n ≤ (e.trunc n : ℝ) + 1) :
    e.toNNReal = y := by
  rw [← NNReal.coe_inj]
  -- compare via the truncation bounds for e.toNNReal
  by_contra hne
  -- |e.toNNReal - y| > 0; derive contradiction by choosing n large
  set z : ℝ := (e.toNNReal:ℝ) with hz
  set w : ℝ := (y:ℝ) with hw
  have hd : (0:ℝ) < |z - w| := by
    have : z - w ≠ 0 := sub_ne_zero.mpr hne
    positivity
  -- Use 10^n growth: there is n with (10:ℝ)^n > 1/|z-w|
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |z - w|) (by norm_num : (1:ℝ) < 10)
  -- bounds for e.toNNReal from trunc_bounds_real
  obtain ⟨hz1, hz2⟩ := trunc_bounds_real e (rfl : e.toNNReal = e.toNNReal) n
  obtain ⟨hy1, hy2⟩ := h n
  -- both z*10^n and w*10^n lie in [trunc n, trunc n + 1]
  have hpos : (0:ℝ) < (10:ℝ)^n := by positivity
  have habs : |z - w| * (10:ℝ)^n ≤ 1 := by
    have e1 : |z * 10^n - w * 10^n| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor
      · nlinarith [hz1, hz2, hy1, hy2]
      · nlinarith [hz1, hz2, hy1, hy2]
    calc |z - w| * (10:ℝ)^n = |(z - w) * 10^n| := by rw [abs_mul, abs_of_pos hpos]
      _ = |z * 10^n - w * 10^n| := by ring_nf
      _ ≤ 1 := e1
  -- but |z-w| * 10^n > 1
  have : 1 < |z - w| * (10:ℝ)^n := by
    rw [div_lt_iff₀ hd] at hn
    nlinarith [hn]
  linarith

/-- The only decimal with value `0` is the all-zero decimal. -/
theorem NNRealDecimal.toNNReal_eq_zero_iff (e:NNRealDecimal) :
    e.toNNReal = 0 ↔ e = mk 0 (fun _ ↦ 0) := by
  constructor
  · intro hx
    -- all truncations are 0
    have htr : ∀ n, e.trunc n = 0 := by
      intro n
      obtain ⟨h1, _⟩ := trunc_bounds_real e hx n
      simp only [NNReal.coe_zero, zero_mul] at h1
      have : (e.trunc n : ℝ) ≤ 0 := h1
      have : (e.trunc n : ℝ) = 0 := le_antisymm this (by positivity)
      exact_mod_cast this
    have hz : ∀ n, (mk 0 (fun _ ↦ 0)).trunc n = 0 := by
      intro n
      induction n with
      | zero => simp [trunc_zero]
      | succ k ih =>
        have hfp : ((NNRealDecimal.mk 0 (fun _ ↦ 0)).fracPart k : ℕ) = 0 := rfl
        rw [trunc_succ, ih, hfp]
    apply eq_of_trunc_eq
    intro n
    rw [htr n, hz n]
  · rintro rfl
    simp [toNNReal]

theorem floor_rec (v:ℝ) (hv: 0 ≤ v) :
    10 * ⌊v⌋₊ ≤ ⌊10*v⌋₊ ∧ ⌊10*v⌋₊ < 10 * ⌊v⌋₊ + 10 := by
  have hf : (⌊v⌋₊:ℝ) ≤ v := Nat.floor_le hv
  have hf2 : v < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
  refine ⟨Nat.le_floor (by push_cast; nlinarith [hf]), ?_⟩
  have hle : (⌊10*v⌋₊:ℝ) ≤ 10*v := Nat.floor_le (by linarith)
  have : (⌊10*v⌋₊:ℝ) < 10*⌊v⌋₊ + 10 := by nlinarith [hf2, hle]
  exact_mod_cast this

theorem NNRealDecimal.ofSeq (t : ℕ → ℕ)
    (h : ∀ n, 10 * t n ≤ t (n+1) ∧ t (n+1) < 10 * t n + 10) :
    ∃ e : NNRealDecimal, ∀ n, e.trunc n = t n := by
  set dig : ℕ → Digit := fun n => Digit.mk (show t (n+1) - 10 * t n < 10 by have := (h n).2; omega) with hdig
  refine ⟨mk (t 0) dig, ?_⟩
  intro n
  induction n with
  | zero => simp [trunc_zero]
  | succ k ih =>
    rw [trunc_succ, ih]
    have : ((dig k : Digit) : ℕ) = t (k+1) - 10 * t k := by simp [hdig]
    rw [this]; have := (h k).1; omega

theorem NNRealDecimal.two_reps {y:NNReal} (hy : 0 < y)
    (N M:ℕ) (hval : (y:ℝ) = N/(10:ℝ)^M) (hN1 : 1 ≤ N) (hND : M = 0 ∨ ¬ 10 ∣ N) :
    ∃ e₁ e₂ : NNRealDecimal, e₁ ≠ e₂ ∧ ∀ e, e.toNNReal = y ↔ e = e₁ ∨ e = e₂ := by
  -- numeric facts
  have hyR : (0:ℝ) < (y:ℝ) := hy
  -- P2: for n ≥ M, y*10^n = N*10^(n-M)
  have P2 : ∀ n, M ≤ n → (y:ℝ) * 10^n = (N * 10^(n-M) : ℕ) := by
    intro n hn; rw [hval]
    have : (10:ℝ)^n = 10^M * 10^(n-M) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp; push_cast; ring
  -- P1: for n < M, y*10^n not integer
  have P1 : ∀ n, n < M → ¬ ∃ k:ℕ, (y:ℝ)*10^n = k := by
    intro n hn
    rcases hND with hM0 | hND'
    · omega
    rintro ⟨k, hk⟩
    rw [hval] at hk
    have h10M : (0:ℝ) < (10:ℝ)^M := by positivity
    have key : (N:ℝ) * 10^n = (k:ℝ) * 10^M := by field_simp at hk; linarith [hk]
    have hpow : (10:ℝ)^M = 10^n * 10^(M-n) := by rw [← pow_add]; congr 1; omega
    rw [hpow] at key
    have h10n : (0:ℝ) < (10:ℝ)^n := by positivity
    have key2 : (N:ℝ) = (k:ℝ) * 10^(M-n) := by
      have : (N:ℝ) * 10^n = (k * 10^(M-n)) * 10^n := by rw [key]; ring
      exact mul_right_cancel₀ (ne_of_gt h10n) this
    have hNk : N = k * 10^(M-n) := by exact_mod_cast key2
    apply hND'; rw [hNk]
    exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) k
  -- K n for n ≥ M
  set K : ℕ → ℕ := fun n => N * 10^(n-M) with hK
  have hKpos : ∀ n, M ≤ n → 1 ≤ K n := by
    intro n hn; simp only [hK]
    have : 1 ≤ 10^(n-M) := Nat.one_le_pow _ _ (by norm_num)
    calc 1 ≤ N := hN1
      _ ≤ N * 10^(n-M) := Nat.le_mul_of_pos_right _ (by positivity)
  -- tA = floor sequence
  set tA : ℕ → ℕ := fun n => ⌊(y:ℝ)*10^n⌋₊ with htA
  have htA_ge : ∀ n, M ≤ n → tA n = K n := by
    intro n hn; simp only [htA]; rw [P2 n hn]; exact Nat.floor_natCast _
  -- value bounds for tA
  have hval_le : ∀ (t : ℕ → ℕ) n, (t n ≤ (y:ℝ)*10^n ∧ (y:ℝ)*10^n ≤ t n + 1) → True := fun _ _ _ => trivial
  -- recursion bound for tA via floor_rec (note v_{n+1} = 10 v_n)
  have hvn : ∀ n, (y:ℝ)*10^(n+1) = 10 * ((y:ℝ)*10^n) := by intro n; rw [pow_succ]; ring
  have htA_rec : ∀ n, 10 * tA n ≤ tA (n+1) ∧ tA (n+1) < 10 * tA n + 10 := by
    intro n; simp only [htA, hvn n]
    exact floor_rec ((y:ℝ)*10^n) (by positivity)
  have htA_val : ∀ n, (tA n : ℝ) ≤ (y:ℝ)*10^n ∧ (y:ℝ)*10^n ≤ tA n + 1 := by
    intro n; simp only [htA]
    exact ⟨Nat.floor_le (by positivity), le_of_lt (Nat.lt_floor_add_one _)⟩
  -- tB sequence
  set tB : ℕ → ℕ := fun n => if n < M then tA n else K n - 1 with htB
  have htB_lt : ∀ n, n < M → tB n = tA n := by intro n hn; simp [htB, hn]
  have htB_ge : ∀ n, M ≤ n → tB n = K n - 1 := by intro n hn; simp [htB, Nat.not_lt.mpr hn]
  -- junction fact: at n = M, tA M = N = K M
  have hKM : K M = N := by simp [hK]
  -- value bounds for tB
  have htB_val : ∀ n, (tB n : ℝ) ≤ (y:ℝ)*10^n ∧ (y:ℝ)*10^n ≤ tB n + 1 := by
    intro n
    rcases lt_or_ge n M with hn | hn
    · rw [htB_lt n hn]; exact htA_val n
    · rw [htB_ge n hn, P2 n hn]
      have h1 : 1 ≤ K n := hKpos n hn
      have h1R : (1:ℝ) ≤ K n := by exact_mod_cast h1
      have hKn : ((N * 10^(n-M) : ℕ):ℝ) = (K n:ℝ) := by simp [hK]
      rw [hKn]
      push_cast [Nat.cast_sub h1]
      refine ⟨by linarith, by linarith⟩
  -- recursion bounds for tB
  have htB_rec : ∀ n, 10 * tB n ≤ tB (n+1) ∧ tB (n+1) < 10 * tB n + 10 := by
    intro n
    rcases lt_or_ge (n+1) M with hn1 | hn1
    · -- both n, n+1 < M
      have hn : n < M := by omega
      rw [htB_lt n hn, htB_lt (n+1) hn1]; exact htA_rec n
    · rcases lt_or_ge n M with hn | hn
      · -- junction: n = M-1, n+1 = M
        have hnM : n + 1 = M := by omega
        rw [htB_lt n hn, htB_ge (n+1) hn1, hnM, hKM]
        -- 10 * tA(M-1) ≤ N-1 < 10 tA(M-1) + 10
        have hrec := htA_rec n
        rw [hnM, htA_ge M (le_refl M), hKM] at hrec
        -- hrec : 10 * tA n ≤ N ∧ N < 10 * tA n + 10
        have hND' : ¬ 10 ∣ N := by
          rcases hND with h | h
          · exact absurd hn (by omega)
          · exact h
        -- 10 * tA n ≠ N since 10 ∣ 10*tA n
        have hne : 10 * tA n ≠ N := by intro h; apply hND'; rw [← h]; exact dvd_mul_right 10 (tA n)
        omega
      · -- both ≥ M
        rw [htB_ge n hn, htB_ge (n+1) hn1]
        have hKrec : K (n+1) = 10 * K n := by
          simp only [hK]; rw [show n+1-M = (n-M)+1 by omega, pow_succ]; ring
        have h1 : 1 ≤ K n := hKpos n hn
        rw [hKrec]; omega
  -- build the two decimals
  obtain ⟨eA, heA⟩ := ofSeq tA (fun n => htA_rec n)
  obtain ⟨eB, heB⟩ := ofSeq tB (fun n => htB_rec n)
  -- values
  have hvalA : eA.toNNReal = y := by
    apply NNRealDecimal.toNNReal_eq_of_bounds; intro n; rw [heA]; exact htA_val n
  have hvalB : eB.toNNReal = y := by
    apply NNRealDecimal.toNNReal_eq_of_bounds; intro n; rw [heB]; exact htB_val n
  -- distinctness: differ at n = M
  have hdist : eA ≠ eB := by
    intro h
    have := congrArg (fun e => NNRealDecimal.trunc e M) h
    simp only [heA, heB] at this
    rw [htA_ge M (le_refl M), htB_ge M (le_refl M), hKM] at this
    -- N = N - 1, but N ≥ 1
    omega
  refine ⟨eA, eB, hdist, ?_⟩
  intro e
  constructor
  · intro he
    -- t = e.trunc; show equals tA or tB
    set t : ℕ → ℕ := fun n => e.trunc n with ht
    -- below M : forced
    have hbelow : ∀ n, n < M → t n = tA n := by
      intro n hn
      have := trunc_forced e he n (P1 n hn)
      simp only [ht, htA]; exact this
    -- value bounds for e (real)
    have heval : ∀ n, (t n : ℝ) ≤ (y:ℝ)*10^n ∧ (y:ℝ)*10^n ≤ t n + 1 :=
      fun n => trunc_bounds_real e he n
    -- recursion for t
    have htrec : ∀ n, t (n+1) = 10 * t n + (e.fracPart n : ℕ) := fun n => trunc_succ e n
    -- choice at M
    have hM_choice : t M = N ∨ t M = N - 1 := by
      have hb := heval M
      rw [P2 M (le_refl M)] at hb
      have hKM' : ((N * 10^(M-M) : ℕ):ℝ) = (N:ℝ) := by simp
      rw [hKM'] at hb
      have h1 : (t M : ℝ) ≤ N := hb.1
      have h2 : (N:ℝ) ≤ t M + 1 := hb.2
      have : t M ≤ N ∧ N ≤ t M + 1 := ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      omega
    -- from M onward, t determined by choice
    have hfromM : ∀ n, M ≤ n → t n = (if t M = N then tA n else tB n) := by
      intro n hn
      induction n with
      | zero =>
        -- M = 0
        have hM0 : M = 0 := by omega
        have hKM0 : K 0 = N := by rw [← hM0]; exact hKM
        have htA0 : tA 0 = N := by rw [htA_ge 0 (by omega), hKM0]
        have htB0 : tB 0 = N - 1 := by rw [htB_ge 0 (by omega), hKM0]
        rw [hM0]
        rcases hM_choice with hc | hc <;> rw [hM0] at hc
        · rw [if_pos hc, htA0, hc]
        · rw [if_neg (by omega), htB0, hc]
      | succ k ih =>
        rcases Nat.lt_or_ge k M with hk | hk
        · -- k < M so k+1 = M (since M ≤ k+1)
          have hkM : k + 1 = M := by omega
          rw [hkM]
          rcases hM_choice with hc | hc
          · rw [if_pos hc, hc, htA_ge M (le_refl M), hKM]
          · rw [if_neg (by omega), htB_ge M (le_refl M), hKM, hc]
        · -- k ≥ M
          have ihk := ih hk
          have hKk1 : K (k+1) = 10 * K k := by
            simp only [hK]; rw [show k+1-M = (k-M)+1 by omega, pow_succ]; ring
          have hKkpos : 1 ≤ K k := hKpos k hk
          -- value bound at k+1 forces t(k+1) ∈ {K(k+1)-1, K(k+1)}
          have hb := heval (k+1)
          rw [P2 (k+1) (by omega)] at hb
          have hKn1 : ((N * 10^(k+1-M) : ℕ):ℝ) = (K (k+1):ℝ) := by simp [hK]
          rw [hKn1] at hb
          have hK1pos : 1 ≤ K (k+1) := hKpos (k+1) (by omega)
          have hbnd : t (k+1) = K (k+1) ∨ t (k+1) = K (k+1) - 1 := by
            have h1 : (t (k+1):ℝ) ≤ K (k+1) := hb.1
            have h2 : (K (k+1):ℝ) ≤ t (k+1) + 1 := hb.2
            have : t (k+1) ≤ K (k+1) ∧ K (k+1) ≤ t (k+1) + 1 := ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
            omega
          -- recursion link
          have hrec := htrec k
          have hd : (e.fracPart k : ℕ) < 10 := (e.fracPart k).lt
          rcases hM_choice with hc | hc
          · -- track tA = K
            rw [if_pos hc] at ihk ⊢
            rw [htA_ge (k+1) (by omega), hKk1]
            rw [htA_ge k hk] at ihk
            -- t k = K k, t(k+1) = 10 K k + d, bounded ⟹ = 10 K k
            rw [ihk] at hrec
            rw [hKk1] at hbnd
            omega
          · rw [if_neg (by omega)] at ihk ⊢
            rw [htB_ge (k+1) (by omega), hKk1]
            rw [htB_ge k hk] at ihk
            -- tB k = K k - 1
            rw [ihk] at hrec
            rw [hKk1] at hbnd
            omega
    -- now t = tA everywhere or t = tB everywhere
    rcases hM_choice with hc | hc
    · left
      apply eq_of_trunc_eq
      intro n
      simp only [← ht]
      rcases Nat.lt_or_ge n M with hn | hn
      · rw [heA, hbelow n hn]
      · rw [heA, hfromM n hn, if_pos hc]
    · right
      apply eq_of_trunc_eq
      intro n
      simp only [← ht]
      rcases Nat.lt_or_ge n M with hn | hn
      · rw [heB, hbelow n hn, htB_lt n hn]
      · rw [heB, hfromM n hn, if_neg (by omega)]
  · rintro (rfl | rfl)
    · exact hvalA
    · exact hvalB


/-- A positive nonneg value can be written in reduced terminating form. -/
theorem NNRealDecimal.reduced_form {y:NNReal} (hy: 0 < y) (h: TerminatingDecimal (y:ℝ)) :
    ∃ (N M:ℕ), (y:ℝ) = N/(10:ℝ)^M ∧ 1 ≤ N ∧ (M = 0 ∨ ¬ (10 ∣ N)) := by
  obtain ⟨n,m,hnm⟩ := h
  have hyR : (0:ℝ) < y := hy
  have hpow : (0:ℝ) < (10:ℝ)^m := by positivity
  have hn0 : 0 ≤ n := by
    by_contra hc; push_neg at hc
    have : (y:ℝ) < 0 := by rw [hnm]; apply div_neg_of_neg_of_pos; exact_mod_cast hc; exact hpow
    linarith
  lift n to ℕ using hn0 with N hN
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0|h0
    · exfalso; rw [h0] at hnm; simp at hnm; linarith [hnm.symm ▸ hyR]
    · exact h0
  clear hN
  induction m generalizing N with
  | zero => exact ⟨N, 0, hnm, hN1, Or.inl rfl⟩
  | succ k ih =>
    by_cases hdvd : 10 ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN'1 : 1 ≤ N' := by omega
      have hnew : (y:ℝ) = N' / (10:ℝ)^k := by
        rw [hnm]; push_cast; rw [pow_succ]; field_simp
      exact ih (by positivity) N' hnew hN'1
    · exact ⟨N, k+1, hnm, hN1, Or.inr hdvd⟩

/-- Two decimal representations for any positive terminating value. -/
theorem NNRealDecimal.two_reps_term {y:NNReal} (hy : 0 < y) (h : TerminatingDecimal (y:ℝ)) :
    ∃ e₁ e₂ : NNRealDecimal, e₁ ≠ e₂ ∧ ∀ e, e.toNNReal = y ↔ e = e₁ ∨ e = e₂ := by
  obtain ⟨N, M, hval, hN1, hND⟩ := reduced_form hy h
  exact two_reps hy N M hval hN1 hND

theorem RealDecimal.not_inj_terminating {x:ℝ} (hx: TerminatingDecimal x) : ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- x < 0: use -x > 0
    have hy : (0:NNReal) < (-x).toNNReal := by
      rw [Real.toNNReal_pos]; linarith
    have hterm : TerminatingDecimal (((-x).toNNReal:ℝ)) := by
      rw [Real.coe_toNNReal _ (by linarith)]
      obtain ⟨n,m,h⟩ := hx; exact ⟨-n, m, by rw [h]; push_cast; ring⟩
    obtain ⟨e₁, e₂, hne, hiff⟩ := NNRealDecimal.two_reps_term hy hterm
    have hcoe : (((-x).toNNReal:ℝ)) = -x := Real.coe_toNNReal _ (by linarith)
    refine ⟨RealDecimal.neg e₁, RealDecimal.neg e₂, by simp [hne], ?_⟩
    intro d
    cases d with
    | pos e =>
      simp only [RealDecimal.instCoeReal]
      constructor
      · intro h; exfalso
        have : (0:ℝ) ≤ (e.toNNReal:ℝ) := (e.toNNReal).coe_nonneg
        change (e.toNNReal:ℝ) = x at h; linarith
      · rintro (h|h) <;> simp at h
    | neg e =>
      constructor
      · intro h
        change -(e.toNNReal:ℝ) = x at h
        have hev : e.toNNReal = (-x).toNNReal := by
          have : (e.toNNReal:ℝ) = -x := by linarith
          rw [← hcoe] at this; exact_mod_cast this
        rcases (hiff e).1 hev with h1|h1 <;> simp [h1]
      · rintro (h|h) <;> rw [h]
        · change -(e₁.toNNReal:ℝ) = x
          rw [show (e₁.toNNReal:ℝ) = -x from by rw [← hcoe]; congr 1; exact ((hiff e₁).2 (Or.inl rfl))]; ring
        · change -(e₂.toNNReal:ℝ) = x
          rw [show (e₂.toNNReal:ℝ) = -x from by rw [← hcoe]; congr 1; exact ((hiff e₂).2 (Or.inr rfl))]; ring
  · -- x = 0
    subst hzero
    refine ⟨RealDecimal.pos (mk 0 (fun _ ↦ 0)), RealDecimal.neg (mk 0 (fun _ ↦ 0)), by simp, ?_⟩
    intro d
    have hz : (mk 0 (fun _ ↦ 0)).toNNReal = 0 :=
      (NNRealDecimal.toNNReal_eq_zero_iff _).2 rfl
    cases d with
    | pos e =>
      constructor
      · intro h
        change (e.toNNReal:ℝ) = 0 at h
        have : e.toNNReal = 0 := by exact_mod_cast h
        left; rw [(NNRealDecimal.toNNReal_eq_zero_iff e).1 this]
      · rintro (h|h)
        · rw [h]; show ((mk 0 (fun _ ↦ 0)).toNNReal:ℝ) = 0; rw [hz]; simp
        · simp at h
    | neg e =>
      constructor
      · intro h
        change -(e.toNNReal:ℝ) = 0 at h
        have : e.toNNReal = 0 := by
          have : (e.toNNReal:ℝ) = 0 := by linarith
          exact_mod_cast this
        right; rw [(NNRealDecimal.toNNReal_eq_zero_iff e).1 this]
      · rintro (h|h)
        · simp at h
        · rw [h]; show -((mk 0 (fun _ ↦ 0)).toNNReal:ℝ) = 0; rw [hz]; simp
  · -- x > 0
    have hy : (0:NNReal) < x.toNNReal := by rw [Real.toNNReal_pos]; exact hpos
    have hterm : TerminatingDecimal ((x.toNNReal:ℝ)) := by
      rw [Real.coe_toNNReal _ (by linarith)]; exact hx
    obtain ⟨e₁, e₂, hne, hiff⟩ := NNRealDecimal.two_reps_term hy hterm
    have hcoe : ((x.toNNReal:ℝ)) = x := Real.coe_toNNReal _ (by linarith)
    refine ⟨RealDecimal.pos e₁, RealDecimal.pos e₂, by simp [hne], ?_⟩
    intro d
    cases d with
    | neg e =>
      constructor
      · intro h; exfalso
        change -(e.toNNReal:ℝ) = x at h
        have : (0:ℝ) ≤ (e.toNNReal:ℝ) := (e.toNNReal).coe_nonneg
        linarith
      · rintro (h|h) <;> simp at h
    | pos e =>
      constructor
      · intro h
        change (e.toNNReal:ℝ) = x at h
        have hev : e.toNNReal = x.toNNReal := by
          rw [← hcoe] at h; exact_mod_cast h
        rcases (hiff e).1 hev with h1|h1 <;> simp [h1]
      · rintro (h|h) <;> rw [h]
        · show (e₁.toNNReal:ℝ) = x
          rw [← hcoe]; congr 1; exact ((hiff e₁).2 (Or.inl rfl))
        · show (e₂.toNNReal:ℝ) = x
          rw [← hcoe]; congr 1; exact ((hiff e₂).2 (Or.inr rfl))

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by infer_instance


end AppendixB
