import Mathlib.Tactic
import Analysis.Appendix_B_1

/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

An implementation of the decimal representation of Mathlib's real numbers `ℝ`.

This is separate from the way decimal numerals are already represented in Mathlib.  We also represent the integer part of the natural numbers just by `ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the `Digit` class.
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

theorem RealDecimal.not_inj_terminating {x:ℝ} (hx: TerminatingDecimal x) : ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by sorry

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by infer_instance


end AppendixB
