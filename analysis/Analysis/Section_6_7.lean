import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  obtain h | rfl | h := lt_trichotomy x 1
  . sorry
  . simp; exact ⟨ 1, lim_of_const 1 ⟩
  have h': 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity)
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [CloseSeq, dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [Close, hn, hm, dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; linarith
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; positivity


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←rpow_add (by linarith)]
      simp [r]
    exact this.2.symm
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . sorry
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  choose q' hq' using eq_lim_of_rat q
  rw [rpow_eq_lim_ratPow hx hq']
  set b : Sequence := ((fun n ↦ x^(q' n:ℝ)):Sequence) with hb
  have hconv : b.Convergent := ratPow_continuous hx hq'
  by_contra hlt
  rw [ge_iff_le, not_le] at hlt
  have htend := lim_def hconv
  rw [Sequence.tendsTo_iff] at htend
  obtain ⟨N, hN⟩ := htend (-(lim b)/2) (by linarith)
  have hclose := hN (max N 0) (le_max_left _ _)
  have hbnn : (0:ℝ) ≤ b (max N 0) := by
    rw [hb]
    simp only [Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos (le_max_right _ _)]
    exact Real.rpow_nonneg (le_of_lt hx) _
  rw [abs_le] at hclose
  linarith [hclose.2, hbnn]

/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←rpow_add]; simp; linarith


/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  sorry

/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  have h0 : rpow x 0 = 1 := by
    have := rpow_of_rat_eq_ratPow hx (q := (0:ℚ)); simpa using this
  have hpos : rpow x q > 0 := by
    rcases lt_or_eq_of_le (ratPow_nonneg hx q) with h | h
    · exact h
    · exfalso
      have hadd := ratPow_add hx q (-q)
      rw [add_neg_cancel, h0, ← h, zero_mul] at hadd
      exact one_ne_zero hadd
  rw [eq_div_iff (ne_of_gt hpos), ← ratPow_add hx (-q) q, neg_add_cancel, h0]

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  choose q' hq' using eq_lim_of_rat q
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hy hq'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hy hq',
    rpow_eq_lim_ratPow (mul_pos hx hy) hq', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n
  rw [← Real.mul_rpow (le_of_lt hx) (le_of_lt hy)]

private lemma Real.rpow_zero' {x:ℝ} (hx: x > 0) : rpow x 0 = 1 := by
  have := rpow_of_rat_eq_ratPow hx (q := (0:ℚ)); simpa using this

private lemma Real.rpow_pos' {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q > 0 := by
  rcases lt_or_eq_of_le (ratPow_nonneg hx q) with h | h
  · exact h
  · exfalso
    have hadd := ratPow_add hx q (-q)
    rw [add_neg_cancel, rpow_zero' hx, ← h, zero_mul] at hadd
    exact one_ne_zero hadd

private lemma Real.rpow_gt_one' {x s:ℝ} (hx: x > 1) (hs: s > 0) : rpow x s > 1 := by
  have hx0 : (0:ℝ) < x := by linarith
  choose s' hs' using eq_lim_of_rat s
  rw [rpow_eq_lim_ratPow hx0 hs']
  set b : Sequence := ((fun n ↦ x^(s' n:ℝ)):Sequence) with hb
  have hconv : b.Convergent := ratPow_continuous hx0 hs'
  set c : ℝ := x^(s/2) with hc
  have hc1 : c > 1 := by rw [hc]; exact Real.one_lt_rpow_iff_of_pos hx0 |>.mpr (Or.inl ⟨hx, by linarith⟩)
  have hs'2 := hs'
  rw [Sequence.tendsTo_iff] at hs'2
  obtain ⟨M, hM⟩ := hs'2 (s/2) (by linarith)
  by_contra hlt; rw [gt_iff_lt, not_lt] at hlt
  have htend := lim_def hconv
  rw [Sequence.tendsTo_iff] at htend
  obtain ⟨N, hN⟩ := htend ((c - 1)/2) (by linarith)
  set n := max (max N M) 0 with hn
  have hbn := hN n (le_trans (le_max_left _ _) (le_max_left _ _))
  have hn0 : (0:ℤ) ≤ n := le_max_right _ _
  have hbge : b n ≥ c := by
    rw [hb]; simp only [Sequence.instCoeFun, Sequence.ofNatFun]
    rw [if_pos hn0]
    apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hx)
    have hMn := hM n (le_trans (le_max_right _ _) (le_max_left _ _))
    simp only [Sequence.instCoeFun, Sequence.ofNatFun] at hMn
    rw [if_pos hn0, abs_le] at hMn
    linarith [hMn.1]
  rw [abs_le] at hbn
  linarith [hbn.2, hbge]

private lemma Real.rpow_gt_one_iff' {x s:ℝ} (hx: x > 1) : rpow x s > 1 ↔ s > 0 := by
  have hx0 : x > 0 := by linarith
  constructor
  · intro h; by_contra hs; push_neg at hs
    rcases lt_or_eq_of_le hs with hlt | heq
    · have hneg : rpow x (-s) > 1 := rpow_gt_one' hx (by linarith)
      have he := ratPow_neg hx0 (-s); rw [neg_neg] at he
      rw [he, gt_iff_lt, lt_div_iff₀ (by linarith)] at h
      linarith
    · rw [heq, rpow_zero' hx0] at h; linarith
  · exact rpow_gt_one' hx

private lemma Real.rpow_one_base' (s:ℝ) : rpow (1:ℝ) s = 1 := by
  choose s' hs' using eq_lim_of_rat s
  rw [rpow_eq_lim_ratPow (by norm_num) hs']
  simp only [Real.one_rpow]
  exact (lim_eq.mp (lim_of_const 1)).2

theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  have hy0 : rpow y q > 0 := rpow_pos' hy q
  have hx0 : rpow x q > 0 := rpow_pos' hx q
  constructor
  · intro hxy
    have hgt : rpow (x/y) q > 1 := rpow_gt_one' (by rw [gt_iff_lt, lt_div_iff₀ hy]; linarith) h
    have he : rpow x q = rpow (x/y) q * rpow y q := by
      rw [← ratPow_mul (by positivity) hy q, div_mul_cancel₀ _ (ne_of_gt hy)]
    rw [he]; nlinarith [hgt, hy0]
  · intro hgt
    by_contra hle; push_neg at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hgt2 : rpow (y/x) q > 1 := rpow_gt_one' (by rw [gt_iff_lt, lt_div_iff₀ hx]; linarith) h
      have he : rpow y q = rpow (y/x) q * rpow x q := by
        rw [← ratPow_mul (by positivity) hx q, div_mul_cancel₀ _ (ne_of_gt hx)]
      rw [he] at hgt; nlinarith [hgt2, hx0, hgt]
    · rw [heq] at hgt; linarith

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  have hx0 : x > 0 := by linarith
  have hr0 : rpow x r > 0 := rpow_pos' hx0 r
  have hqr : rpow x q = rpow x (q-r) * rpow x r := by
    rw [← ratPow_add hx0 (q-r) r, sub_add_cancel]
  rw [hqr, gt_iff_lt, lt_mul_iff_one_lt_left hr0]
  constructor
  · intro hh; have := (rpow_gt_one_iff' hx).mp hh; linarith
  · intro hh; exact (rpow_gt_one_iff' hx).mpr (by linarith)

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q > rpow x r ↔ q < r := by
  have hinvpos : (0:ℝ) < 1/x := by positivity
  have hinv1 : (1/x) > 1 := by rw [gt_iff_lt, lt_div_iff₀ hx0]; linarith
  have hpq : rpow (1/x) q > 0 := rpow_pos' hinvpos q
  have hpr : rpow (1/x) r > 0 := rpow_pos' hinvpos r
  have hrel : ∀ s, rpow x s * rpow (1/x) s = 1 := by
    intro s
    rw [← ratPow_mul hx0 hinvpos, mul_one_div_cancel (ne_of_gt hx0), rpow_one_base']
  have hxq : rpow x q = 1 / rpow (1/x) q := by rw [eq_div_iff (ne_of_gt hpq)]; linarith [hrel q]
  have hxr : rpow x r = 1 / rpow (1/x) r := by rw [eq_div_iff (ne_of_gt hpr)]; linarith [hrel r]
  rw [hxq, hxr, gt_iff_lt, one_div_lt_one_div hpr hpq, ← gt_iff_lt, ratPow_mono_of_gt_one hinv1]

end Chapter6
