import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from {name}`Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by rw [_root_.pow_add]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by rw [← _root_.pow_mul]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by rw [_root_.mul_pow]

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by exact pow_eq_zero_iff hn.ne'

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by positivity

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by positivity

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by exact pow_le_pow_left₀ hy hxy n

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by exact pow_lt_pow_left₀ hxy hy hn.ne'

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by rw [abs_pow]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from {name}`DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by rw [zpow_add₀ hx]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by rw [← _root_.zpow_mul]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by rw [_root_.mul_zpow]

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by positivity

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  rw [zpow_natCast, zpow_natCast]
  exact pow_le_pow_left₀ hy.le hxy m

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨m, rfl⟩ : ∃ m:ℕ, n = -(m:ℤ) := ⟨(-n).toNat, by omega⟩
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  gcongr

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  have pc : ∀ {a b:Real} {k:ℕ}, a > 0 → b > 0 → k ≠ 0 → a^k = b^k → a = b := by
    intro a b k ha hb hk hab
    apply le_antisymm <;>
    · by_contra hc
      push_neg at hc
      have := pow_lt_pow_left₀ hc (by positivity) hk
      simp [hab] at this
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · obtain ⟨m, rfl⟩ : ∃ m:ℕ, n = -(m:ℤ) := ⟨(-n).toNat, by omega⟩
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast] at hxy
    have hm : m ≠ 0 := by omega
    have : x^m = y^m := by field_simp at hxy; linarith
    exact pc hx hy (by omega) this
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    rw [zpow_natCast, zpow_natCast] at hxy
    exact pc hx hy (by omega) hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by rw [abs_zpow]

/-- Definition 5.6.2. We permit "junk values" when {lean}`x` is negative or {lean}`n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  refine ⟨le_refl _, ?_⟩
  rw [zero_pow (by omega)]; exact hx

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      calc (1:Real) = 1^n := (one_pow n).symm
        _ < y^n := pow_lt_pow_left₀ hy' (by norm_num) (by omega)
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    calc x < y := hy'
      _ = y^1 := (pow_one y).symm
      _ ≤ y^n := pow_le_pow_right₀ (by linarith) (by omega)
  linarith

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  apply le_csSup (rootset_bddAbove n hn)
  refine ⟨le_refl _, ?_⟩; rw [zero_pow (by omega)]; exact hx

private theorem powdiff (a b : Real) (n:ℕ) (hb: 0 ≤ b) (hab: b ≤ a) :
    a^n - b^n ≤ (a-b) * (n * a^(n-1)) := by
  rw [← geom_sum₂_mul a b n, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have ha : 0 ≤ a := le_trans hb hab
  calc (∑ i ∈ Finset.range n, a^i * b^(n-1-i))
      ≤ ∑ i ∈ Finset.range n, a^(n-1) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_range] at hi
        calc a^i * b^(n-1-i) ≤ a^i * a^(n-1-i) := by gcongr
          _ = a^(i + (n-1-i)) := by rw [pow_add]
          _ = a^(n-1) := by congr 1; omega
    _ = n * a^(n-1) := by rw [Finset.sum_const, Finset.card_range]; ring

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  set S := { y:Real | y ≥ 0 ∧ y^n ≤ x }
  have hbdd := Real.rootset_bddAbove (x:=x) n hn
  have hne := Real.rootset_nonempty hx n hn
  set r := x.root n with hr
  have hr0 : r ≥ 0 := Real.root_nonneg hx hn
  have hrsup : r = sSup S := rfl
  rcases lt_trichotomy (r^n) x with hlt | heq | hgt
  · exfalso
    set M := (n:Real)*(r+1)^(n-1) + 1 with hM
    have hMpos : M > 0 := by
      have : (0:Real) ≤ (n:Real)*(r+1)^(n-1) := by positivity
      linarith
    set ε := min 1 ((x - r^n)/M) with hε
    have hεpos : ε > 0 := by
      apply lt_min (by norm_num)
      apply div_pos (by linarith) hMpos
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεM : ε * M ≤ x - r^n := by
      have h2 : ε ≤ (x - r^n)/M := min_le_right _ _
      calc ε * M ≤ ((x-r^n)/M) * M := by apply mul_le_mul_of_nonneg_right h2 (le_of_lt hMpos)
        _ = x - r^n := by field_simp
    have hbound : (r+ε)^n ≤ x := by
      have hp := powdiff (r+ε) r n hr0 (by linarith)
      have : (r+ε - r) * (n*(r+ε)^(n-1)) ≤ ε * M := by
        rw [show r+ε-r = ε by ring]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hεpos)
        have : (r+ε)^(n-1) ≤ (r+1)^(n-1) := pow_le_pow_left₀ (by linarith : (0:Real) ≤ r+ε) (by linarith) _
        calc (n:Real)*(r+ε)^(n-1) ≤ (n:Real)*(r+1)^(n-1) := by gcongr
          _ ≤ M := by rw [hM]; linarith
      linarith
    have hmem : (r+ε) ∈ S := ⟨by linarith, hbound⟩
    have := le_csSup hbdd hmem
    rw [← hrsup] at this; linarith
  · exact heq
  · exfalso
    have hrpos : r > 0 := by
      rcases eq_or_lt_of_le hr0 with h | h
      · rw [← h, zero_pow (by omega)] at hgt; linarith
      · exact h
    set M := (n:Real)*r^(n-1) + 1 with hM
    have hMpos : M > 0 := by have : (0:Real) ≤ (n:Real)*r^(n-1) := by positivity
                             linarith
    set ε := min (r/2) ((r^n - x)/M) with hε
    have hεpos : ε > 0 := lt_min (by linarith) (div_pos (by linarith) hMpos)
    have hεr : ε ≤ r/2 := min_le_left _ _
    have hεM : ε * M ≤ r^n - x := by
      have h2 : ε ≤ (r^n - x)/M := min_le_right _ _
      calc ε * M ≤ ((r^n-x)/M)*M := mul_le_mul_of_nonneg_right h2 (le_of_lt hMpos)
        _ = r^n - x := by field_simp
    have hbound : x ≤ (r-ε)^n := by
      have hp := powdiff r (r-ε) n (by linarith) (by linarith)
      have : (r - (r-ε)) * (n*r^(n-1)) ≤ ε * M := by
        rw [show r-(r-ε) = ε by ring]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hεpos)
        rw [hM]
        have hpn : (0:Real) ≤ r^(n-1) := by positivity
        linarith
      have : r^n - (r-ε)^n ≤ r^n - x := le_trans hp (le_trans this hεM)
      linarith
    have hub : ∀ y ∈ S, y ≤ r - ε := by
      rintro y ⟨hy0, hyx⟩
      by_contra! hc
      have hlt2 : (r-ε)^n < y^n := pow_lt_pow_left₀ hc (by linarith) (by omega)
      linarith
    have := csSup_le hne hub
    rw [← hrsup] at this; linarith

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  have hrn : (x.root n)^n = x := Real.pow_of_root hx hn
  have hr0 := Real.root_nonneg hx hn
  constructor
  · rintro rfl; exact hrn
  · intro h
    rcases eq_or_lt_of_le hy with hy0 | hypos
    · have hx0 : x = 0 := by rw [← h, ← hy0, zero_pow (by omega)]
      have : x.root n = 0 := by
        have : (x.root n)^n = 0 := by rw [hrn, hx0]
        exact pow_eq_zero_iff (by omega) |>.mp this
      rw [this, ← hy0]
    · rcases eq_or_lt_of_le hr0 with hrr0 | hrpos
      · have hx0 : x = 0 := by rw [← hrn, ← hrr0, zero_pow (by omega)]
        rw [hx0] at h
        have : y = 0 := pow_eq_zero_iff (by omega) |>.mp h
        linarith
      · apply le_antisymm <;>
        · by_contra hc
          push_neg at hc
          have := pow_lt_pow_left₀ hc (by positivity) (show n ≠ 0 by omega)
          rw [hrn, h] at this
          simp at this

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  symm
  rw [Real.eq_root_iff_pow_eq (by positivity) hx hn]

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have hrn : (x.root n)^n = x := Real.pow_of_root hx hn
  have hr0 := Real.root_nonneg hx hn
  constructor
  · intro h; rw [← hrn]; positivity
  · intro h
    rcases eq_or_lt_of_le hr0 with he | hlt
    · exfalso; rw [← he, zero_pow (by omega)] at hrn; linarith
    · exact hlt

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  have hxn : (x.root n)^n = x := Real.pow_of_root hx hn
  have hyn : (y.root n)^n = y := Real.pow_of_root hy hn
  have hx0 := Real.root_nonneg hx hn
  have hy0 := Real.root_nonneg hy hn
  constructor
  · intro h
    by_contra! hc
    have : (x.root n)^n ≤ (y.root n)^n := pow_le_pow_left₀ hx0 hc n
    rw [hxn, hyn] at this; linarith
  · intro h
    rw [← hxn, ← hyn]
    exact pow_lt_pow_left₀ h hy0 (by omega)

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  have hk : k ≥ 1 := by omega
  have hx0 : x ≥ 0 := by linarith
  have hrk := Real.root_nonneg hx0 hk
  have hrl := Real.root_nonneg hx0 hl
  have e1 : (x.root k)^(k*l) = x^l := by rw [_root_.pow_mul, Real.pow_of_root hx0 hk]
  have e2 : (x.root l)^(k*l) = x^k := by rw [mul_comm, _root_.pow_mul, Real.pow_of_root hx0 hl]
  have hxlt : x^l < x^k := pow_lt_pow_right₀ hx hkl
  by_contra! hc
  have : (x.root l)^(k*l) ≤ (x.root k)^(k*l) := pow_le_pow_left₀ hrl hc _
  rw [e1, e2] at this; linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  have hk : k ≥ 1 := by omega
  have hx0' : x ≥ 0 := by linarith
  have hrk := Real.root_nonneg hx0' hk
  have hrl := Real.root_nonneg hx0' hl
  have e1 : (x.root k)^(k*l) = x^l := by rw [_root_.pow_mul, Real.pow_of_root hx0' hk]
  have e2 : (x.root l)^(k*l) = x^k := by rw [mul_comm, _root_.pow_mul, Real.pow_of_root hx0' hl]
  have hxlt : x^k < x^l := pow_lt_pow_right_of_lt_one₀ hx0 hx hkl
  by_contra! hc
  have : (x.root k)^(k*l) ≤ (x.root l)^(k*l) := pow_le_pow_left₀ hrk hc _
  rw [e1, e2] at this; linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  show sSup { y:Real | y ≥ 0 ∧ y^k ≤ 1 } = 1
  apply le_antisymm
  · apply csSup_le ⟨1, by refine ⟨by norm_num, by rw [one_pow]⟩⟩
    rintro y ⟨hy0, hyk⟩
    by_contra! hy'
    have : 1 < y^k := by
      calc (1:Real) = 1^k := (one_pow k).symm
        _ < y^k := pow_lt_pow_left₀ hy' (by norm_num) (by omega)
    linarith
  · apply le_csSup (rootset_bddAbove k hk)
    exact ⟨by norm_num, by rw [one_pow]⟩

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  have hx0 := Real.root_nonneg hx hn
  have hy0 := Real.root_nonneg hy hn
  symm
  rw [Real.eq_root_iff_pow_eq (by positivity) (mul_nonneg hx0 hy0) hn]
  rw [mul_pow, Real.pow_of_root hx hn, Real.pow_of_root hy hn]

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have hnm : n*m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrn0 := Real.root_nonneg hx hn
  have hrnm0 := Real.root_nonneg hx hnm
  symm
  rw [Real.eq_root_iff_pow_eq hrn0 hrnm0 hm]
  have key : ((x.root (n*m))^m) = x.root n := by
    rw [Real.eq_root_iff_pow_eq hx (_root_.pow_nonneg hrnm0 m) hn]
    rw [← _root_.pow_mul, mul_comm m n, Real.pow_of_root hx hnm]
  exact key

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  show sSup { y:Real | y ≥ 0 ∧ y^1 ≤ x } = x
  simp only [pow_one]
  have h : { y:Real | y ≥ 0 ∧ y ≤ x } = Set.Icc 0 x := by ext y; simp [Set.mem_Icc]
  rw [h, csSup_Icc hx.le]

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  apply le_antisymm <;>
  · by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (by positivity) (by omega : n ≠ 0)
    simp [h] at this

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by
      rw [ha] at hq
      have hb'0 : (b':ℚ) ≠ 0 := by positivity
      simp only [Int.cast_zero, zero_div] at hq
      rw [eq_comm, div_eq_zero_iff] at hq
      rcases hq with h | h
      · exact_mod_cast h
      · exact absurd h hb'0
    simp_all
  have : a' > 0 := by
    have hbq : (0:ℚ) < b := by exact_mod_cast hb
    have hb'q : (0:ℚ) < b' := by exact_mod_cast hb'
    have hpos : (0:ℚ) < a/b := by positivity
    rw [hq] at hpos
    have : (0:ℚ) < a' := by
      rw [div_pos_iff] at hpos
      rcases hpos with ⟨h1,_⟩ | ⟨_,h2⟩
      · exact h1
      · linarith
    exact_mod_cast this
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have hb : n > 0 := by omega
  have : ((1:ℤ)/(n:ℕ):ℚ) = (1/n:ℚ) := by push_cast; ring
  rw [← this, Real.ratPow_def hx 1 hb, zpow_one]

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have hb : (1:ℕ) > 0 := by norm_num
  have : ((n:ℚ)) = ((n:ℤ)/(1:ℕ):ℚ) := by push_cast; ring
  rw [this, Real.ratPow_def hx n hb, Real.root_one hx]

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  show (x.root q.den)^(q.num) > 0
  have hd : q.den ≥ 1 := by have := q.den_nz; omega
  have : x.root q.den > 0 := (Real.root_pos hx.le hd).mpr hx
  positivity

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  set b : ℕ := q.den * r.den with hb
  have hbpos : b > 0 := by have := q.den_nz; have := r.den_nz; positivity
  have hqd : (q.den:ℚ) ≠ 0 := by have := q.den_nz; positivity
  have hrd : (r.den:ℚ) ≠ 0 := by have := r.den_nz; positivity
  set a1 : ℤ := q.num * r.den with ha1
  set a2 : ℤ := r.num * q.den with ha2
  have hq : q = (a1 / b : ℚ) := by
    rw [ha1, hb]; push_cast; rw [mul_div_mul_right _ _ hrd, Rat.num_div_den]
  have hr : r = (a2 / b : ℚ) := by
    rw [ha2, hb]; push_cast
    rw [mul_comm (q.den:ℚ) (r.den:ℚ), mul_div_mul_right _ _ hqd, Rat.num_div_den]
  have hsum : q + r = ((a1+a2) / b : ℚ) := by rw [hq, hr]; push_cast; ring
  have hrt : x.root b ≠ 0 := ne_of_gt ((Real.root_pos hx.le hbpos).mpr hx)
  have eq1 : x^q = (x.root b)^a1 := by rw [hq]; exact Real.ratPow_def hx a1 hbpos
  have eq2 : x^r = (x.root b)^a2 := by rw [hr]; exact Real.ratPow_def hx a2 hbpos
  have eq3 : x^(q+r) = (x.root b)^(a1+a2) := by
    rw [hsum]
    have := Real.ratPow_def hx (a1+a2) hbpos
    rw [show ((a1+a2:ℤ):ℚ) = (a1:ℚ)+(a2:ℚ) by push_cast; ring] at this
    exact this
  rw [eq1, eq2, eq3, zpow_add₀ hrt]

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
private theorem zpow_ratPow {x:Real} (hx: x > 0) (q:ℚ) (m:ℤ) : (x^q)^m = x^((m:ℚ)*q) := by
  have hd : q.den ≥ 1 := by have := q.den_nz; omega
  have hdpos : q.den > 0 := by omega
  rw [show x^q = (x.root q.den)^(q.num) from rfl, ← _root_.zpow_mul]
  have hmq : (m:ℚ)*q = ((q.num*m) / q.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    field_simp
  rw [hmq, show ((q.num:ℚ) * (m:ℚ) / (q.den:ℚ)) = (((q.num*m:ℤ):ℚ) / (q.den:ℚ)) by push_cast; ring]
  exact (Real.ratPow_def hx (q.num*m) hdpos).symm

theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  have hrd : r.den ≥ 1 := by have := r.den_nz; omega
  have hxq : x^q > 0 := Real.ratPow_pos hx q
  have hxqr : x^(q*r) > 0 := Real.ratPow_pos hx (q*r)
  have hupos : (x^q).root r.den > 0 := (Real.root_pos hxq.le hrd).mpr hxq
  have hud : ((x^q).root r.den)^(r.den) = x^q := Real.pow_of_root hxq.le hrd
  have lhs_eq : (x^q)^r = ((x^q).root r.den)^(r.num) := rfl
  have hrnum : (r.num:ℚ) = r * r.den := by
    have h := Rat.num_div_den r
    have hd : (r.den:ℚ) ≠ 0 := by have := r.den_nz; positivity
    field_simp at h ⊢; linarith [h]
  have key1 : ((x^q)^r)^(r.den) = x^((r.num:ℚ)*q) := by
    rw [lhs_eq, ← _root_.zpow_natCast (((x^q).root r.den)^r.num) r.den, ← _root_.zpow_mul,
        mul_comm r.num, _root_.zpow_mul, _root_.zpow_natCast, hud]
    exact zpow_ratPow hx q r.num
  have key2 : (x^(q*r))^(r.den) = x^((r.num:ℚ)*q) := by
    rw [← _root_.zpow_natCast (x^(q*r)) r.den, zpow_ratPow hx (q*r) (r.den:ℤ)]
    congr 1
    rw [hrnum]; push_cast; ring
  exact Real.pow_cancel (Real.ratPow_pos hxq r) hxqr hrd (key1.trans key2.symm)

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  show (x.root (-q).den)^((-q).num) = 1 / (x.root q.den)^(q.num)
  rw [Rat.neg_den, Rat.neg_num, _root_.zpow_neg, one_div]

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  have hd : q.den ≥ 1 := by have := q.den_nz; omega
  have hnum : q.num > 0 := Rat.num_pos.mpr h
  rw [show x^q = (x.root q.den)^(q.num) from rfl, show y^q = (y.root q.den)^(q.num) from rfl]
  have hrx := Real.root_pos hx.le hd |>.mpr hx
  have hry := Real.root_pos hy.le hd |>.mpr hy
  set n := q.num.toNat with hn
  have hnn : q.num = (n:ℤ) := by rw [hn, Int.toNat_of_nonneg hnum.le]
  rw [hnn, zpow_natCast, zpow_natCast]
  have hnpos : n ≥ 1 := by omega
  constructor
  · intro hxy
    have : x.root q.den > y.root q.den := (Real.root_mono hx.le hy.le hd).mp hxy
    exact pow_lt_pow_left₀ this hry.le (by omega)
  · intro hxy
    by_contra! hc
    rcases eq_or_lt_of_le hc with he | hlt
    · rw [he] at hxy; exact lt_irrefl _ hxy
    · have hle : x.root q.den ≤ y.root q.den := le_of_lt ((Real.root_mono hy.le hx.le hd).mp hlt)
      have : (x.root q.den)^n ≤ (y.root q.den)^n := pow_le_pow_left₀ hrx.le hle n
      linarith

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
private theorem rp_gt_one {x:Real} (hx: x > 1) (s:ℚ) : x^s > 1 ↔ s > 0 := by
  have hd : s.den ≥ 1 := by have := s.den_nz; omega
  have hroot1 : x.root s.den > 1 := by
    have := (Real.root_mono (x:=x) (y:=1) (by linarith) (zero_le_one) hd).mp hx
    rwa [Real.root_of_one hd] at this
  rw [show x^s = (x.root s.den)^(s.num) from rfl]
  rw [show (1:Real) = (x.root s.den)^(0:ℤ) by simp, gt_iff_lt, zpow_lt_zpow_iff_right₀ hroot1]
  exact ⟨fun h => Rat.num_pos.mp h, fun h => Rat.num_pos.mpr h⟩

private theorem rp_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) (s:ℚ) : x^s > 1 ↔ s < 0 := by
  have hd : s.den ≥ 1 := by have := s.den_nz; omega
  have hr0 : x.root s.den > 0 := (Real.root_pos hx0.le hd).mpr hx0
  have hroot1 : x.root s.den < 1 := by
    have := (Real.root_mono (x:=1) (y:=x) (zero_le_one) hx0.le hd).mp hx
    rwa [Real.root_of_one hd] at this
  rw [show x^s = (x.root s.den)^(s.num) from rfl]
  rw [show (1:Real) = (x.root s.den)^(0:ℤ) by simp, gt_iff_lt]
  constructor
  · intro h
    by_contra! hc
    have hn0 : s.num ≥ 0 := Rat.num_nonneg.mpr hc
    rcases eq_or_lt_of_le hn0 with he | hlt
    · rw [← he] at h; simp at h
    · have := zpow_lt_zpow_right_of_lt_one₀ hr0 hroot1 (show (0:ℤ) < s.num from hlt)
      linarith
  · intro h
    have hnum : s.num < 0 := Rat.num_neg.mpr h
    exact zpow_lt_zpow_right_of_lt_one₀ hr0 hroot1 hnum

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  have hxp : x > 0 := by linarith
  have hrpos : x^r > 0 := Real.ratPow_pos hxp r
  have key : x^(q-r) > 1 ↔ q-r > 0 := rp_gt_one hx (q-r)
  have hqr : x^(q-r) * x^r = x^q := by rw [← Real.ratPow_add hxp]; ring_nf
  constructor
  · intro h
    have h1 : x^(q-r) > 1 := by
      by_contra! hc
      have : x^(q-r) * x^r ≤ 1 * x^r := mul_le_mul_of_nonneg_right hc hrpos.le
      rw [hqr, one_mul] at this; linarith
    have := key.mp h1; linarith
  · intro h
    have h1 : x^(q-r) > 1 := key.mpr (by linarith)
    have : x^(q-r) * x^r > 1 * x^r := mul_lt_mul_of_pos_right h1 hrpos
    rw [hqr, one_mul] at this; exact this

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  have hrpos : x^r > 0 := Real.ratPow_pos hx0 r
  have key : x^(q-r) > 1 ↔ q-r < 0 := rp_lt_one hx0 hx (q-r)
  have hqr : x^(q-r) * x^r = x^q := by rw [← Real.ratPow_add hx0]; ring_nf
  constructor
  · intro h
    have h1 : x^(q-r) > 1 := by
      by_contra! hc
      have : x^(q-r) * x^r ≤ 1 * x^r := mul_le_mul_of_nonneg_right hc hrpos.le
      rw [hqr, one_mul] at this; linarith
    have := key.mp h1; linarith
  · intro h
    have h1 : x^(q-r) > 1 := key.mpr (by linarith)
    have : x^(q-r) * x^r > 1 * x^r := mul_lt_mul_of_pos_right h1 hrpos
    rw [hqr, one_mul] at this; exact this

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  show ((x*y).root q.den)^(q.num) = (x.root q.den)^(q.num) * (y.root q.den)^(q.num)
  have hd : q.den ≥ 1 := by have := q.den_nz; omega
  rw [Real.root_mul hx.le hy.le hd, mul_zpow]

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, _root_.pow_mul]
  positivity

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]
    · exact le_of_lt ((Real.ratPow_mono hy hx hq).mp hlt)
  · rw [max_eq_left h, max_eq_left]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]
    · exact le_of_lt ((Real.ratPow_mono hx hy hq).mp hlt)

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]
    · exact le_of_lt ((Real.ratPow_mono hy hx hq).mp hlt)
  · rw [min_eq_right h, min_eq_right]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]
    · exact le_of_lt ((Real.ratPow_mono hx hy hq).mp hlt)

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
