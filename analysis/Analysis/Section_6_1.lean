import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $ε$-closeness, $ε$-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed s, the function ε ↦ ε.Steady s is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed s, the function ε ↦ ε.EventuallySteady s is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as Chapter5.Sequence.IsCauchy.coe -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  rw [Rat.steady_def, Real.steady_def]
  constructor
  · intro h n hn m hm
    have hh := h n hn m hm
    simp only [Rat.Close] at hh
    rw [Real.Close, Real.dist_eq, Chapter5.coe_sequence_eval, Chapter5.coe_sequence_eval]
    exact_mod_cast hh
  · intro h n hn m hm
    have hh := h n hn m hm
    rw [Real.Close, Real.dist_eq, Chapter5.coe_sequence_eval, Chapter5.coe_sequence_eval] at hh
    simp only [Rat.Close]
    exact_mod_cast hh

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  have hcomm : ∀ N:ℤ, ((a:Sequence)).from N = ((a.from N : Chapter5.Sequence):Sequence) := by
    intro N
    ext n
    · rfl
    · by_cases hc : n ≥ N
      · rw [Sequence.from_eval (a:Sequence) hc, Chapter5.coe_sequence_eval,
          Chapter5.coe_sequence_eval, Chapter5.Sequence.from_eval a hc]
      · have hlt : n < max a.n₀ N := lt_of_lt_of_le (lt_of_not_ge hc) (le_max_right _ _)
        rw [((a:Sequence).from N).vanish n hlt, Chapter5.coe_sequence_eval,
          (a.from N).vanish n hlt]
        norm_num
  rw [Rat.eventuallySteady_def, Real.eventuallySteady_def]
  constructor
  · rintro ⟨N, hN, hs⟩
    refine ⟨N, hN, ?_⟩
    rw [hcomm]
    exact (is_steady_of_rat ε (a.from N)).mp hs
  · rintro ⟨N, hN, hs⟩
    refine ⟨N, hN, (is_steady_of_rat ε (a.from N)).mpr ?_⟩
    rw [← hcomm]
    exact hs

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hNm, hclose⟩ := h ε hε
    refine ⟨max a.m N, fun n hn => ?_⟩
    have hc := hclose n (by show n ≥ max a.m N; exact hn)
    rwa [Sequence.from_eval a (le_trans (le_max_right _ _) hn), Real.Close, Real.dist_eq] at hc
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max a.m N, le_max_left _ _, fun n hn => ?_⟩
    have hm : (a.from (max a.m N)).m = max a.m N := by show max a.m (max a.m N) = max a.m N; omega
    rw [hm] at hn
    have hnN : n ≥ N := le_trans (le_max_right _ _) hn
    rw [Real.Close, Sequence.from_eval a hn, Real.dist_eq]
    exact hN n hnN

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  have hm : seq_6_1_6.m = 0 := rfl
  have heval : ∀ n:ℤ, n ≥ 0 → seq_6_1_6 n = 1 - (10:ℝ)^(-n-1) := by
    intro n hn
    rw [seq_6_1_6]
    simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le]
    rw [if_pos (by omega), show ((n.toNat:ℕ):ℤ) = n from Int.toNat_of_nonneg hn]
  rw [Real.eventuallyClose_def]
  refine ⟨1, by rw [hm]; norm_num, ?_⟩
  rw [Real.closeSeq_def]
  intro n hn
  have hfm : (seq_6_1_6.from 1).m = 1 := by show max seq_6_1_6.m 1 = 1; rw [hm]; norm_num
  rw [hfm] at hn
  rw [Sequence.from_eval seq_6_1_6 hn, heval n (by omega), Real.dist_eq,
    show (1 - (10:ℝ)^(-n-1)) - 1 = -(10^(-n-1)) by ring, abs_neg, abs_of_nonneg (by positivity)]
  calc (10:ℝ)^(-n-1) ≤ (10:ℝ)^(-2:ℤ) := by apply zpow_le_zpow_right₀ (by norm_num); omega
    _ = 0.01 := by norm_num

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  have heval : ∀ n:ℤ, n ≥ 0 → seq_6_1_6 n = 1 - (10:ℝ)^(-n-1) := by
    intro n hn
    rw [seq_6_1_6]; simp only [Sequence.instCoeFun, Sequence.ofNatFun, ge_iff_le]
    rw [if_pos (by omega), show ((n.toNat:ℕ):ℤ) = n from Int.toNat_of_nonneg hn]
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1/ε)
  refine ⟨max K 1, fun n hn => ?_⟩
  have hn0 : n ≥ 0 := by have : max (K:ℤ) 1 ≤ n := hn; omega
  have hnK : (K:ℝ) ≤ (n:ℝ) := by
    have : (K:ℤ) ≤ n := by have : max (K:ℤ) 1 ≤ n := hn; omega
    exact_mod_cast this
  rw [heval n hn0, show (1 - (10:ℝ)^(-n-1)) - 1 = -(10^(-n-1)) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  have h10pos : (0:ℝ) < (10:ℝ)^(n+1) := by positivity
  have hpow : (n:ℝ) + 1 ≤ (10:ℝ)^(n+1) := by
    have key : (1:ℝ) + ((n+1).toNat:ℝ) * 9 ≤ (1+9)^((n+1).toNat) :=
      one_add_mul_le_pow (by norm_num) _
    have hcast : ((n+1).toNat:ℝ) = (n:ℝ)+1 := by
      have h := Int.toNat_of_nonneg (show (0:ℤ) ≤ n+1 by omega)
      exact_mod_cast h
    rw [hcast] at key
    norm_num at key
    have hnn : (0:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn0
    rw [show (10:ℝ)^(n+1) = (10:ℝ)^((n+1).toNat) from by rw [← zpow_natCast]; congr 1; omega]
    nlinarith [key, hnn]
  rw [div_lt_iff₀ hε] at hK
  rw [show (10:ℝ)^(-n-1) = 1/(10:ℝ)^(n+1) from by rw [one_div, ← zpow_neg]; congr 1; omega,
    div_le_iff₀ h10pos]
  nlinarith [hK, mul_le_mul_of_nonneg_right hnK hε.le, mul_le_mul_of_nonneg_right hpow hε.le,
    mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ (n:ℝ)+1 by linarith) hε.le, hε]

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of 0 if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  obtain ⟨L, hL⟩ := h
  rw [tendsTo_iff] at hL
  rw [Sequence.isCauchy_def]
  intro ε hε
  obtain ⟨N0, hN0⟩ := hL (ε/2) (by linarith)
  set M := max a.m N0 with hMdef
  refine ⟨M, le_max_left _ _, ?_⟩
  rw [Real.steady_def]
  intro n hn m hm
  have hfm : (a.from M).m = M := by rw [hMdef]; show max a.m (max a.m N0) = max a.m N0; omega
  rw [hfm] at hn hm
  rw [Real.close_def, Real.dist_eq, Sequence.from_eval a hn, Sequence.from_eval a hm]
  have h1 := hN0 n (le_trans (le_max_right _ _) hn)
  have h2 := hN0 m (le_trans (le_max_right _ _) hm)
  calc |a n - a m| = |(a n - L) + -(a m - L)| := by congr 1; ring
    _ ≤ |a n - L| + |-(a m - L)| := abs_add_le _ _
    _ ≤ ε/2 + ε/2 := by rw [abs_neg]; linarith
    _ = ε := by ring

/-- Example 6.1.13 -/
example : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  rw [Real.eventuallySteady_def]
  rintro ⟨N, hN, hsteady⟩
  rw [Real.steady_def] at hsteady
  set a : Sequence := ((fun n ↦ (-1:ℝ)^n):Sequence) with ha
  have hm : a.m = 0 := rfl
  have hfm : (a.from N).m = max 0 N := by show max a.m N = max 0 N; rw [hm]
  set k : ℕ := (max 0 N).toNat with hk
  have hkz : ((k:ℕ):ℤ) = max 0 N := by rw [hk, Int.toNat_of_nonneg (le_max_left _ _)]
  have hge0 : (k:ℤ) ≥ (a.from N).m := by rw [hfm, hkz]
  have hge1 : (k:ℤ)+1 ≥ (a.from N).m := by rw [hfm, hkz]; omega
  have hc := hsteady (k:ℤ) hge0 ((k:ℤ)+1) hge1
  rw [Real.close_def, Real.dist_eq,
      Sequence.from_eval a (by rw [hkz]; exact le_max_right _ _ : (k:ℤ) ≥ N),
      Sequence.from_eval a (by rw [hkz]; have := le_max_right 0 N; omega : (k:ℤ)+1 ≥ N)] at hc
  rw [ha, show ((k:ℤ)+1) = (((k+1:ℕ)):ℤ) by push_cast; ring] at hc
  simp only [Sequence.instCoeFun] at hc
  rw [if_pos (by positivity), if_pos (by positivity), Int.toNat_natCast, Int.toNat_natCast,
    pow_succ] at hc
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow] at hc; norm_num at hc
  · rw [ho.neg_one_pow] at hc; norm_num at hc

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  intro h
  obtain ⟨N, hN, hsteady⟩ := h 0.1 (by norm_num)
  rw [Real.steady_def] at hsteady
  set a : Sequence := ((fun n ↦ (-1:ℝ)^n):Sequence) with ha
  have hm : a.m = 0 := rfl
  have hfm : (a.from N).m = max 0 N := by show max a.m N = max 0 N; rw [hm]
  set k : ℕ := (max 0 N).toNat with hk
  have hkz : ((k:ℕ):ℤ) = max 0 N := by rw [hk, Int.toNat_of_nonneg (le_max_left _ _)]
  have hge0 : (k:ℤ) ≥ (a.from N).m := by rw [hfm, hkz]
  have hge1 : (k:ℤ)+1 ≥ (a.from N).m := by rw [hfm, hkz]; omega
  have hc := hsteady (k:ℤ) hge0 ((k:ℤ)+1) hge1
  rw [Real.close_def, Real.dist_eq,
      Sequence.from_eval a (by rw [hkz]; exact le_max_right _ _ : (k:ℤ) ≥ N),
      Sequence.from_eval a (by rw [hkz]; have := le_max_right 0 N; omega : (k:ℤ)+1 ≥ N)] at hc
  rw [ha, show ((k:ℤ)+1) = (((k+1:ℕ)):ℤ) by push_cast; ring] at hc
  simp only [Sequence.instCoeFun] at hc
  rw [if_pos (by positivity), if_pos (by positivity), Int.toNat_natCast, Int.toNat_natCast,
    pow_succ] at hc
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow] at hc; norm_num at hc
  · rw [ho.neg_one_pow] at hc; norm_num at hc

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  rintro ⟨L, hL⟩
  rw [Sequence.tendsTo_iff] at hL
  obtain ⟨N, hN⟩ := hL 0.5 (by norm_num)
  set a : Sequence := ((fun n ↦ (-1:ℝ)^n):Sequence) with ha
  set k : ℕ := (max 0 N).toNat with hk
  have hkz : ((k:ℕ):ℤ) = max 0 N := by rw [hk, Int.toNat_of_nonneg (le_max_left _ _)]
  have e1 : a (2*(k:ℤ)) = 1 := by
    rw [ha]; simp only [Sequence.instCoeFun]
    rw [if_pos (by positivity), show (2*(k:ℤ)).toNat = 2*k by omega, (even_two_mul k).neg_one_pow]
  have e2 : a (2*(k:ℤ)+1) = -1 := by
    rw [ha]; simp only [Sequence.instCoeFun]
    rw [if_pos (by positivity), show (2*(k:ℤ)+1).toNat = 2*k+1 by omega,
      Odd.neg_one_pow (show Odd (2*k+1) from ⟨k, rfl⟩)]
  have h1 := hN (2*(k:ℤ)) (by rw [hkz] at *; have := le_max_right 0 N; omega)
  have h2 := hN (2*(k:ℤ)+1) (by rw [hkz] at *; have := le_max_right 0 N; omega)
  rw [e1] at h1; rw [e2] at h2
  rw [abs_le] at h1 h2
  norm_num at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by sorry

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  obtain ⟨N0, hN0, hsteady⟩ := h 1 one_pos
  rw [Real.steady_def] at hsteady
  set N := max a.m N0 with hNdef
  have hfm : (a.from N0).m = N := by rw [hNdef]
  have htail : ∀ n, n ≥ N → |a n| ≤ |a N| + 1 := by
    intro n hn
    have hc := hsteady n (by rw [hfm]; exact hn) N (by rw [hfm])
    rw [Real.close_def, Real.dist_eq,
        Sequence.from_eval a (le_trans (le_max_right _ _) hn),
        Sequence.from_eval a (le_max_right _ _)] at hc
    calc |a n| = |(a n - a N) + a N| := by congr 1; ring
      _ ≤ |a n - a N| + |a N| := abs_add_le _ _
      _ ≤ |a N| + 1 := by linarith
  have hne : (Finset.Icc a.m N).Nonempty := Finset.nonempty_Icc.mpr (le_max_left _ _)
  set B := (Finset.Icc a.m N).sup' hne (fun n => |a n|) with hB
  refine ⟨max B (|a N|+1), le_trans (by positivity) (le_max_right _ _), fun n => ?_⟩
  rcases le_or_gt N n with hge | hlt
  · exact le_trans (htail n hge) (le_max_right _ _)
  · rcases le_or_gt a.m n with hge2 | hlt2
    · have hmem : n ∈ Finset.Icc a.m N := by rw [Finset.mem_Icc]; omega
      exact le_trans (Finset.le_sup' (fun n => |a n|) hmem) (le_max_left _ _)
    · rw [a.vanish n hlt2, abs_zero]
      exact le_trans (by positivity) (le_max_right _ _)

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  obtain ⟨L, hL⟩ := h
  rw [tendsTo_iff] at hL
  obtain ⟨N0, hN0⟩ := hL 1 one_pos
  set N := max N0 a.m with hNdef
  have htail : ∀ n, n ≥ N → |a n| ≤ |L| + 1 := by
    intro n hn
    have hc := hN0 n (le_trans (le_max_left _ _) hn)
    calc |a n| = |(a n - L) + L| := by congr 1; ring
      _ ≤ |a n - L| + |L| := abs_add_le _ _
      _ ≤ |L| + 1 := by linarith
  have hne : (Finset.Icc a.m N).Nonempty := Finset.nonempty_Icc.mpr (le_max_right _ _)
  set B := (Finset.Icc a.m N).sup' hne (fun n => |a n|) with hB
  refine ⟨max B (|L|+1), le_trans (by positivity) (le_max_right _ _), fun n => ?_⟩
  rcases le_or_gt N n with hge | hlt
  · exact le_trans (htail n hge) (le_max_right _ _)
  · rcases le_or_gt a.m n with hge2 | hlt2
    · have hmem : n ∈ Finset.Icc a.m N := by rw [Finset.mem_Icc]; omega
      exact le_trans (Finset.le_sup' (fun n => |a n|) hmem) (le_max_left _ _)
    · rw [a.vanish n hlt2, abs_zero]
      exact le_trans (by positivity) (le_max_right _ _)

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  rintro ⟨M, hM, hB⟩
  obtain ⟨m, hm⟩ := exists_nat_gt M
  have hb := hB (m:ℤ)
  rw [Sequence.eval_coe] at hb
  rw [abs_of_pos (by positivity)] at hb
  linarith

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  rintro ⟨L, hL⟩
  rw [Sequence.tendsTo_iff] at hL
  obtain ⟨N, hN⟩ := hL 1 one_pos
  obtain ⟨m0, hm0⟩ := exists_nat_gt (L+1)
  set m : ℕ := max m0 N.toNat with hmdef
  have hmN : (m:ℤ) ≥ N := by rw [hmdef]; omega
  have hb := hN (m:ℤ) hmN
  rw [Sequence.eval_coe, abs_le] at hb
  have hm0le : (m0:ℝ) ≤ (m:ℝ) := by rw [hmdef]; exact_mod_cast le_max_left _ _
  linarith [hb.2, hm0, hm0le]

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  rw [tendsTo_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  refine ⟨max Na Nb, fun n hn => ?_⟩
  rw [Sequence.add_eval]
  have h1 := hNa n (le_trans (le_max_left _ _) hn)
  have h2 := hNb n (le_trans (le_max_right _ _) hn)
  calc |a n + b n - (L + M)| = |(a n - L) + (b n - M)| := by congr 1; ring
    _ ≤ |a n - L| + |b n - M| := abs_add_le _ _
    _ ≤ ε/2 + ε/2 := by linarith
    _ = ε := by ring

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  have htab := tendsTo_add (lim_def ha) (lim_def hb)
  have hconv : (a+b).Convergent := ⟨_, htab⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (a+b) hne ⟨lim_def hconv, htab⟩

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  rw [tendsTo_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := ha 1 one_pos
  obtain ⟨N1, hN1⟩ := ha (ε/2/(|M|+1)) (by positivity)
  obtain ⟨N2, hN2⟩ := hb (ε/2/(|L|+1)) (by positivity)
  refine ⟨max N0 (max N1 N2), fun n hn => ?_⟩
  have e0 := hN0 n (le_trans (le_max_left _ _) hn)
  have e1 := hN1 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have e2 := hN2 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  rw [Sequence.mul_eval]
  have habs : |a n| ≤ |L| + 1 := by
    calc |a n| = |(a n - L) + L| := by congr 1; ring
      _ ≤ |a n - L| + |L| := abs_add_le _ _
      _ ≤ |L| + 1 := by linarith
  have t1 : |a n| * |b n - M| ≤ ε/2 := by
    calc |a n| * |b n - M| ≤ (|L|+1) * (ε/2/(|L|+1)) := by gcongr
      _ = ε/2 := by field_simp
  have t2 : |M| * |a n - L| ≤ ε/2 := by
    calc |M| * |a n - L| ≤ (|M|+1) * (ε/2/(|M|+1)) := by
          gcongr
          · linarith [abs_nonneg M]
      _ = ε/2 := by field_simp
  calc |a n * b n - L * M| = |a n * (b n - M) + M * (a n - L)| := by congr 1; ring
    _ ≤ |a n * (b n - M)| + |M * (a n - L)| := abs_add_le _ _
    _ = |a n| * |b n - M| + |M| * |a n - L| := by rw [abs_mul, abs_mul]
    _ ≤ ε := by linarith

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  have hmul := tendsTo_mul (lim_def ha) (lim_def hb)
  have hconv : (a*b).Convergent := ⟨_, hmul⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (a*b) hne ⟨lim_def hconv, hmul⟩


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  rw [tendsTo_iff] at ha ⊢
  intro ε hε
  rcases eq_or_ne c 0 with hc | hc
  · refine ⟨a.m, fun n _ => ?_⟩
    rw [Sequence.smul_eval, hc]; simp; linarith
  · obtain ⟨N, hN⟩ := ha (ε/|c|) (div_pos hε (abs_pos.mpr hc))
    refine ⟨N, fun n hn => ?_⟩
    rw [Sequence.smul_eval, show c * a n - c * L = c * (a n - L) by ring, abs_mul,
      show ε = |c| * (ε/|c|) by field_simp]
    gcongr
    exact hN n hn

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  have hsm := tendsTo_smul c (lim_def ha)
  have hconv : (c • a).Convergent := ⟨_, hsm⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (c • a) hne ⟨lim_def hconv, hsm⟩

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  rw [tendsTo_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  refine ⟨max Na Nb, fun n hn => ?_⟩
  rw [Sequence.sub_eval]
  have h1 := hNa n (le_trans (le_max_left _ _) hn)
  have h2 := hNb n (le_trans (le_max_right _ _) hn)
  calc |a n - b n - (L - M)| = |(a n - L) + -(b n - M)| := by congr 1; ring
    _ ≤ |a n - L| + |-(b n - M)| := abs_add_le _ _
    _ ≤ ε/2 + ε/2 := by rw [abs_neg]; linarith
    _ = ε := by ring

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  have hsub := tendsTo_sub (lim_def ha) (lim_def hb)
  have hconv : (a-b).Convergent := ⟨_, hsub⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (a-b) hne ⟨lim_def hconv, hsub⟩

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  rw [tendsTo_iff] at ha ⊢
  intro ε hε
  have hL : |L| > 0 := abs_pos.mpr hnon
  obtain ⟨N0, hN0⟩ := ha (|L|/2) (by positivity)
  obtain ⟨N1, hN1⟩ := ha (ε * |L|^2 / 2) (by positivity)
  refine ⟨max N0 N1, fun n hn => ?_⟩
  have e0 := hN0 n (le_trans (le_max_left _ _) hn)
  have e1 := hN1 n (le_trans (le_max_right _ _) hn)
  rw [Sequence.inv_eval]
  have hab : |a n| ≥ |L|/2 := by
    have h := abs_sub_abs_le_abs_sub L (a n)
    rw [abs_sub_comm L (a n)] at h
    linarith
  have han : a n ≠ 0 := abs_pos.mp (by linarith)
  rw [show (a n)⁻¹ - L⁻¹ = (L - a n)/(a n * L) by field_simp, abs_div, abs_mul,
    div_le_iff₀ (by positivity), abs_sub_comm L (a n)]
  calc |a n - L| ≤ ε * |L|^2 / 2 := e1
    _ ≤ ε * (|a n| * |L|) := by nlinarith [hab, hL, hε.le, mul_le_mul_of_nonneg_left hab hε.le]

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  have hinv := tendsTo_inv (lim_def ha) hnon
  have hconv : (a⁻¹).Convergent := ⟨_, hinv⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (a⁻¹) hne ⟨lim_def hconv, hinv⟩

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  have key : a / b = a * b⁻¹ := by
    ext n <;> first | rfl | (show a n / b n = a n * (b n)⁻¹; rw [div_eq_mul_inv])
  rw [key, show L / M = L * M⁻¹ from div_eq_mul_inv L M]
  exact tendsTo_mul ha (tendsTo_inv hb hnon)

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  have hdiv := tendsTo_div (lim_def ha) (lim_def hb) hnon
  have hconv : (a/b).Convergent := ⟨_, hdiv⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (a/b) hne ⟨lim_def hconv, hdiv⟩

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  rw [tendsTo_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha ε hε
  obtain ⟨Nb, hNb⟩ := hb ε hε
  refine ⟨max Na Nb, fun n hn => ?_⟩
  have h1 := hNa n (le_trans (le_max_left _ _) hn)
  have h2 := hNb n (le_trans (le_max_right _ _) hn)
  rw [Sequence.max_eval]
  exact le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le h1 h2)

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  have hmax := tendsTo_max (lim_def ha) (lim_def hb)
  have hconv : (max a b).Convergent := ⟨_, hmax⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (max a b) hne ⟨lim_def hconv, hmax⟩

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  rw [tendsTo_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha ε hε
  obtain ⟨Nb, hNb⟩ := hb ε hε
  refine ⟨max Na Nb, fun n hn => ?_⟩
  have h1 := hNa n (le_trans (le_max_left _ _) hn)
  have h2 := hNb n (le_trans (le_max_right _ _) hn)
  rw [Sequence.min_eval]
  exact le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le h1 h2)

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  have hmin := tendsTo_min (lim_def ha) (lim_def hb)
  have hconv : (min a b).Convergent := ⟨_, hmin⟩
  refine ⟨hconv, ?_⟩
  by_contra hne
  exact tendsTo_unique (min a b) hne ⟨lim_def hconv, hmin⟩

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n :=
  strictMono_nat_of_lt_succ (fun k => ha k) hnm

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  rw [tendsTo_iff, tendsTo_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N m, fun n hn => ?_⟩
    rw [Sequence.from_eval a (le_trans (le_max_right _ _) hn)]
    exact hN n (le_trans (le_max_left _ _) hn)
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N m, fun n hn => ?_⟩
    have hc := hN n (le_trans (le_max_left _ _) hn)
    rwa [Sequence.from_eval a (le_trans (le_max_right _ _) hn)] at hc

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  rw [tendsTo_iff, tendsTo_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N a.m, fun n hn => ?_⟩
    have hnm : n ≥ a.m := le_trans (le_max_right _ _) hn
    rw [Sequence.eval_mk _ hnm]
    exact hN (n + (k:ℤ)) (by have := le_trans (le_max_left _ _) hn; omega)
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max (N+k) (a.m+k), fun n hn => ?_⟩
    have hnk : n - (k:ℤ) ≥ a.m := by have := le_trans (le_max_right _ _) hn; omega
    have hb := hN (n - (k:ℤ)) (by have := le_trans (le_max_left _ _) hn; omega)
    rw [Sequence.eval_mk _ hnk] at hb
    rwa [show (n - (k:ℤ)) + (k:ℤ) = n by ring] at hb

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  sorry

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  sorry

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  sorry
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by sorry

end Chapter6
