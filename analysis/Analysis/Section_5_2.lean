import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro n h1 _
  rw [Sequence.n0_coe] at h1
  rw [Sequence.eval_coe_at_int, Sequence.eval_coe_at_int, if_pos h1, if_pos h1]
  unfold Rat.Close
  rw [show ((-1:ℚ)^n.toNat - 1.1*(-1)^n.toNat) = (-1)^n.toNat * (-0.1) by ring,
    abs_mul, abs_pow, abs_neg, abs_one, one_pow]
  norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; push_neg; exact ⟨0, 1, by unfold Rat.Close; norm_num⟩

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.Steady.coe]; push_neg; exact ⟨0, 1, by unfold Rat.Close; norm_num⟩

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Rat.eventuallyClose_def]
  constructor
  · rintro ⟨N, hc⟩
    rw [Rat.closeSeq_def] at hc
    refine ⟨N.toNat, fun m hm => ?_⟩
    have hmz : (m:ℤ) ≥ N := by omega
    have hmz0 : (m:ℤ) ≥ 0 := by positivity
    have hcond_a : (m:ℤ) ≥ ((a:Chapter5.Sequence).from N).n₀ := by
      show (m:ℤ) ≥ max ((a:Chapter5.Sequence).n₀) N; rw [Sequence.n0_coe]; omega
    have hcond_b : (m:ℤ) ≥ ((b:Chapter5.Sequence).from N).n₀ := by
      show (m:ℤ) ≥ max ((b:Chapter5.Sequence).n₀) N; rw [Sequence.n0_coe]; omega
    have hc' := hc (m:ℤ) hcond_a hcond_b
    unfold Rat.Close at hc'
    rwa [Sequence.from_eval _ hmz, Sequence.from_eval _ hmz, Sequence.eval_coe_at_int,
      Sequence.eval_coe_at_int, if_pos hmz0, Int.toNat_natCast] at hc'
  · rintro ⟨N, hb⟩
    refine ⟨(N:ℤ), ?_⟩
    rw [Rat.closeSeq_def]
    intro n hca _
    have hn0eq : ((a:Chapter5.Sequence).from (N:ℤ)).n₀ = max 0 (N:ℤ) := by
      simp [Sequence.from, Sequence.n0_coe]
    rw [hn0eq] at hca
    have hn_n : n ≥ (N:ℤ) := by omega
    have hn0 : n ≥ 0 := by omega
    unfold Rat.Close
    rw [Sequence.from_eval _ hn_n, Sequence.from_eval _ hn_n, Sequence.eval_coe_at_int,
      Sequence.eval_coe_at_int, if_pos hn0, if_pos hn0]
    exact hb n.toNat (by omega)

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.closeSeq_def]; push_neg
  refine ⟨0, by simp [Sequence.n0_coe], by simp [Sequence.n0_coe], ?_⟩
  rw [Sequence.eval_coe_at_int, Sequence.eval_coe_at_int, if_pos (le_refl 0), if_pos (le_refl 0)]
  unfold Rat.Close; push_neg
  norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  refine ⟨1, fun n hn => ?_⟩
  rw [show ((1:ℚ)+10^(-(n:ℤ)-1)) - (1 - 10^(-(n:ℤ)-1)) = 2*(10:ℚ)^(-(n:ℤ)-1) by ring,
    abs_of_pos (by positivity)]
  calc 2*(10:ℚ)^(-(n:ℤ)-1) ≤ 2*(10:ℚ)^(-2:ℤ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ ≤ 0.1 := by norm_num

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  refine ⟨2, fun n hn => ?_⟩
  rw [show ((1:ℚ)+10^(-(n:ℤ)-1)) - (1 - 10^(-(n:ℤ)-1)) = 2*(10:ℚ)^(-(n:ℤ)-1) by ring,
    abs_of_pos (by positivity)]
  calc 2*(10:ℚ)^(-(n:ℤ)-1) ≤ 2*(10:ℚ)^(-3:ℤ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ ≤ 0.01 := by norm_num

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Sequence.equiv_def]
  simp_rw [Rat.eventuallyClose_iff]

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  have key : ∀ a b : ℕ → ℚ, Equiv a b → (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by
    intro a b hab hca
    rw [Sequence.IsCauchy.coe] at hca ⊢
    intro ε hε
    obtain ⟨N1, hN1⟩ := (equiv_iff a b).mp hab (ε/3) (by linarith)
    obtain ⟨N2, hN2⟩ := hca (ε/3) (by linarith)
    refine ⟨max N1 N2, fun j hj k hk => ?_⟩
    have e1 := hN1 j (le_trans (le_max_left _ _) hj)
    have e2 := hN1 k (le_trans (le_max_left _ _) hk)
    have e3 := hN2 j (le_trans (le_max_right _ _) hj) k (le_trans (le_max_right _ _) hk)
    rw [Section_4_3.dist_eq] at e3 ⊢
    have t1 : |b j - b k| ≤ |b j - a j| + |a j - a k| + |a k - b k| := by
      calc |b j - b k| ≤ |b j - a k| + |a k - b k| := abs_sub_le _ _ _
        _ ≤ |b j - a j| + |a j - a k| + |a k - b k| := by
            have := abs_sub_le (b j) (a j) (a k); linarith
    rw [abs_sub_comm (b j) (a j)] at t1
    linarith [e1, e2, e3, t1]
  have hba : Equiv b a := by
    have h := (equiv_iff a b).mp hab
    rw [equiv_iff]
    intro ε hε; obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩
  exact ⟨key a b hab, key b a hba⟩

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  have key : ∀ a b : ℕ → ℚ, ε.EventuallyClose (a:Sequence) (b:Sequence) →
      (a:Sequence).IsBounded → (b:Sequence).IsBounded := by
    intro a b hab hba
    obtain ⟨M, hM, hBM⟩ := hba
    obtain ⟨N, hN⟩ := (Rat.eventuallyClose_iff ε a b).mp hab
    obtain ⟨M0, hM0, hB0⟩ := IsBounded.finite (fun i:Fin N => b i)
    have hε0 : (0:ℚ) ≤ ε := le_trans (abs_nonneg _) (hN N (le_refl N))
    refine ⟨max (M + ε) M0, le_max_of_le_left (by linarith), fun n => ?_⟩
    rw [Sequence.eval_coe_at_int]
    by_cases hn0 : n ≥ 0
    · rw [if_pos hn0]
      by_cases hnN : n.toNat ≥ N
      · have ha := hBM n
        rw [Sequence.eval_coe_at_int, if_pos hn0] at ha
        have hc := hN n.toNat hnN
        have htri : |b n.toNat| ≤ |a n.toNat| + ε := by
          calc |b n.toNat| = |a n.toNat + (b n.toNat - a n.toNat)| := by congr 1; ring
            _ ≤ |a n.toNat| + |b n.toNat - a n.toNat| := abs_add_le _ _
            _ ≤ |a n.toNat| + ε := by rw [abs_sub_comm]; linarith
        exact le_trans (by linarith) (le_max_left _ _)
      · have hh := hB0 ⟨n.toNat, by omega⟩
        exact le_trans (by simpa using hh) (le_max_right _ _)
    · rw [if_neg hn0, abs_zero]
      exact le_trans hM0 (le_max_right _ _)
  have hba : ε.EventuallyClose (b:Sequence) (a:Sequence) := by
    rw [Rat.eventuallyClose_iff] at hab ⊢
    obtain ⟨N, hN⟩ := hab
    exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩
  exact ⟨key a b hab, key b a hba⟩

end Chapter5
