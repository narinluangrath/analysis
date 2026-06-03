import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    constructor
    · intro h ε hε N hN
      obtain ⟨n, hn, hclose⟩ := h ε hε N hN
      have hnN : n ≥ N := le_trans (le_max_right _ _) hn
      refine ⟨n, hnN, ?_⟩
      rwa [Sequence.from_eval a hnN, Real.Close, Real.dist_eq] at hclose
    · intro h ε hε N hN
      obtain ⟨n, hnN, hbound⟩ := h ε hε N hN
      refine ⟨n, max_le (le_trans hN hnN) hnN, ?_⟩
      rw [Sequence.from_eval a hnN, Real.Close, Real.dist_eq]
      exact hbound

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

private theorem E3_eval {n:ℤ} (hn: 0 ≤ n) :
    Example_6_4_3 n = 1 - (10:ℝ)^(-(n.toNat:ℤ)-1) := by
  simp only [Example_6_4_3, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn]

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  refine ⟨0, le_refl _, ?_⟩
  rw [Real.Close, Real.dist_eq, E3_eval (le_refl 0)]
  norm_num

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  intro h
  obtain ⟨n, hn, hclose⟩ := h 1 (by norm_num)
  rw [show (Example_6_4_3.from 1).m = max Example_6_4_3.m 1 from rfl] at hn
  have hn1 : (1:ℤ) ≤ n := le_trans (le_max_right _ _) hn
  rw [Sequence.from_eval Example_6_4_3 hn1, Real.Close, Real.dist_eq,
    E3_eval (by omega)] at hclose
  have hpow : (10:ℝ)^(-(n.toNat:ℤ)-1) ≤ (10:ℝ)^(-2:ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num); omega
  rw [abs_le] at hclose
  have h001 : (10:ℝ)^(-2:ℤ) = 0.01 := by norm_num
  rw [h001] at hpow
  linarith [hclose.2, hpow]

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN
  have hN0 : (0:ℤ) ≤ N := hN
  refine ⟨N, (max_eq_right hN).le, ?_⟩
  rw [Sequence.from_eval Example_6_4_3 (le_refl N), Real.Close, Real.dist_eq, E3_eval hN0]
  rw [show (1:ℝ) - 10^(-(N.toNat:ℤ)-1) - 1 = -(10^(-(N.toNat:ℤ)-1)) by ring, abs_neg,
    abs_of_pos (by positivity), show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  apply zpow_le_zpow_right₀ (by norm_num); omega

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/10 < 1)
  refine ⟨max N (k:ℤ), le_max_left _ _, ?_⟩
  set n := max N (k:ℤ)
  have hn0 : (0:ℤ) ≤ n := le_trans hN (le_max_left _ _)
  rw [E3_eval hn0, show (1:ℝ) - 10^(-(n.toNat:ℤ)-1) - 1 = -(10^(-(n.toNat:ℤ)-1)) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have hbound : (10:ℝ)^(-(n.toNat:ℤ)-1) ≤ (1/10:ℝ)^n.toNat := by
    have e : (1/10:ℝ)^n.toNat = (10:ℝ)^(-(n.toNat:ℤ)) := by
      rw [div_pow, one_pow, one_div, ← zpow_natCast, ← zpow_neg]
    rw [e]; apply zpow_le_zpow_right₀ (by norm_num); omega
  have hmono : (1/10:ℝ)^n.toNat ≤ (1/10:ℝ)^k := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    have : (k:ℤ) ≤ n := le_max_right _ _
    omega
  linarith [hbound, hmono, hk]

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

private theorem E4_eval {n:ℤ} (hn: 0 ≤ n) :
    Example_6_4_4 n = (-1:ℝ)^n.toNat * (1 + (10:ℝ)^(-(n.toNat:ℤ)-1)) := by
  simp only [Example_6_4_4, Sequence.instCoeFun, Sequence.ofNatFun]
  rw [if_pos hn]

/-- For any `ε > 0`, the tail `10^(-m-1)` is eventually below `ε`. -/
private theorem tail_le {ε:ℝ} (hε: 0 < ε) : ∃ k:ℕ, ∀ m:ℕ, k ≤ m → (10:ℝ)^(-(m:ℤ)-1) ≤ ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/10 < 1)
  refine ⟨k, fun m hm => ?_⟩
  have hbound : (10:ℝ)^(-(m:ℤ)-1) ≤ (1/10:ℝ)^m := by
    have e : (1/10:ℝ)^m = (10:ℝ)^(-(m:ℤ)) := by
      rw [div_pow, one_pow, one_div, ← zpow_natCast, ← zpow_neg]
    rw [e]; apply zpow_le_zpow_right₀ (by norm_num); omega
  have hmono : (1/10:ℝ)^m ≤ (1/10:ℝ)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  linarith

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  refine ⟨0, le_refl _, ?_⟩
  rw [Real.Close, Real.dist_eq, E4_eval (le_refl 0)]
  norm_num

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  intro N hN
  have hN0 : (0:ℤ) ≤ N := hN
  refine ⟨2*N, ?_, ?_⟩
  · rw [show (Example_6_4_4.from N).m = max Example_6_4_4.m N from rfl, max_eq_right hN0]; omega
  · have h2N : (0:ℤ) ≤ 2*N := by omega
    rw [Sequence.from_eval Example_6_4_4 (by omega : 2*N ≥ N), Real.Close, Real.dist_eq, E4_eval h2N]
    have heven : Even (2*N).toNat := ⟨N.toNat, by omega⟩
    rw [Even.neg_one_pow heven, one_mul,
      show (1:ℝ) + 10^(-((2*N).toNat:ℤ)-1) - 1 = 10^(-((2*N).toNat:ℤ)-1) by ring,
      abs_of_pos (by positivity), show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
    apply zpow_le_zpow_right₀ (by norm_num); omega

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hNt : (N.toNat:ℤ) = N := Int.toNat_of_nonneg hN
  obtain ⟨k, hk⟩ := tail_le hε
  set n := 2 * (max N.toNat k : ℤ) with hndef
  have hn0 : 0 ≤ n := by positivity
  refine ⟨n, by omega, ?_⟩
  rw [E4_eval hn0]
  have heven : Even n.toNat := ⟨max N.toNat k, by omega⟩
  rw [Even.neg_one_pow heven, one_mul,
    show (1:ℝ) + 10^(-(n.toNat:ℤ)-1) - 1 = 10^(-(n.toNat:ℤ)-1) by ring, abs_of_pos (by positivity)]
  apply hk; omega

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  have hNt : (N.toNat:ℤ) = N := Int.toNat_of_nonneg hN
  obtain ⟨k, hk⟩ := tail_le hε
  set n := 2 * (max N.toNat k : ℤ) + 1 with hndef
  have hn0 : 0 ≤ n := by positivity
  have hodd : Odd n.toNat := ⟨max N.toNat k, by omega⟩
  refine ⟨n, by omega, ?_⟩
  have hval : Example_6_4_4 n - (-1) = -(10^(-(n.toNat:ℤ)-1)) := by
    rw [E4_eval hn0, Odd.neg_one_pow hodd]; ring
  rw [hval, abs_neg, abs_of_pos (by positivity)]
  apply hk; omega

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def]; push_neg
  refine ⟨0.5, by norm_num, 0, le_refl _, fun n hn => ?_⟩
  rw [sub_zero, E4_eval hn]
  have ht : (0:ℝ) < 10^(-(n.toNat:ℤ)-1) := by positivity
  rcases Nat.even_or_odd n.toNat with he | ho
  · rw [Even.neg_one_pow he, one_mul, abs_of_pos (by linarith)]; linarith
  · rw [Odd.neg_one_pow ho, neg_one_mul, abs_neg, abs_of_pos (by linarith)]; linarith

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [limit_point_def]
  intro ε hε N hN
  rw [Sequence.tendsTo_iff] at h
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨max N M, le_max_left _ _, hM (max N M) (le_max_right _ _)⟩

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

example (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  sorry

example : Example_6_4_7.limsup = 1 := by sorry

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example : Example_6_4_7.liminf = -1 := by sorry

example : Example_6_4_7.sup = (1.1:ℝ) := by sorry

example : Example_6_4_7.inf = (-1.01:ℝ) := by sorry

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

example (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by sorry

example : Example_6_4_8.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by sorry

example : Example_6_4_8.liminf = ⊥ := by sorry

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else -(n+2:ℝ)⁻¹ := by sorry

example : Example_6_4_9.limsup = 0 := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by sorry

example : Example_6_4_9.liminf = 0 := by sorry

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by sorry

example : Example_6_4_9.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = n+1 := by sorry

example : Example_6_4_9.liminf = ⊤ := by sorry

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp only [limsup, sInf_lt_iff] at h
  obtain ⟨y, hy, ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy
  rw [hNy] at ha; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp only [liminf, lt_sSup_iff] at h
  obtain ⟨z, hz, ha⟩ := h
  obtain ⟨N, hN, hNz⟩ := hz
  rw [hNz] at ha; use N
  simp [hN, lowerseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_lt_of_le ha ((a.from N).ge_inf hn') using 1
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx : a.lowerseq N < x := by apply lt_of_le_of_lt (le_sSup _) h; simp; use N
  choose n hn hxn _ using exists_between_gt_inf hx
  grind

/-- The value set of `a.from a.m` is the same as that of `a`. -/
private theorem from_self_value_set (a:Sequence) :
    {x:EReal | ∃ n ≥ (a.from a.m).m, x = (a.from a.m) n} = {x:EReal | ∃ n ≥ a.m, x = a n} := by
  have hm : (a.from a.m).m = a.m := by show max a.m a.m = a.m; omega
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [hm] at hn
    exact ⟨n, hn, by rw [Sequence.from_eval a hn]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by rw [hm]; exact hn, by rw [Sequence.from_eval a hn]⟩

private theorem from_self_inf (a:Sequence) : (a.from a.m).inf = a.inf := by
  unfold Sequence.inf; rw [from_self_value_set]

private theorem from_self_sup (a:Sequence) : (a.from a.m).sup = a.sup := by
  unfold Sequence.sup; rw [from_self_value_set]

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  apply le_sSup
  exact ⟨a.m, le_refl _, (from_self_inf a).symm⟩

/-- The value set of a later tail is contained in that of an earlier tail. -/
private theorem from_tail_subset {a:Sequence} {N K:ℤ} (hN: a.m ≤ N) (hNK: N ≤ K) :
    {x:EReal | ∃ n ≥ (a.from K).m, x = (a.from K) n}
    ⊆ {x:EReal | ∃ n ≥ (a.from N).m, x = (a.from N) n} := by
  have hmK : (a.from K).m = K := by show max a.m K = K; omega
  have hmN : (a.from N).m = N := by show max a.m N = N; omega
  rintro x ⟨n, hn, rfl⟩
  rw [hmK] at hn
  refine ⟨n, by rw [hmN]; omega, ?_⟩
  rw [Sequence.from_eval a (show n ≥ K by omega), Sequence.from_eval a (show n ≥ N by omega)]

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  apply sSup_le
  rintro l ⟨N, hN, rfl⟩
  apply le_sInf
  rintro u ⟨M, hM, rfl⟩
  show (a.from N).inf ≤ (a.from M).sup
  set K := max N M with hK
  have hNK : N ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have hmid : (a.from K).inf ≤ (a.from K).sup := by
    have hmem : ((a.from K) ((a.from K).m) : EReal)
        ∈ {x:EReal | ∃ n ≥ (a.from K).m, x = (a.from K) n} := ⟨(a.from K).m, le_refl _, rfl⟩
    exact le_trans (sInf_le hmem) (le_sSup hmem)
  calc (a.from N).inf ≤ (a.from K).inf := sInf_le_sInf (from_tail_subset hN hNK)
    _ ≤ (a.from K).sup := hmid
    _ ≤ (a.from M).sup := sSup_le_sSup (from_tail_subset hM hMK)

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  apply sInf_le
  exact ⟨a.m, le_refl _, (from_self_sup a).symm⟩

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  sorry

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by sorry

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  sorry

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  sorry

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  sorry

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by sorry

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by sorry

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry


end Chapter6
