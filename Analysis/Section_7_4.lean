import Mathlib.Tactic
import Analysis.Section_7_3
/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

/-- Proposition 7.4.1 -/
theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  set s : Series := (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series) with hsdef
  have hs : s.nonneg := by intro n; by_cases h : n ≥ 0 <;> simp [s, h]; positivity
  rw [converges_of_nonneg_iff hs]
  set t : Series := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2:ℝ) : Series) with htdef
  have htnn : t.nonneg := by
    intro n; by_cases h : n ≥ 1
    · rw [Series.eval_mk' _ h]; positivity
    · simp [t, h]
  have htconv : t.converges := (converges_qseries 2 (by norm_num)).mpr (by norm_num)
  obtain ⟨Q, hQ⟩ := (converges_of_nonneg_iff htnn).mp htconv
  use Q
  intro N
  have key : s.partial N ≤ t.partial (N+1) := by
    by_cases hN : N ≥ 0
    · apply le_of_eq
      unfold Series.partial
      have hsm : s.m = 0 := rfl
      have htm : t.m = 1 := rfl
      rw [hsm, htm]
      apply Finset.sum_nbij' (i := fun n => n + 1) (j := fun n => n - 1)
      · intro a ha; simp only [Finset.mem_Icc] at *; omega
      · intro a ha; simp only [Finset.mem_Icc] at *; omega
      · intro a ha; omega
      · intro a ha; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha
        have ha0 : a ≥ 0 := ha.1
        have hseqs : s.seq a = 1/((a.toNat:ℝ)+1)^2 := by simp [s, ha0]
        have hcast : ((a+1).toNat:ℝ) = (a.toNat:ℝ) + 1 := by
          have : (a+1).toNat = a.toNat + 1 := by omega
          rw [this]; push_cast; ring
        have hseqt : t.seq (a+1) = 1/((a.toNat:ℝ)+1)^2 := by
          rw [htdef, Series.eval_mk' _ (show a + 1 ≥ 1 by omega), Real.rpow_two]
          congr 2
          have h2 : ((a.toNat:ℤ):ℝ) = (a:ℝ) := by rw [Int.toNat_of_nonneg ha0]
          push_cast at h2 ⊢
          first | rfl | (rw [h2]; ring) | linarith [h2]
        rw [hseqs, hseqt]
    · simp only [not_le] at hN
      rw [Series.partial_of_lt (by simp [s]; omega)]
      exact partial_nonneg htnn _
  exact le_trans key (hQ _)

/-- The swap bijection: n+1 if even, n-1 if odd. -/
private abbrev Series.swap_pair : ℕ → ℕ := fun n ↦ if Even n then n+1 else n-1

private theorem Series.swap_pair_bij : Function.Bijective swap_pair := by
  have key : ∀ n, swap_pair n = if n % 2 = 0 then n+1 else n-1 := by
    intro n; simp only [swap_pair, Nat.even_iff]
  constructor
  · intro a b hab
    rw [key a, key b] at hab
    split at hab <;> split at hab <;> omega
  · intro m
    rcases Nat.even_or_odd m with hm | hm
    · refine ⟨m+1, ?_⟩; rw [key]
      rw [Nat.even_iff] at hm; split <;> omega
    · refine ⟨m-1, ?_⟩; rw [key]
      rw [Nat.odd_iff] at hm; split <;> omega

private theorem Series.permuted_zeta_eq_perm :
    (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2)
      = (fun n ↦ (fun m:ℕ ↦ 1/(m+1:ℝ)^2) (swap_pair n)) := by
  funext n
  simp only [swap_pair]
  by_cases h : Even n
  · rw [if_pos h, if_pos h]; push_cast; norm_num; ring
  · rw [if_neg h, if_neg h]
    rw [Nat.not_even_iff_odd] at h
    have h1 : 1 ≤ n := h.pos
    have hc : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by
      have : (n-1:ℕ) + 1 = n := by omega
      have := congrArg (Nat.cast (R:=ℝ)) this; push_cast at this; linarith
    rw [hc]; norm_num

private theorem Series.zeta_perm_nonneg : ((fun m:ℕ ↦ 1/(m+1:ℝ)^2 : ℕ → ℝ):Series).nonneg := by
  intro n; by_cases h : n ≥ 0 <;> simp [h]; positivity

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
    have h := (converges_of_permute_nonneg (a := fun m:ℕ ↦ 1/(m+1:ℝ)^2) zeta_perm_nonneg zeta_2_converges swap_pair_bij).1
    rw [permuted_zeta_eq_perm]; exact h

theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
    have h := ((converges_of_permute_nonneg (a := fun m:ℕ ↦ 1/(m+1:ℝ)^2) zeta_perm_nonneg zeta_2_converges swap_pair_bij).2).symm
    rw [permuted_zeta_eq_perm]; exact h

/-- Proposition 7.4.3 (Rearrangement of series) -/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    intro n hn
    simp only [Finset.mem_Iic] at hn
    rw [Finset.mem_image]
    refine ⟨finv n, ?_, ?_⟩
    · simp only [Finset.mem_Iic]
      have := hM n hn
      omega
    · exact Function.invFun_eq (hf.2 n)
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro n hn
    have hnX : n ∉ Finset.Iic N.toNat := by
      simp only [X, Finset.mem_sdiff] at hn; exact hn.2
    simp only [Finset.mem_Iic] at hnX
    simp only [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have : n ≤ q' := hq hn
    omega
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring


/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  set a : {k:ℤ // k ≥ 0} → ℝ := fun n => 1/(((n:ℤ):ℝ) + 2) with ha_def
  have ha : ∀ n, a n ≥ 0 := by
    intro n; simp only [ha_def]
    have h0 : (0:ℝ) ≤ ((n:ℤ):ℝ) := by exact_mod_cast n.2
    apply div_nonneg one_pos.le; linarith
  have ha' : Antitone a := by
    intro x y hxy
    have hxy0 : (x:ℤ) ≤ (y:ℤ) := hxy
    have hx0 : (0:ℝ) ≤ ((x:ℤ):ℝ) := by exact_mod_cast x.2
    have hxy' : ((x:ℤ):ℝ) ≤ ((y:ℤ):ℝ) := by exact_mod_cast hxy0
    simp only [ha_def]; apply one_div_le_one_div_of_le (by linarith) (by linarith)
  have hadecay : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have hval : Filter.Tendsto (fun n:{k:ℤ//k≥0} => (n:ℤ)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_comp_val_Ici_atTop (a:=(0:ℤ)) (f := id)).mpr Filter.tendsto_id
    have h2z : Filter.Tendsto (fun z:ℤ => (1:ℝ)/((z:ℝ)+2)) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun z:ℤ => ((z:ℝ)+2)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 2 tendsto_intCast_atTop_atTop
      simpa using this.inv_tendsto_atTop
    exact h2z.comp hval
  have heq : (Series.a_7_4_4 : Series) = mk' (m := 0) (fun n => (-1:ℝ)^(n:ℤ) * a n) := by
    apply Series.ext
    · rfl
    funext n
    by_cases hn : n ≥ (0:ℤ)
    · rw [Series.eval_mk' _ hn]
      simp only [Series.eval_coe, ha_def] at *
      show (Series.a_7_4_4 : Series).seq n = _
      rw [show (Series.a_7_4_4 : Series).seq n = if n ≥ 0 then Series.a_7_4_4 n.toNat else 0 from rfl, if_pos hn]
      simp only [Series.a_7_4_4]
      rw [div_eq_mul_one_div]
      congr 1
      · rw [show ((-1:ℝ)^(n.toNat)) = (-1:ℝ)^(n:ℤ) from by rw [← zpow_natCast]; congr 1; omega]
      · have : (n.toNat:ℝ) = (n:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
        rw [this]
    · rw [(mk' (m := 0) (fun n => (-1:ℝ)^(n:ℤ) * a n)).vanish n (by simp; omega)]
      rw [(Series.a_7_4_4 : Series).vanish n (by simp; omega)]
  rw [heq]
  exact (converges_of_alternating ha ha').mpr hadecay

/-- Partial-sum bracketing for an alternating series `mk' (fun n => (-1)^n * a n)`
with `m = 0`: for every `n ≥ 0`, `a 0 - a 1 ≤ partial n ≤ a 0`. -/
private theorem Series.alternating_bracket {a: { k:ℤ // k ≥ (0:ℤ)} → ℝ} (ha: ∀ n, a n ≥ 0)
    (ha': Antitone a) {n:ℤ} (hn: n ≥ 0) :
    a ⟨0, le_refl 0⟩ - a ⟨1, by norm_num⟩ ≤ (mk' (fun k ↦ (-1)^(k:ℤ) * a k)).partial n
      ∧ (mk' (fun k ↦ (-1)^(k:ℤ) * a k)).partial n ≤ a ⟨0, le_refl 0⟩ := by
  set b := mk' (m := (0:ℤ)) fun k ↦ (-1) ^ (k:ℤ) * a k with hb
  set S := b.partial with hS
  have hbm : b.m = 0 := rfl
  have claim0 {N:ℤ} (hN: N ≥ 0) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; · simp [b, hb, show N+1 ≥ (0:ℤ) by grind]
    rw [hbm]; linarith
  have claim1 {N:ℤ} (hN: N ≥ 0) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ 0) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ 0) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ 0) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction k with
    | zero => simp
    | succ k ih =>
      have heven : Even (N + 2*(k:ℤ)) := h'.add (even_two_mul _)
      calc S (N+2*(↑(k+1):ℤ)) = S ((N+2*(k:ℤ))+2) := by congr 1; push_cast; ring
        _ ≤ S (N+2*(k:ℤ)) := claim3 (by omega) heven
        _ ≤ S N := ih
  have why3 {N:ℤ} (hN: N ≥ 0) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    have heven : Even (N + 2*(k:ℤ)) := h'.add (even_two_mul _)
    have hodd : Odd (N + 2*(k:ℤ) + 1) := heven.add_one
    have hc0 := claim0 (N := N + 2*(k:ℤ)) (by omega)
    rw [show N+2*(k:ℤ)+1 = (N+2*(k:ℤ))+1 by ring, hc0, hodd.neg_one_zpow]
    have hpos := ha ⟨ N + 2*(k:ℤ) + 1, by grind ⟩
    nlinarith [hpos]
  have why2 {N:ℤ} (hN: N ≥ 0) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, add_zero]
      have hodd : Odd (N+1) := h'.add_one
      rw [claim0 hN, hodd.neg_one_zpow]; linarith
    | succ k ih =>
      have hodd : Odd (N + 2*(k:ℤ) + 1) := (h'.add (even_two_mul _)).add_one
      calc S (N+2*(↑(k+1):ℤ)+1) = S ((N+2*(k:ℤ)+1)+2) := by congr 1; push_cast; ring
        _ ≥ S (N+2*(k:ℤ)+1) := claim2 (by omega) hodd
        _ ≥ S N - a ⟨ N+1, by grind ⟩ := ih
  have why4 {N j:ℤ} (hN: N ≥ 0) (h': Even N) (hj: j ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S j ∧ S j ≤ S N := by
    obtain ⟨i, hi⟩ : ∃ i:ℕ, j = N + i := ⟨(j-N).toNat, by omega⟩
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hn2 : j = N + 2*(k:ℤ) := by rw [hi, hk]; push_cast; ring
      rw [hn2]
      exact ⟨le_trans (ge_iff_le.mp (why2 hN h' k)) (why3 hN h' k), why1 hN h' k⟩
    · have hn2 : j = N + 2*(k:ℤ) + 1 := by rw [hi, hk]; push_cast; ring
      rw [hn2]
      exact ⟨ge_iff_le.mp (why2 hN h' k), le_trans (why3 hN h' k) (why1 hN h' k)⟩
  have key := why4 (N := 0) (by norm_num) ⟨0, by ring⟩ hn
  simp only [zero_add] at key
  have hS0 : S 0 = a ⟨0, le_refl 0⟩ := by
    show b.partial 0 = _
    show ∑ i ∈ Finset.Icc b.m 0, b.seq i = _
    rw [hbm, Finset.Icc_self, Finset.sum_singleton]
    rw [show b.seq 0 = (-1:ℝ)^(0:ℤ) * a ⟨0, le_refl 0⟩ from Series.eval_mk' _ (le_refl 0)]
    simp
  rw [hS0] at key
  exact key

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  set a : {k:ℤ // k ≥ 0} → ℝ := fun n => 1/(((n:ℤ):ℝ) + 2) with ha_def
  have ha : ∀ n, a n ≥ 0 := by
    intro n; simp only [ha_def]
    have h0 : (0:ℝ) ≤ ((n:ℤ):ℝ) := by exact_mod_cast n.2
    apply div_nonneg one_pos.le; linarith
  have ha' : Antitone a := by
    intro x y hxy
    have hxy0 : (x:ℤ) ≤ (y:ℤ) := hxy
    have hx0 : (0:ℝ) ≤ ((x:ℤ):ℝ) := by exact_mod_cast x.2
    have hxy' : ((x:ℤ):ℝ) ≤ ((y:ℤ):ℝ) := by exact_mod_cast hxy0
    simp only [ha_def]; apply one_div_le_one_div_of_le (by linarith) (by linarith)
  have hadecay : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have hval : Filter.Tendsto (fun n:{k:ℤ//k≥0} => (n:ℤ)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_comp_val_Ici_atTop (a:=(0:ℤ)) (f := id)).mpr Filter.tendsto_id
    have h2z : Filter.Tendsto (fun z:ℤ => (1:ℝ)/((z:ℝ)+2)) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun z:ℤ => ((z:ℝ)+2)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 2 tendsto_intCast_atTop_atTop
      simpa using this.inv_tendsto_atTop
    exact h2z.comp hval
  have heq : (Series.a_7_4_4 : Series) = mk' (m := 0) (fun n => (-1:ℝ)^(n:ℤ) * a n) := by
    apply Series.ext
    · rfl
    funext n
    by_cases hn : n ≥ (0:ℤ)
    · rw [Series.eval_mk' _ hn]
      simp only [Series.eval_coe, ha_def] at *
      show (Series.a_7_4_4 : Series).seq n = _
      rw [show (Series.a_7_4_4 : Series).seq n = if n ≥ 0 then Series.a_7_4_4 n.toNat else 0 from rfl, if_pos hn]
      simp only [Series.a_7_4_4]
      rw [div_eq_mul_one_div]
      congr 1
      · rw [show ((-1:ℝ)^(n.toNat)) = (-1:ℝ)^(n:ℤ) from by rw [← zpow_natCast]; congr 1; omega]
      · have : (n.toNat:ℝ) = (n:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
        rw [this]
    · rw [(mk' (m := 0) (fun n => (-1:ℝ)^(n:ℤ) * a n)).vanish n (by simp; omega)]
      rw [(Series.a_7_4_4 : Series).vanish n (by simp; omega)]
  have hconv : (a_7_4_4 : Series).converges := ex_7_4_4_conv
  have htend := convergesTo_sum hconv
  -- lower bound the limit by a 0 - a 1 = 1/6 > 0
  have hev : ∀ᶠ n in Filter.atTop, (a ⟨0, le_refl 0⟩ - a ⟨1, by norm_num⟩)
      ≤ (a_7_4_4 : Series).partial n := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun n hn => ?_⟩
    rw [heq]
    exact (alternating_bracket ha ha' hn).1
  have hlow : (a ⟨0, le_refl 0⟩ - a ⟨1, by norm_num⟩) ≤ (a_7_4_4 : Series).sum :=
    ge_of_tendsto htend hev
  have hval : a ⟨0, le_refl 0⟩ - a ⟨1, by norm_num⟩ = 1/6 := by
    simp only [ha_def]; norm_num
  rw [hval] at hlow
  linarith

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by
  constructor
  · intro a b hab
    simp only [f_7_4_4] at hab
    by_cases ha : a % 3 = 0 <;> by_cases hb : b % 3 = 0 <;>
      simp only [ha, hb, if_false, if_pos] at hab <;> omega
  · intro m
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨3*k, ?_⟩; simp only [f_7_4_4]; rw [if_pos (by omega)]; omega
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨3*j+1, ?_⟩; simp only [f_7_4_4]; rw [if_neg (by omega)]; omega
      · refine ⟨3*j+2, ?_⟩; simp only [f_7_4_4]; rw [if_neg (by omega)]; omega

open Filter

private noncomputable abbrev G : Series := (fun n ↦ Series.a_7_4_4 (Series.f_7_4_4 n) : Series)
private noncomputable abbrev g : ℕ → ℝ := fun n ↦ Series.a_7_4_4 (Series.f_7_4_4 n)
private theorem gm : G.m = 0 := rfl
private theorem gseq (N:ℤ) (hN : N ≥ 0) : G.seq N = g N.toNat := by simp [G, Series.eval_coe, hN]
private theorem Psucc (N:ℕ) : G.partial (N+1) = G.partial N + g (N+1) := by
  have h := Series.partial_succ G (N := (N:ℤ)) (by rw [gm]; omega)
  rw [h, gseq ((N:ℤ)+1) (by omega), show ((N:ℤ)+1).toNat = N+1 by omega]
private theorem Psucc3 (M:ℕ) : G.partial (M+3) = G.partial M + (g (M+1) + g (M+2) + g (M+3)) := by
  have r0 := Psucc M
  have e1 : G.partial (M+2) = G.partial (M+1) + g (M+2) := by have := Psucc (M+1); rwa [show M+1+1 = M+2 by ring] at this
  have e2 : G.partial (M+3) = G.partial (M+2) + g (M+3) := by have := Psucc (M+2); rwa [show M+2+1 = M+3 by ring] at this
  rw [e2, e1, r0]; ring
private theorem PZsucc (M:ℤ) (hM : M ≥ 0) : G.partial (M+1) = G.partial M + g (M+1).toNat := by
  have h := Series.partial_succ G (N := M) (by rw [gm]; omega)
  rw [h, gseq (M+1) (by omega)]
private noncomputable abbrev T : ℕ → ℝ := fun k => G.partial (3*k+2)
private noncomputable abbrev c : ℕ → ℝ := fun k => 1/(2*k+2) - 1/(4*k+3) - 1/(4*k+5)
private theorem gval0 (k:ℕ) : g (3*k) = 1/(2*k+2) := by
  simp only [g, Series.f_7_4_4, Series.a_7_4_4]
  rw [if_pos (by omega), show (3*k)/3 = k by omega, (show Even (2*k) from ⟨k, by ring⟩).neg_one_pow]; push_cast; ring
private theorem gval1 (k:ℕ) : g (3*k+1) = -(1/(4*k+3)) := by
  simp only [g, Series.f_7_4_4, Series.a_7_4_4]
  rw [if_neg (by omega), show (3*k+1)/3 = k by omega, show (3*k+1)%3 = 1 by omega,
    show 4*k+2*1-1 = 4*k+1 by omega, (show Odd (4*k+1) from ⟨2*k, by ring⟩).neg_one_pow]; push_cast; ring
private theorem gval2 (k:ℕ) : g (3*k+2) = -(1/(4*k+5)) := by
  simp only [g, Series.f_7_4_4, Series.a_7_4_4]
  rw [if_neg (by omega), show (3*k+2)/3 = k by omega, show (3*k+2)%3 = 2 by omega,
    show 4*k+2*2-1 = 4*k+3 by omega, (show Odd (4*k+3) from ⟨2*k+1, by ring⟩).neg_one_pow]; push_cast; ring
private theorem cval (k:ℕ) : c k = g (3*k) + g (3*k+1) + g (3*k+2) := by rw [gval0, gval1, gval2]; ring
private theorem Tsucc (k:ℕ) : T (k+1) = T k + c (k+1) := by
  have h := Psucc3 (3*k+2)
  rw [show g ((3*k+2)+1) = g (3*(k+1)) from rfl,
      show g ((3*k+2)+2) = g (3*(k+1)+1) from rfl,
      show g ((3*k+2)+3) = g (3*(k+1)+2) from rfl] at h
  have hc := cval (k+1)
  have hT1 : T (k+1) = G.partial (((3*k+2:ℕ):ℤ)+3) := by simp only [T]; norm_cast
  have hTk : T k = G.partial (((3*k+2 : ℕ):ℤ)) := by simp only [T]; norm_cast
  rw [hT1, hTk, h, hc]
private theorem cclosed (k:ℕ) : c k = -(1/((2*(k:ℝ)+2)*(4*(k:ℝ)+3)*(4*(k:ℝ)+5))) := by
  have h1 : (2*(k:ℝ)+2) ≠ 0 := by positivity
  have h2 : (4*(k:ℝ)+3) ≠ 0 := by positivity
  have h3 : (4*(k:ℝ)+5) ≠ 0 := by positivity
  simp only [c]; field_simp; ring
private theorem cneg (k:ℕ) : c k < 0 := by
  rw [cclosed]
  rw [neg_lt, neg_zero]; positivity
private theorem cbound (k:ℕ) : c k ≥ -(1/((k:ℝ)+1)^2) := by
  rw [cclosed]
  have hd : (0:ℝ) < (2*(k:ℝ)+2)*(4*(k:ℝ)+3)*(4*(k:ℝ)+5) := by positivity
  have hk : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
  rw [ge_iff_le, neg_le_neg_iff]
  have hle : ((k:ℝ)+1)^2 ≤ (2*(k:ℝ)+2)*(4*(k:ℝ)+3)*(4*(k:ℝ)+5) := by
    nlinarith [sq_nonneg ((k:ℝ)), (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
  calc (1:ℝ)/((2*(k:ℝ)+2)*(4*(k:ℝ)+3)*(4*(k:ℝ)+5)) ≤ 1/((k:ℝ)+1)^2 := one_div_le_one_div_of_le hk hle
private theorem T0eq : T 0 = c 0 := by
  show G.partial (3*(0:ℕ)+2) = c 0
  have hp0 : G.partial 0 = g 0 := by
    show ∑ n ∈ Finset.Icc G.m 0, G.seq n = _
    rw [gm, Finset.Icc_self, Finset.sum_singleton, gseq 0 (le_refl 0)]; norm_num
  have h1 : G.partial 1 = G.partial 0 + g 1 := by have := Psucc 0; simpa using this
  have h2 : G.partial 2 = G.partial 1 + g 2 := by have := Psucc 1; norm_num at this ⊢; rw [this]
  rw [cval]
  have e2 : G.partial (3*(0:ℕ)+2) = G.partial 2 := by norm_num
  rw [e2, h2, h1, hp0]
private theorem Tanti : Antitone T := by
  apply antitone_nat_of_succ_le
  intro k
  rw [Tsucc]
  have := cneg (k+1); linarith
-- harmonic-square partial bound
private theorem sqsum_strong (k:ℕ) (hk : 1 ≤ k) : ∑ j ∈ Finset.range k, (1/((j:ℝ)+1)^2) ≤ 2 - 1/(k:ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; norm_num
    · rw [Finset.sum_range_succ]
      have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk0
      have hterm : (1:ℝ)/((k:ℝ)+1)^2 ≤ 1/(k:ℝ) - 1/((k:ℝ)+1) := by
        rw [div_sub_div _ _ (ne_of_gt hkr) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf; nlinarith [hkr]
      have ihh := ih hk0
      have : (1:ℝ)/((k:ℝ)+1) = 1/((k+1:ℕ):ℝ) := by push_cast; ring
      push_cast
      push_cast at ihh
      linarith [ihh, hterm]
private theorem sqsum_bound (k:ℕ) : ∑ j ∈ Finset.range k, (1/((j:ℝ)+1)^2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have := sqsum_strong k hk
    have : (0:ℝ) < 1/(k:ℝ) := by positivity
    linarith [sqsum_strong k hk]
private theorem Tlow (k:ℕ) : T k ≥ T 0 - ∑ j ∈ Finset.range k, (1/((j:ℝ)+2)^2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Tsucc, Finset.sum_range_succ]
    have hcb := cbound (k+1)
    have : -(1/(((k:ℝ)+1)+1)^2) = -(1/((k:ℝ)+2)^2) := by ring_nf
    rw [show ((k+1:ℕ):ℝ) = (k:ℝ)+1 by push_cast; ring] at hcb
    rw [this] at hcb
    linarith [ih, hcb]
private theorem Tbdd : BddBelow (Set.range T) := by
  refine ⟨T 0 - 2, ?_⟩
  rintro x ⟨k, rfl⟩
  have h1 := Tlow k
  have h2 : ∑ j ∈ Finset.range k, (1/((j:ℝ)+2)^2) ≤ 2 := by
    have hmono : ∑ j ∈ Finset.range k, (1/((j:ℝ)+2)^2) ≤ ∑ j ∈ Finset.range (k+1), (1/((j:ℝ)+1)^2) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one]
      have : ∀ j ∈ Finset.range k, (1/(((j:ℝ)+1)+1)^2) = (1/((j:ℝ)+2)^2) := by intro j _; ring_nf
      rw [Finset.sum_congr rfl this]
      have : (0:ℝ) ≤ 1/((0:ℝ)+1)^2 := by positivity
      linarith
    linarith [sqsum_bound (k+1)]
  linarith
private noncomputable def L : ℝ := ⨅ i, T i
private theorem Ttend : Tendsto T atTop (nhds L) := tendsto_atTop_ciInf Tanti Tbdd
private theorem gap1 (k:ℕ) : |G.partial (3*(k:ℤ)+3) - T k| ≤ 1/((k:ℝ)+1) := by
  have e : G.partial (3*(k:ℤ)+3) = G.partial (3*(k:ℤ)+2) + g (3*(k:ℤ)+3).toNat := by
    have := PZsucc (3*(k:ℤ)+2) (by positivity)
    rw [show 3*(k:ℤ)+2+1 = 3*(k:ℤ)+3 by ring] at this; rw [this]
  rw [show T k = G.partial (3*(k:ℤ)+2) from rfl, e]; simp only [add_sub_cancel_left]
  rw [show (3*(k:ℤ)+3).toNat = 3*(k+1) by omega, gval0, abs_of_pos (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  push_cast; nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
private theorem gap2 (k:ℕ) : |G.partial (3*(k:ℤ)+4) - T k| ≤ 1/((k:ℝ)+1) := by
  have e1 : G.partial (3*(k:ℤ)+3) = G.partial (3*(k:ℤ)+2) + g (3*(k:ℤ)+3).toNat := by
    have := PZsucc (3*(k:ℤ)+2) (by positivity)
    rw [show 3*(k:ℤ)+2+1 = 3*(k:ℤ)+3 by ring] at this; rw [this]
  have e2 : G.partial (3*(k:ℤ)+4) = G.partial (3*(k:ℤ)+3) + g (3*(k:ℤ)+4).toNat := by
    have := PZsucc (3*(k:ℤ)+3) (by positivity)
    rw [show 3*(k:ℤ)+3+1 = 3*(k:ℤ)+4 by ring] at this; rw [this]
  rw [show T k = G.partial (3*(k:ℤ)+2) from rfl, e2, e1]
  rw [show (3*(k:ℤ)+3).toNat = 3*(k+1) by omega, show (3*(k:ℤ)+4).toNat = 3*(k+1)+1 by omega, gval0, gval1]
  set x : ℝ := ((k+1:ℕ):ℝ) with hx
  have hxpos : (0:ℝ) < x := by rw [hx]; positivity
  rw [show G.partial (3*(k:ℤ)+2) + 1/(2*x+2) + -(1/(4*x+3)) - G.partial (3*(k:ℤ)+2)
        = 1/(2*x+2) - 1/(4*x+3) by ring]
  have hp : (0:ℝ) ≤ 1/(2*x+2) - 1/(4*x+3) := by
    have : (1:ℝ)/(4*x+3) ≤ 1/(2*x+2) := by apply one_div_le_one_div_of_le (by positivity); linarith
    linarith
  rw [abs_of_nonneg hp]
  have hle : 1/(2*x+2) - 1/(4*x+3) ≤ 1/(2*x+2) := by
    have : (0:ℝ) ≤ 1/(4*x+3) := by positivity
    linarith
  refine le_trans hle ?_
  apply one_div_le_one_div_of_le (by positivity)
  rw [hx]; push_cast; nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
-- every nonneg integer is 3k+2, 3k+3, or 3k+4 for some k (covering N≥2)
private theorem Gconv : G.convergesTo L := by
  show Tendsto G.partial atTop (nhds L)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hT := Ttend
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨K1, hK1⟩ := hT (ε/2) (by linarith)
  obtain ⟨K2, hK2⟩ : ∃ K2:ℕ, ∀ k ≥ K2, 1/((k:ℝ)+1) < ε/2 := by
    obtain ⟨K2, hK2⟩ := exists_nat_gt (2/ε)
    refine ⟨K2, fun k hk => ?_⟩
    have hkr : (K2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h2e : 2/ε < (k:ℝ)+1 := by linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at h2e
    nlinarith [h2e, hε]
  set K := max K1 K2 with hKdef
  refine ⟨3*(K:ℤ)+2, fun N hN => ?_⟩
  set k : ℕ := ((N-2)/3).toNat with hk
  have hNk : ∃ r:ℤ, (r = 2 ∨ r = 3 ∨ r = 4) ∧ N = 3*(k:ℤ)+r ∧ k ≥ K := by
    have hkge : (k:ℤ) = (N-2)/3 := by rw [hk]; omega
    refine ⟨N - 3*(k:ℤ), ?_, by ring, ?_⟩
    · rw [hkge]; omega
    · have : (k:ℤ) ≥ (K:ℤ) := by rw [hkge]; omega
      exact_mod_cast this
  obtain ⟨r, hr, hNeq, hkK⟩ := hNk
  have hkK1 : k ≥ K1 := le_trans (le_max_left _ _) hkK
  have hkK2 : k ≥ K2 := le_trans (le_max_right _ _) hkK
  have hTL : |T k - L| ≤ ε/2 := le_of_lt (by have := hK1 k hkK1; rwa [Real.dist_eq] at this)
  have hgap : |G.partial N - T k| ≤ 1/((k:ℝ)+1) := by
    rcases hr with h | h | h
    · rw [hNeq, h, show T k = G.partial (3*(k:ℤ)+2) from rfl, sub_self, abs_zero]
      positivity
    · rw [hNeq, h]; exact gap1 k
    · rw [hNeq, h]; exact gap2 k
  have hsmall : 1/((k:ℝ)+1) < ε/2 := hK2 k hkK2
  rw [Real.dist_eq]
  calc |G.partial N - L| = |(G.partial N - T k) + (T k - L)| := by ring_nf
    _ ≤ |G.partial N - T k| + |T k - L| := abs_add_le _ _
    _ ≤ 1/((k:ℝ)+1) + ε/2 := by linarith [hgap, hTL]
    _ < ε/2 + ε/2 := by linarith [hsmall]
    _ = ε := by ring
private theorem Lneg : L < 0 := by
  have h1 : L ≤ T 0 := by
    rw [L]
    exact ciInf_le Tbdd 0
  rw [T0eq] at h1
  linarith [cneg 0]

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := ⟨L, Gconv⟩

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  have heq : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum = L := Series.sum_of_converges Gconv
  rw [heq]; exact Lneg

/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
  set af : ℕ → ℝ := fun n ↦ a (f n) with hafdef
  -- The abs of (a:Series) is nonneg
  have hAnn : (a:Series).abs.nonneg := by
    intro n; by_cases h : n ≥ (0:ℤ)
    · rw [show (a:Series).abs.seq n = |(a:Series).seq n| from Series.eval_mk' _ h]; positivity
    · rw [(a:Series).abs.vanish n (by simp [Series.abs] at h ⊢; omega)]
  have hAFnn : (af:Series).abs.nonneg := by
    intro n; by_cases h : n ≥ (0:ℤ)
    · rw [show (af:Series).abs.seq n = |(af:Series).seq n| from Series.eval_mk' _ h]; positivity
    · rw [(af:Series).abs.vanish n (by simp [Series.abs] at h ⊢; omega)]
  obtain ⟨Q, hQ⟩ := (converges_of_nonneg_iff hAnn).mp ha
  rw [show (af:Series).absConverges = (af:Series).abs.converges from rfl]
  rw [converges_of_nonneg_iff hAFnn]
  use Q
  intro N
  by_cases hN : N ≥ (0:ℤ)
  · have hAFm : (af:Series).abs.m = 0 := rfl
    have e1 : (af:Series).abs.partial N = ∑ m ∈ Finset.Iic N.toNat, |a (f m)| := by
      unfold Series.partial; rw [hAFm]
      rw [← Series.sum_eq_sum (fun m => |a (f m)|) hN]
      apply Finset.sum_congr rfl
      intro x hx; simp only [Finset.mem_Icc] at hx
      by_cases hx0 : (0:ℤ) ≤ x
      · rw [show (af:Series).abs.seq x = |(af:Series).seq x| from Series.eval_mk' _ hx0]
        simp [Series.eval_coe, af, hx0]
      · omega
    rw [e1]
    have e2 : ∑ m ∈ Finset.Iic N.toNat, |a (f m)| = ∑ n ∈ (Finset.Iic N.toNat).image f, |a n| := by
      rw [Finset.sum_image]; intro x _ y _ h; exact hf.injective h
    rw [e2]
    have hsub : (Finset.Iic N.toNat).image f ⊆ Finset.Iic (f N.toNat) := by
      intro n hn; simp only [Finset.mem_image, Finset.mem_Iic] at hn ⊢
      obtain ⟨x, hx, rfl⟩ := hn; exact hf.monotone hx
    calc ∑ n ∈ (Finset.Iic N.toNat).image f, |a n|
        ≤ ∑ n ∈ Finset.Iic (f N.toNat), |a n| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub; intro i _ _; positivity
      _ = (a:Series).abs.partial (f N.toNat) := by
          have hAm : (a:Series).abs.m = 0 := rfl
          unfold Series.partial; rw [hAm]
          have hcongr : ∀ n ∈ Finset.Icc (0:ℤ) (f N.toNat : ℤ), (a:Series).abs.seq n = (if 0 ≤ n then |a n.toNat| else 0) := by
            intro x hx; simp only [Finset.mem_Icc] at hx
            by_cases hx0 : (0:ℤ) ≤ x
            · rw [show (a:Series).abs.seq x = |(a:Series).seq x| from Series.eval_mk' _ hx0]
              simp [Series.eval_coe, hx0]
            · omega
          rw [Finset.sum_congr rfl hcongr]
          rw [Series.sum_eq_sum (fun m => |a m|) (by positivity : ((f N.toNat:ℤ)) ≥ 0)]
          rw [show ((f N.toNat : ℤ)).toNat = f N.toNat from by simp]
      _ ≤ Q := hQ _
  · rw [Series.partial_of_lt (by simp [Series.abs] at *; omega)]
    have := hQ (-1); have hp : (a:Series).abs.partial (-1) = 0 := by
      rw [Series.partial_of_lt (by simp [Series.abs])]
    linarith [hp ▸ this]

/--
{given -show}`n : ℕ`
Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
and expressing {lean}`a n` as the difference of {lean}`a n + |a n|` and {lean}`|a n|`.
-/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum :=
  Series.absConverges_of_permute ha hf

end Chapter7
