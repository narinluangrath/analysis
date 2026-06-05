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

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by sorry

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

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by sorry

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by sorry

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

/-- Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
    and expressing `a n` as the difference of `a n + |a n|` and `|a n|`. -/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum :=
  Series.absConverges_of_permute ha hf

end Chapter7
