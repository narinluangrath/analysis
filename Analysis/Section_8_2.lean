import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2: Summation on infinite sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Absolute convergence and summation on countably infinite or general sets.
- Connections with Mathlib's {name}`Summable` and {name}`tsum`.
- The Riemann rearrangement theorem.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

After this section, the summation notation developed here will be deprecated in favor of Mathlib's API for {name}`Summable` and {name}`tsum`.

-/

namespace Chapter8
open Chapter7 Chapter7.Series Finset Function Filter

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use {lit}`AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when {name}`X` is finite, even though
{name}`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!; choose g hg _ using this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX; apply hX; infer_instance
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  choose g' hbij hconv using hf
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := .mk h hfg
  simp [Sum, this]
  choose hbij hconv using this.choose_spec
  set g' := this.choose
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  convert convergesTo_sum (converges_of_absConverges hfg) using 1
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  choose g' hbij' hconv' using h
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Bijective (g_inv ∘ g') := .comp ⟨hright.injective, hleft.surjective⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  solve_by_elim [convergesTo_uniq, eq]

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) := by
  ext n; simp; constructor
  . intro ⟨ hn, _ ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ _, ⟨ _, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Icc 0 N = ∅ := by
  ext; simp; intros; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  set a : ℕ → Series := fun n ↦ ((fun m ↦ f (n, m)):Series)
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]; apply sum_of_nonneg; intro n; by_cases h: n ≥ 0 <;> simp [h]; grind
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by
    obtain ⟨g, hg, hconv⟩ := hf
    have hL : ((f ∘ g:ℕ→ℝ):Series).convergesTo (Sum f) := Sum.eq hg (AbsConvergent.comp hg ⟨g,hg,hconv⟩)
    set s : Series := ((f ∘ g:ℕ→ℝ):Series)
    have hpos' : ∀ p, 0 ≤ f p := by rintro ⟨n,m⟩; exact hpos n m
    have hnon : s.nonneg := by intro n; simp only [s]; by_cases h: n ≥ 0 <;> simp [h, hpos']
    have hsconv : s.converges := ⟨_, hL⟩
    have hssum : s.sum = L := convergesTo_uniq (convergesTo_sum hsconv) hL
    choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
    classical
    set B : Finset ℕ := X.image g_inv
    obtain ⟨N, hN⟩ : ∃ N:ℕ, ∀ b ∈ B, b ≤ N := ⟨B.sup id, fun b hb => Finset.le_sup (f := id) hb⟩
    have hsum_eq : ∑ p ∈ X, f p = ∑ n ∈ B, (f ∘ g) n := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl; intro x hx; simp [hright x]
      · intro a _ b _ h; rw [← hright a, ← hright b, h]
    rw [hsum_eq]
    have hBsub : B ⊆ Finset.Icc 0 N := by intro b hb; simp [hN b hb]
    have h1 : ∑ n ∈ B, (f ∘ g) n ≤ ∑ n ∈ Finset.Icc (0:ℕ) N, (f ∘ g) n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hBsub; intros; exact hpos' _
    have h2 : ∑ n ∈ Finset.Icc (0:ℕ) N, (f ∘ g) n = s.partial (N:ℤ) := by
      simp [Series.partial, s, Finset.Icc_eq_cast]
    rw [h2] at h1
    rw [← hssum]
    exact h1.trans (Series.partial_le_sum_of_nonneg hnon hsconv N)
  have hfinsum' (n M:ℕ) : (a n).partial M ≤ L := by
    simp [a, Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ .map (Embedding.sectR n ℕ) (.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : (a n).nonneg := by
    simp [a, nonneg]; intro m; split_ifs <;> simp [hpos]
  have hconv (n:ℕ) : (a n).converges := by
    rw [converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [partial_of_lt (by simp [a]; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply sum_eq_zero; intro n _
      simp [a, Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Icc 0 N) ×ˢ (.Icc 0 M), f x ≤ L
    . simp [a, sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).sum ≤ L := by
    apply le_of_tendsto' (x := .atTop) (tendsto_finset_sum _ _) (this N)
    solve_by_elim [convergesTo_sum]
  replace (N:ℤ) : (fun n ↦ (a n).sum:Series).partial N ≤ L := by
    convert this N with n hn; simp_all
  have hnon' : (fun n ↦ (a n).sum:Series).nonneg := by
    intro n; simp; split_ifs
    . exact sum_of_nonneg (hnon n.toNat)
    simp
  have hconv' : (fun n ↦ (a n).sum:Series).converges := by
    rw [converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ (a n).sum:Series).sum ≤ L := le_of_tendsto' (convergesTo_sum hconv') this
  replace : (fun n ↦ (a n).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      obtain ⟨g, hg, hconv⟩ := hf
      have hL : ((f ∘ g:ℕ→ℝ):Series).convergesTo L := Sum.eq hg (AbsConvergent.comp hg ⟨g,hg,hconv⟩)
      set s : Series := ((f ∘ g:ℕ→ℝ):Series)
      have htend := hL
      rw [Series.convergesTo, Metric.tendsto_atTop] at htend
      obtain ⟨N₀, hN₀⟩ := htend ε hε
      set N : ℤ := max N₀ 0 with hNdef
      have hNN : N ≥ N₀ := le_max_left _ _
      have hNnn : N ≥ 0 := le_max_right _ _
      have hd := hN₀ N hNN
      rw [Real.dist_eq] at hd
      lift N to ℕ using hNnn with Nn
      classical
      set X : Finset (ℕ × ℕ) := (Finset.Icc 0 Nn).image g
      refine ⟨X, ?_⟩
      have hsum_eq : ∑ p ∈ X, f p = s.partial (Nn:ℤ) := by
        rw [show (s.partial (Nn:ℤ)) = ∑ n ∈ Finset.Icc (0:ℕ) Nn, (f ∘ g) n by
            simp [Series.partial, s, Finset.Icc_eq_cast]]
        rw [Finset.sum_image (by intro a _ b _ h; exact hg.1 h)]
        rfl
      rw [hsum_eq]
      have hlt : |s.partial (Nn:ℤ) - L| < ε := hd
      rw [abs_lt] at hlt
      linarith [hlt.1]
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      refine ⟨X.sup (·.1), X.sup (·.2), ?_⟩
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, Finset.le_sup (f := (·.1)) hp⟩,
             ⟨Nat.zero_le _, Finset.le_sup (f := (·.2)) hp⟩⟩
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p := sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Icc 0 N, ∑ m ∈ Icc 0 M, f (n, m) := sum_product _ _ _
      _ ≤ ∑ n ∈ Icc 0 N, (a n).sum := by
        apply sum_le_sum; intro n _
        convert partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [a, Series.partial]
      _ = (fun n ↦ (a n).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := partial_le_sum_of_nonneg hnon' hconv' _
  simp [a, hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by
    funext p; simp [fplus, fminus, max_def]; split_ifs <;> simp_all <;> linarith
  have hfplus_conv : AbsConvergent fplus := by
    obtain ⟨g, hg, hconv⟩ := hf
    refine ⟨g, hg, ?_⟩
    apply (Series.converges_of_le (s := ((fplus ∘ g : ℕ→ℝ):Series)) (t := ((f ∘ g:ℕ→ℝ):Series).abs) rfl ?_ hconv).1
    intro n hn
    simp only [Series.abs, Series.mk', Series.eval_coe, ge_iff_le]
    simp only [show ((fplus ∘ g : ℕ→ℝ):Series).m = 0 from rfl, le_refl] at hn ⊢
    rw [if_pos hn]
    split
    · show |((f ⊔ 0) ∘ g) n.toNat| ≤ |(f ∘ g) n.toNat|
      simp only [comp_apply, Pi.sup_apply, Pi.zero_apply]
      rcases le_total (f (g n.toNat)) 0 with h|h
      · rw [sup_eq_right.2 h]; simp
      · rw [sup_eq_left.2 h]
    · simp at *; omega
  have hfminus_conv : AbsConvergent fminus := by
    obtain ⟨g, hg, hconv⟩ := hf
    refine ⟨g, hg, ?_⟩
    apply (Series.converges_of_le (s := ((fminus ∘ g : ℕ→ℝ):Series)) (t := ((f ∘ g:ℕ→ℝ):Series).abs) rfl ?_ hconv).1
    intro n hn
    simp only [Series.abs, Series.mk', Series.eval_coe, ge_iff_le]
    simp only [show ((fminus ∘ g : ℕ→ℝ):Series).m = 0 from rfl, le_refl] at hn ⊢
    rw [if_pos hn]
    split
    · show |((-f ⊔ 0) ∘ g) n.toNat| ≤ |(f ∘ g) n.toNat|
      simp only [comp_apply, Pi.sup_apply, Pi.zero_apply, Pi.neg_apply]
      rcases le_total (f (g n.toNat)) 0 with h|h
      · rw [sup_eq_left.2 (by linarith), abs_neg]
      · rw [sup_eq_right.2 (by linarith)]; simp
    · simp at *; omega
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    set t : Series := ((fun m ↦ fplus (n,m)):Series) + ((fun m ↦ fminus (n,m)):Series) with ht
    have hsum_conv : t.converges := (Series.add (hfplus_conv' n) (hfminus_conv' n)).1
    have htm : t.m = 0 := rfl
    have htseq : ∀ k:ℤ, t.seq k = (if k ≥ 0 then fplus (n,k.toNat) else 0) + (if k ≥ 0 then fminus (n,k.toNat) else 0) := by
      intro k; simp [ht, HAdd.hAdd, Add.add, Series.add]
    apply (Series.converges_of_le (s := ((fun m ↦ f (n,m)):Series)) (t := t) htm.symm ?_ hsum_conv).1
    intro k hk
    simp only [Series.eval_coe, show ((fun m ↦ f (n,m)):Series).m = 0 from rfl] at hk
    simp only [Series.eval_coe]
    rw [if_pos hk, htseq, if_pos hk, if_pos hk]
    have e1 : f (n, k.toNat) = fplus (n, k.toNat) - fminus (n, k.toNat) := by rw [hdiff]; rfl
    rw [e1]
    have h1 := hfplus_nonneg n k.toNat
    have h2 := hfminus_nonneg n k.toNat
    rw [abs_sub_le_iff]
    constructor <;> linarith [abs_nonneg (fplus (n,k.toNat))]
  convert convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert sub_coe _ _
    rcongr _ n; simp
    convert (sub _ _).2 with m; rfl
    split_ifs with h <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have ⟨ g, hg, _ ⟩ := hf
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply convergesTo_uniq h1 _
  convert (convergesTo.sub hplus hminus) using 3 with n
  split_ifs with h <;> simp [h, hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Bijective π := Involutive.bijective (congrFun rfl)
  have ⟨ g, hg, hconv ⟩ := hf
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ _, hπ.comp hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ ) := by
  constructor
  · intro hf
    obtain ⟨g, hg, hconv⟩ := hf
    set s : Series := ((f ∘ g : ℕ → ℝ) : Series)
    have hnon : s.abs.nonneg := by
      intro n; simp [Series.abs, s]; positivity
    have habsconv : s.abs.converges := hconv
    set S := s.abs.sum
    rw [bddAbove_def]; use S
    rintro y ⟨A, -, rfl⟩
    choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
    classical
    set B : Finset ℕ := A.image g_inv
    obtain ⟨N, hN⟩ : ∃ N:ℕ, ∀ b ∈ B, b ≤ N := ⟨B.sup id, fun b hb => Finset.le_sup (f := id) hb⟩
    have hsum_eq : ∑ x ∈ A, |f x| = ∑ n ∈ B, |(f ∘ g) n| := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl; intro x hx; simp [hright x]
      · intro a _ b _ h; rw [← hright a, ← hright b, h]
    simp only []
    rw [hsum_eq]
    have hBsub : B ⊆ Finset.Icc 0 N := by intro b hb; simp [hN b hb]
    have h1 : ∑ n ∈ B, |(f ∘ g) n| ≤ ∑ n ∈ Finset.Icc (0:ℕ) N, |(f ∘ g) n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hBsub; intros; positivity
    have h2 : ∑ n ∈ Finset.Icc (0:ℕ) N, |(f ∘ g) n| = s.abs.partial (N:ℤ) := by
      simp [Series.partial, s, Finset.Icc_eq_cast]
    rw [h2] at h1
    exact h1.trans (Series.partial_le_sum_of_nonneg hnon habsconv N)
  · intro hf
    simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    · use L; intro N; by_cases hN: N ≥ 0
      · lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (Finset.map g' (Finset.Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf; simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    . use L; intro N; by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf; rwa [AbsConvergent.iff hX f] at hf

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
  rw [AtMostCountable.iff, Set.countable_coe_iff]
  have hsummable : Summable f := by
    rw [← summable_abs_iff]
    obtain ⟨c, hc⟩ := hf
    apply summable_of_sum_le (c := c) (fun _ => abs_nonneg _)
    intro s; apply hc; exact ⟨s, by simp⟩
  exact hsummable.countable_support

/-- Compare with Mathlib's {name}`Summable.subtype`-/
theorem AbsConvergent'.subtype {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (A: Set X) :
  AbsConvergent' (fun x:A ↦ f x) := by
  apply BddAbove.mono _ hf
  intro z hz; simp at *; choose A hA using hz
  use A.map (Embedding.subtype _); simp [hA]

/-- A generalized sum.  Note that this will give junk values if {name}`f` is not {name}`AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by intro _; simp [E]; grind
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←E'.sum_subtype (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply sum_subset hE; aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) :=
    (AbsConvergent'.of_countable hA).mp (hconv.subtype A)
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by intro _; simp [E]; by_contra!; aesop
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  choose g hg using hA.symm
  have hsum := Sum.eq hg (hconv'.comp hg)
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ g n, by aesop ⟩
  have hι: Bijective ι := by
    split_ands
    . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩ h; simp [ι, E', Subtype.val_inj] at *; exact hg.1 h
    . intro ⟨ x, hx ⟩; choose n hn using hg.2 ⟨ _, hE hx ⟩; use ⟨ n, by aesop ⟩; grind
  -- The cases of infinite and finite E' are handled separately.
  obtain hE' | hE' := Nat.atMostCountable_subset E'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    choose a ha_bij ha_mono using (Nat.monotone_enum_of_infinite E').exists
    have : atTop.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) atTop := by
      apply tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop _)
      intro _ _ hnm; simp [ha_mono hnm]
    apply tendsto_nhds_unique  _ (hsum.comp this)
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . exact hconv.subtype E
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (hconv''.comp (hι.comp ha_bij))
    convert this.comp tendsto_natCast_atTop_atTop using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ .image (Subtype.val ∘ a) (.Icc 0 N), f ↑(g x) := by
        symm; apply sum_subset
        . intro m hm; simp at hm ⊢; obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'; contrapose! hx'
        choose n hn using (hι.comp ha_bij).2 ⟨ g x, hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        apply hg.1 at hn; subst hn
        use n; simpa [ha_mono.le_iff_le] using hx
      _ = _ := by
        apply sum_image
        intro _ _ _ _ h; simp [Subtype.val_inj] at h; exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := .ofFinite _
  let hEfintype : Fintype E := .ofFinite _
  apply convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; choose N hN using hE'bound
  rw [eventually_atTop]
  use N; intro N' hN'
  lift N' to ℕ using (LE.le.trans (by positivity) hN')
  simp [Series.partial] at hN' ⊢
  calc
    _ = ∑ n ∈ E', f (g n) := by
      symm; apply sum_subset
      . intro x hx; simp at *; linarith [hN _ hx]
      intro _ _ hx'; simpa [E',E] using hx'
    _ = ∑ n:E', f (g n) := by convert (sum_set_coe _).symm
    _ = ∑ n, f (ι n) := sum_congr rfl (by grind)
    _ = _ := hι.sum_comp (g := fun x ↦ f x)

/-- Connection with Mathlib's {name}`Summable` property. Some version of this might be suitable
    for Mathlib? -/
theorem AbsConvergent'.iff_Summable {X:Type} (f:X → ℝ) : AbsConvergent' f ↔ Summable f := by
  simp [←summable_abs_iff, AbsConvergent']
  simp [summable_iff_vanishing_norm]
  classical
  constructor
  . intro h ε hε
    set s := Set.range fun A ↦ ∑ x ∈ A, |f x|
    have hnon : s.Nonempty := by simp [s]; use 0, ∅; simp
    have : (sSup s)-ε < sSup s := by linarith
    simp [lt_csSup_iff h hnon,s] at this; choose S hS using this
    use S; intro T hT
    rw [abs_of_nonneg (by positivity)]
    have : ∑ x ∈ T, |f x| + ∑ x ∈ S, |f x| ≤ sSup s := by
      apply le_csSup h
      simp [s]; exact ⟨ T ∪ S, sum_union hT ⟩
    linarith
  intro h; choose S hS using h 1 (by norm_num)
  rw [bddAbove_def]
  use ∑ x ∈ S, |f x| + 1; simp; intro T
  calc
    _ = ∑ x ∈ (T ∩ S), |f x| + ∑ x ∈ (T \ S), |f x| := (sum_inter_add_sum_diff _ _ _).symm
    _ ≤ _ := by
      gcongr
      . exact inter_subset_right
      apply le_of_lt (lt_of_abs_lt (hS _ disjoint_sdiff_self_left))

/-- Maybe suitable for porting to Mathlib?-/
theorem Filter.Eventually.int_natCast_atTop (p: ℤ → Prop) :
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n := by
  refine ⟨ Eventually.natCast_atTop, ?_ ⟩
  simp [eventually_atTop]
  intro N hN; use N; intro n hn
  lift n to ℕ using (by omega)
  simp at hn; solve_by_elim

theorem Filter.Tendsto.int_natCast_atTop {R:Type} (f: ℤ → R) (l: Filter R) :
atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l := by
  simp [tendsto_iff_eventually]
  peel with p h
  simp [←eventually_atTop]
  convert Eventually.int_natCast_atTop _


/-- Connection with Mathlib's {name}`tsum` (or {kw (of := «termΣ'_,_»)}`Σ'`) operation -/
theorem Sum'.eq_tsum {X:Type} (f:X → ℝ) (h: AbsConvergent' f) :
  Sum' f = ∑' x, f x := by
  set E := {x | f x ≠ 0}
  obtain hE | hE := h.countable_supp
  . simp [Sum']
    choose g hg using hE.symm
    have : ((f ∘ Subtype.val) ∘ g:Series).absConverges := by
      apply AbsConvergent.comp hg
      rw [←AbsConvergent'.of_countable hE]
      exact h.subtype E
    replace this := Sum.eq hg this
    convert convergesTo_uniq this _ using 1
    · replace : ∑' x, f x = ∑' n, f (g n) := calc
        _ = ∑' x:E, f x := by
          exact (tsum_subtype_eq_of_support_subset (fun x hx => hx)).symm
        _ = _ := (Equiv.tsum_eq (Equiv.ofBijective _ hg) _).symm
      rw [this]
      unfold convergesTo; rw [Filter.Tendsto.int_natCast_atTop]
      convert (Summable.tendsto_sum_tsum_nat ?_).comp (tendsto_add_atTop_nat 1) with n
      . ext N; simp [Series.partial, Nat.range_succ_eq_Icc_zero]
      rw [AbsConvergent'.iff_Summable] at h
      exact h.comp_injective (i := Subtype.val ∘ g) (Subtype.val_injective.comp hg.1)
  rw [of_finsupp (A := E.toFinite.toFinset)]; symm; apply tsum_eq_sum
  all_goals simp [E]


/-- Proposition 8.2.6 (a) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.add {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f+g) ∧ Sum' (f + g) = Sum' f + Sum' g := by
  rw [AbsConvergent'.iff_Summable] at hf hg
  have hfg : AbsConvergent' (f+g) := by rw [AbsConvergent'.iff_Summable]; exact hf.add hg
  refine ⟨hfg, ?_⟩
  rw [Sum'.eq_tsum _ hfg, Sum'.eq_tsum _ (by rw [AbsConvergent'.iff_Summable]; exact hf),
      Sum'.eq_tsum _ (by rw [AbsConvergent'.iff_Summable]; exact hg)]
  rw [← Summable.tsum_add hf hg]; rfl

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  rw [AbsConvergent'.iff_Summable] at hf
  have hcf : AbsConvergent' (c • f) := by rw [AbsConvergent'.iff_Summable]; exact hf.const_smul c
  refine ⟨hcf, ?_⟩
  rw [Sum'.eq_tsum _ hcf, Sum'.eq_tsum _ (by rw [AbsConvergent'.iff_Summable]; exact hf)]
  rw [← tsum_mul_left]; rfl

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert add hf (smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to {lean}`AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  have h12 : AbsConvergent' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) := hf.subtype _
  have h1 : AbsConvergent' (fun x : X₁ ↦ f x) := hf.subtype _
  have h2 : AbsConvergent' (fun x : X₂ ↦ f x) := hf.subtype _
  rw [Sum'.eq_tsum _ h12, Sum'.eq_tsum _ h1, Sum'.eq_tsum _ h2]
  rw [AbsConvergent'.iff_Summable] at hf
  rw [tsum_subtype (X₁ ∪ X₂) f, tsum_subtype X₁ f, tsum_subtype X₂ f]
  rw [Set.indicator_union_of_disjoint hdisj]
  exact (Summable.tsum_add (hf.indicator X₁) (hf.indicator X₂))

/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  have h1 : AbsConvergent' (fun x: (.univ : Set X) ↦ f x) := hf.subtype _
  rw [Sum'.eq_tsum _ h1, Sum'.eq_tsum _ hf]
  exact tsum_univ f

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  rw [AbsConvergent'.iff_Summable] at hf
  have hcomp : AbsConvergent' (f ∘ φ) := by
    rw [AbsConvergent'.iff_Summable]; exact (Equiv.ofBijective φ hφ).summable_iff.mpr hf
  refine ⟨hcomp, ?_⟩
  rw [Sum'.eq_tsum _ hcomp, Sum'.eq_tsum _ (by rw [AbsConvergent'.iff_Summable]; exact hf)]
  exact ((Equiv.ofBijective φ hφ).tsum_eq f).symm

set_option maxHeartbeats 1000000 in
theorem bddabove_of_absconv {X:Type} {f : X → ℝ} (hf : AbsConvergent f) :
    BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' Set.univ ) := by
  obtain ⟨g, hg, hconv⟩ := hf
  set s : Series := ((f ∘ g : ℕ → ℝ) : Series)
  have hnon : s.abs.nonneg := by intro n; simp [Series.abs, s]; positivity
  have habsconv : s.abs.converges := hconv
  set S := s.abs.sum
  rw [bddAbove_def]; use S
  rintro y ⟨A, -, rfl⟩
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
  classical
  set B : Finset ℕ := A.image g_inv
  obtain ⟨N, hN⟩ : ∃ N:ℕ, ∀ b ∈ B, b ≤ N := ⟨B.sup id, fun b hb => Finset.le_sup (f := id) hb⟩
  have hsum_eq : ∑ x ∈ A, |f x| = ∑ n ∈ B, |(f ∘ g) n| := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl; intro x hx; simp [hright x]
    · intro a _ b _ h; rw [← hright a, ← hright b, h]
  simp only []
  rw [hsum_eq]
  have hBsub : B ⊆ Finset.Icc 0 N := by intro b hb; simp [hN b hb]
  have h1 : ∑ n ∈ B, |(f ∘ g) n| ≤ ∑ n ∈ Finset.Icc (0:ℕ) N, |(f ∘ g) n| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hBsub; intros; positivity
  have h2 : ∑ n ∈ Finset.Icc (0:ℕ) N, |(f ∘ g) n| = s.abs.partial (N:ℤ) := by
    simp [Series.partial, s, Finset.Icc_eq_cast]
  rw [h2] at h1
  exact h1.trans (Series.partial_le_sum_of_nonneg hnon habsconv N)

set_option maxHeartbeats 1000000 in
/-- Lemma 8.2.7 / Exercise 8.2.4 -/
theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  classical
  have absbridge : ∀ N:ℕ, (a:Series).abs.partial ((N:ℤ)-1) = ∑ n ∈ Finset.range N, |a n| := by
    intro N; cases N with
    | zero => simp [Series.partial, Series.partial_of_lt]
    | succ M =>
      rw [show ((M+1:ℕ):ℤ)-1 = (M:ℤ) by push_cast; ring]
      simp only [Series.partial, Series.abs, Series.mk']
      rw [Finset.Icc_eq_cast, Finset.sum_map, Nat.range_succ_eq_Icc_zero M]
      apply Finset.sum_congr rfl; intro n hn; simp [Nat.castEmbedding, Series.eval_coe]
  have parbridge : ∀ N:ℕ, (a:Series).partial ((N:ℤ)-1) = ∑ n ∈ Finset.range N, a n := by
    intro N; cases N with
    | zero => simp [Series.partial, Series.partial_of_lt]
    | succ M =>
      rw [show ((M+1:ℕ):ℤ)-1 = (M:ℤ) by push_cast; ring]
      simp only [Series.partial]
      rw [Finset.Icc_eq_cast, Finset.sum_map, Nat.range_succ_eq_Icc_zero M]
      apply Finset.sum_congr rfl; intro n hn; simp [Nat.castEmbedding, Series.eval_coe]
  have habnn : (a:Series).abs.nonneg := by
    intro n; simp only [Series.abs, Series.mk']; split_ifs
    · exact abs_nonneg _
    · exact le_refl 0
  obtain ⟨La, hLa⟩ := ha
  obtain ⟨C, hC⟩ : ∃ C, ∀ N:ℕ, |(a:Series).partial ((N:ℤ)-1)| ≤ C := by
    set g : ℕ → ℝ := fun N => (a:Series).partial ((N:ℤ)-1) with hg
    have htend : Tendsto g atTop (nhds La) := by
      apply hLa.comp; apply Filter.tendsto_atTop_atTop.mpr
      intro b; exact ⟨(b+1).toNat, fun n hn => by omega⟩
    have hb := htend.cauchySeq.isBounded_range
    rw [Metric.isBounded_iff_subset_closedBall 0] at hb
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun N => by simpa [Metric.mem_closedBall, Real.dist_eq, hg] using hC (Set.mem_range_self N)⟩
  -- key: contradiction from bound on the "selected" part sums.
  -- abs.partial(N-1) = ∑range N |a| = 2*Pr N - ∑range N a (positive selected)
  --                                 = 2*Mr N + ∑range N a (negative selected)
  -- where Pr N = ∑ max(a,0), Mr N = ∑ max(-a,0).
  have decompabs : ∀ N:ℕ, ∑ n ∈ Finset.range N, |a n|
      = (∑ n ∈ Finset.range N, max (a n) 0) + (∑ n ∈ Finset.range N, max (-(a n)) 0) := by
    intro N; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro n _; rcases le_total 0 (a n) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  have decompsum : ∀ N:ℕ, ∑ n ∈ Finset.range N, a n
      = (∑ n ∈ Finset.range N, max (a n) 0) - (∑ n ∈ Finset.range N, max (-(a n)) 0) := by
    intro N; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl
    intro n _; rcases le_total 0 (a n) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  -- final contradiction lemma
  have makeconv : ∀ B:ℝ, (∀ N:ℕ, ∑ n ∈ Finset.range N, |a n| ≤ B) → (a:Series).absConverges := by
    intro B hB
    rw [Series.absConverges, Series.converges_of_nonneg_iff habnn]
    refine ⟨max B 0, fun K => ?_⟩
    rcases lt_or_ge K 0 with hK | hK
    · rw [Series.partial_of_lt (by simpa using hK)]; exact le_max_right _ _
    · have : K = ((K.toNat + 1 : ℕ):ℤ) - 1 := by omega
      rw [this, absbridge]; exact le_trans (hB _) (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · intro hpos
    apply ha'
    obtain ⟨B, hB⟩ := bddAbove_def.mp (bddabove_of_absconv hpos)
    -- Pr N ≤ B
    have hPr : ∀ N:ℕ, ∑ n ∈ Finset.range N, max (a n) 0 ≤ B := by
      intro N
      have keyeq : (∑ x ∈ ((Finset.range N).subtype (fun n => a n ≥ 0)),
          |(fun n : {n | a n ≥ 0} ↦ a n) x|) = ∑ n ∈ Finset.range N, max (a n) 0 := by
        rw [show (∑ x ∈ ((Finset.range N).subtype (fun n => a n ≥ 0)), |(fun n : {n | a n ≥ 0} ↦ a n) x|)
              = ∑ x ∈ ((Finset.range N).subtype (fun n => a n ≥ 0)), |a ↑x| from rfl]
        rw [Finset.sum_subtype_eq_sum_filter (fun n => |a n|)]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun n => a n ≥ 0) (fun n => max (a n) 0)]
        have h2 : ∑ n ∈ (Finset.range N).filter (fun n => ¬ a n ≥ 0), max (a n) 0 = 0 := by
          apply Finset.sum_eq_zero; intro n hn; simp only [Finset.mem_filter, not_le] at hn
          rw [max_eq_right]; linarith [hn.2]
        rw [h2, add_zero]
        apply Finset.sum_congr rfl; intro n hn; simp only [Finset.mem_filter] at hn
        rw [abs_of_nonneg hn.2, max_eq_left hn.2]
      rw [← keyeq]; exact hB _ ⟨_, Set.mem_univ _, rfl⟩
    -- ∑|a| = 2 Pr - ∑a ≤ 2B + C
    apply makeconv (2*B + C); intro N
    rw [decompabs N]
    have e1 : ∑ n ∈ Finset.range N, max (-(a n)) 0
        = (∑ n ∈ Finset.range N, max (a n) 0) - ∑ n ∈ Finset.range N, a n := by
      rw [decompsum N]; ring
    rw [e1]
    have hca : ∑ n ∈ Finset.range N, a n ≥ -C := by
      rw [← parbridge N]; have := hC N; rw [_root_.abs_le] at this; linarith [this.1]
    have := hPr N; linarith
  · intro hneg
    apply ha'
    obtain ⟨B, hB⟩ := bddAbove_def.mp (bddabove_of_absconv hneg)
    have hMr : ∀ N:ℕ, ∑ n ∈ Finset.range N, max (-(a n)) 0 ≤ B := by
      intro N
      have keyeq : (∑ x ∈ ((Finset.range N).subtype (fun n => a n < 0)),
          |(fun n : {n | a n < 0} ↦ a n) x|) = ∑ n ∈ Finset.range N, max (-(a n)) 0 := by
        rw [show (∑ x ∈ ((Finset.range N).subtype (fun n => a n < 0)), |(fun n : {n | a n < 0} ↦ a n) x|)
              = ∑ x ∈ ((Finset.range N).subtype (fun n => a n < 0)), |a ↑x| from rfl]
        rw [Finset.sum_subtype_eq_sum_filter (fun n => |a n|)]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun n => a n < 0) (fun n => max (-(a n)) 0)]
        have h2 : ∑ n ∈ (Finset.range N).filter (fun n => ¬ a n < 0), max (-(a n)) 0 = 0 := by
          apply Finset.sum_eq_zero; intro n hn; simp only [Finset.mem_filter, not_lt] at hn
          rw [max_eq_right]; linarith [hn.2]
        rw [h2, add_zero]
        apply Finset.sum_congr rfl; intro n hn; simp only [Finset.mem_filter] at hn
        rw [abs_of_neg hn.2, max_eq_left (by linarith [hn.2])]
      rw [← keyeq]; exact hB _ ⟨_, Set.mem_univ _, rfl⟩
    apply makeconv (2*B + C); intro N
    rw [decompabs N]
    have e1 : ∑ n ∈ Finset.range N, max (a n) 0
        = (∑ n ∈ Finset.range N, max (-(a n)) 0) + ∑ n ∈ Finset.range N, a n := by
      rw [decompsum N]; ring
    rw [e1]
    have hca : ∑ n ∈ Finset.range N, a n ≤ C := by
      rw [← parbridge N]; have := hC N; rw [_root_.abs_le] at this; linarith [this.2]
    have := hMr N; linarith

/-- The positive and negative index sets of a conditionally convergent series are both infinite. -/
private theorem divergent_parts_infinite {a: ℕ → ℝ} (ha: (a:Series).converges)
    (ha': ¬ (a:Series).absConverges) :
    Set.Infinite { n | a n ≥ 0 } ∧ Set.Infinite { n | a n < 0 } := by
  classical
  -- Bridges between partial sums and finite range-sums.
  have absbridge : ∀ N:ℕ, (a:Series).abs.partial ((N:ℤ)-1) = ∑ n ∈ Finset.range N, |a n| := by
    intro N; cases N with
    | zero => simp [Series.partial, Series.partial_of_lt]
    | succ M =>
      rw [show ((M+1:ℕ):ℤ)-1 = (M:ℤ) by push_cast; ring]
      simp only [Series.partial, Series.abs, Series.mk']
      rw [Finset.Icc_eq_cast, Finset.sum_map, Nat.range_succ_eq_Icc_zero M]
      apply Finset.sum_congr rfl; intro n hn; simp [Nat.castEmbedding, Series.eval_coe]
  have parbridge : ∀ N:ℕ, (a:Series).partial ((N:ℤ)-1) = ∑ n ∈ Finset.range N, a n := by
    intro N; cases N with
    | zero => simp [Series.partial, Series.partial_of_lt]
    | succ M =>
      rw [show ((M+1:ℕ):ℤ)-1 = (M:ℤ) by push_cast; ring]
      simp only [Series.partial]
      rw [Finset.Icc_eq_cast, Finset.sum_map, Nat.range_succ_eq_Icc_zero M]
      apply Finset.sum_congr rfl; intro n hn; simp [Nat.castEmbedding, Series.eval_coe]
  have habnn : (a:Series).abs.nonneg := by
    intro n; simp only [Series.abs, Series.mk']; split_ifs
    · exact abs_nonneg _
    · exact le_refl 0
  obtain ⟨La, hLa⟩ := ha
  obtain ⟨C, hC⟩ : ∃ C, ∀ N:ℕ, |(a:Series).partial ((N:ℤ)-1)| ≤ C := by
    set g : ℕ → ℝ := fun N => (a:Series).partial ((N:ℤ)-1) with hg
    have htend : Tendsto g atTop (nhds La) := by
      apply hLa.comp; apply Filter.tendsto_atTop_atTop.mpr
      intro b; exact ⟨(b+1).toNat, fun n hn => by omega⟩
    have hb := htend.cauchySeq.isBounded_range
    rw [Metric.isBounded_iff_subset_closedBall 0] at hb
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun N => by simpa [Metric.mem_closedBall, Real.dist_eq, hg] using hC (Set.mem_range_self N)⟩
  have decompabs : ∀ N:ℕ, ∑ n ∈ Finset.range N, |a n|
      = (∑ n ∈ Finset.range N, max (a n) 0) + (∑ n ∈ Finset.range N, max (-(a n)) 0) := by
    intro N; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro n _; rcases le_total 0 (a n) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  have decompsum : ∀ N:ℕ, ∑ n ∈ Finset.range N, a n
      = (∑ n ∈ Finset.range N, max (a n) 0) - (∑ n ∈ Finset.range N, max (-(a n)) 0) := by
    intro N; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl
    intro n _; rcases le_total 0 (a n) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have makeconv : ∀ B:ℝ, (∀ N:ℕ, ∑ n ∈ Finset.range N, |a n| ≤ B) → (a:Series).absConverges := by
    intro B hB
    rw [Series.absConverges, Series.converges_of_nonneg_iff habnn]
    refine ⟨max B 0, fun K => ?_⟩
    rcases lt_or_ge K 0 with hK | hK
    · rw [Series.partial_of_lt (by simpa using hK)]; exact le_max_right _ _
    · have : K = ((K.toNat + 1 : ℕ):ℤ) - 1 := by omega
      rw [this, absbridge]; exact le_trans (hB _) (le_max_left _ _)
  -- A bound on one part's partial sums forces absConverges (via the convergence bound C).
  have boundp : ∀ Bp:ℝ, (∀ N:ℕ, ∑ n ∈ Finset.range N, max (a n) 0 ≤ Bp) → (a:Series).absConverges := by
    intro Bp hPr
    apply makeconv (2*Bp + C); intro N
    rw [decompabs N]
    have e1 : ∑ n ∈ Finset.range N, max (-(a n)) 0
        = (∑ n ∈ Finset.range N, max (a n) 0) - ∑ n ∈ Finset.range N, a n := by
      rw [decompsum N]; ring
    rw [e1]
    have hca : ∑ n ∈ Finset.range N, a n ≥ -C := by
      rw [← parbridge N]; have := hC N; rw [_root_.abs_le] at this; linarith [this.1]
    have := hPr N; linarith
  have boundm : ∀ Bm:ℝ, (∀ N:ℕ, ∑ n ∈ Finset.range N, max (-(a n)) 0 ≤ Bm) → (a:Series).absConverges := by
    intro Bm hMr
    apply makeconv (2*Bm + C); intro N
    rw [decompabs N]
    have e1 : ∑ n ∈ Finset.range N, max (a n) 0
        = (∑ n ∈ Finset.range N, max (-(a n)) 0) + ∑ n ∈ Finset.range N, a n := by
      rw [decompsum N]; ring
    rw [e1]
    have hca : ∑ n ∈ Finset.range N, a n ≤ C := by
      rw [← parbridge N]; have := hC N; rw [_root_.abs_le] at this; linarith [this.2]
    have := hMr N; linarith
  -- bound the part sum by the sum over the (finite) part set
  have part_bound : ∀ (p : ℕ → ℝ) (S : Set ℕ) (hS : S.Finite),
      (∀ n, n ∉ S → p n = 0) → (∀ n, 0 ≤ p n) →
      ∀ N:ℕ, ∑ n ∈ Finset.range N, p n ≤ ∑ n ∈ hS.toFinset, p n := by
    intro p S hS hzero hnn N
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (· ∈ S) p]
    have h0 : ∑ n ∈ (Finset.range N).filter (fun n => ¬ n ∈ S), p n = 0 := by
      apply Finset.sum_eq_zero; intro n hn
      rw [Finset.mem_filter] at hn; exact hzero n hn.2
    rw [h0, add_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; rw [Finset.mem_filter] at hn
      rw [Set.Finite.mem_toFinset]; exact hn.2
    · intro n _ _; exact hnn n
  constructor
  · rw [← Set.not_finite]; intro hfin
    apply ha'; apply boundp (∑ n ∈ hfin.toFinset, max (a n) 0)
    apply part_bound (fun n => max (a n) 0) { n | a n ≥ 0 } hfin
    · intro n hn; simp only [Set.mem_setOf_eq, not_le] at hn; exact max_eq_right (le_of_lt hn)
    · intro n; positivity
  · rw [← Set.not_finite]; intro hfin
    apply ha'; apply boundm (∑ n ∈ hfin.toFinset, max (-(a n)) 0)
    apply part_bound (fun n => max (-(a n)) 0) { n | a n < 0 } hfin
    · intro n hn; simp only [Set.mem_setOf_eq, not_lt] at hn; exact max_eq_right (by linarith)
    · intro n; positivity

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L
  := by
  -- This proof is written to follow the structure of the original text.
  choose h1 h2 using divergent_parts_of_divergent ha ha'
  set A_plus := { n | a n ≥ 0 }
  set A_minus := {n | a n < 0 }
  have hdisj : Disjoint A_plus A_minus := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext; simp [A_plus, A_minus]
  have hunion : A_plus ∪ A_minus = .univ := by
    ext; simp [A_plus, A_minus]; grind
  obtain ⟨hAp_inf, hAm_inf⟩ := divergent_parts_infinite ha ha'
  have hA_plus_inf : Infinite A_plus := hAp_inf.to_subtype
  have hA_minus_inf : Infinite A_minus := hAm_inf.to_subtype
  obtain ⟨ a_plus, ha_plus_bij, ha_plus_mono ⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
  obtain ⟨ a_minus, ha_minus_bij, ha_minus_mono ⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
    fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i (by simp) }
  let n' : ℕ → ℕ := Nat.strongRec F
  have hn' (j:ℕ) : n' j = if ∑ i:Fin j, a (n' i) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }
    := Nat.strongRec.eq_def _ j
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by
    have hsub : { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } = A_plus \ Set.range (fun i:Fin j => n' i) := by
      ext n; simp [Set.mem_diff, A_plus]; tauto
    rw [hsub]
    apply Set.Infinite.to_subtype
    apply Set.Infinite.diff hAp_inf (Set.finite_range _)
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by
    have hsub : { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } = A_minus \ Set.range (fun i:Fin j => n' i) := by
      ext n; simp [Set.mem_diff, A_minus]; tauto
    rw [hsub]
    apply Set.Infinite.to_subtype
    apply Set.Infinite.diff hAm_inf (Set.finite_range _)
  -- Membership: n' j lies in the appropriate selection set, hence differs from all earlier n' i.
  have hn'_ne : ∀ (j:ℕ) (i:ℕ), i < j → n' j ≠ n' i := by
    intro j i hij
    have hnep : { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }.Nonempty := by
      have := hn'_plus_inf j; exact Set.nonempty_coe_sort.mp inferInstance
    have hnem : { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }.Nonempty := by
      have := hn'_minus_inf j; exact Set.nonempty_coe_sort.mp inferInstance
    have key := hn' j
    by_cases hc : ∑ i:Fin j, a (n' i) < L
    · rw [if_pos hc] at key
      rw [key]
      have hne := (Nat.min_spec hnep).1
      simp only [Set.mem_setOf_eq] at hne
      exact hne.2 ⟨i, hij⟩
    · rw [if_neg hc] at key
      rw [key]
      have hne := (Nat.min_spec hnem).1
      simp only [Set.mem_setOf_eq] at hne
      exact hne.2 ⟨i, hij⟩
  have hn'_inj : Injective n' := by
    intro x y hxy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy.symm (hn'_ne y x h)
    · exact h
    · exact absurd hxy (hn'_ne x y h)
  -- Scaffolding: nonemptiness of greedy sets at each step
  have hnep : ∀ j:ℕ, { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }.Nonempty := by
    intro j; have := hn'_plus_inf j; exact Set.nonempty_coe_sort.mp inferInstance
  have hnem : ∀ j:ℕ, { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }.Nonempty := by
    intro j; have := hn'_minus_inf j; exact Set.nonempty_coe_sort.mp inferInstance
  -- membership of the chosen index, with sign information
  have hmem_pos : ∀ j:ℕ, ∑ i:Fin j, a (n' i) < L →
      n' j ∈ { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by
    intro j hc; have key := hn' j; rw [if_pos hc] at key; rw [key]
    exact (Nat.min_spec (hnep j)).1
  have hmem_neg : ∀ j:ℕ, ¬ (∑ i:Fin j, a (n' i) < L) →
      n' j ∈ { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by
    intro j hc; have key := hn' j; rw [if_neg hc] at key; rw [key]
    exact (Nat.min_spec (hnem j)).1
  -- sign of the picked term
  have hsign_pos : ∀ j:ℕ, ∑ i:Fin j, a (n' i) < L → 0 ≤ a (n' j) := by
    intro j hc; have h := hmem_pos j hc
    simp only [Set.mem_setOf_eq, A_plus] at h; exact h.1
  have hsign_neg : ∀ j:ℕ, ¬ (∑ i:Fin j, a (n' i) < L) → a (n' j) < 0 := by
    intro j hc; have h := hmem_neg j hc
    simp only [Set.mem_setOf_eq, A_minus] at h; exact h.1
  -- Bridge: the series partial sum of (a∘n') equals the finite sum over Fin j.
  have hbridge : ∀ j:ℕ, ((a ∘ n':Series).partial ((j:ℤ) - 1)) = ∑ i:Fin j, a (n' i) := by
    intro j; induction j with
    | zero =>
      rw [show ((0:ℕ):ℤ)-1 = -1 by ring,
        Series.partial_of_lt (show (-1:ℤ) < ((a∘n':Series)).m by norm_num [Series.instCoe])]
      simp
    | succ k ih =>
      have hstep : ((a ∘ n':Series).partial (((k:ℤ)+1) - 1))
          = ((a ∘ n':Series).partial ((k:ℤ) - 1)) + (a ∘ n':Series).seq (k:ℤ) := by
        have hm0 : ((a∘n':Series)).m = 0 := rfl
        have := (a ∘ n':Series).partial_succ (N := (k:ℤ)-1)
          (by rw [hm0]; omega)
        rw [show (k:ℤ)-1+1 = (k:ℤ)+1-1 by ring] at this
        convert this using 2 <;> ring
      rw [show ((k:ℕ):ℤ)+1-1 = ((k+1:ℕ):ℤ)-1 by push_cast; ring] at hstep
      rw [hstep, ih, Fin.sum_univ_castSucc]
      simp [Function.comp]
  -- Unboundedness of finite-subset abs-sums for each divergent part.
  have hunbdd_minus : ∀ B : ℝ, ∃ S : Finset ℕ, (↑S ⊆ A_minus) ∧ ∑ n ∈ S, |a n| > B := by
    have hCI : CountablyInfinite (↥A_minus) :=
      (show Chapter8.EqualCard ℕ _ from ⟨a_minus, ha_minus_bij⟩).symm
    rw [← AbsConvergent'.of_countable hCI] at h2
    unfold AbsConvergent' at h2
    rw [not_bddAbove_iff] at h2
    intro B
    obtain ⟨y, hy, hyB⟩ := h2 B
    simp only [Set.mem_image, Set.mem_univ, true_and] at hy
    obtain ⟨S, rfl⟩ := hy
    refine ⟨S.map (Embedding.subtype _), ?_, ?_⟩
    · intro x hx; rw [Finset.mem_coe, Finset.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx; exact b.2
    · rw [Finset.sum_map]; simpa using hyB
  have hunbdd_plus : ∀ B : ℝ, ∃ S : Finset ℕ, (↑S ⊆ A_plus) ∧ ∑ n ∈ S, |a n| > B := by
    have hCI : CountablyInfinite (↥A_plus) :=
      (show Chapter8.EqualCard ℕ _ from ⟨a_plus, ha_plus_bij⟩).symm
    rw [← AbsConvergent'.of_countable hCI] at h1
    unfold AbsConvergent' at h1
    rw [not_bddAbove_iff] at h1
    intro B
    obtain ⟨y, hy, hyB⟩ := h1 B
    simp only [Set.mem_image, Set.mem_univ, true_and] at hy
    obtain ⟨S, rfl⟩ := hy
    refine ⟨S.map (Embedding.subtype _), ?_, ?_⟩
    · intro x hx; rw [Finset.mem_coe, Finset.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx; exact b.2
    · rw [Finset.sum_map]; simpa using hyB
  -- abbreviation (local notation only)
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
    rw [Set.infinite_coe_iff]
    by_contra hfin; rw [Set.not_infinite] at hfin
    -- bound J past which all steps are negative branch
    obtain ⟨J, hJ⟩ : ∃ J, ∀ j ≥ J, ¬ (∑ i:Fin j, a (n' i) < L) := by
      by_cases hne : { j | ∑ i:Fin j, a (n' i) < L }.Nonempty
      · obtain ⟨J, hJ⟩ := hfin.bddAbove
        refine ⟨J + 1, fun j hj hc => ?_⟩
        have : j ∈ { j | ∑ i:Fin j, a (n' i) < L } := hc
        exact absurd (hJ this) (by omega)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        refine ⟨0, fun j _ hc => ?_⟩
        have : j ∈ { j | ∑ i:Fin j, a (n' i) < L } := hc
        rw [hne] at this; exact this
    -- localized exhaustion: every x ∈ A_minus is picked (using negative branch past J)
    have hexhloc : ∀ x ∈ A_minus, ∃ j, n' j = x := by
      intro x hx
      by_contra hcon; push_neg at hcon
      have hstep_in : ∀ j ≥ J, n' j ≤ x := by
        intro j hj
        have hc : ¬ (∑ i:Fin j, a (n' i) < L) := hJ j hj
        have hxelig : x ∈ { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } :=
          ⟨hx, fun i h => hcon i h.symm⟩
        have key := hn' j; rw [if_neg hc] at key
        rw [key]; exact (Nat.min_spec (hnem j)).2 x hxelig
      -- {n' j : j ≥ J} ⊆ [0,x] finite, but n' injective on infinite domain
      have : (n' '' { j | J ≤ j }).Infinite := by
        apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => n' (J + k))
        · intro p q hpq
          have := hn'_inj hpq; omega
        · intro k; exact ⟨J + k, by simp, rfl⟩
      have hsub : n' '' { j | J ≤ j } ⊆ Set.Iic x := by
        rintro y ⟨j, hj, rfl⟩; exact hstep_in j hj
      exact (Set.finite_Iic x |>.subset hsub).not_infinite this
    -- choose a finite negative subset whose sum drowns S' J
    set Pre : Finset ℕ := (Finset.range J).image n' with hPre
    obtain ⟨S, hSsub, hSbig⟩ := hunbdd_minus (((∑ i:Fin J, a (n' i)) - L) + ∑ n ∈ Pre, |a n|)
    -- all of S is picked; take K large enough to cover S and ≥ J
    have hScov : ∀ x ∈ S, ∃ j, n' j = x := fun x hx => hexhloc x (hSsub hx)
    choose pick hpick using hScov
    set K : ℕ := max J (S.attach.sup (fun p => pick p.1 p.2) + 1) with hK
    have hKJ : J ≤ K := le_max_left _ _
    have hcovered : ∀ x ∈ S, ∃ i, i < K ∧ n' i = x := by
      intro x hx
      refine ⟨pick x hx, ?_, hpick x hx⟩
      have hle : pick x hx ≤ S.attach.sup (fun p => pick p.1 p.2) :=
        Finset.le_sup (f := fun p => pick p.1 p.2) (Finset.mem_attach S ⟨x, hx⟩)
      have : S.attach.sup (fun p => pick p.1 p.2) + 1 ≤ K := le_max_right _ _
      omega
    -- S(K) = S(J) + ∑_{J≤i<K} a(n' i), all those terms negative
    have hSK_eq : (∑ i:Fin K, a (n' i))
        = (∑ i:Fin J, a (n' i)) + ∑ i ∈ Finset.Ico J K, a (n' i) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => a (n' i)) K,
          Fin.sum_univ_eq_sum_range (fun i => a (n' i)) J]
      exact (Finset.sum_range_add_sum_Ico _ hKJ).symm
    -- all terms in the Ico sum are negative
    have hIco_neg : ∀ i ∈ Finset.Ico J K, a (n' i) ≤ 0 := by
      intro i hi; rw [Finset.mem_Ico] at hi
      exact le_of_lt (hsign_neg i (hJ i hi.1))
    -- the negative subset S \ Pre injects into the picked indices Ico J K
    have hImg_sub : (S \ Pre) ⊆ (Finset.Ico J K).image n' := by
      intro x hx; rw [Finset.mem_sdiff] at hx
      obtain ⟨i, hiK, hni⟩ := hcovered x hx.1
      rw [Finset.mem_image]
      refine ⟨i, ?_, hni⟩
      rw [Finset.mem_Ico]; refine ⟨?_, hiK⟩
      by_contra hlt; push_neg at hlt
      exact hx.2 (by rw [hPre, Finset.mem_image]; exact ⟨i, Finset.mem_range.mpr hlt, hni⟩)
    -- bound the Ico sum above by the sum over S \ Pre (adding more negative terms)
    have hIco_le : ∑ i ∈ Finset.Ico J K, a (n' i) ≤ ∑ x ∈ (S \ Pre), a x := by
      have himg : ∑ i ∈ Finset.Ico J K, a (n' i) = ∑ x ∈ (Finset.Ico J K).image n', a x := by
        rw [Finset.sum_image]; intro i _ j _ h; exact hn'_inj h
      rw [himg]
      apply Finset.sum_le_sum_of_subset_of_nonpos' hImg_sub
      intro i hi _
      rw [Finset.mem_image] at hi; obtain ⟨k, hk, rfl⟩ := hi
      rw [Finset.mem_Ico] at hk
      exact le_of_lt (hsign_neg k (hJ k hk.1))
    -- value bound: ∑_{S\Pre} a ≤ ∑_S a + ∑_Pre |a|
    have hsplit : ∑ x ∈ (S \ Pre), a x ≤ (∑ x ∈ S, a x) + ∑ n ∈ Pre, |a n| := by
      have h1 : ∑ x ∈ S, a x = ∑ x ∈ (S \ Pre), a x + ∑ x ∈ (S ∩ Pre), a x := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S Pre)]
        congr 1; rw [Finset.sdiff_union_inter]
      have h2 : - ∑ x ∈ (S ∩ Pre), a x ≤ ∑ n ∈ Pre, |a n| := by
        calc - ∑ x ∈ (S ∩ Pre), a x = ∑ x ∈ (S ∩ Pre), (- a x) := by rw [Finset.sum_neg_distrib]
          _ ≤ ∑ x ∈ (S ∩ Pre), |a x| := by
                apply Finset.sum_le_sum; intro x _; exact neg_le_abs _
          _ ≤ ∑ n ∈ Pre, |a n| := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
                intro i _ _; exact abs_nonneg _
      linarith
    -- value of ∑_S a from the abs-sum
    have hSval : ∑ x ∈ S, a x = - ∑ n ∈ S, |a n| := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl
      intro x hx; have : a x < 0 := hSsub hx; rw [abs_of_neg this]; ring
    -- combine: S' K < L, contradicting S' K ≥ L
    have hbad : ∑ i:Fin K, a (n' i) < L := by
      have hSJ : ¬ (∑ i:Fin K, a (n' i) < L) := hJ K hKJ
      rw [hSK_eq]
      have : ∑ i ∈ Finset.Ico J K, a (n' i) ≤ ∑ x ∈ S, a x + ∑ n ∈ Pre, |a n| :=
        le_trans hIco_le hsplit
      rw [hSval] at this
      have : ∑ i:Fin J, a (n' i) + ∑ i ∈ Finset.Ico J K, a (n' i)
          ≤ ∑ i:Fin J, a (n' i) + (- ∑ n ∈ S, |a n| + ∑ n ∈ Pre, |a n|) := by linarith
      have hbig : ∑ n ∈ S, |a n| > (∑ i:Fin J, a (n' i) - L) + ∑ n ∈ Pre, |a n| := hSbig
      linarith
    exact (hJ K hKJ) hbad
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
    rw [Set.infinite_coe_iff]
    by_contra hfin; rw [Set.not_infinite] at hfin
    -- bound J past which all steps are positive branch
    obtain ⟨J, hJ⟩ : ∃ J, ∀ j ≥ J, (∑ i:Fin j, a (n' i) < L) := by
      have hJ' : ∃ J, ∀ j ≥ J, ¬ (L ≤ ∑ i:Fin j, a (n' i)) := by
        by_cases hne : { j | ∑ i:Fin j, a (n' i) ≥ L }.Nonempty
        · obtain ⟨J, hJ⟩ := hfin.bddAbove
          refine ⟨J + 1, fun j hj hc => ?_⟩
          have : j ∈ { j | ∑ i:Fin j, a (n' i) ≥ L } := hc
          exact absurd (hJ this) (by omega)
        · rw [Set.not_nonempty_iff_eq_empty] at hne
          refine ⟨0, fun j _ hc => ?_⟩
          have : j ∈ { j | ∑ i:Fin j, a (n' i) ≥ L } := hc
          rw [hne] at this; exact this
      obtain ⟨J, hJ⟩ := hJ'
      exact ⟨J, fun j hj => not_le.mp (hJ j hj)⟩
    -- localized exhaustion: every x ∈ A_plus is picked (using positive branch past J)
    have hexhloc : ∀ x ∈ A_plus, ∃ j, n' j = x := by
      intro x hx
      by_contra hcon; push_neg at hcon
      have hstep_in : ∀ j ≥ J, n' j ≤ x := by
        intro j hj
        have hc : (∑ i:Fin j, a (n' i) < L) := hJ j hj
        have hxelig : x ∈ { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } :=
          ⟨hx, fun i h => hcon i h.symm⟩
        have key := hn' j; rw [if_pos hc] at key
        rw [key]; exact (Nat.min_spec (hnep j)).2 x hxelig
      have : (n' '' { j | J ≤ j }).Infinite := by
        apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => n' (J + k))
        · intro p q hpq
          have := hn'_inj hpq; omega
        · intro k; exact ⟨J + k, by simp, rfl⟩
      have hsub : n' '' { j | J ≤ j } ⊆ Set.Iic x := by
        rintro y ⟨j, hj, rfl⟩; exact hstep_in j hj
      exact (Set.finite_Iic x |>.subset hsub).not_infinite this
    -- choose a finite positive subset whose sum exceeds L - S' J (plus Pre corrections)
    set Pre : Finset ℕ := (Finset.range J).image n' with hPre
    obtain ⟨S, hSsub, hSbig⟩ := hunbdd_plus ((L - (∑ i:Fin J, a (n' i))) + ∑ n ∈ Pre, |a n|)
    have hScov : ∀ x ∈ S, ∃ j, n' j = x := fun x hx => hexhloc x (hSsub hx)
    choose pick hpick using hScov
    set K : ℕ := max J (S.attach.sup (fun p => pick p.1 p.2) + 1) with hK
    have hKJ : J ≤ K := le_max_left _ _
    have hcovered : ∀ x ∈ S, ∃ i, i < K ∧ n' i = x := by
      intro x hx
      refine ⟨pick x hx, ?_, hpick x hx⟩
      have hle : pick x hx ≤ S.attach.sup (fun p => pick p.1 p.2) :=
        Finset.le_sup (f := fun p => pick p.1 p.2) (Finset.mem_attach S ⟨x, hx⟩)
      have : S.attach.sup (fun p => pick p.1 p.2) + 1 ≤ K := le_max_right _ _
      omega
    have hSK_eq : (∑ i:Fin K, a (n' i))
        = (∑ i:Fin J, a (n' i)) + ∑ i ∈ Finset.Ico J K, a (n' i) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => a (n' i)) K,
          Fin.sum_univ_eq_sum_range (fun i => a (n' i)) J]
      exact (Finset.sum_range_add_sum_Ico _ hKJ).symm
    -- the positive subset S \ Pre injects into the picked indices Ico J K
    have hImg_sub : (S \ Pre) ⊆ (Finset.Ico J K).image n' := by
      intro x hx; rw [Finset.mem_sdiff] at hx
      obtain ⟨i, hiK, hni⟩ := hcovered x hx.1
      rw [Finset.mem_image]
      refine ⟨i, ?_, hni⟩
      rw [Finset.mem_Ico]; refine ⟨?_, hiK⟩
      by_contra hlt; push_neg at hlt
      exact hx.2 (by rw [hPre, Finset.mem_image]; exact ⟨i, Finset.mem_range.mpr hlt, hni⟩)
    -- bound the Ico sum below by the sum over S \ Pre (terms are nonneg, superset ≥ subset)
    have hIco_ge : ∑ x ∈ (S \ Pre), a x ≤ ∑ i ∈ Finset.Ico J K, a (n' i) := by
      have himg : ∑ i ∈ Finset.Ico J K, a (n' i) = ∑ x ∈ (Finset.Ico J K).image n', a x := by
        rw [Finset.sum_image]; intro i _ j _ h; exact hn'_inj h
      rw [himg]
      apply Finset.sum_le_sum_of_subset_of_nonneg hImg_sub
      intro i hi _
      rw [Finset.mem_image] at hi; obtain ⟨k, hk, rfl⟩ := hi
      rw [Finset.mem_Ico] at hk
      exact hsign_pos k (hJ k hk.1)
    -- value bound: ∑_S a - ∑_Pre |a| ≤ ∑_{S\Pre} a
    have hsplit : (∑ x ∈ S, a x) - ∑ n ∈ Pre, |a n| ≤ ∑ x ∈ (S \ Pre), a x := by
      have h1 : ∑ x ∈ S, a x = ∑ x ∈ (S \ Pre), a x + ∑ x ∈ (S ∩ Pre), a x := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S Pre)]
        congr 1; rw [Finset.sdiff_union_inter]
      have h2 : ∑ x ∈ (S ∩ Pre), a x ≤ ∑ n ∈ Pre, |a n| := by
        calc ∑ x ∈ (S ∩ Pre), a x ≤ ∑ x ∈ (S ∩ Pre), |a x| := by
                apply Finset.sum_le_sum; intro x _; exact le_abs_self _
          _ ≤ ∑ n ∈ Pre, |a n| := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
                intro i _ _; exact abs_nonneg _
      linarith
    -- value of ∑_S a from the abs-sum (a ≥ 0 on A_plus)
    have hSval : ∑ x ∈ S, a x = ∑ n ∈ S, |a n| := by
      apply Finset.sum_congr rfl
      intro x hx; have : 0 ≤ a x := hSsub hx; rw [abs_of_nonneg this]
    -- combine: S' K ≥ L, contradicting S' K < L
    have hbad : ¬ (∑ i:Fin K, a (n' i) < L) := by
      rw [not_lt, hSK_eq]
      have hchain : ∑ x ∈ S, a x - ∑ n ∈ Pre, |a n| ≤ ∑ i ∈ Finset.Ico J K, a (n' i) :=
        le_trans hsplit hIco_ge
      rw [hSval] at hchain
      have hbig : ∑ n ∈ S, |a n| > (L - (∑ i:Fin J, a (n' i))) + ∑ n ∈ Pre, |a n| := hSbig
      linarith
    exact hbad (hJ K hKJ)
  -- Greedy exhaustion for A_plus: any x ∈ A_plus is eventually picked.
  have hexh_plus : ∀ x ∈ A_plus, ∃ j, n' j = x := by
    intro x hx
    by_contra hcon; push_neg at hcon
    -- x never picked ⟹ at every positive step, x is eligible and ≥ the pick
    -- the positive picks are distinct elements of A_plus ∩ [0,x], a finite set
    set Pos := { n ∈ A_plus | n ≤ x } with hPos
    have hPosfin : Pos.Finite := Set.Finite.subset (Set.finite_Iic x) (by
      intro n hn; simp only [hPos, Set.mem_setOf_eq] at hn; exact hn.2)
    -- the map sending a positive step j to n' j lands in Pos and is injective
    have hstep_in : ∀ j, (∑ i:Fin j, a (n' i) < L) → n' j ∈ Pos := by
      intro j hc
      have hmem := hmem_pos j hc
      have hxelig : x ∈ { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by
        refine ⟨hx, ?_⟩; intro i; exact fun h => hcon i h.symm
      have key := hn' j; rw [if_pos hc] at key
      have hle : n' j ≤ x := by rw [key]; exact (Nat.min_spec (hnep j)).2 x hxelig
      simp only [hPos, Set.mem_setOf_eq]
      exact ⟨(by simp only [Set.mem_setOf_eq, A_plus] at hmem ⊢; exact hmem.1), hle⟩
    -- Now: infinitely many positive steps, all mapping injectively into finite Pos: contradiction
    have hPsetinf : ({j | ∑ i:Fin j, a (n' i) < L}).Infinite := Set.infinite_coe_iff.mp h_case_I
    have himg_sub : n' '' {j | ∑ i:Fin j, a (n' i) < L} ⊆ Pos := by
      rintro y ⟨j, hj, rfl⟩; exact hstep_in j hj
    have himg_inf : (n' '' {j | ∑ i:Fin j, a (n' i) < L}).Infinite :=
      hPsetinf.image (Set.injOn_of_injective hn'_inj)
    exact (hPosfin.subset himg_sub).not_infinite himg_inf
  -- Greedy exhaustion for A_minus: any x ∈ A_minus is eventually picked.
  have hexh_minus : ∀ x ∈ A_minus, ∃ j, n' j = x := by
    intro x hx
    by_contra hcon; push_neg at hcon
    set Neg := { n ∈ A_minus | n ≤ x } with hNeg
    have hNegfin : Neg.Finite := Set.Finite.subset (Set.finite_Iic x) (by
      intro n hn; simp only [hNeg, Set.mem_setOf_eq] at hn; exact hn.2)
    have hstep_in : ∀ j, ¬ (∑ i:Fin j, a (n' i) < L) → n' j ∈ Neg := by
      intro j hc
      have hmem := hmem_neg j hc
      have hxelig : x ∈ { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by
        refine ⟨hx, ?_⟩; intro i; exact fun h => hcon i h.symm
      have key := hn' j; rw [if_neg hc] at key
      have hle : n' j ≤ x := by rw [key]; exact (Nat.min_spec (hnem j)).2 x hxelig
      simp only [hNeg, Set.mem_setOf_eq]
      exact ⟨(by simp only [Set.mem_setOf_eq, A_minus] at hmem ⊢; exact hmem.1), hle⟩
    have hPsetinf : ({j | ∑ i:Fin j, a (n' i) ≥ L}).Infinite := Set.infinite_coe_iff.mp h_case_II
    have himg_sub : n' '' {j | ∑ i:Fin j, a (n' i) ≥ L} ⊆ Neg := by
      rintro y ⟨j, hj, rfl⟩
      exact hstep_in j (by simp only [Set.mem_setOf_eq] at hj; exact not_lt.mpr hj)
    have himg_inf : (n' '' {j | ∑ i:Fin j, a (n' i) ≥ L}).Infinite :=
      hPsetinf.image (Set.injOn_of_injective hn'_inj)
    exact (hNegfin.subset himg_sub).not_infinite himg_inf
  have hn'_surj : Surjective n' := by
    intro x
    rcases (show x ∈ A_plus ∨ x ∈ A_minus by
      have : x ∈ A_plus ∪ A_minus := by rw [hunion]; trivial
      exact this) with hx | hx
    · exact hexh_plus x hx
    · exact hexh_minus x hx
  -- terms of a tend to 0 (zero test), then so do the rearranged terms (n' injective)
  have ha0 : atTop.Tendsto a (nhds 0) := by
    have hd := Series.decay_of_converges ha
    have hcast : Tendsto (fun n:ℕ => (a:Series).seq (n:ℤ)) atTop (nhds 0) :=
      hd.comp (tendsto_natCast_atTop_atTop)
    apply hcast.congr; intro n; simp
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by
    rw [← Nat.cofinite_eq_atTop, tendsto_iff_forall_eventually_mem] at ha0 ⊢
    intro s hs
    have hfin := ha0 s hs
    rw [eventually_cofinite] at hfin ⊢
    apply Set.Finite.subset (hfin.preimage (Set.injOn_of_injective hn'_inj))
    intro x hx; exact hx
  -- partial sums S j = ∑_{i<j} a(n' i) tend to L.
  have hStendsto : atTop.Tendsto (fun j:ℕ => ∑ i:Fin j, a (n' i)) (nhds L) := by
    rw [Metric.tendsto_atTop]
    intro ε0 hε0
    obtain ⟨ε, hε, hεlt⟩ : ∃ ε, 0 < ε ∧ ε < ε0 := ⟨ε0/2, by positivity, by linarith⟩
    -- amplitude bound: |a (n' j)| < ε for j ≥ N₁
    have hamp : ∃ N₁, ∀ j ≥ N₁, |a (n' j)| < ε := by
      rw [Metric.tendsto_atTop] at hconv
      obtain ⟨N₁, hN₁⟩ := hconv ε hε
      exact ⟨N₁, fun j hj => by have := hN₁ j hj; simpa [Real.dist_eq] using this⟩
    obtain ⟨N₁, hN₁⟩ := hamp
    -- band invariance: if j ≥ N₁ and |S j - L| ≤ ε then |S (j+1) - L| ≤ ε
    have hinv : ∀ j ≥ N₁, |(∑ i:Fin j, a (n' i)) - L| ≤ ε →
        |(∑ i:Fin (j+1), a (n' i)) - L| ≤ ε := by
      intro j hj hband
      have hstep : (∑ i:Fin (j+1), a (n' i)) = (∑ i:Fin j, a (n' i)) + a (n' j) := by
        rw [Fin.sum_univ_castSucc]; simp [Function.comp]
      have haj := hN₁ j hj
      rw [abs_lt] at haj
      rw [_root_.abs_le] at hband ⊢
      rw [hstep]
      by_cases hc : ∑ i:Fin j, a (n' i) < L
      · have hsgn := hsign_pos j hc
        constructor <;> nlinarith [hband.1, hband.2, haj.1, haj.2, hsgn]
      · have hsgn := hsign_neg j hc
        push_neg at hc
        constructor <;> nlinarith [hband.1, hband.2, haj.1, haj.2, hsgn]
    -- existence of an entry index j₀ ≥ N₁ with |S j₀ - L| ≤ ε
    have hentry : ∃ j₀ ≥ N₁, |(∑ i:Fin j₀, a (n' i)) - L| ≤ ε := by
      -- a positive-branch index a₁ ≥ N₁
      have hI : ({j | ∑ i:Fin j, a (n' i) < L}).Infinite := Set.infinite_coe_iff.mp h_case_I
      obtain ⟨a₁, ha₁mem, ha₁ge⟩ := hI.exists_gt N₁  -- a₁ > N₁ with S a₁ < L
      -- a later index b > a₁ with S b ≥ L
      have hII : ({j | ∑ i:Fin j, a (n' i) ≥ L}).Infinite := Set.infinite_coe_iff.mp h_case_II
      obtain ⟨b, hbmem, hbgt⟩ := hII.exists_gt a₁
      simp only [Set.mem_setOf_eq] at ha₁mem hbmem
      -- find the last index in [a₁, b) with S < L; its successor enters the band
      -- use well-ordering: the set of k in [a₁,b] with S k ≥ L is nonempty (b), take its min ≥ a₁+1
      classical
      let P : ℕ → Prop := fun k => a₁ < k ∧ k ≤ b ∧ L ≤ ∑ i:Fin k, a (n' i)
      have hPb : P b := ⟨hbgt, le_refl b, hbmem⟩
      let j1 := Nat.find ⟨b, hPb⟩
      have hj1P : P j1 := Nat.find_spec ⟨b, hPb⟩
      have hj1min : ∀ k < j1, ¬ P k := fun k hk => Nat.find_min ⟨b, hPb⟩ hk
      -- j1 - 1 ≥ a₁ has S < L
      obtain ⟨hj1gt, hj1le, hj1ge⟩ := hj1P
      have hj1pos : 1 ≤ j1 := by omega
      have hprev : ∑ i:Fin (j1 - 1), a (n' i) < L := by
        by_contra hcon; push_neg at hcon
        rcases Nat.lt_or_ge a₁ (j1 - 1) with hlt | hge
        · exact hj1min (j1 - 1) (by omega) ⟨hlt, by omega, hcon⟩
        · -- j1 - 1 ≤ a₁, but S a₁ < L; if j1-1 = a₁ then contradiction with hcon
          have : j1 - 1 = a₁ := by omega
          rw [this] at hcon; exact absurd ha₁mem (not_lt.mpr hcon)
      -- entry at j1: |S j1 - L| ≤ ε
      refine ⟨j1, by omega, ?_⟩
      obtain ⟨p, hp⟩ : ∃ p, j1 = p + 1 := ⟨j1 - 1, by omega⟩
      have hprev' : ∑ i:Fin p, a (n' i) < L := by rwa [show p = j1 - 1 by omega]
      have hstep : (∑ i:Fin j1, a (n' i)) = (∑ i:Fin p, a (n' i)) + a (n' p) := by
        rw [hp, Fin.sum_univ_castSucc]; simp [Function.comp]
      have hampj : |a (n' p)| < ε := hN₁ p (by omega)
      rw [abs_lt] at hampj
      rw [_root_.abs_le]
      rw [hstep]
      have hsgn := hsign_pos p hprev'
      have hj1ge' : L ≤ (∑ i:Fin p, a (n' i)) + a (n' p) := by rw [← hstep]; exact hj1ge
      constructor
      · nlinarith [hampj.1, hsgn, hprev']
      · nlinarith [hampj.2, hprev', hj1ge']
    -- from entry + invariance, S stays in band forever after
    obtain ⟨j₀, hj₀ge, hj₀band⟩ := hentry
    refine ⟨j₀, fun j hj => ?_⟩
    -- prove |S j - L| ≤ ε for all j ≥ j₀ by induction
    have hall : ∀ k, |(∑ i:Fin (j₀ + k), a (n' i)) - L| ≤ ε := by
      intro k; induction k with
      | zero => simpa using hj₀band
      | succ m ih =>
        have := hinv (j₀ + m) (by omega) ih
        simpa [show j₀ + (m + 1) = (j₀ + m) + 1 by ring] using this
    have : |(∑ i:Fin j, a (n' i)) - L| ≤ ε := by
      have := hall (j - j₀); rwa [show j₀ + (j - j₀) = j by omega] at this
    rw [Real.dist_eq]; linarith [this]
  -- transfer to the series partial sums
  have hsum : (a ∘ n':Series).convergesTo L := by
    rw [Series.convergesTo]
    have hpb : ∀ j:ℕ, ((a ∘ n':Series).partial ((j:ℤ) - 1)) = ∑ i:Fin j, a (n' i) := hbridge
    -- partial N for N ≥ 0 equals S (N+1)
    have hkey : atTop.Tendsto (fun N:ℤ => (a ∘ n':Series).partial N) (nhds L) := by
      rw [Metric.tendsto_atTop]
      rw [Metric.tendsto_atTop] at hStendsto
      intro ε hε
      obtain ⟨M, hM⟩ := hStendsto ε hε
      refine ⟨(M:ℤ), fun N hN => ?_⟩
      have hN0 : (0:ℤ) ≤ N := le_trans (by positivity) hN
      lift N to ℕ using hN0 with n hn
      have hbr : (a ∘ n':Series).partial ((n:ℤ)) = ∑ i:Fin (n+1), a (n' i) := by
        have := hpb (n + 1)
        rwa [show ((n+1:ℕ):ℤ) - 1 = (n:ℤ) by push_cast; ring] at this
      rw [hbr]
      apply hM (n + 1)
      have : (M:ℤ) ≤ (n:ℤ) := hN
      have : M ≤ n := by exact_mod_cast this
      omega
    exact hkey
  use n'
  refine ⟨ ⟨ hn'_inj, hn'_surj ⟩, ?_ ⟩; convert hsum

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  sorry

theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  sorry

end Chapter8
