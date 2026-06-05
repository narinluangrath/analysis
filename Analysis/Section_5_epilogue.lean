import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers `Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers `ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers `ℚ`.

From this point onwards, `Chapter5.Real` will be deprecated, and we will use the standard real
numbers `ℝ` instead.  In particular, one should use the full Mathlib API for `ℝ` for all
subsequent chapters, in lieu of the `Chapter5.Real` API.

Filling the sorries here requires both the Chapter5.Real API and the Mathlib API for the standard
natural numbers `ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, _, hq⟩ := Real.rat_between (show x - 1 < x by linarith)
  exact ⟨q, hq⟩

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq, _⟩ := Real.rat_between (show x < x + 1 by linarith)
  refine ⟨q, ?_⟩
  intro r hr
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hr
  have : (r:Real) < (q:Real) := lt_trans hr hq
  exact le_of_lt ((Real.lt_of_coe r q).mpr this)

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  intro a b hba ha
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at *
  rcases lt_or_eq_of_le hba with h|h
  · exact lt_trans ((Real.lt_of_coe _ _).mp h) ha
  · rw [h]; exact ha

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
  obtain ⟨r, hqr, hrx⟩ := Real.rat_between hq
  exact ⟨r, hrx, (Real.gt_of_coe _ _).mpr hqr⟩

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty :=
  c.nonempty.image _

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  obtain ⟨b, hb⟩ := c.bounded
  refine ⟨(b:Real), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rcases lt_or_eq_of_le (hb hq) with h|h
  · exact le_of_lt ((Real.lt_of_coe _ _).mp h)
  · rw [h]

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    show (x.toCut).toReal = x
    have hlub := (x.toCut).toReal_isLUB
    refine IsLUB.unique hlub ?_
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact le_of_lt hq
    · intro y hy
      by_contra h
      push_neg at h
      obtain ⟨r, hyr, hrx⟩ := Real.rat_between h
      have hmem : (r:Real) ∈ (x.toCut).toSet_Real := ⟨r, hrx, rfl⟩
      have := hy hmem
      exact absurd this (not_le.mpr hyr)
  right_inv c := by
    apply DedekindCut.ext
    ext q
    show (q:Real) < c.toReal ↔ q ∈ c.E
    constructor
    · intro hq
      have hlub := c.toReal_isLUB
      by_contra hqc
      have hub : (q:Real) ∈ upperBounds c.toSet_Real := by
        rintro _ ⟨r, hr, rfl⟩
        by_contra hlt
        push_neg at hlt
        have hrq : r > q := (Real.gt_of_coe _ _).mpr hlt
        exact hqc (c.lower (le_of_lt hrq) hr)
      have := hlub.2 hub
      exact absurd this (not_le.mpr hq)
    · intro hq
      have hlub := c.toReal_isLUB
      obtain ⟨r, hr, hrq⟩ := c.nomax q hq
      have hmem : (r:Real) ∈ c.toSet_Real := ⟨r, hr, rfl⟩
      have hle := hlub.1 hmem
      have hqr : (q:Real) < (r:Real) := (Real.lt_of_coe _ _).mp hrq
      exact lt_of_lt_of_le hqr hle

end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  exact ⟨q, hq⟩

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq⟩ := exists_rat_gt x
  refine ⟨q, ?_⟩
  intro r hr
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hr
  exact_mod_cast le_of_lt (lt_trans hr hq)

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  intro a b hba ha
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at *
  calc (b:ℝ) ≤ a := by exact_mod_cast hba
    _ < x := ha

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
  obtain ⟨r, hqr, hrx⟩ := exists_rat_btwn hq
  exact ⟨r, hrx, by exact_mod_cast hqr⟩

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty :=
  c.nonempty.image _

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  obtain ⟨b, hb⟩ := c.bounded
  refine ⟨(b:ℝ), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  show (q:ℝ) ≤ (b:ℝ)
  exact_mod_cast hb hq

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    show sSup ((fun (q:ℚ) ↦ (q:ℝ)) '' x.toSet_Rat) = x
    have hne : ((fun (q:ℚ) ↦ (q:ℝ)) '' x.toSet_Rat).Nonempty := by
      obtain ⟨q, hq⟩ := exists_rat_lt x; exact ⟨q, q, hq, rfl⟩
    apply IsLUB.csSup_eq _ hne
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact le_of_lt hq
    · intro y hy
      by_contra h
      push_neg at h
      obtain ⟨r, hyr, hrx⟩ := exists_rat_btwn h
      have : (r:ℝ) ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' x.toSet_Rat := ⟨r, hrx, rfl⟩
      have := hy this
      linarith
  right_inv c := by
    apply Chapter5.DedekindCut.ext
    ext q
    show (q:ℝ) < c.toR ↔ q ∈ c.E
    constructor
    · intro hq
      have hlub := c.toR_isLUB
      by_contra hqc
      have hub : (q:ℝ) ∈ upperBounds c.toSet_R := by
        rintro _ ⟨r, hr, rfl⟩
        by_contra hlt
        push_neg at hlt
        have hrq : r > q := by exact_mod_cast hlt
        exact hqc (c.lower (le_of_lt hrq) hr)
      have := hlub.2 hub
      linarith
    · intro hq
      have hlub := c.toR_isLUB
      obtain ⟨r, hr, hrq⟩ := c.nomax q hq
      have hmem : (r:ℝ) ∈ c.toSet_R := ⟨r, hr, rfl⟩
      have hle := hlub.1 hmem
      have : (q:ℝ) < (r:ℝ) := by exact_mod_cast hrq
      linarith

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

-- In order to use this definition, we need some machinery
-----

-- We start by showing it works for ratCasts
theorem Real.equivR_ratCast {q: ℚ} : equivR q = (q: ℝ) := by
  symm
  rw [Real.equivR_iff]
  apply DedekindCut.ext
  ext r
  show (r:ℝ) < (q:ℝ) ↔ (r:Real) < (q:Real)
  rw [← Real.lt_of_coe r q]
  exact_mod_cast Iff.rfl

lemma Real.equivR_nat {n: ℕ} : equivR n = (n: ℝ) := equivR_ratCast
lemma Real.equivR_int {n: ℤ} : equivR n = (n: ℝ) := equivR_ratCast

----

-- We then want to set up a way to convert from the Real `LIM` to the ℝ `Real.mk`
-- To do this we need a few things:

-- Convertion between the notions of Cauchy Sequences
theorem Sequence.IsCauchy.to_IsCauSeq {a: ℕ → ℚ} (ha: IsCauchy a) : IsCauSeq _root_.abs a := by
  rw [Sequence.IsCauchy.coe] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε/2) (by linarith)
  refine ⟨N, ?_⟩
  intro j hj
  have := hN j hj N le_rfl
  rw [Section_4_3.dist_eq] at this
  calc |a j - a N| ≤ ε/2 := this
    _ < ε := by linarith

-- Convertion of an `IsCauchy` to a `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a: ℕ → ℚ} : (ha: IsCauchy a) → CauSeq ℚ _root_.abs := 
  (⟨a, ·.to_IsCauSeq⟩)

-- We then set up the conversion from Sequence.Equiv to CauSeq.LimZero because 
-- it is the equivalence relation
example {a b: CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) (h:Equiv a b) 
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    rw [Sequence.equiv_iff] at h
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε/2) (by linarith)
    refine ⟨N, fun j hj => ?_⟩
    have := hN j hj
    show |a j - b j| < ε
    calc |a j - b j| ≤ ε/2 := this
      _ < ε := by linarith

-- We can now use it to convert between different functions in Real.mk
theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

-- Both directions of the equivalence
theorem Sequence.Equiv_iff_LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) 
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    intro h
    rw [Sequence.equiv_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    show |a n - b n| ≤ ε
    exact le_of_lt this

----
-- We create some cauchy sequences with useful properties

-- We show that for any sequence, it will eventually be arbitrarily close to its LIM
open Real in
theorem Sequence.difference_approaches_zero {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) :
  ∀ε > 0, ∃N, ∀n ≥ N, |LIM a - a n| ≤ (ε: ℚ) := by
    intro ε hε
    have hacoe := (Sequence.IsCauchy.coe a).mp ha
    obtain ⟨N, hN⟩ := hacoe ε hε
    refine ⟨N, fun n hn => ?_⟩
    set b : ℕ → ℚ := fun m => a (m + N) with hb
    have hbcau : (b:Sequence).IsCauchy := by
      rw [Sequence.IsCauchy.coe]
      intro δ hδ
      obtain ⟨M, hM⟩ := hacoe δ hδ
      exact ⟨M, fun j _ k _ => hM (j+N) (by omega) (k+N) (by omega)⟩
    have heqL : LIM a = LIM b := by
      apply (Real.LIM_eq_LIM ha hbcau).mpr
      rw [Sequence.equiv_iff]
      intro δ hδ
      obtain ⟨M, hM⟩ := hacoe δ hδ
      refine ⟨M, fun m hm => ?_⟩
      simp only [hb]
      have := hM m (by omega) (m+N) (by omega)
      rwa [Section_4_3.dist_eq] at this
    have hbnd : ∀ m, |b m - a n| ≤ ε := by
      intro m
      have := hN (m+N) (by omega) n hn
      rwa [Section_4_3.dist_eq] at this
    rw [heqL]
    rw [show ((ε:ℚ):Real) = (ε:Real) from by norm_cast, abs_le]
    constructor
    · have hge : ∀ m, ((a n : ℚ) - ε) ≤ b m := by
        intro m; have := abs_le.mp (hbnd m); linarith [this.1]
      have := Real.LIM_of_ge hbcau (x := ((a n : ℚ) - ε : ℚ)) (by
        intro m; push_cast; exact_mod_cast hge m)
      push_cast at this ⊢
      linarith
    · have hle : ∀ m, b m ≤ ((a n : ℚ) + ε) := by
        intro m; have := abs_le.mp (hbnd m); linarith [this.2]
      have := Real.LIM_of_le hbcau (x := ((a n : ℚ) + ε : ℚ)) (by
        intro m; exact_mod_cast hle m)
      push_cast at this ⊢
      linarith

-- There exists a Cauchy sequence entirely above the LIM
theorem Real.exists_equiv_above {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) 
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by
    have hpick : ∀ n : ℕ, ∃ q : ℚ, LIM a < (q:Real) ∧ (q:Real) < LIM a + (1/(n+1):ℚ) := by
      intro n; apply Real.rat_between
      have : (0:Real) < ((1/(n+1):ℚ):Real) := by
        have : (0:ℚ) < 1/(n+1) := by positivity
        exact_mod_cast this
      linarith
    choose b hb1 hb2 using hpick
    have habove : ∀ n, LIM a ≤ (b n : Real) := fun n => le_of_lt (hb1 n)
    have hequiv : Sequence.Equiv a b := by
      rw [Sequence.equiv_iff]
      intro ε hε
      obtain ⟨N1, hN1⟩ := Sequence.difference_approaches_zero ha (ε/2) (by linarith)
      obtain ⟨N2, hN2⟩ := exists_nat_gt (2/ε : ℚ)
      refine ⟨max N1 (N2+1), fun n hn => ?_⟩
      have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
      have hn2 : N2 + 1 ≤ n := le_trans (le_max_right _ _) hn
      have hsmall : (1/(n+1):ℚ) ≤ ε/2 := by
        rw [div_le_iff₀ (by positivity), ← sub_nonneg]
        have hb : (2/ε:ℚ) < (n:ℚ)+1 := by
          have : (N2:ℚ) ≤ (n:ℚ) := by exact_mod_cast (by omega : N2 ≤ n)
          linarith
        have : (2:ℚ) ≤ ε * ((n:ℚ)+1) := by rw [div_lt_iff₀ hε] at hb; nlinarith
        linarith
      have hd2 : |LIM a - (a n:Real)| ≤ ((ε/2:ℚ):Real) := hN1 n hn1
      have hbub : (b n:Real) - LIM a ≤ ((ε/2:ℚ):Real) := by
        have h1 := hb2 n
        have h2 : ((1/(n+1):ℚ):Real) ≤ ((ε/2:ℚ):Real) := by exact_mod_cast hsmall
        linarith
      have hblb : (b n:Real) - LIM a ≥ 0 := by have := habove n; linarith
      have key : |((a n:Real) - (b n:Real))| ≤ ((ε:ℚ):Real) := by
        rw [abs_le] at hd2 ⊢
        refine ⟨?_, ?_⟩ <;> push_cast at hd2 hbub hblb ⊢ <;> linarith [hd2.1, hd2.2]
      have : ((|a n - b n|:ℚ):Real) ≤ ((ε:ℚ):Real) := by
        rw [show ((|a n - b n|:ℚ):Real) = |((a n:Real) - (b n:Real))| by
          rw [Rat.cast_abs]; push_cast; ring_nf]
        exact key
      exact_mod_cast this
    exact ⟨b, (Sequence.isCauchy_of_equiv hequiv).mp ha, hequiv, habove⟩

-- There exists a Cauchy sequence entirely below the LIM
theorem Real.exists_equiv_below {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) 
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by
    have hpick : ∀ n : ℕ, ∃ q : ℚ, LIM a - (1/(n+1):ℚ) < (q:Real) ∧ (q:Real) < LIM a := by
      intro n; apply Real.rat_between
      have : (0:Real) < ((1/(n+1):ℚ):Real) := by
        have : (0:ℚ) < 1/(n+1) := by positivity
        exact_mod_cast this
      linarith
    choose b hb1 hb2 using hpick
    have hbelow : ∀ n, (b n : Real) ≤ LIM a := fun n => le_of_lt (hb2 n)
    have hequiv : Sequence.Equiv a b := by
      rw [Sequence.equiv_iff]
      intro ε hε
      obtain ⟨N1, hN1⟩ := Sequence.difference_approaches_zero ha (ε/2) (by linarith)
      obtain ⟨N2, hN2⟩ := exists_nat_gt (2/ε : ℚ)
      refine ⟨max N1 (N2+1), fun n hn => ?_⟩
      have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
      have hn2 : N2 + 1 ≤ n := le_trans (le_max_right _ _) hn
      have hsmall : (1/(n+1):ℚ) ≤ ε/2 := by
        rw [div_le_iff₀ (by positivity), ← sub_nonneg]
        have hb : (2/ε:ℚ) < (n:ℚ)+1 := by
          have : (N2:ℚ) ≤ (n:ℚ) := by exact_mod_cast (by omega : N2 ≤ n)
          linarith
        have : (2:ℚ) ≤ ε * ((n:ℚ)+1) := by rw [div_lt_iff₀ hε] at hb; nlinarith
        linarith
      have hd2 : |LIM a - (a n:Real)| ≤ ((ε/2:ℚ):Real) := hN1 n hn1
      have hbub : LIM a - (b n:Real) ≤ ((ε/2:ℚ):Real) := by
        have h1 := hb1 n
        have h2 : ((1/(n+1):ℚ):Real) ≤ ((ε/2:ℚ):Real) := by exact_mod_cast hsmall
        linarith
      have hblb : LIM a - (b n:Real) ≥ 0 := by have := hbelow n; linarith
      have key : |((a n:Real) - (b n:Real))| ≤ ((ε:ℚ):Real) := by
        rw [abs_le] at hd2 ⊢
        refine ⟨?_, ?_⟩ <;> push_cast at hd2 hbub hblb ⊢ <;> linarith [hd2.1, hd2.2]
      have : ((|a n - b n|:ℚ):Real) ≤ ((ε:ℚ):Real) := by
        rw [show ((|a n - b n|:ℚ):Real) = |((a n:Real) - (b n:Real))| by
          rw [Rat.cast_abs]; push_cast; ring_nf]
        exact key
      exact_mod_cast this
    exact ⟨b, (Sequence.isCauchy_of_equiv hequiv).mp ha, hequiv, hbelow⟩

----

-- useful theorems for the following proof
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Relating the ordering of `LIM a` against a rational to the ordering of `Real.mk ha.CauSeq`
theorem Real.keyle {a:ℕ → ℚ} (ha: Sequence.IsCauchy a) (q:ℚ) :
    LIM a ≤ (q:Real) ↔ Real.mk ha.CauSeq ≤ (q:ℝ) := by
  constructor
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨ε', hε'0, hε'ε⟩ := exists_rat_btwn hε
    obtain ⟨N, hN⟩ := Sequence.difference_approaches_zero ha ε' (by exact_mod_cast hε'0)
    apply Real.mk_le_of_forall_le
    refine ⟨N, fun j hj => ?_⟩
    have hd := hN j hj
    have hle : (a j : Real) ≤ (q:Real) + (ε':ℚ) := by
      rw [abs_le] at hd; push_cast at hd; linarith [hd.1, hd.2]
    have hcoe : (a j : ℚ) ≤ q + ε' := by
      by_contra hc; push_neg at hc
      have : ((q+ε':ℚ):Real) < (a j:Real) := (Real.lt_of_coe _ _).mp (by exact_mod_cast hc)
      push_cast at this; linarith
    show ((a j:ℚ):ℝ) ≤ (q:ℝ) + ε
    have : ((a j:ℚ):ℝ) ≤ ((q + ε':ℚ):ℝ) := by exact_mod_cast hcoe
    push_cast at this; linarith
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hqr, hrL⟩ := Real.rat_between hcon
    have hrq : (0:ℚ) < r - q := by
      have := (Real.lt_of_coe q r).mpr hqr; linarith
    set δ : ℚ := (r - q)/2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    obtain ⟨N, hN⟩ := Sequence.difference_approaches_zero ha δ hδ0
    set r' : ℚ := q + δ with hr'
    have hr'q : q < r' := by rw [hr']; linarith
    have hlower : ∀ j ≥ N, (r':ℝ) ≤ ((a j:ℚ):ℝ) := by
      intro j hj
      have hd := hN j hj
      rw [abs_le] at hd
      have h2 : LIM a - (a j:Real) ≤ ((δ:ℚ):Real) := hd.2
      have h1 : (r:Real) < LIM a := hrL
      have h3 : (r':Real) ≤ (a j:Real) := by
        have : (a j:Real) ≥ LIM a - (δ:Real) := by push_cast at h2 ⊢; linarith
        have hrr : (r':Real) = (r:Real) - (δ:Real) := by rw [hr', hδ]; push_cast; ring
        rw [hrr]; push_cast at h1 ⊢; linarith
      have hcoe : (r':ℚ) ≤ a j := by
        by_contra hc; push_neg at hc
        exact absurd h3 (not_le.mpr ((Real.lt_of_coe _ _).mp hc))
      exact_mod_cast hcoe
    have hge : (r':ℝ) ≤ Real.mk ha.CauSeq := Real.le_mk_of_forall_le ⟨N, hlower⟩
    have hle : (r':ℝ) ≤ (q:ℝ) := le_trans hge h
    have : r' ≤ q := by exact_mod_cast hle
    linarith

-- Transform a `Real` to an `ℝ` by going through Cauchy Sequences
-- we can use the conversion of Real.mk_eq to use different sequences to show different parts
theorem Real.equivR_eq' {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : (LIM a).equivR = Real.mk ha.CauSeq := by
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · rintro _ ⟨q, hq, rfl⟩
      simp only [Real.toSet_Rat, Set.mem_setOf_eq] at hq
      have : ¬ (LIM a ≤ (q:Real)) := not_le.mpr hq
      rw [keyle ha] at this
      exact le_of_lt (not_le.mp this)
    · intro M hM
      apply le_of_forall_rat_lt_imp_le
      intro q hq
      have hlt : (q:Real) < LIM a := by
        by_contra hc; push_neg at hc
        rw [keyle ha] at hc; exact absurd hq (not_lt.mpr hc)
      exact hM ⟨q, hlt, rfl⟩

lemma Real.equivR_eq (x: Real) : ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a), 
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by 
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

-- `(q:ℝ) < equivR x ↔ (q:Real) < x`, from `keyle`
theorem Real.equivR_rat_lt {x:Real} (q:ℚ) : ((q:ℝ) < equivR x) ↔ ((q:Real) < x) := by
  obtain ⟨a, ha, rfl, hax⟩ := Real.equivR_eq x
  rw [hax, ← not_le, ← not_le, Real.keyle ha]

theorem Real.real_le_iff (x y : Real) : x ≤ y ↔ ∀ q:ℚ, (q:Real) < x → (q:Real) < y := by
  constructor
  · intro h q hq; exact lt_of_lt_of_le hq h
  · intro h
    by_contra hc; push_neg at hc
    obtain ⟨q, hyq, hqx⟩ := Real.rat_between hc
    exact absurd (h q hqx) (not_lt.mpr (le_of_lt hyq))

theorem Real.real_le_iff_R (x y : ℝ) : x ≤ y ↔ ∀ q:ℚ, (q:ℝ) < x → (q:ℝ) < y := by
  constructor
  · intro h q hq; exact lt_of_lt_of_le hq h
  · intro h
    by_contra hc; push_neg at hc
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hc
    exact absurd (h q hqx) (not_lt.mpr (le_of_lt hyq))

theorem Real.equivR_le_iff (x y : Real) : equivR x ≤ equivR y ↔ x ≤ y := by
  rw [real_le_iff_R, real_le_iff]
  constructor
  · intro h q hq; rw [← equivR_rat_lt]; exact h q ((equivR_rat_lt q).mpr hq)
  · intro h q hq; rw [equivR_rat_lt]; exact h q ((equivR_rat_lt q).mp hq)

/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by
    intro x y
    show equivR (x + y) = equivR x + equivR y
    obtain ⟨a, ha, rfl, hax⟩ := Real.equivR_eq x
    obtain ⟨b, hb, rfl, hby⟩ := Real.equivR_eq y
    rw [hax, hby, Real.LIM_add ha hb, equivR_eq' (Sequence.IsCauchy.add ha hb)]
    rw [show (Sequence.IsCauchy.add ha hb).CauSeq = ha.CauSeq + hb.CauSeq from rfl, Real.mk_add]
  map_mul' := by
    intro x y
    show equivR (x * y) = equivR x * equivR y
    obtain ⟨a, ha, rfl, hax⟩ := Real.equivR_eq x
    obtain ⟨b, hb, rfl, hby⟩ := Real.equivR_eq y
    rw [hax, hby, Real.LIM_mul ha hb, equivR_eq' (Sequence.IsCauchy.mul ha hb)]
    rw [show (Sequence.IsCauchy.mul ha hb).CauSeq = ha.CauSeq * hb.CauSeq from rfl, Real.mk_mul]
  map_le_map_iff' := by
    intro x y
    show equivR x ≤ equivR y ↔ x ≤ y
    exact Real.equivR_le_iff x y

-- helpers for converting properties between Real and ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x: Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

theorem Real.equivR_map_pos {x: Real} : 0 < x ↔ 0 < equivR x := by
  have hz : equivR (0:Real) = 0 := map_zero equivR_ordered_ring
  have hinj : Function.Injective equivR := equivR.injective
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := (equivR_le_iff 0 x).mpr h1; rwa [hz] at this
    · intro he; exact h2 (hinj (by rw [hz]; exact he))
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : equivR 0 ≤ equivR x := by rw [hz]; exact h1
      exact (equivR_le_iff 0 x).mp this
    · intro he; exact h2 (by rw [← he, hz])

theorem Real.equivR_map_nonneg {x: Real} : 0 ≤ x ↔ 0 ≤ equivR x := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, equivR_map_pos]
  have hz : equivR (0:Real) = 0 := map_zero equivR_ordered_ring
  have hinj : Function.Injective equivR := equivR.injective
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h, hz])
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (hinj (by rw [hz]; exact h))


-- Showing equivalence of the different pows
theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n :=
  map_pow equivR_ordered_ring x n

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n :=
  map_zpow₀ equivR_ordered_ring x n

theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  sorry


end Chapter5
