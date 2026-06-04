import Mathlib.Tactic
import Analysis.Section_9_8
import Analysis.Section_11_5

/-!
# Analysis I, Section 11.6: Riemann integrability of monotone functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions.

-/

namespace Chapter11
open Chapter9 BoundedInterval

set_option maxHeartbeats 300000 in
/-- Proposition 11.6.1 -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1; rw [←BoundedInterval.length_of_subsingleton]; aesop
  have hbound := BddOn.of_monotone hf
  set I := Icc a b
  have hab' : a ≤ b := by linarith
  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    choose N hN using exists_nat_gt (1/ε)
    have hNpos : 0 < N := by rify; linarith [show 0 < 1/ε by positivity]
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    have hbeq : b = a + δ*N := by simp [δ]; field_simp; linarith
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' j k hjk := by simp at hjk; obtain _ | _ := hjk <;> linarith
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (.map e (.range N))
      exists_unique := by
        intro x hx; simp; by_cases hb: x = b
        . apply ExistsUnique.intro (Icc b b)
          . simp [hb, mem_iff]
          rintro J ⟨ rfl | ⟨ j, hA, rfl ⟩, hJb ⟩; rfl
          simp [e, mem_iff, hb, hbeq] at hJb
          replace hJb := hJb.2
          rw [mul_lt_mul_iff_of_pos_left hδpos] at hJb
          norm_cast at hJb; linarith
        simp [I, mem_iff] at hx
        set j := ⌊ (x-a)/δ ⌋₊
        have hxa : 0 ≤ x-a := by linarith
        have hxaδ : 0 ≤ (x-a)/δ := by positivity
        have hxb : x < b := lt_of_le_of_ne hx.2 hb
        have hxj : x ∈ e j := by
          simp [e, mem_iff, j]; split_ands
          . calc
              _ ≤ a + δ * ((x-a)/δ) := by gcongr; grind [Nat.floor_le]
              _ = x := by grind
          calc
            _ = a + δ * ((x-a)/δ) := by field_simp; linarith
            _ < _ := by gcongr; apply Nat.lt_floor_add_one
        apply ExistsUnique.intro (e j)
        . refine ⟨ ?_, hxj ⟩; right; use j; simp [j, Nat.floor_lt hxaδ, div_lt_iff₀' hδpos]; linarith
        rintro J ⟨ rfl | ⟨ k, hk, rfl ⟩, hxJ ⟩
        . simp [mem_iff] at hxJ; grind
        simp [mem_iff, e] at hxJ hxj
        obtain hjk | rfl | hjk := lt_trichotomy j k
        . replace hjk : δ*((j:ℝ)+1) ≤ δ*(k:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
          linarith
        . rfl
        replace hjk : δ*((k:ℝ)+1) ≤ δ*(j:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
        linarith
      contains J hJ := by
        simp at hJ; obtain rfl | ⟨ j, hj, rfl ⟩ := hJ <;> simp [subset_iff, e, I]
        . linarith
        apply Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc _ _)
        . simp; positivity
        simp [hbeq]; gcongr; norm_cast
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ .range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply csSup_le
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ (by order) <;> simp [I, hδj1, this]; grind
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ :=
        lower_integ_ge_lower_sum hbound P
      _ = ∑ j ∈ .range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≥ ∑ j ∈ .range N, f (a + δ*j) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply le_csInf
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have hajb': a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply_rules [hf] <;> simp [I, hδj] <;> grind
    calc
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ - ∑ j ∈ .range N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        rw [←Finset.sum_sub_distrib]
        have := Finset.sum_range_sub (fun n ↦ f (a + δ*n) * δ) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        convert this using 1; simp [hbeq]; ring
      _ ≤ _ := by
        have : 0 ≤ f b - f a := by simp; apply hf <;> simp [I, hab']
        simp [mul_assoc, δ]; gcongr
        rw [div_le_iff₀', mul_comm, mul_assoc]
        nth_rewrite 1 [←mul_one (b-a)]
        gcongr; rw [←div_le_iff₀']; linarith
        all_goals positivity
  refine ⟨ hbound, ?_ ⟩
  observe low_le_up : lower_integral f I ≤ upper_integral f I
  linarith [nonneg_of_le_const_mul_eps this]


/-- Proposition 11.6.1 -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  rw [←neg_neg f]; apply (integ_of_monotone _).neg.1; convert hf.neg using 1

/-- Corollary 11.6.3 / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  rcases lt_or_ge I.a I.b with hlt | hge
  · classical
    obtain ⟨M, hM⟩ := hbound
    have hbddB : BddBelow (f '' (I:Set ℝ)) :=
      ⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hM x hx)).1⟩
    have hbddA : BddAbove (f '' (I:Set ℝ)) :=
      ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hM x hx)).2⟩
    set lo := sInf (f '' (I:Set ℝ)) with hlodef
    set hi := sSup (f '' (I:Set ℝ)) with hhidef
    have hcore : Set.Ioo I.a I.b ⊆ (I:Set ℝ) := by
      have := I.Ioo_subset; rwa [BoundedInterval.subset_iff, BoundedInterval.set_Ioo] at this
    have hInonempty : (I:Set ℝ).Nonempty :=
      ⟨(I.a+I.b)/2, hcore ⟨by linarith, by linarith⟩⟩
    have hlo_le : ∀ x ∈ (I:Set ℝ), lo ≤ f x := fun x hx => csInf_le hbddB ⟨x, hx, rfl⟩
    have hle_hi : ∀ x ∈ (I:Set ℝ), f x ≤ hi := fun x hx => le_csSup hbddA ⟨x, hx, rfl⟩
    have hlohi : lo ≤ hi := by
      obtain ⟨x, hx⟩ := hInonempty; exact le_trans (hlo_le x hx) (hle_hi x hx)
    set g : ℝ → ℝ := fun x => if x ∈ (I:Set ℝ) then f x else if x ≤ I.a then lo else hi with hgdef
    have hgI : ∀ x ∈ (I:Set ℝ), g x = f x := fun x hx => by simp only [hgdef, if_pos hx]
    have hga : I.a ∉ (I:Set ℝ) → g I.a = lo := fun h => by
      simp only [hgdef, if_neg h, if_pos (le_refl I.a)]
    have hgb : I.b ∉ (I:Set ℝ) → g I.b = hi := fun h => by
      simp only [hgdef, if_neg h, if_neg (by linarith : ¬ I.b ≤ I.a)]
    have hclass : ∀ z ∈ Set.Icc I.a I.b, z ∈ (I:Set ℝ) ∨ z = I.a ∨ z = I.b := by
      intro z hz
      by_cases hzI : z ∈ (I:Set ℝ)
      · left; exact hzI
      · right
        rcases lt_or_ge I.a z with h | h
        · right
          rcases lt_or_ge z I.b with h2 | h2
          · exact absurd (hcore ⟨h, h2⟩) hzI
          · exact le_antisymm hz.2 h2
        · left; exact le_antisymm h hz.1
    have hEqOn : Set.EqOn f g (I:Set ℝ) := fun x hx => (hgI x hx).symm
    have hgmono : MonotoneOn g (Set.Icc I.a I.b) := by
      intro x hx y hy hxy
      rcases hclass x hx with hxI | rfl | rfl <;> rcases hclass y hy with hyI | rfl | rfl
      · rw [hgI x hxI, hgI y hyI]; exact hf hxI hyI hxy
      · have hxeq : x = I.a := le_antisymm hxy hx.1; rw [hxeq]
      · rw [hgI x hxI]
        by_cases hbI : I.b ∈ (I:Set ℝ)
        · rw [hgI _ hbI]; exact hf hxI hbI hxy
        · rw [hgb hbI]; exact hle_hi x hxI
      · rw [hgI y hyI]
        by_cases haI : I.a ∈ (I:Set ℝ)
        · rw [hgI _ haI]; exact hf haI hyI hxy
        · rw [hga haI]; exact hlo_le y hyI
      · exact le_refl _
      · by_cases haI : I.a ∈ (I:Set ℝ)
        · rw [hgI _ haI]
          by_cases hbI : I.b ∈ (I:Set ℝ)
          · rw [hgI _ hbI]; exact hf haI hbI hxy
          · rw [hgb hbI]; exact hle_hi _ haI
        · rw [hga haI]
          by_cases hbI : I.b ∈ (I:Set ℝ)
          · rw [hgI _ hbI]; exact hlo_le _ hbI
          · rw [hgb hbI]; exact hlohi
      · have hyeq : y = I.b := le_antisymm hy.2 hxy; rw [hyeq]
      · exact absurd hxy (not_le.mpr hlt)
      · exact le_refl _
    have hgInt : IntegrableOn g (BoundedInterval.Icc I.a I.b) := integ_of_monotone hgmono
    obtain ⟨_, hge2⟩ := hgInt.mono' I.subset_Icc
    exact ⟨⟨M, hM⟩, by rw [lower_integral_congr hEqOn, upper_integral_congr hEqOn]; exact hge2⟩
  · have hI0 : |I|ₗ = 0 := by rw [BoundedInterval.length]; exact max_eq_right (by linarith)
    exact (integ_on_subsingleton hI0).1

theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  rw [←neg_neg f]
  apply (integ_of_bdd_monotone (f := -f) ?_ ?_).neg.1
  · obtain ⟨M, hM⟩ := hbound
    exact ⟨M, fun x hx => by simp only [Pi.neg_apply, abs_neg]; exact hM x hx⟩
  · intro x hx y hy hxy; simp only [Pi.neg_apply]; exact neg_le_neg (hf hx hy hxy)

/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (.Ici 0)) :
  Summable f ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.

/-- Exercise 11.6.4 -/
example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), Summable f ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), ¬ Summable f ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

end Chapter11
