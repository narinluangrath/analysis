import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 11.8: The Riemann-Stieltjes integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of `α_length`.
- The piecewise constant Riemann-Stieltjes integral.
- The full Riemann-Stieltjes integral.

{open Set}

Technical notes:
- In Lean it is more convenient to make definitions such as `α_length` and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of `α_length`, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `x` `f` is defined on {lean}`Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of `α_length`. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of `α_length` and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Ioi x₀)).map f)

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Iio x₀)).map f)

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo x₀ (x₀ + ε))).Tendsto f  (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ico_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]; congr 1; simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo (x₀ - ε) x₀)).Tendsto f (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ioc_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  choose l u hx₀ hX using h; simp at hx₀
  have hl : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X :=
    ⟨ x₀-l, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  have hu : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X :=
    ⟨ u-x₀, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Ioi x₀) f (sInf (f '' .Ioi x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsGT
  rw [bddBelow_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' .Ioi x₀) := right_lim_def (right_lim_of_monotone x₀ hf)

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Iio x₀) f (sSup (f '' .Iio x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsLT
  rw [bddAbove_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' .Iio x₀) := left_lim_def (left_lim_of_monotone x₀ hf)

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le (by simp); intro a ha
  apply le_csInf (by simp); intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; grind

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply csInf_le
      . rw [bddBelow_def]; use f a; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply le_csSup
      . rw [bddAbove_def]; use f b; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

syntax:max term "[" term "]ₗ" : term
macro_rules | `($α[$I]ₗ) => `(α_length $α $I)

theorem α_length_of_empty (α: ℝ → ℝ) {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc _ _ => by simp [Set.Icc_eq_empty_iff] at *; simp [*]
  | Ico a b => by simp [Set.Ico_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioc a b => by simp [Set.Ioc_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioo _ _ => by simp [Set.Ioo_eq_empty_iff] at *; simp [*]

@[simp]
theorem α_length_of_pt {α: ℝ → ℝ} (a:ℝ) : α[Icc a a]ₗ = jump α a := by simp [α_length, jump]

theorem α_length_of_cts {α:ℝ → ℝ} {I: BoundedInterval} {a b: ℝ}
  (haa: a < I.a) (hab: I.a ≤ I.b) (hbb: I.b < b)
  (hI : I ⊆ Ioo a b) (hα: ContinuousOn α (Ioo a b)) :
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.a - a, by grind, by intro _; simp; grind ⟩
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.a, by grind, by intro _; simp; grind ⟩
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.b - a, by grind, by intro _; simp; grind ⟩
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.b, by grind, by intro _; simp; grind ⟩
  cases I with
  | Icc _ _ => grind
  | Ico _ _ => grind
  | Ioc _ _ => grind
  | Ioo _ _ => simp [α_length, ha_right, hb_left]; intro h; have := le_antisymm h (by linarith); subst this; simp

/-- Example 11.8.2-/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  rw [α_length_of_cts (a := 1) (b := 4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [BoundedInterval.subset_iff, BoundedInterval.set_Icc, BoundedInterval.set_Ioo]
        intro x hx; rw [Set.mem_Icc] at hx; rw [Set.mem_Ioo]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (by exact (continuous_pow 2).continuousOn)]
  norm_num

example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  rw [α_length_of_cts (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
    (by rw [BoundedInterval.subset_iff, BoundedInterval.set_Icc, BoundedInterval.set_Ioo]
        intro x hx; rw [Set.mem_Icc] at hx; rw [Set.mem_Ioo]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (by exact (continuous_pow 2).continuousOn)]
  norm_num

example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  simp [α_length]

/-- Example 11.8.3-/
@[simp]
theorem α_len_of_id (I: BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  rcases lt_or_ge I.b I.a with hab | hab
  · rw [α_length_of_empty _ (BoundedInterval.empty_of_lt hab)]
    simp only [BoundedInterval.length]
    exact (max_eq_right (by linarith)).symm
  · rw [α_length_of_cts (a := I.a - 1) (b := I.b + 1) (by linarith) hab (by linarith)
      (by rw [BoundedInterval.subset_iff]
          refine (?_ : (I:Set ℝ) ⊆ Set.Icc I.a I.b).trans ?_
          · have := BoundedInterval.subset_Icc I; rwa [BoundedInterval.subset_iff] at this
          · rw [BoundedInterval.set_Ioo]; intro x hx; rw [Set.mem_Icc] at hx; rw [Set.mem_Ioo]
            exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by exact continuous_id.continuousOn)]
    simp only [BoundedInterval.length]
    exact (max_eq_left (by linarith)).symm

/-- An improved version of {name}`BoundedInterval.joins` that also controls {name}`α_length`. -/
abbrev BoundedInterval.joins' (K I J: BoundedInterval) : Prop :=  K.joins I J ∧ ∀ α:ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

theorem BoundedInterval.join_Icc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := ⟨ join_Icc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩


theorem BoundedInterval.join_Icc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := ⟨ join_Icc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := ⟨ join_Ioc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := ⟨ join_Ioc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a < c by grind] ⟩

theorem BoundedInterval.join_Ico_Icc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := ⟨ join_Ico_Icc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ico_Ico' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := ⟨ join_Ico_Ico hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Icc' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := ⟨ join_Ioo_Icc hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Ico' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := ⟨ join_Ioo_Ico hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a < c by grind] ⟩

section
open Classical
open Classical in
private noncomputable def Lend (α:ℝ→ℝ) (I:BoundedInterval) : ℝ := if I.a ∈ (I:Set ℝ) then left_lim α I.a else right_lim α I.a
open Classical in
private noncomputable def Rend (α:ℝ→ℝ) (I:BoundedInterval) : ℝ := if I.b ∈ (I:Set ℝ) then right_lim α I.b else left_lim α I.b
private theorem αlen_eq {α:ℝ→ℝ} {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) : α[I]ₗ = Rend α I - Lend α I := by
  cases I with
  | Icc a b => simp only [set_Icc] at h; obtain ⟨x,hx⟩ := h; rw [Set.mem_Icc] at hx
               have hab : a ≤ b := le_trans hx.1 hx.2
               simp [α_length, Lend, Rend, BoundedInterval.toSet, Set.mem_Icc, hab, le_refl]
  | Ico a b => simp only [set_Ico] at h; obtain ⟨x,hx⟩ := h; rw [Set.mem_Ico] at hx
               have hab : a < b := lt_of_le_of_lt hx.1 hx.2
               simp [α_length, Lend, Rend, BoundedInterval.toSet, Set.mem_Ico, hab.le, hab, le_refl]
  | Ioc a b => simp only [set_Ioc] at h; obtain ⟨x,hx⟩ := h; rw [Set.mem_Ioc] at hx
               have hab : a < b := lt_of_lt_of_le hx.1 hx.2
               simp [α_length, Lend, Rend, BoundedInterval.toSet, Set.mem_Ioc, hab.le, hab, le_refl]
  | Ioo a b => simp only [set_Ioo] at h; obtain ⟨x,hx⟩ := h; rw [Set.mem_Ioo] at hx
               have hab : a < b := lt_trans hx.1 hx.2
               simp [α_length, Lend, Rend, BoundedInterval.toSet, Set.mem_Ioo, hab, le_refl, not_lt, le_of_lt]
private theorem αl_csInf_eq_a {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) : sInf (I:Set ℝ) = I.a := by
  cases I with
  | Icc a b => simp only [set_Icc] at h ⊢; exact csInf_Icc (Set.nonempty_Icc.mp h)
  | Ico a b => simp only [set_Ico] at h ⊢; exact csInf_Ico (Set.nonempty_Ico.mp h)
  | Ioc a b => simp only [set_Ioc] at h ⊢; exact csInf_Ioc (Set.nonempty_Ioc.mp h)
  | Ioo a b => simp only [set_Ioo] at h ⊢; exact csInf_Ioo (Set.nonempty_Ioo.mp h)
private theorem αl_csSup_eq_b {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) : sSup (I:Set ℝ) = I.b := by
  cases I with
  | Icc a b => simp only [set_Icc] at h ⊢; exact csSup_Icc (Set.nonempty_Icc.mp h)
  | Ico a b => simp only [set_Ico] at h ⊢; exact csSup_Ico (Set.nonempty_Ico.mp h)
  | Ioc a b => simp only [set_Ioc] at h ⊢; exact csSup_Ioc (Set.nonempty_Ioc.mp h)
  | Ioo a b => simp only [set_Ioo] at h ⊢; exact csSup_Ioo (Set.nonempty_Ioo.mp h)
private theorem αl_ab_le {I:BoundedInterval} (h:(I:Set ℝ).Nonempty) : I.a ≤ I.b := by
  obtain ⟨x,hx⟩ := h; have := BoundedInterval.subset_Icc I; rw [subset_iff,set_Icc] at this
  have := this hx; rw [Set.mem_Icc] at this; linarith
private theorem αl_ge_a {I:BoundedInterval} {x:ℝ} (hx: x ∈ (I:Set ℝ)) : I.a ≤ x := by
  have := BoundedInterval.subset_Icc I; rw [subset_iff,set_Icc] at this; have := this hx; rw [Set.mem_Icc] at this; exact this.1
private theorem αl_le_b {I:BoundedInterval} {x:ℝ} (hx: x ∈ (I:Set ℝ)) : x ≤ I.b := by
  have := BoundedInterval.subset_Icc I; rw [subset_iff,set_Icc] at this; have := this hx; rw [Set.mem_Icc] at this; exact this.2
private theorem αl_len_eq {I:BoundedInterval} (h:(I:Set ℝ).Nonempty) : |I|ₗ = I.b - I.a := by
  simp only [BoundedInterval.length]; exact max_eq_left (by linarith [αl_ab_le h])
private theorem αl_eq_of_set_eq {K K':BoundedInterval} (h: (K:Set ℝ)=(K':Set ℝ)) (α) : α[K]ₗ = α[K']ₗ := by
  rcases eq_or_ne (K:Set ℝ) ∅ with he | hne
  · rw [α_length_of_empty α he, α_length_of_empty α (h ▸ he)]
  · have hne' : (K:Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have hne'' : (K':Set ℝ).Nonempty := h ▸ hne'
    rw [αlen_eq hne', αlen_eq hne'']
    have ha : K.a = K'.a := by rw [← αl_csInf_eq_a hne', ← αl_csInf_eq_a hne'', h]
    have hb : K.b = K'.b := by rw [← αl_csSup_eq_b hne', ← αl_csSup_eq_b hne'', h]
    simp only [Rend, Lend, ha, hb, h]
private theorem αl_core_mem {I:BoundedInterval} {x:ℝ} (h1: I.a < x) (h2: x < I.b) : x ∈ (I:Set ℝ) := by
  have := BoundedInterval.Ioo_subset I; rw [subset_iff, set_Ioo] at this; exact this ⟨h1,h2⟩
private theorem αl_pt_mem {I:BoundedInterval} (h: (I:Set ℝ).Nonempty) (hab: I.a = I.b) : I.a ∈ (I:Set ℝ) := by
  obtain ⟨x, hx⟩ := h
  have hxa : x = I.a := le_antisymm (by rw [hab]; exact αl_le_b hx) (αl_ge_a hx)
  rwa [hxa] at hx
private theorem αl_sep {I J:BoundedInterval} (hI:(I:Set ℝ).Nonempty)(hJ:(J:Set ℝ).Nonempty)
    (hd:(I:Set ℝ)∩(J:Set ℝ)=∅) : I.b ≤ J.a ∨ J.b ≤ I.a := by
  by_contra hcon; push_neg at hcon; obtain ⟨h1, h2⟩ := hcon
  rw [Set.eq_empty_iff_forall_notMem] at hd
  rcases eq_or_lt_of_le (αl_ab_le hI) with hIpt | hIlt
  · exact hd I.a ⟨αl_pt_mem hI hIpt, αl_core_mem (I:=J) (x:=I.a) (by rw [hIpt]; exact h1) h2⟩
  rcases eq_or_lt_of_le (αl_ab_le hJ) with hJpt | hJlt
  · exact hd J.a ⟨αl_core_mem (I:=I) (x:=J.a) (by rw [hJpt]; exact h2) h1, αl_pt_mem hJ hJpt⟩
  · have hca : I.a ≤ max I.a J.a := le_max_left _ _
    have hcb : J.a ≤ max I.a J.a := le_max_right _ _
    have hdb : min I.b J.b ≤ I.b := min_le_left _ _
    have hdb' : min I.b J.b ≤ J.b := min_le_right _ _
    have hcd : max I.a J.a < min I.b J.b := by
      simp only [max_lt_iff, lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> assumption
    have hp1 : max I.a J.a < (max I.a J.a + min I.b J.b)/2 := by linarith
    have hp2 : (max I.a J.a + min I.b J.b)/2 < min I.b J.b := by linarith
    exact hd ((max I.a J.a + min I.b J.b)/2)
      ⟨αl_core_mem (lt_of_le_of_lt hca hp1) (lt_of_lt_of_le hp2 hdb),
       αl_core_mem (lt_of_le_of_lt hcb hp1) (lt_of_lt_of_le hp2 hdb')⟩
private theorem αl_ordConn (I:BoundedInterval) : (I:Set ℝ).OrdConnected := by
  cases I with
  | Ioo a b => rw [set_Ioo]; exact Set.ordConnected_Ioo
  | Icc a b => rw [set_Icc]; exact Set.ordConnected_Icc
  | Ioc a b => rw [set_Ioc]; exact Set.ordConnected_Ioc
  | Ico a b => rw [set_Ico]; exact Set.ordConnected_Ico
private theorem joins_α_aux {K I J:BoundedInterval} (α:ℝ→ℝ)
    (hI:(I:Set ℝ).Nonempty)(hJ:(J:Set ℝ).Nonempty)(hsep: I.b ≤ J.a)
    (hd:(I:Set ℝ)∩(J:Set ℝ)=∅)(hc:(K:Set ℝ)=(I:Set ℝ)∪(J:Set ℝ))
    (hlen: |K|ₗ = |I|ₗ + |J|ₗ) : α[K]ₗ = α[I]ₗ + α[J]ₗ := by
  have hK : (K:Set ℝ).Nonempty := by rw [hc]; obtain ⟨x,hx⟩ := hI; exact ⟨x, Or.inl hx⟩
  have hKbdd : BddBelow (K:Set ℝ) := (Bornology.IsBounded.of_boundedInterval K).bddBelow
  have hKbdda : BddAbove (K:Set ℝ) := (Bornology.IsBounded.of_boundedInterval K).bddAbove
  have hIsubK : (I:Set ℝ) ⊆ (K:Set ℝ) := by rw [hc]; exact Set.subset_union_left
  have hJsubK : (J:Set ℝ) ⊆ (K:Set ℝ) := by rw [hc]; exact Set.subset_union_right
  have hKa : K.a = I.a := by
    rw [← αl_csInf_eq_a hK]; apply le_antisymm
    · rw [← αl_csInf_eq_a hI]; exact csInf_le_csInf hKbdd hI hIsubK
    · apply le_csInf hK; intro x hx; rw [hc] at hx
      rcases hx with h | h
      · exact αl_ge_a h
      · exact le_trans (le_trans (αl_ab_le hI) hsep) (αl_ge_a h)
  have hKb : K.b = J.b := by
    rw [← αl_csSup_eq_b hK]; apply le_antisymm
    · apply csSup_le hK; intro x hx; rw [hc] at hx
      rcases hx with h | h
      · exact le_trans (αl_le_b h) (le_trans hsep (αl_ab_le hJ))
      · exact αl_le_b h
    · rw [← αl_csSup_eq_b hJ]; exact csSup_le_csSup hKbdda hJ hJsubK
  have hmid : I.b = J.a := by
    have h1 := αl_len_eq hI; have h2 := αl_len_eq hJ; have h3 := αl_len_eq hK
    rw [h1, h2, h3, hKa, hKb] at hlen; linarith
  have hbK : I.b ∈ (K:Set ℝ) := by
    obtain ⟨x, hx⟩ := hI; obtain ⟨y, hy⟩ := hJ
    exact (αl_ordConn K).out' (hIsubK hx) (hJsubK hy)
      ⟨αl_le_b hx, le_trans (by rw [hmid]) (αl_ge_a hy)⟩
  have hA : Lend α K = Lend α I := by
    have hmemA : (I.a ∈ (K:Set ℝ)) ↔ (I.a ∈ (I:Set ℝ)) := by
      constructor
      · intro hm; by_contra hni; rw [hc] at hm; rcases hm with h | h
        · exact hni h
        · exact hni (αl_pt_mem hI (le_antisymm (αl_ab_le hI) (le_trans hsep (αl_ge_a h))))
      · intro hm; rw [hc]; exact Or.inl hm
    unfold Lend; rw [hKa, hmemA]
  have hB : Rend α K = Rend α J := by
    have hmemB : (J.b ∈ (K:Set ℝ)) ↔ (J.b ∈ (J:Set ℝ)) := by
      constructor
      · intro hm; rw [hc] at hm; rcases hm with h | h
        · have hbb : J.a = J.b := le_antisymm (αl_ab_le hJ) (le_trans (αl_le_b h) hsep)
          rw [← hbb]; exact αl_pt_mem hJ hbb
        · exact h
      · intro hm; rw [hc]; exact Or.inr hm
    unfold Rend; rw [hKb, hmemB]
  have hC : Rend α I = Lend α J := by
    unfold Rend Lend
    by_cases hbI : I.b ∈ (I:Set ℝ)
    · rw [if_pos hbI]
      have hJa : J.a ∉ (J:Set ℝ) := by
        rw [← hmid]; intro h
        have : I.b ∈ (I:Set ℝ) ∩ (J:Set ℝ) := ⟨hbI, h⟩; rw [hd] at this; exact this
      rw [if_neg hJa, hmid]
    · rw [if_neg hbI]
      have hJa : J.a ∈ (J:Set ℝ) := by
        rw [hc] at hbK; rcases hbK with h | h
        · exact absurd h hbI
        · rwa [hmid] at h
      rw [if_pos hJa, hmid]
  rw [αlen_eq hK, αlen_eq hI, αlen_eq hJ, hA, hB, hC]; ring
private theorem joins_α {K I J:BoundedInterval} (hj: K.joins I J) (α:ℝ→ℝ) : α[K]ₗ = α[I]ₗ + α[J]ₗ := by
  obtain ⟨hd, hc, hl⟩ := hj
  rcases eq_or_ne (I:Set ℝ) ∅ with hIe | hIne
  · rw [α_length_of_empty α hIe, zero_add]
    exact αl_eq_of_set_eq (by rw [hc, hIe, Set.empty_union]) α
  rcases eq_or_ne (J:Set ℝ) ∅ with hJe | hJne
  · rw [α_length_of_empty α hJe, add_zero]
    exact αl_eq_of_set_eq (by rw [hc, hJe, Set.union_empty]) α
  have hI := Set.nonempty_iff_ne_empty.mpr hIne
  have hJ := Set.nonempty_iff_ne_empty.mpr hJne
  rcases αl_sep hI hJ hd with hs | hs
  · exact joins_α_aux α hI hJ hs hd hc hl
  · rw [add_comm]
    exact joins_α_aux α hJ hI hs (by rw [Set.inter_comm]; exact hd)
      (by rw [Set.union_comm]; exact hc) (by rw [hl]; ring)

end

/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  generalize hcard : P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  · rw [Finset.card_eq_zero] at hcard
    have hIe : (I:Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x hx
      obtain ⟨J,⟨hJ,_⟩,_⟩ := P.exists_unique x ((mem_iff I x).mpr hx); rw [hcard] at hJ; simp at hJ
    rw [hcard, Finset.sum_empty, α_length_of_empty α hIe]
  · rcases lt_or_ge I.a I.b with hlt | hge
    · obtain ⟨K, L, P', hK, hjoin, hP'⟩ := P.exists_peel hlt
      have hαI : α[I]ₗ = α[L]ₗ + α[K]ₗ := joins_α hjoin α
      have hcardL : P'.intervals.card = n := by rw [hP', Finset.card_erase_of_mem hK]; omega
      have hLsum := hn P' hcardL
      rw [← Finset.add_sum_erase _ (fun J => α[J]ₗ) hK, ← hP', hLsum, hαI]; ring
    · rcases eq_or_ne (I:Set ℝ) ∅ with hIe | hIne
      · rw [α_length_of_empty α hIe]; apply Finset.sum_eq_zero; intro J hJ
        have hsub : (J:Set ℝ) ⊆ (I:Set ℝ) := by have := P.contains J hJ; rwa [subset_iff] at this
        exact α_length_of_empty α (Set.subset_eq_empty hsub hIe)
      · have hne := Set.nonempty_iff_ne_empty.mpr hIne
        have hpt : I.a = I.b := le_antisymm (αl_ab_le hne) hge
        have hIset : (I:Set ℝ) = {I.a} := by
          apply Set.eq_singleton_iff_unique_mem.mpr
          exact ⟨αl_pt_mem hne hpt, fun x hx => le_antisymm (le_trans (αl_le_b hx) hge) (αl_ge_a hx)⟩
        obtain ⟨Js, ⟨hJsmem, hJsa⟩, hJsuniq⟩ := P.exists_unique I.a ((mem_iff I I.a).mpr (αl_pt_mem hne hpt))
        refine (Finset.sum_eq_single Js ?_ ?_).trans ?_
        · intro J hJ hne2
          apply α_length_of_empty
          rw [Set.eq_empty_iff_forall_notMem]; intro x hx
          have hxI : x ∈ (I:Set ℝ) := by have := P.contains J hJ; rw [subset_iff] at this; exact this hx
          rw [hIset, Set.mem_singleton_iff] at hxI; subst hxI
          exact hne2 (hJsuniq J ⟨hJ, (mem_iff J I.a).mpr hx⟩)
        · intro h; exact absurd hJsmem h
        · apply αl_eq_of_set_eq; rw [hIset]
          apply Set.eq_singleton_iff_unique_mem.mpr
          refine ⟨(mem_iff Js I.a).mp hJsa, fun x hx => ?_⟩
          have := P.contains Js hJsmem; rw [subset_iff, hIset] at this; exact this hx

/-- Definition 11.8.5 (Piecewise constant RS integral)-/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ)   :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x) = 22 := by
  sorry

/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) :RS_integ f P (fun x ↦ x) = integ f P := by
  simp only [PiecewiseConstantWith.RS_integ, PiecewiseConstantWith.integ]
  apply Finset.sum_congr rfl
  intro J hJ; rw [α_len_of_id]

theorem PiecewiseConstantWith.RS_integ_eq_of_le {f:ℝ → ℝ} {I: BoundedInterval} {Q R: Partition I}
    (hQR: Q ≤ R) (hQ: PiecewiseConstantWith f Q) (α:ℝ → ℝ) : RS_integ f Q α = RS_integ f R α := by
  classical
  have hg : ∀ K ∈ R.intervals, ∃ J ∈ Q.intervals, (K:Set ℝ) ⊆ (J:Set ℝ) := by
    intro K hK; obtain ⟨J, hJ, hsub⟩ := hQR K hK
    rw [BoundedInterval.subset_iff] at hsub; exact ⟨J, hJ, hsub⟩
  choose! g hgmem hgsub using hg
  have hcval : ∀ J ∈ Q.intervals, ∀ K, (K:Set ℝ).Nonempty → (K:Set ℝ) ⊆ (J:Set ℝ) →
      constant_value_on f (K:Set ℝ) = constant_value_on f (J:Set ℝ) := by
    intro J hJ K hKne hKJ
    obtain ⟨x, hx⟩ := hKne
    have hcK : ConstantOn f (K:Set ℝ) :=
      ConstantOn.of_const (fun y hy => ConstantOn.eq (hQ J hJ) (hKJ hy))
    rw [← ConstantOn.eq hcK hx, ← ConstantOn.eq (hQ J hJ) (hKJ hx)]
  have hsumlen : ∀ J ∈ Q.intervals,
      ∑ K ∈ R.intervals.filter (fun K => g K = J), α[K]ₗ = α[J]ₗ := by
    intro J hJ
    have hex : ∃ QJ : Partition J, QJ.intervals = R.intervals.filter (fun K => g K = J) := by
      refine ⟨⟨R.intervals.filter (fun K => g K = J), ?_, ?_⟩, rfl⟩
      · intro x hx
        have hxI : x ∈ (I:Set ℝ) := by
          have := Q.contains J hJ; rw [BoundedInterval.subset_iff] at this
          exact this ((BoundedInterval.mem_iff J x).mp hx)
        obtain ⟨K, ⟨hKmem, hxK⟩, hKuniq⟩ := R.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)
        have hgKJ : g K = J := by
          have hxgK : x ∈ (g K:Set ℝ) := hgsub K hKmem ((BoundedInterval.mem_iff K x).mp hxK)
          exact (Q.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).unique
            ⟨hgmem K hKmem, (BoundedInterval.mem_iff (g K) x).mpr hxgK⟩ ⟨hJ, hx⟩
        refine ⟨K, ⟨Finset.mem_filter.mpr ⟨hKmem, hgKJ⟩, hxK⟩, ?_⟩
        rintro K' ⟨hK'F, hxK'⟩
        exact hKuniq K' ⟨(Finset.mem_filter.mp hK'F).1, hxK'⟩
      · intro K hKF
        have hKmem := (Finset.mem_filter.mp hKF).1
        have hgKJ := (Finset.mem_filter.mp hKF).2
        rw [BoundedInterval.subset_iff]; intro y hy
        have := hgsub K hKmem hy; rw [hgKJ] at this; exact this
    obtain ⟨QJ, hQJ⟩ := hex
    have := Partition.sum_of_α_length QJ α; rw [hQJ] at this; exact this
  show ∑ J ∈ Q.intervals, _ = ∑ K ∈ R.intervals, _
  rw [← Finset.sum_fiberwise_of_maps_to hgmem (fun K => constant_value_on f (K:Set ℝ) * α[K]ₗ)]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← hsumlen J hJ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hKF
  have hKmem := (Finset.mem_filter.mp hKF).1
  have hgKJ := (Finset.mem_filter.mp hKF).2
  rcases eq_or_ne (K:Set ℝ) ∅ with hKe | hKne
  · rw [α_length_of_empty α hKe]; ring
  · have hKsub : (K:Set ℝ) ⊆ (J:Set ℝ) := by
      have := hgsub K hKmem; rw [hgKJ] at this; exact this
    rw [hcval J hJ K (Set.nonempty_iff_ne_empty.mpr hKne) hKsub]

/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  rw [RS_integ_eq_of_le (BoundedInterval.le_max P P').1 hP α,
      RS_integ_eq_of_le (BoundedInterval.le_max P P').2 hP' α]

open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ):
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

theorem PiecewiseConstantOn.RS_integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) (α:ℝ → ℝ) : RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [RS_integ, h']; exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- {name}`α_length` non-negative when α monotone -/
theorem α_length_nonneg_of_monotone {α:ℝ → ℝ}  (hα: Monotone α) (I: BoundedInterval):
  0 ≤ α[I]ₗ := by
  have hl_le : ∀ x, left_lim α x ≤ α x := fun x => by
    rw [left_lim_of_monotone' x hα]; apply csSup_le (by simp); rintro y ⟨z, hz, rfl⟩; exact hα hz.le
  have hr_ge : ∀ x, α x ≤ right_lim α x := fun x => by
    rw [right_lim_of_monotone' x hα]; apply le_csInf (by simp); rintro y ⟨z, hz, rfl⟩; exact hα hz.le
  have hl_mono : ∀ {x y:ℝ}, x ≤ y → left_lim α x ≤ left_lim α y := fun {x y} h => by
    rw [left_lim_of_monotone' x hα, left_lim_of_monotone' y hα]
    apply csSup_le_csSup ⟨α y, by rintro w ⟨z, hz, rfl⟩; exact hα hz.le⟩
      ((Set.nonempty_Iio).image α) (Set.image_mono (Set.Iio_subset_Iio h))
  have hr_mono : ∀ {x y:ℝ}, x ≤ y → right_lim α x ≤ right_lim α y := fun {x y} h => by
    rw [right_lim_of_monotone' x hα, right_lim_of_monotone' y hα]
    apply csInf_le_csInf ⟨α x, by rintro w ⟨z, hz, rfl⟩; exact hα hz.le⟩
      ((Set.nonempty_Ioi).image α) (Set.image_mono (Set.Ioi_subset_Ioi h))
  cases I with
  | Icc a b =>
    simp only [α_length]
    split_ifs with hab
    · linarith [hl_le a, hα hab, hr_ge b]
    · exact le_refl 0
  | Ico a b =>
    simp only [α_length]
    split_ifs with hab
    · linarith [hl_mono hab]
    · exact le_refl 0
  | Ioc a b =>
    simp only [α_length]
    split_ifs with hab
    · linarith [hr_mono hab]
    · exact le_refl 0
  | Ioo a b =>
    simp only [α_length]
    split_ifs with hab
    · linarith [right_lim_le_left_lim_of_monotone hab hα]
    · exact le_refl 0

/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  have hfR : PiecewiseConstantWith f (P ⊔ Q) := hP.mono (BoundedInterval.le_max P Q).1
  have hgR : PiecewiseConstantWith g (P ⊔ Q) := hQ.mono (BoundedInterval.le_max P Q).2
  have hfgR : PiecewiseConstantWith (f + g) (P ⊔ Q) := fun J hJ => by
    obtain ⟨vf, hvf⟩ := hfR J hJ; obtain ⟨vg, hvg⟩ := hgR J hJ
    exact ⟨vf + vg, fun y => by show f ↑y + g ↑y = vf + vg; simp only [hvf, hvg]⟩
  rw [RS_integ_def hfgR α, RS_integ_def hfR α, RS_integ_def hgR α]
  simp only [PiecewiseConstantWith.RS_integ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hJne : (J:Set ℝ).Nonempty
  · rw [show constant_value_on (f + g) ↑J = constant_value_on f ↑J + constant_value_on g ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show f x + g x = _; rw [(hfR J hJ).eq hx, (hgR J hJ).eq hx]]
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  obtain ⟨P, hP⟩ := hf
  have hcf : PiecewiseConstantWith (c • f) P := fun J hJ => by
    obtain ⟨v, hv⟩ := hP J hJ
    exact ⟨c • v, fun y => by show c • f ↑y = c • v; simp only [hv]⟩
  rw [RS_integ_def hcf α, RS_integ_def hP α]
  simp only [PiecewiseConstantWith.RS_integ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hJne : (J:Set ℝ).Nonempty
  · rw [show constant_value_on (c • f) ↑J = c * constant_value_on f ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show c • f x = _; rw [(hP J hJ).eq hx, smul_eq_mul]]
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  have hfR : PiecewiseConstantWith f (P ⊔ Q) := hP.mono (BoundedInterval.le_max P Q).1
  have hgR : PiecewiseConstantWith g (P ⊔ Q) := hQ.mono (BoundedInterval.le_max P Q).2
  have hfgR : PiecewiseConstantWith (f - g) (P ⊔ Q) := fun J hJ => by
    obtain ⟨vf, hvf⟩ := hfR J hJ; obtain ⟨vg, hvg⟩ := hgR J hJ
    exact ⟨vf - vg, fun y => by show f ↑y - g ↑y = vf - vg; simp only [hvf, hvg]⟩
  rw [RS_integ_def hfgR α, RS_integ_def hfR α, RS_integ_def hgR α]
  simp only [PiecewiseConstantWith.RS_integ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hJne : (J:Set ℝ).Nonempty
  · rw [show constant_value_on (f - g) ↑J = constant_value_on f ↑J - constant_value_on g ↑J from by
      apply ConstantOn.const_eq hJne; intro x hx
      show f x - g x = _; rw [(hfR J hJ).eq hx, (hgR J hJ).eq hx]]
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ RS_integ f I α := by
  obtain ⟨P, hP⟩ := hf
  rw [RS_integ_def hP α]
  simp only [PiecewiseConstantWith.RS_integ]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases hJne : (J:Set ℝ).Nonempty
  · apply mul_nonneg _ (α_length_nonneg_of_monotone hα J)
    obtain ⟨x, hx⟩ := hJne
    have hxI : x ∈ I := by
      rw [mem_iff]; have hsub := P.contains J hJ; rw [subset_iff] at hsub; exact hsub hx
    rw [← (hP J hJ).eq hx]; exact h x hxI
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; simp

/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ f I α ≤ RS_integ g I α := by
  have hnn := RS_integ_of_nonneg (f := g - f) hα
    (fun x hx => by show 0 ≤ g x - f x; linarith [h x hx]) (hg.sub hf)
  rw [RS_integ_sub hα hg hf] at hnn
  linarith

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  have hpc : PiecewiseConstantWith (fun _:ℝ ↦ c) (⊥:Partition I) := fun J hJ => by
    have hmem : J ∈ (⊥:Partition I).intervals := hJ
    rw [Partition.intervals_of_bot, Finset.mem_singleton] at hmem; subst hmem
    exact ConstantOn.of_const' c _
  rw [RS_integ_def hpc α]
  simp only [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot, Finset.sum_singleton]
  by_cases hne : (I:Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hne (fun x _ => rfl)]
  · rw [Set.not_nonempty_iff_eq_empty] at hne; rw [α_length_of_empty α hne]; ring

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  have hpc : PiecewiseConstantWith f (⊥:Partition I) := fun J hJ => by
    have hmem : J ∈ (⊥:Partition I).intervals := hJ
    rw [Partition.intervals_of_bot, Finset.mem_singleton] at hmem; subst hmem; exact h
  rw [RS_integ_def hpc α]
  simp only [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot, Finset.sum_singleton]

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J :=
  PiecewiseConstantOn.of_extend hIJ h

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  classical
  set g : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hgdef
  have hg0 : ∀ K : BoundedInterval, (∀ x ∈ (K:Set ℝ), x ∉ (I:Set ℝ)) →
      constant_value_on g (K:Set ℝ) * α[K]ₗ = 0 := by
    intro K hK
    rcases eq_or_ne (K:Set ℝ) ∅ with he | hne
    · rw [α_length_of_empty α he, mul_zero]
    · rw [ConstantOn.const_eq (Set.nonempty_iff_ne_empty.mpr hne) (c := 0)
        (fun x hx => by rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by
          rw [BoundedInterval.mem_iff]; exact hK x hx)]), zero_mul]
  by_cases hIemp : (I:Set ℝ) = ∅
  · have hRg : RS_integ g J α = 0 := by
      have hcg : ConstantOn g (J:Set ℝ) := ConstantOn.of_const (c := 0) (fun x _ => by
        rw [hgdef]; simp only [if_neg (show ¬ (x ∈ I) by
          rw [BoundedInterval.mem_iff, hIemp]; exact Set.notMem_empty x)])
      rw [RS_integ_const' hα hcg]
      exact hg0 J (fun x _ => by rw [hIemp]; exact Set.notMem_empty x)
    have hRf : RS_integ f I α = 0 := by
      have hcf : ConstantOn f (I:Set ℝ) := ConstantOn.of_const (c := 0)
        (fun x hx => absurd hx (by rw [hIemp]; exact Set.notMem_empty x))
      rw [RS_integ_const' hα hcf, α_length_of_empty α hIemp, mul_zero]
    rw [hRg, hRf]
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, L, R, hpcQ, hQint, hgL, hgR⟩ := PiecewiseConstantOn.of_extend_aux hIJ hP hIemp
  have key : ∀ (a:BoundedInterval) (s:Finset BoundedInterval),
      constant_value_on g (a:Set ℝ) * α[a]ₗ = 0 →
      ∑ K ∈ insert a s, constant_value_on g (K:Set ℝ) * α[K]ₗ
        = ∑ K ∈ s, constant_value_on g (K:Set ℝ) * α[K]ₗ := by
    intro a s ha
    by_cases hmem : a ∈ s
    · rw [Finset.insert_eq_self.mpr hmem]
    · rw [Finset.sum_insert hmem, ha, zero_add]
  rw [RS_integ_def hpcQ α, RS_integ_def hP α]
  simp only [PiecewiseConstantWith.RS_integ, hQint]
  rw [key L _ (hg0 L hgL), key R _ (hg0 R hgR)]
  apply Finset.sum_congr rfl
  intro K hK
  congr 1
  apply constant_value_on_congr
  intro x hx
  have hxI : x ∈ (I:Set ℝ) := by
    have := P.contains K hK; rw [BoundedInterval.subset_iff] at this; exact this hx
  rw [hgdef]; simp only [if_pos (show x ∈ I by rw [BoundedInterval.mem_iff]; exact hxI)]

/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  classical
  have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.1.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.1.2.1]; exact Set.subset_union_right
  obtain ⟨PI, hPI⟩ := h.restrict hIK
  obtain ⟨PJ, hPJ⟩ := h.restrict hJK
  have hjoinpc : PiecewiseConstantWith f (PI.join PJ hIJK.1) := by
    intro L hL; rcases Finset.mem_union.mp hL with hL | hL
    · exact hPI L hL
    · exact hPJ L hL
  rw [RS_integ_def hjoinpc α, RS_integ_def hPI α, RS_integ_def hPJ α]
  simp only [PiecewiseConstantWith.RS_integ]
  have hinter0 : ∑ L ∈ PI.intervals ∩ PJ.intervals, (constant_value_on f (L:Set ℝ) * α[L]ₗ) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    rw [Finset.mem_inter] at hL
    have hLI := PI.contains L hL.1; rw [BoundedInterval.subset_iff] at hLI
    have hLJ := PJ.contains L hL.2; rw [BoundedInterval.subset_iff] at hLJ
    have hLe : (L:Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x hx
      have hxIJ : x ∈ (I:Set ℝ) ∩ (J:Set ℝ) := ⟨hLI hx, hLJ hx⟩
      rw [hIJK.1.1] at hxIJ; exact hxIJ
    rw [α_length_of_empty α hLe, mul_zero]
  have hsui := Finset.sum_union_inter (s₁ := PI.intervals) (s₂ := PJ.intervals)
    (f := fun L => constant_value_on f (L:Set ℝ) * α[L]ₗ)
  rw [hinter0, add_zero] at hsui
  exact hsui

/-- Analogue of Definition 11.3.2 (Uppper and lower Riemann integrals )-/
noncomputable abbrev upper_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sInf ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sSup ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

lemma RS_integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_ ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : -M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_ ⟩, by convert PiecewiseConstantOn.RS_integ_const _ _ hα using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

lemma RS_integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

lemma RS_integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  {α:ℝ → ℝ} (hα: Monotone α)
  (ha: a ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    have ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    have ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]; apply hhp.RS_integ_mono hα _ hgp; intro _ hx; linarith [hmin _ hx, hmaj _ hx]

lemma RS_integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

lemma RS_integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  BddAbove ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

lemma le_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

lemma lower_RS_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply csSup_le (RS_integral_bound_lower_nonempty h hα)
  intros
  apply le_csInf (RS_integral_bound_upper_nonempty h hα)
  intros; solve_by_elim [RS_integral_bound_lower_le_upper]

lemma RS_upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
  csInf_le (RS_integral_bound_below (.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

lemma upper_RS_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
  csInf_le (RS_integral_bound_below hf hα) ⟨ g, by simpa [hg] ⟩

lemma integ_le_lower_RS_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above hf hα) ⟨ h, by simpa [hg] ⟩

lemma lt_of_gt_upper_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α: ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: upper_RS_integral f I α < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY; have ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY; exact ⟨ g, hmaj, hgp, by rwa [hgi] ⟩

lemma gt_of_lt_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: X < lower_RS_integral f I α) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY; have ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY; exact ⟨ h, hmin, hhp, by rwa [hhi] ⟩

/-- Analogue of Definition 11.3.4 -/
noncomputable abbrev RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ) : ℝ := upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

/-- Analogue of various components of Lemma 11.3.3 -/
private theorem pc_RS_integ_id_eq_integ {g:ℝ → ℝ} {I: BoundedInterval} (hg: PiecewiseConstantOn g I) :
    PiecewiseConstantOn.RS_integ g I (fun x ↦ x) = PiecewiseConstantOn.integ g I := by
  rw [PiecewiseConstantOn.RS_integ_def hg.choose_spec, PiecewiseConstantOn.integ_def hg.choose_spec]
  exact PiecewiseConstantWith.RS_integ_eq_integ hg.choose

theorem upper_RS_integral_eq_upper_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  unfold upper_RS_integral upper_integral
  congr 1
  exact Set.image_congr (fun g ⟨_, hg⟩ => pc_RS_integ_id_eq_integ hg)

theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  unfold lower_RS_integral lower_integral
  congr 1
  exact Set.image_congr (fun g ⟨_, hg⟩ => pc_RS_integ_id_eq_integ hg)

theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I :=
  upper_RS_integral_eq_upper_integral f I

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  unfold RS_IntegrableOn IntegrableOn
  rw [upper_RS_integral_eq_upper_integral, lower_RS_integral_eq_lower_integral]

theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  have hbdd : BddOn f I := by
    obtain ⟨P, hP⟩ := hf
    by_cases hne : P.intervals.Nonempty
    · refine ⟨(P.intervals.image (fun K : BoundedInterval => |constant_value_on f (K:Set ℝ)|)).max' (hne.image _), fun x hx => ?_⟩
      obtain ⟨J, ⟨hJmem, hxJ⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [(hP J hJmem).eq ((BoundedInterval.mem_iff J x).mp hxJ)]
      apply Finset.le_max'
      exact Finset.mem_image_of_mem (fun K : BoundedInterval => |constant_value_on f (K:Set ℝ)|) hJmem
    · refine ⟨0, fun x hx => ?_⟩
      obtain ⟨J, ⟨hJmem, _⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact absurd hJmem (hne ▸ Finset.notMem_empty J)
  have hup := upper_RS_integral_le_integ hbdd (fun x _ => le_refl (f x)) hf hα
  have hlow := integ_le_lower_RS_integral hbdd (fun x _ => le_refl (f x)) hf hα
  have hlu := lower_RS_integral_le_upper hbdd hα
  refine ⟨⟨hbdd, by linarith⟩, ?_⟩
  show upper_RS_integral f I α = PiecewiseConstantOn.RS_integ f I α
  linarith


/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
 {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  classical
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  by_cases hsing : |I|ₗ = 0
  · haveI : Subsingleton ((I:Set ℝ)) := BoundedInterval.length_of_subsingleton.mpr hsing
    exact (RS_integ_of_piecewise_const ConstantOn.of_subsingleton.piecewiseConstantOn hα).1
  refine ⟨hfbound, ?_⟩
  have hab : I.a < I.b := by
    by_contra hcon; push_neg at hcon
    exact hsing (by simp only [BoundedInterval.length]; exact max_eq_right (by linarith))
  obtain ⟨M, hM⟩ := id hfbound
  have hcont := hf
  rw [UniformContinuousOn.iff] at hcont
  have key : ∀ ε:ℝ, 0 < ε → upper_RS_integral f I α - lower_RS_integral f I α ≤ ε * α[I]ₗ := by
    intro ε hε
    obtain ⟨δ, hδ, hfu⟩ := hcont ε hε; simp [Real.Close, Real.dist_eq] at hfu
    obtain ⟨N, hN⟩ := exists_nat_gt ((I.b-I.a)/δ)
    have hNpos : 0 < N := by
      have h0 : 0 < (I.b-I.a)/δ := div_pos (by linarith) hδ
      rify; order
    have hN' : (I.b-I.a)/(N:ℝ) < δ := by rw [div_lt_comm₀ (by positivity) hδ]; exact hN
    obtain ⟨P, hcard, hlength⟩ := unif_gen N hNpos I hab
    have hcontJ : ∀ J ∈ P.intervals, (J:Set ℝ) ⊆ (I:Set ℝ) := by
      intro J hJ; have := P.contains J hJ; rwa [subset_iff] at this
    have hbddA : ∀ J ∈ P.intervals, BddAbove (f '' (J:Set ℝ)) := fun J hJ =>
      ⟨M, by rintro y ⟨z, hz, rfl⟩; linarith [(abs_le.mp (hM z (hcontJ J hJ hz))).2]⟩
    have hbddB : ∀ J ∈ P.intervals, BddBelow (f '' (J:Set ℝ)) := fun J hJ =>
      ⟨-M, by rintro y ⟨z, hz, rfl⟩; linarith [(abs_le.mp (hM z (hcontJ J hJ hz))).1]⟩
    have hpos : (0:ℝ) < (I.b-I.a)/N := div_pos (by linarith) (by positivity)
    have hJne : ∀ J ∈ P.intervals, (f '' (J:Set ℝ)).Nonempty := by
      intro J hJ
      have hJl := hlength J hJ
      refine Set.Nonempty.image _ ?_
      rw [Set.nonempty_iff_ne_empty]; intro he
      rw [BoundedInterval.length_of_empty he] at hJl; linarith
    have hosc : ∀ J ∈ P.intervals, sSup (f '' (J:Set ℝ)) - sInf (f '' (J:Set ℝ)) ≤ ε := by
      intro J hJ
      have h1 : ∀ y ∈ (J:Set ℝ), sSup (f '' (J:Set ℝ)) ≤ f y + ε := by
        intro y hy; apply csSup_le (hJne J hJ); rintro _ ⟨z, hz, rfl⟩
        have hdd : |f z - f y| ≤ ε := by
          apply hfu y (hcontJ J hJ hy) z (hcontJ J hJ hz)
          exact le_of_lt (lt_of_le_of_lt (BoundedInterval.dist_le_length hz hy)
            (by rw [hlength J hJ]; exact hN'))
        linarith [(abs_le.mp hdd).2]
      have h2 : sSup (f '' (J:Set ℝ)) - ε ≤ sInf (f '' (J:Set ℝ)) := by
        apply le_csInf (hJne J hJ); rintro _ ⟨y, hy, rfl⟩; linarith [h1 y hy]
      linarith
    -- step functions
    set gs : ℝ → ℝ := fun x => if h : x ∈ (I:Set ℝ) then
      sSup (f '' (((P.exists_unique x ((BoundedInterval.mem_iff I x).mpr h)).exists.choose : BoundedInterval) : Set ℝ)) else 0 with hgsdef
    set gi : ℝ → ℝ := fun x => if h : x ∈ (I:Set ℝ) then
      sInf (f '' (((P.exists_unique x ((BoundedInterval.mem_iff I x).mpr h)).exists.choose : BoundedInterval) : Set ℝ)) else 0 with hgidef
    have hgsval : ∀ J, J ∈ P.intervals → ∀ x, x ∈ (J:Set ℝ) → gs x = sSup (f '' (J:Set ℝ)) := by
      intro J hJ x hx
      have hxI : x ∈ (I:Set ℝ) := hcontJ J hJ hx
      have hch := (P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).unique
        (P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).exists.choose_spec
        ⟨hJ, (BoundedInterval.mem_iff J x).mpr hx⟩
      simp only [gs, dif_pos hxI, hch]
    have hgival : ∀ J, J ∈ P.intervals → ∀ x, x ∈ (J:Set ℝ) → gi x = sInf (f '' (J:Set ℝ)) := by
      intro J hJ x hx
      have hxI : x ∈ (I:Set ℝ) := hcontJ J hJ hx
      have hch := (P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).unique
        (P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hxI)).exists.choose_spec
        ⟨hJ, (BoundedInterval.mem_iff J x).mpr hx⟩
      simp only [gi, dif_pos hxI, hch]
    have hgspc : PiecewiseConstantOn gs I := ⟨P, fun J hJ => ConstantOn.of_const (hgsval J hJ)⟩
    have hgipc : PiecewiseConstantOn gi I := ⟨P, fun J hJ => ConstantOn.of_const (hgival J hJ)⟩
    have hgsmaj : MajorizesOn gs f I := by
      intro x hx
      obtain ⟨J, ⟨hJmem, hxJ⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [hgsval J hJmem x ((BoundedInterval.mem_iff J x).mp hxJ)]
      exact le_csSup (hbddA J hJmem) ⟨x, (BoundedInterval.mem_iff J x).mp hxJ, rfl⟩
    have hgimin : MinorizesOn gi f I := by
      intro x hx
      obtain ⟨J, ⟨hJmem, hxJ⟩, _⟩ := P.exists_unique x ((BoundedInterval.mem_iff I x).mpr hx)
      rw [hgival J hJmem x ((BoundedInterval.mem_iff J x).mp hxJ)]
      exact csInf_le (hbddB J hJmem) ⟨x, (BoundedInterval.mem_iff J x).mp hxJ, rfl⟩
    have hup := upper_RS_integral_le_integ hfbound hgsmaj hgspc hα
    have hlo := integ_le_lower_RS_integral hfbound hgimin hgipc hα
    -- RS_integ gs - RS_integ gi = ∑ (sSup - sInf) α[J] ≤ ε α[I]
    have hRSs : PiecewiseConstantOn.RS_integ gs I α = ∑ J ∈ P.intervals, sSup (f '' (J:Set ℝ)) * α[J]ₗ := by
      rw [PiecewiseConstantOn.RS_integ_def (fun J hJ => ConstantOn.of_const (hgsval J hJ)) α]
      simp only [PiecewiseConstantWith.RS_integ]
      apply Finset.sum_congr rfl; intro J hJ
      by_cases hJn : (J:Set ℝ).Nonempty
      · rw [ConstantOn.const_eq hJn (hgsval J hJ)]
      · rw [Set.not_nonempty_iff_eq_empty] at hJn; rw [α_length_of_empty α hJn]; ring
    have hRSi : PiecewiseConstantOn.RS_integ gi I α = ∑ J ∈ P.intervals, sInf (f '' (J:Set ℝ)) * α[J]ₗ := by
      rw [PiecewiseConstantOn.RS_integ_def (fun J hJ => ConstantOn.of_const (hgival J hJ)) α]
      simp only [PiecewiseConstantWith.RS_integ]
      apply Finset.sum_congr rfl; intro J hJ
      by_cases hJn : (J:Set ℝ).Nonempty
      · rw [ConstantOn.const_eq hJn (hgival J hJ)]
      · rw [Set.not_nonempty_iff_eq_empty] at hJn; rw [α_length_of_empty α hJn]; ring
    have hdiff : PiecewiseConstantOn.RS_integ gs I α - PiecewiseConstantOn.RS_integ gi I α ≤ ε * α[I]ₗ := by
      rw [hRSs, hRSi, ← Finset.sum_sub_distrib]
      calc ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ)) * α[J]ₗ - sInf (f '' (J:Set ℝ)) * α[J]ₗ)
          = ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ)) - sInf (f '' (J:Set ℝ))) * α[J]ₗ := by
            apply Finset.sum_congr rfl; intro J hJ; ring
        _ ≤ ∑ J ∈ P.intervals, ε * α[J]ₗ := by
            apply Finset.sum_le_sum; intro J hJ
            apply mul_le_mul_of_nonneg_right (hosc J hJ) (α_length_nonneg_of_monotone hα J)
        _ = ε * ∑ J ∈ P.intervals, α[J]ₗ := by rw [Finset.mul_sum]
        _ = ε * α[I]ₗ := by rw [Partition.sum_of_α_length P α]
    linarith [hup, hlo, hdiff]
  have hlu := lower_RS_integral_le_upper hfbound hα
  have hle0 : upper_RS_integral f I α - lower_RS_integral f I α ≤ 0 :=
    nonneg_of_le_const_mul_eps (fun ε hε => by rw [mul_comm]; exact key ε hε)
  show lower_RS_integral f I α = upper_RS_integral f I α
  linarith

/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc (-1) 1)) : RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) (fun x ↦ -Real.sign x) = 2 * f 0 := by
  sorry

end Chapter11
