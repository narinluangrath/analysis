import Mathlib.Tactic
import Analysis.Section_9_6

/-!
# Analysis I, Section 9.8: Monotonic functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Review of Mathlib monotonicity concepts.
-/

namespace Chapter9

/-- Definition 9.8.1 -/
theorem MonotoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictMono.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictMonoOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y > f x := by
  constructor <;> intros <;> solve_by_elim

theorem AntitoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictAntitone.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictAntiOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y < f x := by
  constructor <;> intros <;> solve_by_elim

/-- Examples 9.8.2 -/
example : StrictMonoOn (fun x:ℝ ↦ x^2) (.Ici 0) := by
  intro a ha b hb hab; simp only [Set.mem_Ici] at ha hb; nlinarith

example : StrictAntiOn (fun x:ℝ ↦ x^2) (.Iic 0) := by
  intro a ha b hb hab; simp only [Set.mem_Iic] at ha hb; nlinarith

example : ¬ MonotoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro h; have := h (Set.mem_univ (-1)) (Set.mem_univ 0) (by norm_num); norm_num at this

example : ¬ AntitoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro h; have := h (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num); norm_num at this

example {X:Set ℝ} {f:ℝ → ℝ} (hf: StrictMonoOn f X) : MonotoneOn f X := hf.monotoneOn

example (X:Set ℝ) : MonotoneOn (fun x:ℝ ↦ (6:ℝ)) X := monotoneOn_const

example (X:Set ℝ) : AntitoneOn (fun x:ℝ ↦ (6:ℝ)) X := antitoneOn_const

#check nontrivial_iff

example {X:Set ℝ} (hX: Nontrivial X) : ¬ StrictMonoOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  rcases lt_trichotomy x.val y.val with hlt | heq | hgt
  · exact absurd (h x.2 y.2 hlt) (by norm_num)
  · exact hxy (Subtype.ext heq)
  · exact absurd (h y.2 x.2 hgt) (by norm_num)

example (X:Set ℝ) (hX: Nontrivial X) : ¬ StrictAntiOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  rcases lt_trichotomy x.val y.val with hlt | heq | hgt
  · exact absurd (h x.2 y.2 hlt) (by norm_num)
  · exact hxy (Subtype.ext heq)
  · exact absurd (h y.2 x.2 hgt) (by norm_num)

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), ContinuousOn f X ∧ ¬ MonotoneOn f X ∧ ¬ AntitoneOn f X := by
  refine ⟨Set.univ, fun x => x^2, by fun_prop, ?_, ?_⟩
  · intro h; have := h (Set.mem_univ (-1)) (Set.mem_univ 0) (by norm_num); norm_num at this
  · intro h; have := h (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num); norm_num at this

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), MonotoneOn f X ∧ ¬ ContinuousOn f X := by
  refine ⟨Set.univ, fun x => if x ≥ 0 then 1 else 0, ?_, ?_⟩
  · intro a _ b _ hab
    by_cases ha : a ≥ 0
    · have hb : b ≥ 0 := le_trans ha hab
      simp [ha, hb]
    · simp only [ha, if_false]
      split_ifs <;> norm_num
  · intro hcont
    rw [continuousOn_univ] at hcont
    have h1 : Filter.Tendsto (fun x => if x ≥ (0:ℝ) then (1:ℝ) else 0)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (if (0:ℝ) ≥ 0 then (1:ℝ) else 0)) :=
      hcont.continuousAt.continuousWithinAt.tendsto
    have h2 : Filter.Tendsto (fun x => if x ≥ (0:ℝ) then (1:ℝ) else 0)
        (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx
      simp [show ¬(x ≥ 0) by linarith]
    have := tendsto_nhds_unique h1 h2
    norm_num at this

/-- Proposition 9.8.3 / Exercise 9.8.4 -/
theorem MonotoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictMonoOn f (.Icc a b)) :
  f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y
   := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, h.le⟩
  have hb : b ∈ Set.Icc a b := ⟨h.le, le_refl b⟩
  have hfab : f a < f b := hmono ha hb h
  have hinj : Set.InjOn f (Set.Icc a b) := hmono.injOn
  have himg : f '' (Set.Icc a b) = Set.Icc (f a) (f b) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hmono.monotoneOn ha hx hx.1, hmono.monotoneOn hx hb hx.2⟩
    · exact hcont.surjOn_Icc ha hb
  set finv := Function.invFunOn f (Set.Icc a b) with hfinv_def
  have hsurj : Set.SurjOn f (Set.Icc a b) (Set.Icc (f a) (f b)) := by
    rw [← himg]; exact Set.surjOn_image f _
  have hright : ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj hy
    exact Function.invFunOn_eq (f := f) (s := Set.Icc a b) ⟨x, hx, hxy⟩
  have hmem : ∀ y ∈ Set.Icc (f a) (f b), finv y ∈ Set.Icc a b := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj hy
    exact Function.invFunOn_mem (f := f) ⟨x, hx, hxy⟩
  have hleft : ∀ x ∈ Set.Icc a b, finv (f x) = x := by
    intro x hx
    have hfx : f x ∈ Set.Icc (f a) (f b) := by rw [← himg]; exact ⟨x, hx, rfl⟩
    apply hinj (hmem (f x) hfx) hx
    exact hright (f x) hfx
  have hfinv_mono : StrictMonoOn finv (Set.Icc (f a) (f b)) := by
    intro u hu v hv huv
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · have : f (finv u) = f (finv v) := by rw [heq]
      rw [hright u hu, hright v hv] at this; linarith
    · have := hmono (hmem v hv) (hmem u hu) hlt
      rw [hright u hu, hright v hv] at this; linarith
  have hfinv_img : finv '' (Set.Icc (f a) (f b)) = Set.Icc a b := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hmem y hy
    · rintro x hx
      refine ⟨f x, ?_, hleft x hx⟩
      rw [← himg]; exact ⟨x, hx, rfl⟩
  have hfinv_cont : ContinuousOn finv (Set.Icc (f a) (f b)) := by
    set s := Set.Icc a b
    set t := Set.Icc (f a) (f b)
    have hmaps : Set.MapsTo f s t := by rw [← himg]; exact Set.mapsTo_image f s
    have hcont' : Continuous (fun x : s => (⟨f x, hmaps x.2⟩ : t)) :=
      Continuous.subtype_mk hcont.restrict _
    have hbij : Function.Bijective (fun x : s => (⟨f x, hmaps x.2⟩ : t)) := by
      constructor
      · intro x y hxy
        have : f x = f y := congrArg Subtype.val hxy
        exact Subtype.ext (hmono.injOn x.2 y.2 this)
      · intro y
        have hy : (y:ℝ) ∈ f '' s := by rw [himg]; exact y.2
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    let e : s ≃ t := Equiv.ofBijective _ hbij
    let homeo : s ≃ₜ t := Continuous.homeoOfEquivCompactToT2 (f := e) hcont'
    rw [continuousOn_iff_continuous_restrict]
    have heq : (t.restrict finv) = fun y : t => ((homeo.symm y : s) : ℝ) := by
      funext y
      have hval : f (homeo.symm y : s) = (y:ℝ) := congrArg Subtype.val (homeo.apply_symm_apply y)
      show finv (y:ℝ) = ((homeo.symm y : s):ℝ)
      rw [← hval, hleft _ (homeo.symm y).2]
    rw [heq]; fun_prop
  exact ⟨himg, finv, hfinv_cont, hfinv_mono, hfinv_img, hleft, hright⟩

/-- Example 9.8.4-/
example {R :ℝ} (hR: R > 0) {n:ℕ} (hn: n > 0) : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (R^n), (g x)^n = x := by
  set f : ℝ → ℝ := fun x ↦ x^n
  have hcont : ContinuousOn f (.Icc 0 R) := by fun_prop
  have hmono : StrictMonoOn f (.Icc 0 R) := by
    intro _ hx _ _ hxy; simp_all [f]
    apply pow_lt_pow_left₀ hxy <;> grind
  obtain ⟨ g, ⟨ _, _, _, _, hg⟩ ⟩ := (MonotoneOn.exist_inverse (by positivity) f hcont hmono).2
  simp only [f, zero_pow (by positivity)] at hg; use g

/-- Exercise 9.8.1 -/
theorem IsMaxOn.of_monotone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  refine ⟨b, Set.mem_Icc.mpr ⟨h.le, le_refl b⟩, ?_⟩
  rw [isMaxOn_iff]
  intro x hx
  exact hf hx (Set.mem_Icc.mpr ⟨h.le, le_refl b⟩) (Set.mem_Icc.mp hx).2

theorem IsMaxOn.of_strictmono_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictMonoOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax :=
  IsMaxOn.of_monotone_on_compact h hf.monotoneOn

theorem IsMaxOn.of_antitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  refine ⟨a, Set.mem_Icc.mpr ⟨le_refl a, h.le⟩, ?_⟩
  rw [isMaxOn_iff]
  intro x hx
  exact hf (Set.mem_Icc.mpr ⟨le_refl a, h.le⟩) hx (Set.mem_Icc.mp hx).1

theorem IsMaxOn.of_strictantitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictAntiOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax :=
  IsMaxOn.of_antitone_on_compact h hf.antitoneOn

theorem BddOn.of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  refine ⟨|f a| + |f b|, fun x hx => ?_⟩
  obtain ⟨hax, hxb⟩ := Set.mem_Icc.mp hx
  have hab : a ≤ b := le_trans hax hxb
  have h1 : f a ≤ f x := hf (Set.mem_Icc.mpr ⟨le_refl a, hab⟩) hx hax
  have h2 : f x ≤ f b := hf hx (Set.mem_Icc.mpr ⟨hab, le_refl b⟩) hxb
  rw [abs_le]
  constructor <;>
    nlinarith [neg_abs_le (f a), le_abs_self (f b), neg_abs_le (f b), le_abs_self (f a),
      abs_nonneg (f a), abs_nonneg (f b)]

theorem BddOn.of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  refine ⟨|f a| + |f b|, fun x hx => ?_⟩
  obtain ⟨hax, hxb⟩ := Set.mem_Icc.mp hx
  have hab : a ≤ b := le_trans hax hxb
  have h1 : f x ≤ f a := hf (Set.mem_Icc.mpr ⟨le_refl a, hab⟩) hx hax
  have h2 : f b ≤ f x := hf hx (Set.mem_Icc.mpr ⟨hab, le_refl b⟩) hxb
  rw [abs_le]
  constructor <;>
    nlinarith [neg_abs_le (f a), le_abs_self (f b), neg_abs_le (f b), le_abs_self (f a),
      abs_nonneg (f a), abs_nonneg (f b)]



/-- Exercise 9.8.2 -/
theorem no_strictmono_intermediate_value : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: StrictMonoOn f (.Icc a b)), ¬ ∃ y, y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b) := by sorry

theorem no_monotone_intermediate_value : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: MonotoneOn f (.Icc a b)), ¬ ∃ y, y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b) := by sorry

theorem no_strictanti_intermediate_value : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: StrictAntiOn f (.Icc a b)), ¬ ∃ y, y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b) := by
  refine ⟨0, 1, by norm_num, fun x ↦ -x, ?_, ?_⟩
  · intro p _ q _ hpq; show -q < -p; linarith
  · rintro ⟨y, hy | hy⟩ <;> · simp only [Set.mem_Icc, neg_zero] at hy; linarith [hy.1, hy.2]

theorem no_antitone_intermediate_value : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: AntitoneOn f (.Icc a b)), ¬ ∃ y, y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b) := by
  refine ⟨0, 1, by norm_num, fun x ↦ -x, ?_, ?_⟩
  · intro p _ q _ hpq; show -q ≤ -p; linarith
  · rintro ⟨y, hy | hy⟩ <;> · simp only [Set.mem_Icc, neg_zero] at hy; linarith [hy.1, hy.2]

/-- Exercise 9.8.3 -/
theorem mono_of_continuous_inj {a b:ℝ} (h: a < b) {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x )) :
  StrictMonoOn f (.Icc a b) ∨ StrictAntiOn f (.Icc a b) := by
  apply ContinuousOn.strictMonoOn_of_injOn_Icc' h.le hf
  rw [Set.injOn_iff_injective]
  exact hinj

/-- Exercise 9.8.4 -/
def MonotoneOn.exist_inverse_without_continuity {a b:ℝ} (h: a < b) {f: ℝ → ℝ} (hmono: StrictMonoOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 9.8.4 -/
def MonotoneOn.exist_inverse_without_strictmono {a b:ℝ} (h: a < b) (f: ℝ → ℝ)
  (hcont: ContinuousOn f (.Icc a b)) (hmono: MonotoneOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


/- Exercise 9.8.4: state and prove an analogue of `MonotoneOne.exist_inverse` for `Antitone` functions. -/
-- theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictAntiOn f (.Icc a b)) : sorry := by sorry

/-- An equivalence between the natural numbers and the rationals. -/
noncomputable abbrev q_9_8_5 : ℕ ≃ ℚ := nonempty_equiv_of_countable.some

noncomputable abbrev g_9_8_5 : ℚ → ℝ := fun q ↦ (2:ℝ)^(-q_9_8_5.symm q:ℤ)

noncomputable abbrev f_9_8_5 : ℝ → ℝ := fun x ↦ ∑' r : {r:ℚ // (r:ℝ) < x}, g_9_8_5 r

theorem g_pos_9_8_5 (q:ℚ) : 0 < g_9_8_5 q := by unfold g_9_8_5; positivity

theorem g_summable_9_8_5 : Summable g_9_8_5 := by
  have h : Summable (fun n:ℕ => (2:ℝ)^(-n:ℤ)) := by
    have e : (fun n:ℕ => (2:ℝ)^(-n:ℤ)) = (fun n:ℕ => ((1:ℝ)/2)^n) := by
      funext n; rw [div_pow, one_pow, zpow_neg, zpow_natCast]; ring
    rw [e]; exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact h.comp_injective q_9_8_5.symm.injective

theorem f_eq_9_8_5 (x:ℝ) : f_9_8_5 x = ∑' q : ℚ, {r:ℚ | (r:ℝ) < x}.indicator g_9_8_5 q :=
  tsum_subtype {r:ℚ | (r:ℝ) < x} g_9_8_5

/-- Exercise 9.8.5(a) -/
theorem StrictMonoOn.of_f_9_8_5 : StrictMonoOn f_9_8_5 .univ := by
  intro x _ y _ hxy
  rw [f_eq_9_8_5, f_eq_9_8_5]
  obtain ⟨r0, hr0x, hr0y⟩ := exists_rat_btwn hxy
  have hsumx : Summable ({r:ℚ | (r:ℝ) < x}.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  have hsumy : Summable ({r:ℚ | (r:ℝ) < y}.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  refine Summable.tsum_lt_tsum (i := r0) ?_ ?_ hsumx hsumy
  · intro q
    by_cases hq : q ∈ {r:ℚ | (r:ℝ) < x}
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {r:ℚ | (r:ℝ) < y} from lt_trans hq hxy)]
    · rw [Set.indicator_of_notMem hq]
      by_cases hqy : q ∈ {r:ℚ | (r:ℝ) < y}
      · rw [Set.indicator_of_mem hqy]; exact (g_pos_9_8_5 q).le
      · rw [Set.indicator_of_notMem hqy]
  · have hn : r0 ∉ {r:ℚ | (r:ℝ) < x} := not_lt.mpr hr0x.le
    have hy : r0 ∈ {r:ℚ | (r:ℝ) < y} := hr0y
    rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hy]
    exact g_pos_9_8_5 r0

/-- The jump lemma: if `r < x` then `f x ≥ f r + g r`. -/
theorem f_jump_9_8_5 (r:ℚ) {x:ℝ} (hrx : (r:ℝ) < x) :
    f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 x := by
  rw [f_eq_9_8_5, f_eq_9_8_5]
  set Sr := {s:ℚ | (s:ℝ) < (r:ℝ)}
  set Sx := {s:ℚ | (s:ℝ) < x}
  have hsumr : Summable (Sr.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  have hsumx : Summable (Sx.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  -- the comparison function h q = indicator_Sr q + (if q = r then g r else 0)
  set h : ℚ → ℝ := fun q => Sr.indicator g_9_8_5 q + (if q = r then g_9_8_5 r else 0) with hh
  have hsumsingle : Summable (fun q:ℚ => if q = r then g_9_8_5 r else 0) := by
    apply summable_of_finite_support
    apply Set.Finite.subset (Set.finite_singleton r)
    intro q hq
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hq
    simp only [Set.mem_singleton_iff]; exact hq.1
  have hsumh : Summable h := hsumr.add hsumsingle
  have htsumsingle : ∑' q:ℚ, (if q = r then g_9_8_5 r else 0) = g_9_8_5 r := by
    rw [tsum_eq_single r]; · simp
    · intro b hb; simp [hb]
  have htsumh : ∑' q, h q = (∑' q, Sr.indicator g_9_8_5 q) + g_9_8_5 r := by
    rw [hh, Summable.tsum_add hsumr hsumsingle, htsumsingle]
  rw [← htsumh]
  apply Summable.tsum_le_tsum _ hsumh hsumx
  intro q
  show Sr.indicator g_9_8_5 q + (if q = r then g_9_8_5 r else 0) ≤ Sx.indicator g_9_8_5 q
  by_cases hqr : q = r
  · subst hqr
    have hmem : q ∈ Sx := show (q:ℝ) < x from hrx
    have hnmem : q ∉ Sr := by show ¬ (q:ℝ) < (q:ℝ); exact lt_irrefl _
    rw [Set.indicator_of_notMem hnmem, Set.indicator_of_mem hmem, if_pos rfl]
    simp
  · simp only [hqr, if_false, add_zero]
    by_cases hqSr : q ∈ Sr
    · have hqSx : q ∈ Sx := lt_trans hqSr hrx
      rw [Set.indicator_of_mem hqSr, Set.indicator_of_mem hqSx]
    · rw [Set.indicator_of_notMem hqSr]
      by_cases hqSx : q ∈ Sx
      · rw [Set.indicator_of_mem hqSx]; exact (g_pos_9_8_5 q).le
      · rw [Set.indicator_of_notMem hqSx]

/-- Exercise 9.8.5(b) -/
theorem ContinuousAt.of_f_9_8_5' (r:ℚ) : ¬ ContinuousAt f_9_8_5 r := by
  intro hcont
  -- sequence x n = r + 1/(n+1) tends to r from above
  set x : ℕ → ℝ := fun n => (r:ℝ) + 1/(n+1) with hx
  have hxr : Filter.Tendsto x Filter.atTop (nhds (r:ℝ)) := by
    have : Filter.Tendsto (fun n:ℕ => (1:ℝ)/(n+1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := this.const_add (r:ℝ)
    simpa [hx] using this
  have htend : Filter.Tendsto (fun n => f_9_8_5 (x n)) Filter.atTop (nhds (f_9_8_5 r)) :=
    (hcont.tendsto).comp hxr
  have hge : ∀ n, f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 (x n) := by
    intro n
    apply f_jump_9_8_5
    rw [hx]; simp only; have : (0:ℝ) < 1/(n+1) := by positivity
    linarith
  have hlim : f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 r :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds htend hge
  have := g_pos_9_8_5 r
  linarith

/-- Tail bound: for `ε > 0` there is a finite set `F` whose complement has small `g`-mass. -/
theorem g_tail_9_8_5 {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℚ, (∑' q : (↥(↑F : Set ℚ)ᶜ), g_9_8_5 q) < ε := by
  have hg := g_summable_9_8_5
  have hs : HasSum g_9_8_5 (∑' q, g_9_8_5 q) := hg.hasSum
  obtain ⟨F, hF⟩ := Metric.tendsto_atTop.mp hs ε hε
  refine ⟨F, ?_⟩
  have hsplit := hg.tsum_subtype_add_tsum_subtype_compl (↑F : Set ℚ)
  have hFsum : (∑' q : (↑F : Set ℚ), g_9_8_5 q) = ∑ q ∈ F, g_9_8_5 q := by
    rw [tsum_subtype]; rw [tsum_eq_sum (s := F)]
    · apply Finset.sum_congr rfl; intro q hq; rw [Set.indicator_of_mem]; exact hq
    · intro q hq; rw [Set.indicator_of_notMem]; exact hq
  rw [hFsum] at hsplit
  have hdist := hF F le_rfl
  rw [Real.dist_eq, abs_lt] at hdist
  have : (∑' q : (↥(↑F : Set ℚ)ᶜ), g_9_8_5 q) = (∑' q, g_9_8_5 q) - ∑ q ∈ F, g_9_8_5 q := by
    linarith [hsplit]
  rw [this]; linarith [hdist.1]

/-- Exercise 9.8.5(c) -/
theorem ContinuousAt.of_f_9_8_5 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) : ContinuousAt f_9_8_5 x := by
  have hxirr : ∀ q : ℚ, (q:ℝ) ≠ x := by
    intro q hq; exact hx ⟨q, hq.symm⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨F, hFtail⟩ := g_tail_9_8_5 (half_pos hε)
  -- choose δ ≤ all distances from x to rationals in F, and δ > 0
  obtain ⟨δ, hδpos, hδle⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ F, δ ≤ |(q:ℝ) - x| := by
    by_cases hFne : F.Nonempty
    · refine ⟨F.inf' hFne (fun q => |(q:ℝ) - x|), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro q _; rw [abs_pos, sub_ne_zero]; exact hxirr q
      · intro q hq; exact Finset.inf'_le _ hq
    · refine ⟨1, by norm_num, ?_⟩
      intro q hq; exact absurd ⟨q, hq⟩ hFne
  refine ⟨δ, hδpos, ?_⟩
  intro y hyx
  rw [Real.dist_eq] at hyx ⊢
  -- bound |f y - f x| by the tail
  rw [f_eq_9_8_5, f_eq_9_8_5]
  set Sx := {r:ℚ | (r:ℝ) < x}
  set Sy := {r:ℚ | (r:ℝ) < y}
  have hsumx : Summable (Sx.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  have hsumy : Summable (Sy.indicator g_9_8_5) := g_summable_9_8_5.indicator _
  set d : ℚ → ℝ := fun q => Sy.indicator g_9_8_5 q - Sx.indicator g_9_8_5 q with hd
  have hsumd : Summable d := hsumy.sub hsumx
  -- pointwise: |d q| ≤ (Fᶜ).indicator g q
  have hdbound : ∀ q : ℚ, |d q| ≤ ((↑F:Set ℚ)ᶜ).indicator g_9_8_5 q := by
    intro q
    show |Sy.indicator g_9_8_5 q - Sx.indicator g_9_8_5 q| ≤ ((↑F:Set ℚ)ᶜ).indicator g_9_8_5 q
    by_cases hsame : (Sy.indicator g_9_8_5 q) = (Sx.indicator g_9_8_5 q)
    · rw [hsame, sub_self, abs_zero]
      apply Set.indicator_nonneg; intro a _; exact (g_pos_9_8_5 a).le
    · -- q is strictly between x and y, so |q - x| < δ, so q ∉ F
      have hqFc : q ∈ ((↑F:Set ℚ)ᶜ) := by
        rw [Set.mem_compl_iff, Finset.mem_coe]
        intro hqF
        -- derive |q - x| < δ
        have hbetween : |(q:ℝ) - x| < δ := by
          by_cases hqx : (q:ℝ) < x
          · -- then q ∈ Sx; for indicators to differ, q ∉ Sy, i.e. q ≥ y, so y ≤ q < x
            have hmemx : q ∈ Sx := hqx
            have hnmemy : q ∉ Sy := by
              intro hmy
              apply hsame
              rw [Set.indicator_of_mem hmy, Set.indicator_of_mem hmemx]
            have hyq : ¬ ((q:ℝ) < y) := hnmemy
            push_neg at hyq
            -- y ≤ q < x, and |y - x| < δ
            rw [abs_lt]; constructor
            · -- q - x ≥ y - x > -δ
              have : y - x > -δ := by rw [abs_lt] at hyx; linarith [hyx.1]
              linarith
            · linarith
          · push_neg at hqx
            -- q ≥ x; for differ need q ∈ Sy, i.e. q < y, so x ≤ q < y
            have hnmemx : q ∉ Sx := by simp only [Sx, Set.mem_setOf_eq]; linarith
            have hmemy : q ∈ Sy := by
              by_contra hmy
              apply hsame
              rw [Set.indicator_of_notMem hmy, Set.indicator_of_notMem hnmemx]
            have hqy : (q:ℝ) < y := hmemy
            rw [abs_lt]; constructor
            · linarith
            · have : y - x < δ := by rw [abs_lt] at hyx; linarith [hyx.2]
              linarith
        exact absurd (hδle q hqF) (not_le.mpr hbetween)
      rw [Set.indicator_of_mem hqFc]
      -- |d q| ≤ g q since each indicator is in [0, g q]
      have hineq : |Sy.indicator g_9_8_5 q - Sx.indicator g_9_8_5 q| ≤ g_9_8_5 q := by
        have hyb : Sy.indicator g_9_8_5 q ≤ g_9_8_5 q :=
          Set.indicator_apply_le' (fun _ => le_refl _) (fun _ => (g_pos_9_8_5 q).le)
        have hxb : Sx.indicator g_9_8_5 q ≤ g_9_8_5 q :=
          Set.indicator_apply_le' (fun _ => le_refl _) (fun _ => (g_pos_9_8_5 q).le)
        have hyn : 0 ≤ Sy.indicator g_9_8_5 q :=
          Set.indicator_nonneg (fun _ _ => (g_pos_9_8_5 q).le) q
        have hxn : 0 ≤ Sx.indicator g_9_8_5 q :=
          Set.indicator_nonneg (fun _ _ => (g_pos_9_8_5 q).le) q
        rw [abs_le]; constructor <;> linarith
      exact hineq
  -- now sum up
  have hstep1 : |(∑' q, Sy.indicator g_9_8_5 q) - (∑' q, Sx.indicator g_9_8_5 q)|
      ≤ ∑' q, ((↑F:Set ℚ)ᶜ).indicator g_9_8_5 q := by
    rw [← Summable.tsum_sub hsumy hsumx]
    calc |∑' q, d q| ≤ ∑' q, |d q| := by
              have := norm_tsum_le_tsum_norm (f := d) hsumd.norm
              simpa [Real.norm_eq_abs] using this
          _ ≤ ∑' q, ((↑F:Set ℚ)ᶜ).indicator g_9_8_5 q := by
              apply Summable.tsum_le_tsum hdbound (hsumd.abs)
              exact g_summable_9_8_5.indicator _
  have hstep2 : (∑' q, ((↑F:Set ℚ)ᶜ).indicator g_9_8_5 q) < ε/2 := by
    rw [← tsum_subtype]; exact hFtail
  linarith

end Chapter9
