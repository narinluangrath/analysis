import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

/-!
# Analysis I, Section 8.3: Uncountable sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Uncountable sets.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

-/

namespace Chapter8

/-- Theorem 8.3.1 -/
theorem EqualCard.power_set_false (X:Type) : ¬ EqualCard X (Set X) := by
  -- This proof is written to follow the structure of the original text.
  by_contra!; choose f hf using this
  set A := {x | x ∉ f x }; choose x hx using hf.2 A
  by_cases h : x ∈ A <;> have h' := h
  . simp [A] at h'; simp_all
  rw [←hx] at h'
  have : x ∈ A := by simp [A, h']
  contradiction

theorem Uncountable.iff (X:Type) : Uncountable X ↔ ¬ AtMostCountable X := by
  rw [AtMostCountable.iff, uncountable_iff_not_countable]


theorem Uncountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Uncountable X ↔ Uncountable Y := by
    simp [Uncountable.iff, AtMostCountable.equiv hXY]

/-- Corollary 8.3.3 -/
theorem Uncountable.power_set_nat : Uncountable (Set ℕ) := by
  -- This proof is written to follow the structure of the original text.
  rw [Uncountable.iff]
  unfold AtMostCountable
  have : ¬ CountablyInfinite (Set ℕ) := by
    have := EqualCard.power_set_false ℕ
    contrapose! this; exact this.symm
  have : ¬ Finite (Set ℕ) := by
    by_contra!
    have : Finite ((fun x:ℕ ↦ ({x}:Set ℕ)) '' .univ) := Finite.Set.subset (s := .univ) (by aesop)
    replace : Finite ℕ := by
      apply Finite.of_finite_univ
      rw [←Set.finite_coe_iff]
      apply Finite.Set.finite_of_finite_image (f := fun x ↦ ({x}:Set ℕ))
      intro _ _ _ _ _; aesop
    have hinf : ¬ Finite ℕ := by rw [not_finite_iff_infinite]; infer_instance
    contradiction
  tauto

open Real in
/-- Corollary 8.3.4 -/
theorem Uncountable.real : Uncountable ℝ := by
  -- This proof is written to follow the structure of the original text.
  set a : ℕ → ℝ := fun n ↦ (10:ℝ)^(-(n:ℝ))
  set f : Set ℕ → ℝ := fun A ↦ ∑' n:A, a n
  have hsummable (A: Set ℕ) : Summable (fun n:A ↦ a n) := by
    apply Summable.subtype (f := a)
    convert summable_geometric_of_lt_one (?_:0 ≤ (1/10:ℝ)) ?_ using 2 with n <;> try norm_num
    unfold a
    rw [one_div_pow, rpow_neg, one_div]; simp; norm_num
  have h_decomp {A B C: Set ℕ} (hC : C = A ∪ B) (hAB: ∀ n, n ∉ A ∩ B) :  ∑' n:C, a n = ∑' n:A, a n + ∑' n:B, a n := by
    convert Summable.tsum_union_disjoint ?_ ?_ ?_ <;> first | infer_instance | try apply hsummable
    . rw [hC]
    rw [Set.disjoint_iff_inter_eq_empty]; grind
  have h_nonneg (A:Set ℕ) : ∑' n:A, a n ≥ 0 := by simp [a]; positivity
  have h_congr {A B: Set ℕ} (hAB: A = B) : ∑' n:A, a n = ∑' n:B, a n  := by rw [hAB]
  have : Function.Injective f := by
    intro A B hAB; by_contra!
    rw [←Set.symmDiff_nonempty] at this
    apply Nat.min_spec at this
    set n₀ := Nat.min (symmDiff A B)
    simp [symmDiff] at this; choose h1 h2 using this
    wlog h : n₀ ∈ A ∧ n₀ ∉ B generalizing A B
    . simp [h] at h1
      apply this hAB.symm <;> simp [symmDiff_comm] <;> grind
    replace h2 {n:ℕ} (hn: n < n₀) : n ∈ A ↔ n ∈ B := by grind
    have : (0:ℝ) > 0 := calc
      _ = f A - f B := by linarith
      _ = ∑' n:A, a n - ∑' n:B, a n := rfl
      _ = (∑' n:{n ∈ A|n ≤ n₀}, a n + ∑' n:{n ∈ A|n > n₀}, a n) -
          (∑' n:{n ∈ B|n ≤ n₀}, a n + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp; grind
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + ∑' n:{n ∈ A|n = n₀}, a n) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + ∑' n:{n ∈ B|n = n₀}, a n) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp [le_iff_lt_or_eq]
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + a n₀) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + 0) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr 3
        . calc
            _ = ∑' n:({n₀}:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
        . calc
            _ = ∑' n:(∅:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
      _ = (∑' n:{n ∈ A|n < n₀}, a n - ∑' n:{n ∈ B|n < n₀}, a n) + a n₀ +
          ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by abel
      _ = 0 + a n₀ + ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by
        congr; rw [sub_eq_zero]; apply tsum_congr_set_coe; grind
      _ ≥ 0 + a n₀ + 0 - ∑' n:{n|n > n₀}, a n := by
        gcongr; positivity
        calc
          _ = ∑' (n : {n ∈ B|n > n₀}), a n + ∑' (n : {n ∉ B|n > n₀}), a n := by
            apply h_decomp
            . ext n; simp; tauto
            intro n hn; simp at hn; tauto
          _ ≥ ∑' (n : {n ∈ B|n > n₀}), a n + 0 := by gcongr; solve_by_elim
          _ = _ := by simp
      _ = 0 + (10:ℝ)^(-(n₀:ℝ)) + 0 - (1 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by
        congr
        set ι : ℕ → {n | n > n₀} := fun j ↦ ⟨ j+(n₀+1), by simp; linarith ⟩
        have hι : Function.Bijective ι := by
          split_ands
          . intro j k hjk; simpa [ι] using hjk
          intro ⟨ n, hn ⟩; simp [ι] at hn ⊢; use n - n₀ - 1; omega
        rw [←(Equiv.ofBijective ι hι).tsum_eq]
        simp [ι, a]
        calc
          _ = ∑' j:ℕ, (10:ℝ)^(-1-n₀:ℝ) * (1/(10:ℝ))^j := by
            apply tsum_congr; intro j
            simp only [Equiv.ofBijective, DFunLike.coe, EquivLike.coe]
            rw [pow_add, pow_add, rpow_sub, rpow_neg, rpow_one, rpow_natCast] <;> try positivity
            simp; congr
          _ = (10:ℝ)^(-1-n₀:ℝ) * ∑' j:ℕ, (1/(10:ℝ))^j := tsum_mul_left
          _ = _ := by
            rw [tsum_geometric_of_lt_one, (?_:-1 - (n₀:ℝ) = (-n₀:ℝ) + (-1:ℝ)),
                rpow_add, rpow_neg, rpow_natCast] <;> try positivity
            ring; abel; norm_num
      _ = (8 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by ring
      _ > 0 := by positivity
    simp at this
  replace : EqualCard (Set ℕ) (Set.range f) := ⟨(Equiv.ofInjective _ this).toFun, (Equiv.ofInjective _ this).bijective⟩
  replace := (equiv this).mp power_set_nat
  contrapose this
  rw [not_uncountable_iff] at this ⊢
  apply SetCoe.countable

/-- Exercise 8.3.1 -/
example {X:Type} [Finite X] : Nat.card (Set X) = 2 ^ Nat.card X := by
  cases nonempty_fintype X
  simp [Nat.card_eq_fintype_card, Fintype.card_set]

open Classical in
/-- Exercise 8.3.2.  Some subtle type changes due to how sets are implemented in Mathlib. Also we shift the sequence {lit}`D` by one so that we can work in {lean}`Set A` rather than {lean}`Set B`. -/
theorem Schroder_Bernstein_lemma {X: Type} {A B C: Set X} (hAB: A ⊆ B) (hBC: B ⊆ C) (f: C ↪ A) :
  let D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A}) (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
  Set.univ.PairwiseDisjoint D ∧
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  Function.Bijective g
  := by
  intro D
  set iAB := A.embeddingOfSubset B hAB with hiAB
  set iBC := B.embeddingOfSubset C hBC with hiBC
  set E : Set B := {x:B | ↑x ∉ A} with hE
  set φ : A → A := fun a => f (iBC (iAB a)) with hφ
  set U : Set A := ⋃ n, D n with hU
  have hiABval : ∀ a:A, ((iAB a):X) = (a:X) := fun a => rfl
  have hD0 : D 0 = f '' (iBC '' E) := rfl
  have hDS : ∀ n, D (n+1) = φ '' (D n) := by
    intro n; show f '' (iBC '' (iAB '' D n)) = φ '' D n
    simp only [hφ, Set.image_image]
  have hφinj : Function.Injective φ := fun a b h => iAB.injective (iBC.injective (f.injective h))
  have hsub : ∀ n, D n ⊆ U := fun n => by rw [hU]; exact Set.subset_iUnion D n
  have hiABmem : ∀ (S:Set A) (x:B), x ∈ iAB '' S → (x:X) ∈ A := by
    intro S x ⟨a, _, ha⟩
    rw [← ha]; show (iAB a : X) ∈ A
    rw [hiABval]; exact a.property
  have hDrange : ∀ n, ∀ x ∈ D n, ∃ y:B, f (iBC y) = x := by
    intro n
    cases n with
    | zero => rw [hD0]; rintro x ⟨c, ⟨b, _, hbc⟩, hcx⟩; exact ⟨b, by rw [hbc, hcx]⟩
    | succ m => rw [hDS]; rintro x ⟨a, _, hax⟩; exact ⟨iAB a, by simpa [hφ] using hax⟩
  have hUrange : ∀ x ∈ U, ∃ y:B, f (iBC y) = x := by
    rw [hU]; intro x hx; rw [Set.mem_iUnion] at hx; obtain ⟨n, hn⟩ := hx; exact hDrange n x hn
  have hD0E : ∀ y:B, f (iBC y) ∈ D 0 → y ∈ E := by
    intro y hy; rw [hD0] at hy
    obtain ⟨c, ⟨b, hbE, hbc⟩, hcx⟩ := hy
    have : iBC b = iBC y := by rw [hbc]; exact f.injective hcx
    rw [iBC.injective this] at hbE; exact hbE
  have hDSiff : ∀ m, ∀ y:B, f (iBC y) ∈ D (m+1) → ∃ a ∈ D m, y = iAB a := by
    intro m y hy; rw [hDS] at hy
    obtain ⟨a, haDm, hax⟩ := hy
    refine ⟨a, haDm, ?_⟩
    have : iBC y = iBC (iAB a) := f.injective (by simpa [hφ] using hax.symm)
    exact iBC.injective this
  refine ⟨?_, ?_⟩
  · -- PairwiseDisjoint
    have hD0disj : ∀ S:Set A, Disjoint (D 0) (φ '' S) := by
      intro S
      rw [hD0, Set.disjoint_left]
      rintro y ⟨c, ⟨b, hbE, hbc⟩, hcy⟩ ⟨a, haS, hay⟩
      simp only [hφ] at hay
      rw [← hcy] at hay
      have hc : c = iBC (iAB a) := f.injective hay.symm
      rw [← hbc] at hc
      have hb : b = iAB a := iBC.injective hc
      have : (b:X) ∈ A := by rw [hb]; exact hiABmem Set.univ (iAB a) ⟨a, trivial, rfl⟩
      exact hbE this
    have hmain : ∀ m k, Disjoint (D m) (D (m+1+k)) := by
      intro m
      induction m with
      | zero =>
        intro k
        rw [show 0+1+k = k+1 by ring, hDS]
        exact hD0disj _
      | succ n ih =>
        intro k
        rw [show (n+1)+1+k = (n+1+k)+1 by ring, hDS n, hDS (n+1+k)]
        exact (Set.disjoint_image_iff hφinj).2 (ih k)
    intro m _ n _ hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · obtain ⟨k, hk⟩ : ∃ k, n = m+1+k := ⟨n-m-1, by omega⟩
      rw [hk]; exact hmain m k
    · obtain ⟨k, hk⟩ : ∃ k, m = n+1+k := ⟨m-n-1, by omega⟩
      rw [hk]; exact (hmain n k).symm
  · -- Bijective g
    intro g
    have hgpos : ∀ x:A, (hx : x ∈ U ∧ ∃ y:B, f (iBC y) = x) → f (iBC (g x)) = x := by
      intro x hx
      have hc : x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x := hx
      show f (iBC (dite _ _ _)) = x
      rw [dif_pos hc]
      exact hc.2.choose_spec
    have hgneg : ∀ x:A, ¬(x ∈ U ∧ ∃ y:B, f (iBC y) = x) → (g x : X) = (x:X) := by
      intro x hx
      have hc : ¬(x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x) := hx
      show ((dite _ _ _ : B) : X) = x
      rw [dif_neg hc]
    constructor
    · intro x1 x2 hgx
      by_cases h1 : x1 ∈ U ∧ ∃ y:B, f (iBC y) = x1 <;> by_cases h2 : x2 ∈ U ∧ ∃ y:B, f (iBC y) = x2
      · have e1 := hgpos x1 h1
        have e2 := hgpos x2 h2
        rw [hgx] at e1; rw [e1] at e2; exact e2
      · exfalso
        have e1 := hgpos x1 h1
        have e2 := hgneg x2 h2
        rw [hgx] at e1
        set y := g x2 with hy
        obtain ⟨x1U, _⟩ := h1
        rw [hU, Set.mem_iUnion] at x1U; obtain ⟨n, hn⟩ := x1U
        cases n with
        | zero =>
          have := hD0E y (by rw [e1]; exact hn)
          exact this (by rw [e2]; exact x2.property)
        | succ m =>
          obtain ⟨a, haDm, hya⟩ := hDSiff m y (by rw [e1]; exact hn)
          have hax2 : a = x2 := by apply Subtype.ext; rw [← e2, hya, hiABval]
          apply h2
          exact ⟨hsub m (hax2 ▸ haDm), hDrange m x2 (hax2 ▸ haDm)⟩
      · exfalso
        have e2 := hgpos x2 h2
        have e1 := hgneg x1 h1
        rw [← hgx] at e2
        set y := g x1 with hy
        obtain ⟨x2U, _⟩ := h2
        rw [hU, Set.mem_iUnion] at x2U; obtain ⟨n, hn⟩ := x2U
        cases n with
        | zero =>
          have := hD0E y (by rw [e2]; exact hn)
          exact this (by rw [e1]; exact x1.property)
        | succ m =>
          obtain ⟨a, haDm, hya⟩ := hDSiff m y (by rw [e2]; exact hn)
          have hax1 : a = x1 := by apply Subtype.ext; rw [← e1, hya, hiABval]
          apply h1
          exact ⟨hsub m (hax1 ▸ haDm), hDrange m x1 (hax1 ▸ haDm)⟩
      · have e1 := hgneg x1 h1
        have e2 := hgneg x2 h2
        apply Subtype.ext
        rw [← e1, ← e2, hgx]
    · intro b
      by_cases hx0 : f (iBC b) ∈ U
      · refine ⟨f (iBC b), ?_⟩
        have hP : f (iBC b) ∈ U ∧ ∃ y:B, f (iBC y) = f (iBC b) := ⟨hx0, b, rfl⟩
        have := hgpos (f (iBC b)) hP
        exact iBC.injective (f.injective this)
      · by_cases hbA : (b:X) ∈ A
        · set a : A := ⟨(b:X), hbA⟩ with ha
          refine ⟨a, ?_⟩
          have hnP : ¬(a ∈ U ∧ ∃ y:B, f (iBC y) = a) := by
            rintro ⟨haU, _⟩
            rw [hU, Set.mem_iUnion] at haU; obtain ⟨n, hn⟩ := haU
            apply hx0
            have hiABab : iAB a = b := by apply Subtype.ext; rw [hiABval]
            have hmem : f (iBC (iAB a)) ∈ D (n+1) := by rw [hDS]; exact ⟨a, hn, rfl⟩
            rw [hiABab] at hmem
            exact hsub (n+1) hmem
          have := hgneg a hnP
          apply Subtype.ext
          rw [this]
        · exfalso; apply hx0
          have : f (iBC b) ∈ D 0 := by rw [hD0]; exact ⟨iBC b, ⟨b, hbA, rfl⟩, rfl⟩
          exact hsub 0 this

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

/-- Exercise 8.3.3 -/
theorem Schroder_Bernstein {X Y:Type} (hXY : LeCard X Y) (hYX : LeCard Y X) : EqualCard X Y := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYX
  exact Function.Embedding.schroeder_bernstein hf hg

abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

/-- Exercise 8.3.4 -/
example {X:Type} : LtCard X (Set X) := by
  constructor
  · exact ⟨fun x => {x}, fun a b h => by simpa using h⟩
  · exact EqualCard.power_set_false X

example {A B C: Type} (hAB: LtCard A B) (hBC: LtCard B C) :
  LtCard A C := by
  obtain ⟨⟨f, hf⟩, hAB'⟩ := hAB
  obtain ⟨⟨g, hg⟩, hBC'⟩ := hBC
  refine ⟨⟨g ∘ f, hg.comp hf⟩, ?_⟩
  intro hAC
  apply hBC'
  obtain ⟨e, he⟩ := hAC
  have einv := (Equiv.ofBijective e he).symm
  exact Schroder_Bernstein ⟨g, hg⟩ ⟨f ∘ einv, hf.comp einv.injective⟩

abbrev CardOrder : Preorder Type := {
  le := LeCard
  lt := LtCard
  le_refl := by
    intro X
    exact ⟨id, Function.injective_id⟩
  le_trans := by
    intro X Y Z ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨g ∘ f, hg.comp hf⟩
  lt_iff_le_not_ge := by
    intro X Y
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨hle, ?_⟩
      intro hge
      exact hne (Schroder_Bernstein hle hge)
    · rintro ⟨hle, hnge⟩
      refine ⟨hle, ?_⟩
      intro heq
      obtain ⟨e, he⟩ := heq
      exact hnge ⟨(Equiv.ofBijective e he).symm, (Equiv.ofBijective e he).symm.injective⟩
}

/-- Exercise 8.3.5 -/
example (X:Type) : ¬ CountablyInfinite (Set X) := by
  intro h
  haveI hcount : Countable (Set X) := h.toCountable
  have hinj : Function.Injective (fun x:X => ({x}:Set X)) := fun a b hab => by simpa using hab
  haveI hX_count : Countable X := hinj.countable
  by_cases hfin : Finite X
  · haveI := hfin
    haveI := h.toInfinite
    exact not_finite (Set X)
  · haveI : Infinite X := not_finite_iff_infinite.mp hfin
    have hXci : CountablyInfinite X := (CountablyInfinite.iff' X).mpr ⟨hX_count, ‹Infinite X›⟩
    exact EqualCard.power_set_false X (hXci.trans h.symm)

end Chapter8
