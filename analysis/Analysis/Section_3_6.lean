import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  set Y := nat.specify (fun x ↦ Even (x:ℕ)) with hY
  have memf : ∀ n : nat, ((2*(n:ℕ):ℕ):Object) ∈ Y := by
    intro n
    rw [hY, specification_axiom'']
    refine ⟨((2*(n:ℕ):ℕ):nat).property, ?_⟩
    rw [SetTheory.Object.ofnat_eq''']; exact even_two_mul _
  refine ⟨fun n => ⟨((2*(n:ℕ):ℕ):Object), memf n⟩, ?_, ?_⟩
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    rw [SetTheory.Object.natCast_inj] at hab
    exact nat_equiv.symm.injective (by omega : (a:ℕ) = (b:ℕ))
  · rintro ⟨y, hy⟩
    rw [hY, specification_axiom''] at hy
    obtain ⟨hyn, k, hk⟩ := hy
    refine ⟨((k:ℕ):nat), ?_⟩
    apply Subtype.ext
    show ((2*((((k:ℕ):nat):ℕ)):ℕ):Object) = y
    rw [nat_equiv_coe_of_coe]
    have : ((⟨y,hyn⟩:nat):ℕ) = 2*k := by omega
    have hy2 : y = (((⟨y,hyn⟩:nat):ℕ):Object) := by
      simp [SetTheory.Object.ofnat_eq''']
    rw [hy2, this]

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  exact ⟨id, Function.bijective_id⟩

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := h
  exact ⟨(Equiv.ofBijective f hf).symm, (Equiv.ofBijective f hf).symm.bijective⟩

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card_iff]
  have key : ∀ s : (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)),
      ∃ h : s.val ∈ nat, 1 ≤ ((⟨s.val,h⟩:nat):ℕ) ∧ ((⟨s.val,h⟩:nat):ℕ) ≤ n := by
    intro s
    exact (specification_axiom'' _ s.val).mp s.property
  refine ⟨fun s => Fin_mk n (((⟨s.val, (key s).choose⟩:nat):ℕ) - 1) (by
    obtain ⟨h1, h2⟩ := (key s).choose_spec; omega), ?_, ?_⟩
  · intro a b hab
    rw [Fin.coe_inj, Fin.toNat_mk, Fin.toNat_mk] at hab
    obtain ⟨ha1, _⟩ := (key a).choose_spec
    obtain ⟨hb1, _⟩ := (key b).choose_spec
    apply Subtype.ext
    have hh : ((⟨a.val, (key a).choose⟩:nat):ℕ) = ((⟨b.val, (key b).choose⟩:nat):ℕ) := by omega
    have e := nat_equiv.symm.injective hh
    have : (⟨a.val, (key a).choose⟩:nat).val = (⟨b.val, (key b).choose⟩:nat).val := congrArg Subtype.val e
    exact this
  · intro i
    have hilt := Fin.toNat_lt i
    refine ⟨⟨(((i:ℕ)+1:ℕ):Object), ?_⟩, ?_⟩
    · rw [specification_axiom'']
      refine ⟨(((i:ℕ)+1:ℕ):nat).property, ?_, ?_⟩
      · rw [SetTheory.Object.ofnat_eq''']; omega
      · rw [SetTheory.Object.ofnat_eq''']; omega
    · rw [Fin.coe_inj]
      dsimp only
      rw [Fin.toNat_mk]
      rw [show ((⟨(((i:ℕ)+1:ℕ):Object), (((i:ℕ)+1:ℕ):nat).property⟩:nat):ℕ) = (i:ℕ)+1 from SetTheory.Object.ofnat_eq''']
      omega

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  obtain ⟨y, hy⟩ := nonempty_def hnon
  obtain ⟨x, hx⟩ := hf.surjective ⟨y, hy⟩
  have hxp := x.property
  rw [eq_empty_iff_forall_notMem] at this
  exact this _ hxp

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  rw [has_card_iff]
  constructor
  · rintro ⟨f, hf⟩
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have := Fin.toNat_lt (f ⟨x, hx⟩)
    omega
  · intro h
    rw [eq_empty_iff_forall_notMem] at h
    refine ⟨fun x => absurd x.property (h _), ?_⟩
    constructor
    · intro a; exact absurd a.property (h _)
    · intro y; have := Fin.toNat_lt y; omega

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by sorry
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  classical
  let g : _root_.Fin n → ℕ := fun j => (f (Fin_mk n j.val j.isLt) : ℕ)
  use Finset.univ.sup g
  intro i
  obtain ⟨hm, hi⟩ := Fin.toNat_spec i
  have : (f i:ℕ) = g ⟨(i:ℕ), hm⟩ := by show _ = (f (Fin_mk n (i:ℕ) hm):ℕ); rw [← hi]
  rw [this]
  exact Finset.le_sup (f := g) (Finset.mem_univ _)

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor
  · intro h
    have hc : X.has_card 0 := has_card_zero.mpr h
    exact ⟨⟨0, hc⟩, has_card_to_card hc⟩
  · rintro ⟨hfin, hcard⟩
    have := has_card_card hfin
    rw [hcard] at this
    exact has_card_zero.mp this

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  obtain ⟨f, hf⟩ := (has_card_iff _ _).mp (has_card_card hX)
  classical
  have embN : ∀ {n N:ℕ} (h:n≤N) (i:SetTheory.Set.Fin n), ((Fin_embed n N h i :ℕ)) = (i:ℕ) := by
    intro n N h i
    have : ((Fin_embed n N h i:ℕ):Object) = ((i:ℕ):Object) := by
      rw [Fin.coe_toNat, Fin.coe_toNat]
    rwa [SetTheory.Object.natCast_inj] at this
  have hcardnew : (X ∪ {x}).has_card (X.card+1) := by
    rw [has_card_iff]
    refine ⟨fun y =>
      if hy : y.val ∈ X then Fin_embed X.card (X.card+1) (by omega) (f ⟨y.val, hy⟩)
      else Fin_mk (X.card+1) X.card (by omega), ?_, ?_⟩
    · rintro a b hab
      simp only at hab
      by_cases ha : a.val ∈ X <;> by_cases hb : b.val ∈ X
      · rw [dif_pos ha, dif_pos hb] at hab
        have hv : (f ⟨a.val,ha⟩:ℕ) = (f ⟨b.val,hb⟩:ℕ) := by
          rw [← embN (show X.card ≤ X.card+1 by omega), ← embN (show X.card ≤ X.card+1 by omega), hab]
        have heq := hf.1 (Fin.coe_inj.mpr hv)
        apply Subtype.ext
        have := congrArg Subtype.val heq
        simpa using this
      · rw [dif_pos ha, dif_neg hb] at hab
        have h1 := embN (show X.card ≤ X.card+1 by omega) (f ⟨a.val,ha⟩)
        have h2 := Fin.coe_inj.mp hab
        simp only [Fin.toNat_mk] at h2
        have h3 := Fin.toNat_lt (f ⟨a.val,ha⟩); omega
      · rw [dif_neg ha, dif_pos hb] at hab
        have h1 := embN (show X.card ≤ X.card+1 by omega) (f ⟨b.val,hb⟩)
        have h2 := Fin.coe_inj.mp hab.symm
        simp only [Fin.toNat_mk] at h2
        have h3 := Fin.toNat_lt (f ⟨b.val,hb⟩); omega
      · have hax : a.val = x := by rcases (mem_union _ _ _).mp a.property with h|h; exact absurd h ha; rwa [mem_singleton] at h
        have hbx : b.val = x := by rcases (mem_union _ _ _).mp b.property with h|h; exact absurd h hb; rwa [mem_singleton] at h
        exact Subtype.ext (hax.trans hbx.symm)
    · intro i
      by_cases hi : (i:ℕ) = X.card
      · refine ⟨⟨x, by rw [mem_union]; right; rw [mem_singleton]⟩, ?_⟩
        simp only [hx, dif_neg, not_false_iff]
        rw [Fin.coe_inj, Fin.toNat_mk, hi]
      · have hilt : (i:ℕ) < X.card := by have := Fin.toNat_lt i; omega
        obtain ⟨j, hj⟩ := hf.surjective (Fin_mk X.card (i:ℕ) hilt)
        refine ⟨⟨j.val, by rw [mem_union]; left; exact j.property⟩, ?_⟩
        dsimp only
        rw [dif_pos j.property]
        have hjeq : (⟨j.val, j.property⟩ : X) = j := rfl
        rw [hjeq, Fin.coe_inj, embN, hj, Fin.toNat_mk]
  exact ⟨⟨X.card+1, hcardnew⟩, has_card_to_card hcardnew⟩

/-- Induction principle for finite sets: prove a predicate for `∅` and closed under inserting a
fresh element. -/
theorem SetTheory.Set.finite_induction (P : Set → Prop) (hempty : P ∅)
    (hinsert : ∀ (X:Set) (x:Object), X.finite → x ∉ X → P X → P (X ∪ {x})) :
    ∀ X:Set, X.finite → P X := by
  intro X hX
  obtain ⟨n, hn⟩ := hX
  induction n generalizing X with
  | zero => rw [has_card_zero] at hn; rw [hn]; exact hempty
  | succ k ih =>
    have hne : X ≠ ∅ := pos_card_nonempty (by omega) hn
    obtain ⟨x, hx⟩ := nonempty_def hne
    have herase := card_erase (by omega) hn ⟨x, hx⟩
    simp only [Nat.add_sub_cancel] at herase
    have hxnot : x ∉ (X \ {x}) := by rw [mem_sdiff]; rintro ⟨_, h2⟩; rw [mem_singleton] at h2; exact h2 rfl
    have hPins := hinsert (X \ {x}) x ⟨k, herase⟩ hxnot (ih _ herase)
    have heq : (X \ {x}) ∪ {x} = X := by
      apply ext; intro y
      rw [mem_union, mem_sdiff, mem_singleton]
      constructor
      · rintro (⟨h,_⟩|h); exact h; rw [h]; exact hx
      · intro h; by_cases hy : y = x; right; exact hy; left; exact ⟨h, hy⟩
    rwa [heq] at hPins

theorem SetTheory.Set.union_finite' {X Y:Set} (hX: X.finite) (hY: Y.finite) : (X ∪ Y).finite := by
  classical
  refine finite_induction (fun Y => (X ∪ Y).finite) ?_ ?_ Y hY
  · show (X ∪ ∅).finite
    rw [union_empty]; exact hX
  · intro Y' y hY' hy ih
    by_cases hyXY : y ∈ X ∪ Y'
    · have : X ∪ (Y' ∪ {y}) = X ∪ Y' := by
        apply ext; intro z; rw [mem_union, mem_union, mem_union, mem_singleton]
        constructor
        · rintro (h|h|h); exact Or.inl h; exact Or.inr h
          subst h; rcases (mem_union _ _ _).mp hyXY with hh|hh; exact Or.inl hh; exact Or.inr hh
        · rintro (h|h); exact Or.inl h; exact Or.inr (Or.inl h)
      rw [this]; exact ih
    · have key : X ∪ (Y' ∪ {y}) = (X ∪ Y') ∪ {y} := by rw [← union_assoc]
      rw [key]; exact (card_insert ih hyXY).1

theorem SetTheory.Set.subset_finite {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) : Y.finite := by
  classical
  have main : ∀ X:Set, X.finite → ∀ Y:Set, Y ⊆ X → Y.finite := by
    intro X hX
    refine finite_induction (fun X => ∀ Y:Set, Y ⊆ X → Y.finite) ?_ ?_ X hX
    · intro Y hY
      have : Y = ∅ := by rw [eq_empty_iff_forall_notMem]; intro z hz; exact not_mem_empty z (hY z hz)
      rw [this]; exact empty_finite
    · intro X' x hX' hx ih Y hY
      by_cases hxY : x ∈ Y
      · have hsub : Y \ {x} ⊆ X' := by
          intro z hz; rw [mem_sdiff, mem_singleton] at hz
          rcases (mem_union _ _ _).mp (hY z hz.1) with h|h
          exact h; rw [mem_singleton] at h; exact absurd h hz.2
        obtain ⟨m, hm⟩ := ih _ hsub
        have hxnot : x ∉ Y \ {x} := by rw [mem_sdiff, mem_singleton]; tauto
        have hfin := (card_insert ⟨m, hm⟩ hxnot).1
        have heq : (Y \ {x}) ∪ {x} = Y := by
          apply ext; intro z; rw [mem_union, mem_sdiff, mem_singleton]
          constructor
          · rintro (⟨h,_⟩|h); exact h; rw [h]; exact hxY
          · intro h; by_cases hz : z = x; right; exact hz; left; exact ⟨h, hz⟩
        rwa [heq] at hfin
      · apply ih
        intro z hz
        rcases (mem_union _ _ _).mp (hY z hz) with h|h
        exact h; rw [mem_singleton] at h; subst h; exact absurd hz hxY
  exact main X hX Y hY

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  classical
  revert hdisj
  refine finite_induction (fun Y => Disjoint X Y → (X ∪ Y).card = X.card + Y.card) ?_ ?_ Y hY
  · intro _; show (X ∪ ∅).card = _; rw [union_empty]; simp
  · intro Y' y hY' hy ih hdisj
    have hdY' : Disjoint X Y' := by
      rw [disjoint_iff, eq_empty_iff_forall_notMem] at hdisj ⊢
      intro z hz; rw [mem_inter] at hz; exact hdisj z ((mem_inter _ _ _).mpr ⟨hz.1, (mem_union _ _ _).mpr (Or.inl hz.2)⟩)
    have hyX : y ∉ X := by
      rw [disjoint_iff, eq_empty_iff_forall_notMem] at hdisj
      intro h; exact hdisj y ((mem_inter _ _ _).mpr ⟨h, (mem_union _ _ _).mpr (Or.inr (by rw [mem_singleton]))⟩)
    have hynot : y ∉ X ∪ Y' := by
      rw [mem_union]; rintro (h|h); exact hyX h; exact hy h
    have key : X ∪ (Y' ∪ {y}) = (X ∪ Y') ∪ {y} := by rw [← union_assoc]
    show (X ∪ (Y' ∪ {y})).card = _
    rw [key, (card_insert (union_finite' hX hY') hynot).2, ih hdY', (card_insert hY' hy).2]; ring

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  classical
  have hYfin : Y.finite := subset_finite hX hY
  refine ⟨hYfin, ?_⟩
  have hdfin : (X \ Y).finite := subset_finite hX (by intro z hz; rw [mem_sdiff] at hz; exact hz.1)
  have hdisj : Disjoint Y (X \ Y) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro z hz; rw [mem_inter, mem_sdiff] at hz; exact hz.2.2 hz.1
  have heq : Y ∪ (X \ Y) = X := by
    apply ext; intro z; rw [mem_union, mem_sdiff]
    constructor
    · rintro (h|⟨h,_⟩); exact hY z h; exact h
    · intro h; by_cases hz : z ∈ Y; exact Or.inl hz; exact Or.inr ⟨h, hz⟩
  have := card_union_disjoint hYfin hdfin hdisj
  rw [heq] at this
  omega

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  classical
  refine ⟨union_finite' hX hY, ?_⟩
  have hdfin : (Y \ X).finite := subset_finite hY (by intro z hz; rw [mem_sdiff] at hz; exact hz.1)
  have hdisj : Disjoint X (Y \ X) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro z hz; rw [mem_inter, mem_sdiff] at hz; exact hz.2.2 hz.1
  have heq : X ∪ (Y \ X) = X ∪ Y := by
    apply ext; intro z; rw [mem_union, mem_union, mem_sdiff]
    constructor
    · rintro (h|⟨h,_⟩); exact Or.inl h; exact Or.inr h
    · rintro (h|h); exact Or.inl h; by_cases hz : z ∈ X; exact Or.inl hz; exact Or.inr ⟨h, hz⟩
  have hdle : (Y \ X).card ≤ Y.card :=
    (card_subset hY (by intro z hz; rw [mem_sdiff] at hz; exact hz.1)).2
  have := card_union_disjoint hX hdfin hdisj
  rw [heq] at this
  omega

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  classical
  rw [ssubset_def] at hY
  obtain ⟨hsub, hne⟩ := hY
  have hex : ∃ x, x ∈ X ∧ x ∉ Y := by
    by_contra hc
    push_neg at hc
    apply hne
    apply subset_antisymm _ _ hsub
    intro z hz; exact hc z hz
  obtain ⟨x, hxX, hxY⟩ := hex
  have hYfin := (card_subset hX hsub).1
  have hins : (Y ∪ {x}).card = Y.card + 1 := (card_insert hYfin hxY).2
  have hsub2 : (Y ∪ {x}) ⊆ X := by
    intro z hz; rcases (mem_union _ _ _).mp hz with h|h
    exact hsub z h; rw [mem_singleton] at h; rw [h]; exact hxX
  have := (card_subset hX hsub2).2
  omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  classical
  set I := image f X with hI
  have hmem : ∀ x:X, (f x).val ∈ I := fun x => (mem_image f X _).mpr ⟨x, x.property, rfl⟩
  set g : X → I := fun x => ⟨(f x).val, hmem x⟩ with hg
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [hI, mem_image] at hy
    obtain ⟨x, _, hfx⟩ := hy
    exact ⟨x, by simp only [hg]; exact Subtype.ext hfx⟩
  set s : I → X := fun y => (hgsurj y).choose with hs
  have hsg : ∀ y, g (s y) = y := fun y => (hgsurj y).choose_spec
  have hsinj : Function.Injective s := by
    intro a b hab
    have : g (s a) = g (s b) := by rw [hab]
    rw [hsg, hsg] at this; exact this
  have hequiv : EqualCard I (image s I) := by
    refine ⟨fun y => ⟨(s y).val, (mem_image s I _).mpr ⟨y, y.property, rfl⟩⟩, ?_, ?_⟩
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact hsinj (Subtype.ext hab)
    · rintro ⟨z, hz⟩
      rw [mem_image] at hz
      obtain ⟨y, _, hsy⟩ := hz
      exact ⟨y, Subtype.ext hsy⟩
  have hsub : image s I ⊆ X := by
    intro z hz; rw [mem_image] at hz; obtain ⟨y, _, hsy⟩ := hz
    rw [← hsy]; exact (s y).property
  have hsubfin := card_subset hX hsub
  have hIfin : I.finite := by
    obtain ⟨n, hn⟩ := hsubfin.1
    exact ⟨n, (EquivCard_to_has_card_eq hequiv).mpr hn⟩
  refine ⟨hIfin, ?_⟩
  rw [EquivCard_to_card_eq hequiv]
  exact hsubfin.2

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  have hequiv : EqualCard X (image f X) := by
    refine ⟨fun x => ⟨(f x).val, (mem_image f X _).mpr ⟨x, x.property, rfl⟩⟩, ?_, ?_⟩
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact hf (Subtype.ext hab)
    · rintro ⟨y, hy⟩
      rw [mem_image] at hy
      obtain ⟨x, hxX, hfx⟩ := hy
      exact ⟨x, Subtype.ext hfx⟩
  have : X ≈ image f X := hequiv
  exact (EquivCard_to_card_eq this).symm

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  classical
  set n := X.card with hn
  set m := Y.card with hm
  obtain ⟨fX, hfX⟩ := (has_card_iff _ _).mp (has_card_card hX)
  obtain ⟨fY, hfY⟩ := (has_card_iff _ _).mp (has_card_card hY)
  have divlem : ∀ (a r : ℕ), r < m → (a*m + r)/m = a := by
    intro a r hr
    have h : a*m + r = r + a*m := by ring
    rw [h, Nat.add_mul_div_right _ _ (by omega : 0 < m), Nat.div_eq_of_lt hr, Nat.zero_add]
  have modlem : ∀ (a r : ℕ), r < m → (a*m + r)%m = r := by
    intro a r hr
    have h : a*m + r = r + a*m := by ring
    rw [h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hcard : (X ×ˢ Y).has_card (n*m) := by
    rw [has_card_iff]
    refine ⟨fun z => Fin_mk (n*m) ((fX (fst z):ℕ)*m + (fY (snd z):ℕ)) (by
      have h1 := Fin.toNat_lt (fX (fst z))
      have h2 := Fin.toNat_lt (fY (snd z))
      calc (fX (fst z):ℕ)*m + (fY (snd z):ℕ) < (fX (fst z):ℕ)*m + m := by omega
        _ = ((fX (fst z):ℕ)+1)*m := by ring
        _ ≤ n*m := by apply Nat.mul_le_mul_right; omega), ?_, ?_⟩
    · intro a b hab
      rw [Fin.coe_inj, Fin.toNat_mk, Fin.toNat_mk] at hab
      have hb2 := Fin.toNat_lt (fY (snd a))
      have hb2' := Fin.toNat_lt (fY (snd b))
      have hdA := divlem (fX (fst a):ℕ) (fY (snd a):ℕ) hb2
      have hdB := divlem (fX (fst b):ℕ) (fY (snd b):ℕ) hb2'
      have hmA := modlem (fX (fst a):ℕ) (fY (snd a):ℕ) hb2
      have hmB := modlem (fX (fst b):ℕ) (fY (snd b):ℕ) hb2'
      rw [hab] at hdA hmA
      have hX_eq : (fX (fst a):ℕ) = (fX (fst b):ℕ) := by rw [← hdA, hdB]
      have hY_eq : (fY (snd a):ℕ) = (fY (snd b):ℕ) := by rw [← hmA, hmB]
      have hfst : fst a = fst b := hfX.1 (Fin.coe_inj.mpr hX_eq)
      have hsnd : snd a = snd b := hfY.1 (Fin.coe_inj.mpr hY_eq)
      have hpa := pair_eq_fst_snd a
      rw [hfst, hsnd, ← pair_eq_fst_snd b] at hpa
      exact Subtype.ext hpa
    · intro k
      have hklt := Fin.toNat_lt k
      have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => by simp only [h, Nat.mul_zero, Nat.not_lt_zero] at hklt)
      set q := (k:ℕ) / m with hq_def
      set r := (k:ℕ) % m with hr_def
      have hr : r < m := Nat.mod_lt _ hmpos
      have hq : q < n := by
        have hle : q*m ≤ (k:ℕ) := Nat.div_mul_le_self _ _
        have : q*m < n*m := lt_of_le_of_lt hle hklt
        exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
      obtain ⟨x, hx⟩ := hfX.surjective (Fin_mk n q hq)
      obtain ⟨y, hy⟩ := hfY.surjective (Fin_mk m r hr)
      refine ⟨mk_cartesian x y, ?_⟩
      rw [Fin.coe_inj]
      dsimp only
      rw [Fin.toNat_mk, fst_of_mk_cartesian, snd_of_mk_cartesian, hx, hy, Fin.toNat_mk, Fin.toNat_mk]
      rw [hq_def, hr_def, Nat.mul_comm]
      exact Nat.div_add_mod (k:ℕ) m
  exact ⟨⟨n*m, hcard⟩, has_card_to_card hcard⟩


open Classical in
noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun x := ((powerset_axiom x.val).mp x.property).choose
  invFun f := ⟨(f : Object), by rw [powerset_axiom]; exact ⟨f, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact ((powerset_axiom x.val).mp x.property).choose_spec
  right_inv f := by
    have h := ((powerset_axiom (⟨(f:Object), by rw [powerset_axiom]; exact ⟨f, rfl⟩⟩ : ↑(A^B)).val)).mp (by rw [powerset_axiom]; exact ⟨f, rfl⟩) |>.choose_spec
    exact (coe_of_fun_inj _ _).mp h

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  exact ⟨prod_commutator A B, (prod_commutator A B).bijective⟩

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  have e1 : ↑((A^B)^C) ≃ (C → ↑(A^B)) := pow_fun_equiv
  have e2 : (C → ↑(A^B)) ≃ (C → (B → A)) := Equiv.arrowCongr (Equiv.refl _) pow_fun_equiv
  have e3 : (C → (B → A)) ≃ (C ×ˢ B → A) := curry_equiv
  have e4 : (C ×ˢ B → A) ≃ (B ×ˢ C → A) := Equiv.arrowCongr (prod_commutator C B) (Equiv.refl _)
  have e5 : (B ×ˢ C → A) ≃ ↑(A ^ (B ×ˢ C)) := pow_fun_equiv.symm
  let E := (((e1.trans e2).trans e3).trans e4).trans e5
  exact ⟨E, E.bijective⟩

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  rw [← pow_mul]

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  classical
  rw [disjoint_iff, eq_empty_iff_forall_notMem] at hd
  have uEquiv : ↑(B ∪ C) ≃ (B ⊕ C) := {
    toFun := fun z => if h : z.val ∈ B then Sum.inl ⟨z.val, h⟩
      else Sum.inr ⟨z.val, by rcases (mem_union _ _ _).mp z.property with hb|hc; exact absurd hb h; exact hc⟩
    invFun := fun s => Sum.elim (fun b => ⟨b.val, by rw [mem_union]; left; exact b.property⟩)
      (fun c => ⟨c.val, by rw [mem_union]; right; exact c.property⟩) s
    left_inv := by
      intro z
      by_cases h : z.val ∈ B <;> simp [h]
    right_inv := by
      intro s
      rcases s with b | c
      · simp [b.property]
      · have hc : c.val ∉ B := by
          intro hb; exact hd c.val ((mem_inter _ _ _).mpr ⟨hb, c.property⟩)
        simp [hc]
  }
  let e1 : ↑(A^(B∪C)) ≃ (↑(B∪C) → A) := pow_fun_equiv
  let e2 : (↑(B∪C) → A) ≃ ((B ⊕ C) → A) := Equiv.arrowCongr uEquiv (Equiv.refl _)
  let e3 : ((B ⊕ C) → A) ≃ ((B → A) × (C → A)) := Equiv.sumArrowEquivProdArrow _ _ _
  let e4 : ↑(A^B) ≃ (B → A) := pow_fun_equiv
  let e5 : ↑(A^C) ≃ (C → A) := pow_fun_equiv
  let e6 : ↑((A^B) ×ˢ (A^C)) ≃ (↑(A^B) × ↑(A^C)) := {
    toFun := fun z => (fst z, snd z)
    invFun := fun z => mk_cartesian z.1 z.2
    left_inv := by intro z; simp
    right_inv := by intro z; simp
  }
  let E := e6.trans (Equiv.prodCongr e4 e5) |>.trans (e3.symm.trans (e2.symm.trans e1.symm))
  exact ⟨E, E.bijective⟩

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  classical
  refine finite_induction (fun X => (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card) ?_ ?_ X hX
  · -- X = ∅ : Y^∅ ≃ (∅ → Y), card 1
    have : EqualCard (Y ^ (∅:Set)) ({(0:Object)}:Set) := by
      refine ⟨fun _ => ⟨0, by rw [mem_singleton]⟩, ?_, ?_⟩
      · intro a b _
        rw [pow_fun_eq_iff]
        funext z; exact absurd z.property (not_mem_empty z.val)
      · rintro ⟨w, hw⟩
        exact ⟨pow_fun_equiv.symm (fun z => absurd z.property (not_mem_empty z.val)), by rw [mem_singleton] at hw; apply Subtype.ext; simp [hw]⟩
    have he : (Y ^ (∅:Set)) ≈ ({(0:Object)}:Set) := this
    refine ⟨⟨1, ?_⟩, ?_⟩
    · exact (EquivCard_to_has_card_eq he).mpr (Example_3_6_7a 0)
    · rw [EquivCard_to_card_eq he, empty_card_eq_zero, pow_zero, has_card_to_card (Example_3_6_7a 0)]
  · intro X' x hX' hx ih
    -- Y^(X'∪{x}) ≃ (Y^X') ×ˢ (Y^{x}) via disjoint
    have hdisj : Disjoint X' ({x}:Set) := by
      rw [disjoint_iff, eq_empty_iff_forall_notMem]
      intro z hz; rw [mem_inter, mem_singleton] at hz; rw [hz.2] at *; exact hx hz.1
    have hequiv : EqualCard ((Y^X') ×ˢ (Y^({x}:Set))) (Y^(X' ∪ {x})) :=
      pow_prod_pow_EqualCard_pow_union Y X' {x} hdisj
    have hsingle : (Y^({x}:Set)).card = Y.card ∧ (Y^({x}:Set)).finite := by
      have : EqualCard (Y^({x}:Set)) Y := by
        refine ⟨fun F => pow_fun_equiv F ⟨x, by rw [mem_singleton]⟩, ?_, ?_⟩
        · intro a b hab
          rw [pow_fun_eq_iff]; funext z
          have : z = ⟨x, by rw [mem_singleton]⟩ := by apply Subtype.ext; have := z.property; rw [mem_singleton] at this; exact this
          rw [this]; exact hab
        · intro y
          refine ⟨pow_fun_equiv.symm (fun _ => y), ?_⟩
          simp [pow_fun_equiv.apply_symm_apply]
      exact ⟨EquivCard_to_card_eq this, ⟨Y.card, (EquivCard_to_has_card_eq this).mpr (has_card_card hY)⟩⟩
    have hprodfin := card_prod ih.1 hsingle.2
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := hprodfin.1
      exact ⟨k, (EquivCard_to_has_card_eq hequiv).mp hk⟩
    · rw [← EquivCard_to_card_eq hequiv, hprodfin.2, ih.2, hsingle.1,
        (card_insert hX' hx).2, pow_succ]



theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  rw [← pow_add]

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  · rintro ⟨f, hf⟩
    have hci := card_image_inj hA hf
    have hsub : image f A ⊆ B := image_in_codomain f A
    have := (card_subset hB hsub).2
    omega
  · intro hle
    obtain ⟨fA, hfA⟩ := (has_card_iff _ _).mp (has_card_card hA)
    obtain ⟨fB, hfB⟩ := (has_card_iff _ _).mp (has_card_card hB)
    let eB := Equiv.ofBijective fB hfB
    refine ⟨fun a => eB.symm (Fin_embed A.card B.card hle (fA a)), ?_⟩
    intro a b hab
    have h1 := eB.symm.injective hab
    have embN : ∀ (i:SetTheory.Set.Fin A.card), ((Fin_embed A.card B.card hle i :ℕ)) = (i:ℕ) := by
      intro i
      have : ((Fin_embed A.card B.card hle i:ℕ):Object) = ((i:ℕ):Object) := by rw [Fin.coe_toNat, Fin.coe_toNat]
      rwa [SetTheory.Object.natCast_inj] at this
    have h2 : (fA a : ℕ) = (fA b : ℕ) := by
      have he : ((Fin_embed A.card B.card hle (fA a)):ℕ) = ((Fin_embed A.card B.card hle (fA b)):ℕ) := by rw [h1]
      rw [embN, embN] at he; exact he
    exact hfA.1 (Fin.coe_inj.mpr h2)

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  classical
  obtain ⟨a0, ha0⟩ := nonempty_def hA
  refine ⟨fun b => if h : ∃ a, f a = b then h.choose else ⟨a0, ha0⟩, ?_⟩
  intro a
  refine ⟨f a, ?_⟩
  have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
  simp only [hex, dite_true]
  apply hf
  exact hex.choose_spec

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  classical
  have hBA : (B \ A).finite := subset_finite hB (by intro z hz; rw [mem_sdiff] at hz; exact hz.1)
  have hAB : (A ∩ B).finite := subset_finite hA (by intro z hz; rw [mem_inter] at hz; exact hz.1)
  have hdisj1 : Disjoint A (B \ A) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]; intro z hz; rw [mem_inter, mem_sdiff] at hz; exact hz.2.2 hz.1
  have heq1 : A ∪ (B \ A) = A ∪ B := by
    apply ext; intro z; rw [mem_union, mem_union, mem_sdiff]
    constructor
    · rintro (h|⟨h,_⟩); exact Or.inl h; exact Or.inr h
    · rintro (h|h); exact Or.inl h; by_cases hz : z ∈ A; exact Or.inl hz; exact Or.inr ⟨h, hz⟩
  have hc1 : (A ∪ B).card = A.card + (B \ A).card := by
    rw [← heq1, card_union_disjoint hA hBA hdisj1]
  have hdisj2 : Disjoint (B \ A) (A ∩ B) := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]; intro z hz; rw [mem_inter, mem_sdiff, mem_inter] at hz
    exact hz.1.2 hz.2.1
  have heq2 : (B \ A) ∪ (A ∩ B) = B := by
    apply ext; intro z; rw [mem_union, mem_sdiff, mem_inter]
    constructor
    · rintro (⟨h,_⟩|⟨_,h⟩); exact h; exact h
    · intro h; by_cases hz : z ∈ A; exact Or.inr ⟨hz, h⟩; exact Or.inl ⟨h, hz⟩
  have hc2 : B.card = (B \ A).card + (A ∩ B).card := by
    conv_lhs => rw [← heq2]
    exact card_union_disjoint hBA hAB hdisj2
  omega

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro hf S hSX hScard
    -- image f S has card = S.card via injectivity. Build restriction g : S → image f S
    classical
    -- map each s:S to f ⟨s.val, hSX⟩
    have hmem : ∀ s : S, (f ⟨s.val, hSX s.val s.property⟩).val ∈ image f S :=
      fun s => (mem_image f S _).mpr ⟨⟨s.val, hSX s.val s.property⟩, s.property, rfl⟩
    have heq : EqualCard S (image f S) := by
      refine ⟨fun s => ⟨(f ⟨s.val, hSX s.val s.property⟩).val, hmem s⟩, ?_, ?_⟩
      · intro a b hab
        simp only [Subtype.mk.injEq] at hab
        have : f ⟨a.val, hSX a.val a.property⟩ = f ⟨b.val, hSX b.val b.property⟩ := Subtype.ext hab
        have he := hf this
        have hval : (⟨a.val, hSX a.val a.property⟩ : X).val = (⟨b.val, hSX b.val b.property⟩ : X).val :=
          congrArg Subtype.val he
        exact Subtype.ext hval
      · rintro ⟨y, hy⟩
        rw [mem_image] at hy
        obtain ⟨x, hxS, hfx⟩ := hy
        refine ⟨⟨x.val, hxS⟩, ?_⟩
        apply Subtype.ext
        change (f ⟨x.val, hSX x.val hxS⟩ : Object) = y
        rw [← hfx]
    rw [← EquivCard_to_card_eq heq, hScard]
  · intro h
    by_contra hni
    rw [Function.not_injective_iff] at hni
    obtain ⟨a, b, hfab, hab⟩ := hni
    -- S = {a.val, b.val}
    set S : Set := {a.val, b.val} with hS
    have hSX : S ⊆ X := by
      intro z hz; rw [hS, mem_pair] at hz
      rcases hz with h|h <;> rw [h]
      exact a.property; exact b.property
    have hne : a.val ≠ b.val := fun he => hab (Subtype.ext he)
    have hSeq : S = {b.val} ∪ {a.val} := by
      apply ext; intro z; rw [hS, mem_pair, mem_union, mem_singleton, mem_singleton]; tauto
    have hScard : S.card = 2 := by
      rw [hSeq, (card_insert ⟨1, Example_3_6_7a b.val⟩ (by rw [mem_singleton]; exact fun he => hne he)).2,
        has_card_to_card (Example_3_6_7a b.val)]
    have himg := h S hSX hScard
    -- image f S = {(f a).val}, card 1
    have himgeq : image f S = {(f a).val} := by
      apply ext; intro z; rw [mem_image, mem_singleton]
      constructor
      · rintro ⟨x, hxS, hfx⟩
        rw [hS, mem_pair] at hxS
        rcases hxS with h1|h1
        · rw [← hfx, show x = a from Subtype.ext h1]
        · rw [← hfx, show x = b from Subtype.ext h1, ← hfab]
      · intro hz
        exact ⟨a, by rw [hS, mem_pair]; left; rfl, by rw [hz]⟩
    rw [himgeq, has_card_to_card (Example_3_6_7a (f a).val)] at himg
    omega


/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have hsub : Permutations n ⊆ ((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)) := by
    unfold Permutations
    exact specify_subset _
  have hfin : ((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)).finite :=
    (card_pow (Fin_finite n) (Fin_finite n)).1
  exact subset_finite hfin hsub

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_toFun_coe {n: ℕ} (p: Permutations n) :
    ((Permutations_toFun p : (SetTheory.Set.Fin n) → (SetTheory.Set.Fin n)) : Object) = ↑p := by
  rw [Permutations_toFun]
  exact @Exists.choose_spec _ (fun f => (coe_of_fun f : Object) = ↑p) _

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
  have hbij := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at hbij
  obtain ⟨hex, hb⟩ := hbij
  have hp2 : (↑p : Object) ∈ ((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)) := by
    rw [powerset_axiom]; exact hex
  have hkey : Permutations_toFun p = pow_fun_equiv ⟨↑p, hp2⟩ := by
    have hsub : (⟨↑p, hp2⟩ : ↑((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)))
        = pow_fun_equiv.invFun (Permutations_toFun p) := by
      apply Subtype.ext
      change (↑p : Object) = ((Permutations_toFun p : (SetTheory.Set.Fin n) → (SetTheory.Set.Fin n)) : Object)
      exact (Permutations_toFun_coe p).symm
    rw [hsub]
    exact (pow_fun_equiv.right_inv (Permutations_toFun p)).symm
  rw [hkey]; convert hb using 2

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  constructor
  · intro h
    apply Subtype.ext
    have h1 := Permutations_toFun_coe p1
    have h2 := Permutations_toFun_coe p2
    rw [h] at h1
    rw [← h1, h2]
  · intro h; rw [h]

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := fun e => ⟨(pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n) : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))).val, by
    rw [Permutations, specification_axiom'']
    refine ⟨(pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n)).property, ?_⟩
    have : (⟨_, (pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n)).property⟩ : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))) = pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n) := rfl
    rw [this, Equiv.apply_symm_apply]; exact e.bijective⟩
  left_inv := by
    intro p
    apply Subtype.ext
    show (pow_fun_equiv.symm (Permutations_toFun p) : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))).val = ↑p
    have hv : ((pow_fun_equiv.symm (Permutations_toFun p) : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))) : Object) = (Permutations_toFun p : Object) := rfl
    rw [hv]; exact Permutations_toFun_coe p
  right_inv := by
    intro e
    apply Equiv.ext
    intro x
    show Permutations_toFun _ x = e x
    set p : Permutations n := ⟨(pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n) : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))).val, by
      rw [Permutations, specification_axiom'']
      refine ⟨(pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n)).property, ?_⟩
      have : (⟨_, (pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n)).property⟩ : ↑((SetTheory.Set.Fin n)^(SetTheory.Set.Fin n))) = pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n) := rfl
      rw [this, Equiv.apply_symm_apply]; exact e.bijective⟩ with hp
    have hp2 : (↑p : Object) ∈ ((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)) :=
      (pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n)).property
    have hkey : Permutations_toFun p = pow_fun_equiv ⟨↑p, hp2⟩ := by
      have hsub : (⟨↑p, hp2⟩ : ↑((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)))
          = pow_fun_equiv.invFun (Permutations_toFun p) := by
        apply Subtype.ext
        change (↑p : Object) = ((Permutations_toFun p : (SetTheory.Set.Fin n) → (SetTheory.Set.Fin n)) : Object)
        exact (Permutations_toFun_coe p).symm
      rw [hsub]
      exact (pow_fun_equiv.right_inv (Permutations_toFun p)).symm
    have hpe : (⟨↑p, hp2⟩ : ↑((SetTheory.Set.Fin n) ^ (SetTheory.Set.Fin n)))
        = pow_fun_equiv.symm (e : SetTheory.Set.Fin n → SetTheory.Set.Fin n) := rfl
    rw [hkey, hpe, Equiv.apply_symm_apply]
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
theorem SetTheory.Set.Fin.castSucc_toNat {n} (x : Fin n) : ((castSucc x : Fin (n+1)) : ℕ) = (x:ℕ) := by
  unfold SetTheory.Set.Fin.castSucc
  simp [Fin_embed]

lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  rw [Fin.coe_inj, castSucc_toNat, castSucc_toNat, ← Fin.coe_inj]

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  have hx := Fin.toNat_lt x
  intro h
  rw [castSucc_toNat] at h
  omega

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by
  rw [Fin.coe_inj, castSucc_toNat]
  unfold SetTheory.Set.Fin.castPred
  rw [Fin.toNat_mk]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by
  rw [Fin.coe_inj]
  unfold SetTheory.Set.Fin.castPred
  rw [Fin.toNat_mk, castSucc_toNat]

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction n with
  | zero =>
    have : (SetTheory.Set.Fin 0).iUnion S = ∅ := by
      apply ext; intro z; rw [mem_iUnion]
      constructor
      · rintro ⟨α, _⟩; exact absurd (Fin.toNat_lt α) (by omega)
      · intro h; exact absurd h (not_mem_empty z)
    rw [this]; exact ⟨empty_finite, by simp⟩
  | succ k ih =>
    have hsplit : (SetTheory.Set.Fin (k+1)).iUnion S
        = ((SetTheory.Set.Fin k).iUnion (fun i => S (SetTheory.Set.Fin.castSucc i))) ∪ S (SetTheory.Set.Fin.last k) := by
      apply ext; intro z
      rw [mem_union, mem_iUnion, mem_iUnion]
      constructor
      · rintro ⟨α, hα⟩
        by_cases hl : (α:ℕ) = k
        · right
          have : α = SetTheory.Set.Fin.last k := by rw [Fin.coe_inj]; unfold SetTheory.Set.Fin.last; rw [Fin.toNat_mk, hl]
          rwa [this] at hα
        · left
          have hαn : (α:ℕ) < k := by have := Fin.toNat_lt α; omega
          refine ⟨Fin_mk k (α:ℕ) hαn, ?_⟩
          have : SetTheory.Set.Fin.castSucc (Fin_mk k (α:ℕ) hαn) = α := by rw [Fin.coe_inj, SetTheory.Set.Fin.castSucc_toNat, Fin.toNat_mk]
          rw [this]; exact hα
      · rintro (⟨β, hβ⟩ | hl)
        · exact ⟨SetTheory.Set.Fin.castSucc β, hβ⟩
        · exact ⟨SetTheory.Set.Fin.last k, hl⟩
    -- ih for the restricted family
    have hSc' : ∀ i, (S (SetTheory.Set.Fin.castSucc i)).has_card m := fun i => hSc _
    have hSd' : Pairwise fun i j => Disjoint (S (SetTheory.Set.Fin.castSucc i)) (S (SetTheory.Set.Fin.castSucc j)) := by
      intro i j hij
      exact hSd (fun he => hij (SetTheory.Set.Fin.castSucc_inj.mp he))
    obtain ⟨hfin', hcard'⟩ := ih hSc' hSd'
    -- SetTheory.Set.Fin.last set finite, card m
    have hlastfin : (S (SetTheory.Set.Fin.last k)).finite := ⟨m, hSc _⟩
    have hlastcard : (S (SetTheory.Set.Fin.last k)).card = m := has_card_to_card (hSc _)
    -- disjoint of restricted union with SetTheory.Set.Fin.last
    have hdisj : Disjoint ((SetTheory.Set.Fin k).iUnion (fun i => S (SetTheory.Set.Fin.castSucc i))) (S (SetTheory.Set.Fin.last k)) := by
      rw [SetTheory.Set.disjoint_iff, eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_inter, mem_iUnion] at hz
      obtain ⟨⟨β, hβ⟩, hzlast⟩ := hz
      have hne : SetTheory.Set.Fin.castSucc β ≠ SetTheory.Set.Fin.last k := by
        intro he
        rw [Fin.coe_inj, SetTheory.Set.Fin.castSucc_toNat] at he
        unfold SetTheory.Set.Fin.last at he
        rw [Fin.toNat_mk] at he
        have := Fin.toNat_lt β; omega
      have hdj := hSd hne
      simp only at hdj
      rw [SetTheory.Set.disjoint_iff, eq_empty_iff_forall_notMem] at hdj
      exact hdj z ((mem_inter _ _ _).mpr ⟨hβ, hzlast⟩)
    rw [hsplit]
    refine ⟨union_finite' hfin' hlastfin, ?_⟩
    rw [card_union_disjoint hfin' hlastfin hdisj]
    rw [hcard', hlastcard]; ring


/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by have := Fin.toNat_lt i; omega)
  else
    Fin_mk _ ((x:ℕ) - 1) (by
      have h1 := Fin.toNat_lt x
      have h2 := Fin.toNat_lt i
      have h3 : (x:ℕ) ≠ (i:ℕ) := fun he => h (Fin.coe_inj.mpr he)
      omega)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by omega) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by have := Fin.toNat_lt x; omega)

theorem SetTheory.Set.Fin.succAbove_toNat {n} (i : Fin (n + 1)) (x : Fin n) :
    ((succAbove i x : Fin (n+1)) : ℕ) = if (x:ℕ) < (i:ℕ) then (x:ℕ) else (x:ℕ) + 1 := by
  unfold SetTheory.Set.Fin.succAbove
  split_ifs with h
  · simp [Fin_embed]
  · rw [Fin.toNat_mk]

theorem SetTheory.Set.Fin.predAbove_toNat {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    ((predAbove i x h : Fin n) : ℕ) = if (x:ℕ) < (i:ℕ) then (x:ℕ) else (x:ℕ) - 1 := by
  unfold SetTheory.Set.Fin.predAbove
  split_ifs with hc
  · rw [Fin.toNat_mk]
  · rw [Fin.toNat_mk]

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  intro he
  rw [Fin.coe_inj, succAbove_toNat] at he
  split_ifs at he with hc <;> omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  rw [Fin.coe_inj, succAbove_toNat, predAbove_toNat]
  have hx := Fin.toNat_lt x
  have hi := Fin.toNat_lt i
  have hne : (x:ℕ) ≠ (i:ℕ) := fun he => h (Fin.coe_inj.mpr he)
  split_ifs with h1 h2 h2 <;> omega

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  rw [Fin.coe_inj, predAbove_toNat, succAbove_toNat]
  have hx := Fin.toNat_lt x
  have hi := Fin.toNat_lt i
  split_ifs with h1 h2 h2 <;> omega

/- Helper constructions for Exercise 3.6.12 (i). -/
open SetTheory.Set.Fin

noncomputable def SetTheory.Set.restEquiv {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (e : SetTheory.Set.Fin (n+1) ≃ SetTheory.Set.Fin (n+1))
    (hei : e (last n) = i) : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n := by
  have hne : ∀ x : SetTheory.Set.Fin n, e (succAbove (last n) x) ≠ i := by
    intro x he; rw [← hei] at he; exact (succAbove_ne (last n) x) (e.injective he)
  have hne2 : ∀ y : SetTheory.Set.Fin n, e.symm (succAbove i y) ≠ last n := by
    intro y hy
    have : e (e.symm (succAbove i y)) = e (last n) := by rw [hy]
    rw [Equiv.apply_symm_apply, hei] at this
    exact (succAbove_ne i y) this
  refine ⟨fun x => predAbove i (e (succAbove (last n) x)) (hne x),
          fun y => predAbove (last n) (e.symm (succAbove i y)) (hne2 y), ?_, ?_⟩
  · intro x; simp only [succAbove_predAbove, Equiv.symm_apply_apply, predAbove_succAbove]
  · intro y; simp only [succAbove_predAbove, Equiv.apply_symm_apply, predAbove_succAbove]

noncomputable def SetTheory.Set.unrestE {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (τ : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n) :
    SetTheory.Set.Fin (n+1) ≃ SetTheory.Set.Fin (n+1) := by
  classical
  refine ⟨fun x => if h : x = last n then i else succAbove i (τ (predAbove (last n) x h)),
          fun y => if h : y = i then last n else succAbove (last n) (τ.symm (predAbove i y h)), ?_, ?_⟩
  · intro x
    by_cases hx : x = last n
    · simp only [hx, dif_pos]
    · simp only [hx, dif_neg, not_false_iff]
      have hne : succAbove i (τ (predAbove (last n) x hx)) ≠ i := succAbove_ne _ _
      rw [dif_neg hne, predAbove_succAbove, Equiv.symm_apply_apply, succAbove_predAbove]
  · intro y
    by_cases hy : y = i
    · simp only [hy, dif_pos]
    · simp only [hy, dif_neg, not_false_iff]
      have hne : succAbove (last n) (τ.symm (predAbove i y hy)) ≠ last n := succAbove_ne _ _
      rw [dif_neg hne, predAbove_succAbove, Equiv.apply_symm_apply, succAbove_predAbove]

theorem SetTheory.Set.unrestE_last {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (τ : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n) :
    unrestE i τ (last n) = i := by
  unfold unrestE; simp only [Equiv.coe_fn_mk, dif_pos]

theorem SetTheory.Set.predAbove_congr {n:ℕ} (i a b : SetTheory.Set.Fin (n+1)) (ha : a ≠ i) (hb : b ≠ i) (hab : a = b) :
    predAbove i a ha = predAbove i b hb := by subst hab; rfl

theorem SetTheory.Set.unrestE_app_succAbove {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (τ : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n)
    (x : SetTheory.Set.Fin n) :
    unrestE i τ (succAbove (last n) x) = succAbove i (τ x) := by
  have hsa : succAbove (last n) x ≠ last n := succAbove_ne _ _
  have : unrestE i τ (succAbove (last n) x)
      = succAbove i (τ (predAbove (last n) (succAbove (last n) x) hsa)) := by
    unfold unrestE; simp only [Equiv.coe_fn_mk, dif_neg hsa]
  rw [this, predAbove_succAbove]

theorem SetTheory.Set.rest_unrest {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (τ : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n) :
    restEquiv i (unrestE i τ) (unrestE_last i τ) = τ := by
  apply Equiv.ext; intro x
  have hgen : ∀ (he : unrestE i τ (succAbove (last n) x) ≠ i),
      restEquiv i (unrestE i τ) (unrestE_last i τ) x
        = predAbove i (unrestE i τ (succAbove (last n) x)) he := fun he => rfl
  have hne : unrestE i τ (succAbove (last n) x) ≠ i := by rw [unrestE_app_succAbove]; exact succAbove_ne _ _
  rw [hgen hne]
  have hne2 : succAbove i (τ x) ≠ i := succAbove_ne _ _
  rw [predAbove_congr i _ (succAbove i (τ x)) hne hne2 (unrestE_app_succAbove i τ x)]
  rw [predAbove_succAbove]

theorem SetTheory.Set.restEquiv_app_aux {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (e : SetTheory.Set.Fin (n+1) ≃ SetTheory.Set.Fin (n+1))
    (hei : e (last n) = i) (x : SetTheory.Set.Fin n)
    (he : e (succAbove (last n) x) ≠ i) :
    restEquiv i e hei x = predAbove i (e (succAbove (last n) x)) he := rfl

theorem SetTheory.Set.unrest_rest {n:ℕ} (i : SetTheory.Set.Fin (n+1)) (e : SetTheory.Set.Fin (n+1) ≃ SetTheory.Set.Fin (n+1))
    (hei : e (last n) = i) :
    unrestE i (restEquiv i e hei) = e := by
  apply Equiv.ext; intro x
  by_cases hx : x = last n
  · rw [hx, unrestE_last, hei]
  · -- unrestE i τ x = succAbove i (τ (predAbove (last n) x hx))
    have hu : unrestE i (restEquiv i e hei) x
        = succAbove i (restEquiv i e hei (predAbove (last n) x hx)) := by
      unfold unrestE; simp only [Equiv.coe_fn_mk, dif_neg hx]
    rw [hu]
    set y := predAbove (last n) x hx with hy
    have hsa : succAbove (last n) y = x := by rw [hy, succAbove_predAbove]
    have hey : e (succAbove (last n) y) ≠ i := by rw [hsa]; intro hc; rw [← hei] at hc; exact hx (e.injective hc)
    rw [restEquiv_app_aux i e hei y hey, succAbove_predAbove, hsa]

theorem SetTheory.Set.restEquiv_congr {n:ℕ} (i : SetTheory.Set.Fin (n+1))
    (e1 e2 : SetTheory.Set.Fin (n+1) ≃ SetTheory.Set.Fin (n+1))
    (h1 : e1 (last n) = i) (h2 : e2 (last n) = i) (he : e1 = e2) :
    restEquiv i e1 h1 = restEquiv i e2 h2 := by subst he; rfl

-- the equiv on the restricted set of e's
noncomputable def SetTheory.Set.SeqPerm {n:ℕ} (i : SetTheory.Set.Fin (n+1)) :
    ((Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (last n) = i)) ≃ Permutations n := by
  set Si := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (last n) = i) with hSi
  have hcond : ∀ p : Si, perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩ (last n) = i :=
    fun p => ((specification_axiom'' _ p.val).mp p.property).2
  -- helper to build membership of Si from an Equiv
  have hmem : ∀ τ : SetTheory.Set.Fin n ≃ SetTheory.Set.Fin n,
      (perm_equiv_equiv.symm (unrestE i τ)).val ∈ Si := by
    intro τ
    rw [hSi, specification_axiom'']
    refine ⟨(perm_equiv_equiv.symm (unrestE i τ)).property, ?_⟩
    have : (⟨_, (perm_equiv_equiv.symm (unrestE i τ)).property⟩ : Permutations (n+1))
        = perm_equiv_equiv.symm (unrestE i τ) := rfl
    rw [this, Equiv.apply_symm_apply, unrestE_last]
  refine ⟨fun p => perm_equiv_equiv.symm (restEquiv i (perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩) (hcond p)),
          fun τ => ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, hmem (perm_equiv_equiv τ)⟩, ?_, ?_⟩
  · intro p
    apply Subtype.ext
    show (perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv (perm_equiv_equiv.symm (restEquiv i (perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩) (hcond p)))))).val = p.val
    rw [Equiv.apply_symm_apply]
    have key : unrestE i (restEquiv i (perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩) (hcond p))
        = perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩ :=
      unrest_rest i _ (hcond p)
    calc (perm_equiv_equiv.symm (unrestE i (restEquiv i (perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩) (hcond p)))).val
        = (perm_equiv_equiv.symm (perm_equiv_equiv ⟨p.val, specify_subset _ p.val p.property⟩)).val :=
          congrArg (fun z => (perm_equiv_equiv.symm z).val) key
      _ = p.val := by rw [Equiv.symm_apply_apply]
  · intro τ
    apply Equiv.injective perm_equiv_equiv.symm.symm
    rw [Equiv.symm_symm]
    show perm_equiv_equiv (perm_equiv_equiv.symm (restEquiv i (perm_equiv_equiv ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, specify_subset _ _ (hmem (perm_equiv_equiv τ))⟩) (hcond ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, hmem (perm_equiv_equiv τ)⟩))) = perm_equiv_equiv τ
    rw [Equiv.apply_symm_apply]
    have heq : restEquiv i (perm_equiv_equiv ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, specify_subset _ _ (hmem (perm_equiv_equiv τ))⟩) (hcond ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, hmem (perm_equiv_equiv τ)⟩)
        = restEquiv i (unrestE i (perm_equiv_equiv τ)) (unrestE_last i (perm_equiv_equiv τ)) := by
      apply restEquiv_congr
      show perm_equiv_equiv ⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, specify_subset _ _ (hmem (perm_equiv_equiv τ))⟩ = unrestE i (perm_equiv_equiv τ)
      have : (⟨(perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ))).val, specify_subset _ _ (hmem (perm_equiv_equiv τ))⟩ : Permutations (n+1))
          = perm_equiv_equiv.symm (unrestE i (perm_equiv_equiv τ)) := rfl
      rw [this, Equiv.apply_symm_apply]
    rw [heq, rest_unrest]


theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (SetTheory.Set.Fin.last n) = i)
  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    have equiv : S i ≃ Permutations n := SeqPerm i
    exact ⟨equiv, equiv.injective, equiv.surjective⟩
  set m := (Permutations n).card with hm
  have hScard : ∀ i, (S i).has_card m := by
    intro i
    rw [hm]
    obtain ⟨k, hk⟩ := Permutations_finite n
    have hsi : (S i).has_card k := (EquivCard_to_has_card_eq (hSe i)).mpr hk
    rwa [has_card_to_card hk]
  have hSd : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    rw [SetTheory.Set.disjoint_iff, eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_inter] at hz
    obtain ⟨hz1, he1⟩ := (specification_axiom'' _ z).mp hz.1
    obtain ⟨hz2, he2⟩ := (specification_axiom'' _ z).mp hz.2
    exact hij (by rw [← he1, ← he2])
  have hUnion : (SetTheory.Set.Fin (n+1)).iUnion S = Permutations (n+1) := by
    apply ext; intro z
    rw [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact specify_subset _ z hi
    · intro hz
      refine ⟨perm_equiv_equiv ⟨z, hz⟩ (SetTheory.Set.Fin.last n), ?_⟩
      rw [specification_axiom'']
      exact ⟨hz, rfl⟩
  have hciu := card_iUnion_card_disjoint hScard hSd
  rw [hUnion] at hciu
  exact hciu.2

theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by
  induction n with
  | zero =>
    -- Permutations 0 has exactly one element (the empty function)
    have h1 : (Permutations 0).card = 1 := by
      have he : EqualCard (Permutations 0) ({(0:Object)}:Set) := by
        refine ⟨fun _ => ⟨0, by rw [mem_singleton]⟩, ?_, ?_⟩
        · intro a b _
          apply Subtype.ext
          -- both encode the empty function; ↑a = ↑b since both functions Fin 0 → Fin 0 unique
          have ha := Permutations_toFun_coe a
          have hb := Permutations_toFun_coe b
          have : Permutations_toFun a = Permutations_toFun b := by
            funext z; exact absurd (Fin.toNat_lt z) (by omega)
          rw [this] at ha; rw [← ha, hb]
        · rintro ⟨w, hw⟩
          exact ⟨perm_equiv_equiv.symm (Equiv.refl _), by rw [mem_singleton] at hw; apply Subtype.ext; simp [hw]⟩
      rw [EquivCard_to_card_eq he, has_card_to_card (Example_3_6_7a 0)]
    rw [h1]; rfl
  | succ k ih =>
    rw [Permutations_ih, ih, Nat.factorial_succ]


/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
