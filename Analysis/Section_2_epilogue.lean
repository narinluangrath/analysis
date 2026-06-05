import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  · rw [succ_add, succ_toNat, hn, succ_toNat]; omega

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_mul, zero_toNat, _root_.Nat.zero_mul]
  · rw [succ_mul, map_add, hn, succ_toNat]; ring

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  have hkk : ∀ k:ℕ, ((k:Chapter2.Nat)).toNat = k := equivNat.right_inv
  constructor
  · intro h
    rw [_root_.le_iff_exists_add] at h
    obtain ⟨k, hk⟩ := h
    rw [Nat.le_iff]
    refine ⟨(k:Chapter2.Nat), equivNat.injective ?_⟩
    show m.toNat = (n + (k:Chapter2.Nat)).toNat
    rw [map_add, hkk]; exact hk
  · intro h
    rw [Nat.le_iff] at h
    obtain ⟨d, hd⟩ := h
    rw [hd, map_add]
    exact _root_.Nat.le_add_right _ _

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m hm
  · rw [show (zero:Chapter2.Nat) = 0 from rfl, zero_toNat, _root_.pow_zero, pow_zero]; rfl
  · rw [succ_toNat, _root_.pow_succ, hm, pow_succ, map_mul]


/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  have key : ∀ n m : ℕ, P.natCast n = P.natCast m → n = m := by
    intro n
    induction' n with n ih
    · intro m h
      cases m with
      | zero => rfl
      | succ m => exact absurd h.symm (P.succ_ne _)
    · intro m h
      cases m with
      | zero => exact absurd h (P.succ_ne _)
      | succ m => exact congrArg _ (ih m (P.succ_cancel h))
  intro n m h
  exact key n m h

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  intro y
  refine P.induction (fun y => ∃ n:ℕ, P.natCast n = y) ⟨0, rfl⟩ ?_ y
  intro k hk
  obtain ⟨n, hn⟩ := hk
  exact ⟨n+1, by show P.succ (P.natCast n) = P.succ k; rw [hn]⟩

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by rw [← equiv.equiv_zero]; exact equiv.equiv.symm_apply_apply P.zero
  equiv_succ n := by
    apply equiv.equiv.injective
    simp only [equiv.equiv_succ, _root_.Equiv.apply_symm_apply]

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    simp only [_root_.Equiv.trans_apply, equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by
    simp only [_root_.Equiv.trans_apply, equiv1.equiv_succ, equiv2.equiv_succ]

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P)
    left_inv := Function.leftInverse_surjInv ⟨natCast_injective P, natCast_surjective P⟩
    right_inv := Function.rightInverse_surjInv (natCast_surjective P)
  }
  equiv_zero := rfl
  equiv_succ n := rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  (Equiv.fromNat P).symm.trans (Equiv.fromNat Q)

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  refine P.induction (fun n => equiv1 n = equiv2 n) ?_ ?_ n
  · show equiv1 P.zero = equiv2 P.zero
    rw [equiv_zero1, equiv_zero2]
  · intro k hk
    show equiv1 (P.succ k) = equiv2 (P.succ k)
    rw [equiv_succ1, equiv_succ2, hk]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  classical
  set ic : ℕ ≃ P.Nat :=
    _root_.Equiv.ofBijective P.natCast ⟨natCast_injective P, natCast_surjective P⟩ with hic
  have hic0 : ic 0 = P.zero := rfl
  have hicsucc : ∀ m:ℕ, ic (m+1) = P.succ (ic m) := fun m => rfl
  set g : ℕ → P.Nat := fun n => Nat.rec (motive := fun _ => P.Nat) c (fun k acc => f (ic k) acc) n
    with hg
  have hg0 : g 0 = c := rfl
  have hgsucc : ∀ k, g (k+1) = f (ic k) (g k) := fun k => rfl
  have hsymm_succ : ∀ x:P.Nat, ic.symm (P.succ x) = ic.symm x + 1 := by
    intro x
    apply ic.injective
    rw [_root_.Equiv.apply_symm_apply, hicsucc, _root_.Equiv.apply_symm_apply]
  refine ⟨fun x => g (ic.symm x), ⟨?_, ?_⟩, ?_⟩
  · show g (ic.symm P.zero) = c
    rw [← hic0, _root_.Equiv.symm_apply_apply, hg0]
  · intro n
    show g (ic.symm (P.succ n)) = f n (g (ic.symm n))
    rw [hsymm_succ, hgsucc, _root_.Equiv.apply_symm_apply]
  · intro a' ⟨ha0, hasucc⟩
    funext x
    refine P.induction (fun x => a' x = g (ic.symm x)) ?_ ?_ x
    · show a' P.zero = g (ic.symm P.zero)
      rw [ha0, ← hic0, _root_.Equiv.symm_apply_apply, hg0]
    · intro k hk
      show a' (P.succ k) = g (ic.symm (P.succ k))
      rw [hasucc, hk, hsymm_succ, hgsucc, _root_.Equiv.apply_symm_apply]

end PeanoAxioms
