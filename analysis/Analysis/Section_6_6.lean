import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  exact ⟨fun n => 2 * n, fun a b (h : a < b) => by show 2 * a < 2 * b; omega, fun _ => rfl⟩

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := hf.injective

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n => 2*n, ?_, fun n => ?_⟩
  · intro x y h; show 2*x < 2*y; omega
  · dsimp only
    rw [if_pos (even_two_mul n)]
    congr 2
    omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n => 2*n+1, ?_, fun n => ?_⟩
  · intro x y h; show 2*x+1 < 2*y+1; omega
  · dsimp only
    rw [if_neg (by simp [Nat.even_add_one, Nat.even_mul, parity_simps])]
    congr 2
    omega

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := ⟨id, strictMono_id, fun _ => rfl⟩

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
  obtain ⟨f, hf, haf⟩ := hab; obtain ⟨g, hg, hbg⟩ := hbc
  exact ⟨f ∘ g, hf.comp hg, fun n => by simp [Function.comp, hbg n, haf]⟩

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor
  · rintro ha b ⟨f, hf, hbf⟩
    rw [tendsTo_iff] at ha ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    refine ⟨max N 0, fun n hn => ?_⟩
    have hn0 : n ≥ 0 := le_trans (le_max_right _ _) hn
    have hNle : (n.toNat:ℤ) ≥ N := by
      rw [Int.toNat_of_nonneg hn0]; exact le_trans (le_max_left _ _) hn
    have hid := hf.id_le n.toNat
    have hge : ((f n.toNat:ℕ):ℤ) ≥ N := le_trans hNle (by exact_mod_cast hid)
    have hkey := hN ((f n.toNat:ℕ):ℤ) hge
    rw [Sequence.eval_coe] at hkey
    rw [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe, hbf]
    exact hkey
  · intro h
    exact h a (subseq_self a)

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  sorry

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    apply isTrue
    refine ⟨fun n => (-1:ℝ)^n, fun n => (-1:ℝ)^(n+1), ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      norm_num at this
    · exact ⟨fun n => n+1, fun x y hxy => by show x+1 < y+1; omega, fun n => rfl⟩
    · exact ⟨fun n => n+1, fun x y hxy => by show x+1 < y+1; omega,
        fun n => by show (-1:ℝ)^n = (-1:ℝ)^(n+1+1); rw [pow_add]; ring⟩

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  sorry


end Chapter6
