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
  constructor
  · intro h
    have base : ∀ (N:ℕ) (ε:ℝ), 0 < ε → ∃ m:ℕ, N ≤ m ∧ |a m - L| ≤ ε := by
      intro N ε hε
      obtain ⟨n, hn, hclose⟩ := (Sequence.limit_point_def _ _).mp h ε hε (N:ℤ)
        (by show ((a:Sequence)).m ≤ (N:ℤ); show (0:ℤ) ≤ (N:ℤ); positivity)
      refine ⟨n.toNat, by omega, ?_⟩
      rwa [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe] at hclose
    have step : ∀ (N:ℕ) (k:ℕ), ∃ m:ℕ, N ≤ m ∧ |a m - L| ≤ 1/((k:ℝ)+1) :=
      fun N k => base N (1/((k:ℝ)+1)) (by positivity)
    choose g hg_ge hg_close using step
    set f : ℕ → ℕ := fun k => Nat.rec (g 0 0) (fun k prev => g (prev+1) (k+1)) k with hf_def
    have hf0 : f 0 = g 0 0 := rfl
    have hfs : ∀ k, f (k+1) = g (f k + 1) (k+1) := fun k => rfl
    have hf_lt : ∀ k, f k < f (k+1) := by
      intro k; rw [hfs k]; have := hg_ge (f k + 1) (k+1); omega
    have hf_mono : StrictMono f := strictMono_nat_of_lt_succ hf_lt
    have hf_close : ∀ k, |a (f k) - L| ≤ 1/((k:ℝ)+1) := by
      intro k; cases k with
      | zero => rw [hf0]; have := hg_close 0 0; simpa using this
      | succ j => rw [hfs j]; have := hg_close (f j + 1) (j+1); exact_mod_cast this
    refine ⟨fun k => a (f k), ⟨f, hf_mono, fun _ => rfl⟩, ?_⟩
    rw [Sequence.tendsTo_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (1/ε)
    have hMpos : 0 < (M:ℝ) := lt_of_le_of_lt (by positivity) hM
    refine ⟨(M:ℤ), fun n hn => ?_⟩
    have hn0 : (0:ℤ) ≤ n := le_trans (by positivity) hn
    rw [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe]
    have hMle : M ≤ n.toNat := by omega
    calc |a (f n.toNat) - L| ≤ 1/((n.toNat:ℝ)+1) := hf_close n.toNat
      _ ≤ 1/(M:ℝ) := by
          apply one_div_le_one_div_of_le hMpos
          have : (M:ℝ) ≤ (n.toNat:ℝ) := by exact_mod_cast hMle
          linarith
      _ ≤ ε := by
          rw [div_le_iff₀ hMpos]
          rw [div_lt_iff₀ hε] at hM
          nlinarith [hM]
  · rintro ⟨b, ⟨f, hf, hbf⟩, hb⟩
    rw [Sequence.limit_point_def]
    intro ε hε N hN
    rw [Sequence.tendsTo_iff] at hb
    obtain ⟨M, hMb⟩ := hb ε hε
    set k : ℕ := max M.toNat N.toNat with hk
    have hkM : (M:ℤ) ≤ (k:ℤ) := by omega
    have hclose := hMb (k:ℤ) hkM
    rw [Sequence.eval_coe, hbf] at hclose
    refine ⟨(f k:ℤ), ?_, ?_⟩
    · have hNk : N ≤ (k:ℤ) := by omega
      have : (k:ℤ) ≤ (f k:ℤ) := by exact_mod_cast hf.id_le k
      omega
    · rw [Sequence.eval_coe]
      exact hclose

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
  have unb : ∀ (M:ℝ) (N:ℕ), ∃ k:ℕ, N ≤ k ∧ M < |a k| := by
    intro M N
    by_contra hcon
    push_neg at hcon
    apply ha
    set C := ∑ k ∈ Finset.range N, |a k| with hC
    refine ⟨max (max M C) 0, le_max_right _ _, ?_⟩
    intro n
    rcases lt_or_ge n 0 with hn | hn
    · have hz : (a:Sequence) n = 0 := by
        simp only [Sequence.instCoeFun, Sequence.ofNatFun]; rw [if_neg (by omega)]
      rw [hz, abs_zero]; exact le_max_right _ _
    · rw [show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe]
      rcases lt_or_ge n.toNat N with hk | hk
      · have hle : |a n.toNat| ≤ C :=
          Finset.single_le_sum (f := fun k => |a k|) (fun i _ => abs_nonneg _)
            (Finset.mem_range.mpr hk)
        exact le_trans hle (le_trans (le_max_right _ _) (le_max_left _ _))
      · exact le_trans (hcon n.toNat hk) (le_trans (le_max_left _ _) (le_max_left _ _))
  have step : ∀ (N:ℕ) (k:ℕ), ∃ m:ℕ, N ≤ m ∧ (k:ℝ)+1 < |a m| :=
    fun N k => unb ((k:ℝ)+1) N
  choose g hg_ge hg_gt using step
  set f : ℕ → ℕ := fun k => Nat.rec (g 0 0) (fun k prev => g (prev+1) (k+1)) k with hf_def
  have hf0 : f 0 = g 0 0 := rfl
  have hfs : ∀ k, f (k+1) = g (f k + 1) (k+1) := fun k => rfl
  have hf_lt : ∀ k, f k < f (k+1) := by
    intro k; rw [hfs k]; have := hg_ge (f k + 1) (k+1); omega
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ hf_lt
  have hf_gt : ∀ (k:ℕ), (k:ℝ)+1 < |a (f k)| := by
    intro k; cases k with
    | zero => rw [hf0]; have := hg_gt 0 0; simpa using this
    | succ j => rw [hfs j]; have := hg_gt (f j + 1) (j+1); exact_mod_cast this
  refine ⟨fun k => a (f k), ⟨f, hf_mono, fun _ => rfl⟩, ?_⟩
  rw [Sequence.tendsTo_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1/ε)
  have hMpos : 0 < (M:ℝ) := lt_of_le_of_lt (by positivity) hM
  refine ⟨(M:ℤ), fun n hn => ?_⟩
  have hn0 : (0:ℤ) ≤ n := le_trans (by positivity) hn
  have hMle : M ≤ n.toNat := by omega
  rw [Sequence.inv_eval, show n = ((n.toNat:ℕ):ℤ) by omega, Sequence.eval_coe]
  have hpos : (0:ℝ) < |a (f n.toNat)| := lt_trans (by positivity) (hf_gt n.toNat)
  have hbig : 1/ε < |a (f n.toNat)| := by
    have h1 : (M:ℝ) ≤ (n.toNat:ℝ) := by exact_mod_cast hMle
    have h2 := hf_gt n.toNat
    linarith
  rw [sub_zero, abs_inv]
  have hposε : (0:ℝ) < 1/ε := by positivity
  have h := (inv_lt_inv₀ hpos hposε).mpr hbig
  rw [one_div, inv_inv] at h
  exact le_of_lt h


end Chapter6
