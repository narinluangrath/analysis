import Analysis.MeasureTheory.Section_1_2_3
import Analysis.Misc.NatBitwise

/-!
# Introduction to Measure Theory, Section 1.3.1: Integration of simple functions

A companion to (the introduction to) Section 1.3.1 of the book "An introduction to Measure Theory".

-/

-- some tools to convert between EReal-valued, ℝ-valued, and ℂ-valued functions

def EReal.abs_fun {X Y:Type*} [RCLike Y] (f: X → Y) : X → EReal := fun x ↦ ‖f x‖.toEReal
def Complex.re_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.re (f x)
def Complex.im_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.im (f x)
def Complex.conj_fun {X:Type*} (f: X → ℂ) : X → ℂ := fun x ↦ starRingEnd ℂ (f x)
def EReal.pos_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (f x) 0).toEReal
def EReal.neg_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (-f x) 0).toEReal
def Real.complex_fun {X:Type*} (f: X → ℝ) : X → ℂ := fun x ↦ Complex.ofReal (f x)
def Real.EReal_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ Real.toEReal (f x)

noncomputable def EReal.indicator {X:Type*} (A: Set X) : X → EReal := Real.EReal_fun A.indicator'

theorem EReal.indicator_of_mem {X:Type*} {A: Set X} {x:X} (h: x ∈ A) : EReal.indicator A x = 1 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h]

theorem EReal.indicator_of_notMem {X:Type*} {A: Set X} {x:X} (h: x ∉ A) : EReal.indicator A x = 0 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h]

noncomputable def Complex.indicator {X:Type*} (A: Set X) : X → ℂ := Real.complex_fun A.indicator'

/-- Definition 1.3.2 -/
def UnsignedSimpleFunction {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := ∃ (k:ℕ) (c: Fin k → EReal) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0) ∧ f = ∑ i, (c i) • (EReal.indicator (E i))

def RealSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (k:ℕ) (c: Fin k → ℝ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (E i).indicator'

def ComplexSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (k:ℕ) (c: Fin k → ℂ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (Complex.indicator (E i))

-- TODO: coercions between these concepts, and vector space structure on real and complex simple functions (and cone structure on unsigned simple functions).


@[coe]
abbrev RealSimpleFunction.toComplex {d:ℕ} (f: EuclideanSpace' d → ℝ) (df: RealSimpleFunction f) : ComplexSimpleFunction (Real.complex_fun f) := by
  obtain ⟨k, c, E, hmes, heq⟩ := df
  use k, fun i => Complex.ofReal (c i), E
  constructor
  · exact hmes
  · ext x
    simp only [Real.complex_fun, Complex.indicator, heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_sum]
    congr 1
    ext i
    exact Complex.ofReal_mul (c i) ((E i).indicator' x)

instance RealSimpleFunction.coe_complex {d:ℕ} (f: EuclideanSpace' d → ℝ) : Coe (RealSimpleFunction f) (ComplexSimpleFunction (Real.complex_fun f)) := {
  coe := RealSimpleFunction.toComplex f
}


lemma UnsignedSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) : UnsignedSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

private lemma EReal.indicator_nonneg' {X:Type*} (A: Set X) (x : X) : 0 ≤ EReal.indicator A x := by
  simp only [EReal.indicator, Real.EReal_fun]
  exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

lemma UnsignedSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {a: EReal} (ha: a ≥ 0) : UnsignedSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact ⟨hmes i |>.1, mul_nonneg ha (hmes i |>.2)⟩
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k a (fun i => (c i) * EReal.indicator (E i) x)
        (fun i => mul_nonneg (hmes i |>.2) (EReal.indicator_nonneg' (E i) x))]
    congr 1
    ext i
    rw [mul_assoc]

lemma RealSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hg: RealSimpleFunction g) : RealSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma ComplexSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hg: ComplexSimpleFunction g) : ComplexSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma RealSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (a: ℝ)  : RealSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

lemma ComplexSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (a: ℂ)  : ComplexSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

private lemma Complex.indicator_conj {X:Type*} (A: Set X) (x : X) :
    starRingEnd ℂ (Complex.indicator A x) = Complex.indicator A x := by
  simp only [Complex.indicator, Real.complex_fun]
  exact Complex.conj_ofReal _

lemma ComplexSimpleFunction.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ComplexSimpleFunction (Complex.conj_fun f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => starRingEnd ℂ (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Complex.conj_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_sum]
    congr 1
    ext i
    rw [map_mul, Complex.indicator_conj]

noncomputable def UnsignedSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-! ## Helper lemmas for Lemma 1.3.4

The proof uses a Venn diagram argument: given two representations of the same simple function,
we partition R^d into atoms (intersections of all sets and their complements), express each
original set as a disjoint union of atoms, and use finite additivity of Lebesgue measure.
-/

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- {given -show}`k, k'` Given families of sets indexed by {lean}`Fin k` and {lean}`Fin k'`, an atom is determined by
    a choice of “in” or “out” for each set. We encode this as a {lean}`Fin (2^(k+k'))` index. -/
def atomMembership (_k _k' : ℕ) (n : ℕ) (i : ℕ) : Bool := (n / 2^i) % 2 = 1

lemma atomMembership_eq_testBit (k k' n i : ℕ) : atomMembership k k' n i = n.testBit i := by
  simp only [atomMembership, Nat.testBit_eq_decide_div_mod_eq]

/-- The atom indexed by n is the intersection over all $`i` of ($`E_i` if bit $`i` is 1, else $`E_i^c`) -/
def atom {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (n : Fin (2^(k+k'))) : Set X :=
  {x | (∀ i : Fin k, atomMembership k k' n i ↔ x ∈ E i) ∧
       (∀ i : Fin k', atomMembership k k' n (k + i) ↔ x ∈ E' i)}

/-- Atoms are pairwise disjoint -/
lemma atom_pairwiseDisjoint {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) :
    Set.univ.PairwiseDisjoint (atom E E') := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [atom, Set.mem_setOf_eq, atomMembership_eq_testBit] at hxi hxj
  -- If i ≠ j, they differ in some bit
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  obtain ⟨bit, hbit⟩ := Nat.exists_testBit_ne_of_ne hne
  -- The bit must be < k + k' since both i, j < 2^(k+k')
  have hi_lt : i.val < 2^(k + k') := i.isLt
  have hj_lt : j.val < 2^(k + k') := j.isLt
  have hbit_bound : bit < k + k' := by
    by_contra h
    push_neg at h
    have hi_false : i.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    have hj_false : j.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    exact hbit (hi_false.trans hj_false.symm)
  -- Now we know bit < k + k', so it indexes into E or E'
  by_cases hbit_k : bit < k
  · -- bit indexes into E
    have hi_iff := hxi.1 ⟨bit, hbit_k⟩
    have hj_iff := hxj.1 ⟨bit, hbit_k⟩
    -- hxi and hxj both give x ∈ E ⟨bit, _⟩ ↔ testBit = true
    -- But i and j have different bits, so one says x ∈ E and the other says x ∉ E
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)
  · -- bit indexes into E' (bit ∈ [k, k+k'))
    have hbit_k' : bit - k < k' := by omega
    have h_add : k + (bit - k) = bit := by omega
    have hi_iff := hxi.2 ⟨bit - k, hbit_k'⟩
    have hj_iff := hxj.2 ⟨bit - k, hbit_k'⟩
    simp only [h_add] at hi_iff hj_iff
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)

/-- Sum of powers of 2 up to n equals 2^n - 1 -/
private lemma sum_pow_two_range (n : ℕ) : ∑ i ∈ Finset.range n, (2:ℕ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- For any subset of {lean}`Fin k`, sum of {given -show (type := "Fin k")}`j` {lean}`2^j.val` is less than {lean}`2^k` -/
private lemma sum_pow_two_fin_lt {k : ℕ} {s : Finset (Fin k)} :
    s.sum (fun j => (2:ℕ)^j.val) < 2^k := by
  have h1 : s.sum (fun j => (2:ℕ)^j.val) ≤ Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.subset_univ s
  have h2 : Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) = ∑ i ∈ Finset.range k, 2^i := by
    rw [Fin.sum_univ_eq_sum_range]
  have h3 : ∑ i ∈ Finset.range k, (2:ℕ)^i = 2^k - 1 := sum_pow_two_range k
  have h4 : 2^k - 1 < 2^k := Nat.sub_lt Nat.one_le_two_pow Nat.one_pos
  omega

/-- Helper: construct atom index from membership pattern.
    The atom index encodes x's membership in each set as bits. -/
noncomputable def atomIndexOf {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) : ℕ :=
  (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => 2^j.val) +
  (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => 2^(k + j'.val))

/-- The atom index is bounded by 2^(k+k') -/
lemma atomIndexOf_lt {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) :
    atomIndexOf E E' x < 2^(k+k') := by
  unfold atomIndexOf
  have hpart1 : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) < 2^k :=
    sum_pow_two_fin_lt
  have hpart2_inner : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^k' :=
    sum_pow_two_fin_lt
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]
    congr 1; ext j'; rw [pow_add]
  rw [hrw]
  have h2k_pos : 0 < 2^k := Nat.two_pow_pos k
  have hpart2 : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^(k+k') := by
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        < 2^k * 2^k' := (Nat.mul_lt_mul_left h2k_pos).mpr hpart2_inner
      _ = 2^(k+k') := by rw [← pow_add]
  -- Use tight bounds: sum1 ≤ 2^k - 1, sum2 ≤ 2^k * (2^k' - 1) = 2^(k+k') - 2^k
  -- So sum1 + sum2 ≤ (2^k - 1) + (2^(k+k') - 2^k) = 2^(k+k') - 1 < 2^(k+k')
  have hpart1_le : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) ≤ 2^k - 1 :=
    Nat.le_sub_one_of_lt hpart1
  have hpart2_le : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^(k+k') - 2^k := by
    have inner_le : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^k' - 1 :=
      Nat.le_sub_one_of_lt hpart2_inner
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        ≤ 2^k * (2^k' - 1) := Nat.mul_le_mul_left _ inner_le
      _ = 2^k * 2^k' - 2^k := by rw [Nat.mul_sub_one]
      _ = 2^(k+k') - 2^k := by rw [pow_add]
  have h2k_le : 2^k ≤ 2^(k+k') := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k k')
  calc (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) +
       2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
      ≤ (2^k - 1) + (2^(k+k') - 2^k) := Nat.add_le_add hpart1_le hpart2_le
    _ = 2^(k+k') - 1 := by omega
    _ < 2^(k+k') := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)

/-- The atom index has bit j set iff x ∈ E j -/
lemma atomIndexOf_testBit_E {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k) :
    (atomIndexOf E E' x).testBit j.val ↔ x ∈ E j := by
  unfold atomIndexOf
  -- atomIndexOf = Part1 + Part2 where Part2 = 2^k * (inner sum)
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for j.val < k and Part1 < 2^k, testBit j only looks at Part1
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt, if_pos j.isLt]
  -- Now show: Part1.testBit j.val ↔ x ∈ E j
  rw [Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The atom index has bit (k+j) set iff x ∈ E' j -/
lemma atomIndexOf_testBit_E' {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k') :
    (atomIndexOf E E' x).testBit (k + j.val) ↔ x ∈ E' j := by
  unfold atomIndexOf
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for k + j.val ≥ k and Part1 < 2^k
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt]
  have hge : ¬ (k + j.val < k) := by omega
  rw [if_neg hge]
  -- Now show: Part2_inner.testBit ((k + j.val) - k) ↔ x ∈ E' j
  have hsub : (k + j.val) - k = j.val := Nat.add_sub_cancel_left k j.val
  rw [hsub, Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original set E\_i is the union of atoms where bit i is 1 -/
lemma set_eq_biUnion_atoms {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k) :
    E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    -- Construct the atom index from x's membership pattern
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · -- Show atomMembership k k' n i = true
      rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E E E' x i]
      exact hx
    · -- Show x ∈ atom E E' n
      simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.1 i).mp hn_bit

/-- Original set E'\_i is the union of atoms where bit (k+i) is 1 -/
lemma set_eq_biUnion_atoms' {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k') :
    E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E' E E' x i]
      exact hx
    · simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.2 i).mp hn_bit

/-- Atoms are measurable if the original sets are -/
lemma atom_measurable {d k k' : ℕ} {E : Fin k → Set (EuclideanSpace' d)} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (hE' : ∀ i, LebesgueMeasurable (E' i)) (n : Fin (2^(k+k'))) :
    LebesgueMeasurable (atom E E' n) := by
  -- The atom is an intersection of sets of the form E_i or (E_i)ᶜ
  -- Rewrite atom as intersection
  have hatom_eq : atom E E' n =
      (⋂ i : Fin k, if atomMembership k k' n i then E i else (E i)ᶜ) ∩
      (⋂ i : Fin k', if atomMembership k k' n (k + i) then E' i else (E' i)ᶜ) := by
    ext x
    simp only [atom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte]
          exact (h1 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h1 i).mpr hx)
      · intro i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte]
          exact (h2 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h2 i).mpr hx)
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        specialize h1 i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte] at h1
          exact ⟨fun _ => h1, fun _ => hbit⟩
        · simp only [hbit] at h1
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h1 hx).elim⟩
      · intro i
        specialize h2 i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte] at h2
          exact ⟨fun _ => h2, fun _ => hbit⟩
        · simp only [hbit] at h2
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h2 hx).elim⟩
  rw [hatom_eq]
  -- Now show the intersection is measurable
  -- Each component is E i or (E i)ᶜ, both measurable
  -- Finite intersection of measurable sets is measurable
  apply LebesgueMeasurable.inter
  · -- First part: ⋂ i : Fin k, ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n i
    · simp only [h]; exact hE i
    · simp only [h]; exact (hE i).complement
  · -- Second part: ⋂ i : Fin k', ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]; exact hE' i
    · simp only [h]; exact (hE' i).complement

/-- Indicator function evaluates to c if x ∈ E -/
lemma indicator_mul_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∈ E) : c * (EReal.indicator E x) = c := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h, EReal.coe_one, mul_one]

/-- Indicator function evaluates to 0 if x ∉ E -/
lemma indicator_mul_not_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∉ E) : c * (EReal.indicator E x) = 0 := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h, EReal.coe_zero, mul_zero]

/-- The weighted measure sum for a representation -/
noncomputable def weightedMeasureSum {d k : ℕ} (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)) : EReal :=
  ∑ i, (c i) * Lebesgue_measure (E i)

/-- Core lemma: Two representations of the same function give the same weighted measure sum.
    This is the heart of Lemma 1.3.4 (Venn diagram argument). -/
lemma weightedMeasureSum_eq_of_eq {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
    weightedMeasureSum c E = weightedMeasureSum c' E' := by
  -- The proof uses the Venn diagram/atom argument
  -- 1. For any x in a non-empty atom A_n, evaluate heq at x:
  --    sum_{i : x ∈ E_i} c_i = sum_{j : x ∈ E'_j} c'_j
  -- 2. The membership in E_i for x ∈ A_n is determined by bit i of n
  -- 3. Multiply by m(A_n) and sum over all atoms
  -- 4. Swap order of summation to get the result

  -- Define atom measures
  let atomMeas : Fin (2^(k+k')) → EReal := fun n => Lebesgue_measure (atom E E' n)

  -- Atoms are measurable
  have hatom_mes : ∀ n, LebesgueMeasurable (atom E E' n) := atom_measurable hmes hmes'

  -- Step 1: For any point in an atom, the pointwise sums are equal
  have hpoint : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) := by
    intro n x hx
    have := congr_fun heq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

  -- Step 2: In atom n, membership in E_i is determined by bit i
  have hmem_E : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k,
      (x ∈ E i) ↔ atomMembership k k' n i := by
    intro n x hx i
    exact (hx.1 i).symm

  have hmem_E' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k',
      (x ∈ E' i) ↔ atomMembership k k' n (k + i) := by
    intro n x hx i
    exact (hx.2 i).symm

  -- Step 3: The pointwise sum simplifies based on bit pattern
  have hsum_simp : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k, if atomMembership k k' n i then c i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n i
    · simp only [h]
      have hx_in : x ∈ E i := (hmem_E n x hx i).mpr h
      exact indicator_mul_mem (E i) (c i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E i := fun hc => h ((hmem_E n x hx i).mp hc)
      exact indicator_mul_not_mem (E i) (c i) x hx_out

  have hsum_simp' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) = ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]
      have hx_in : x ∈ E' i := (hmem_E' n x hx i).mpr h
      exact indicator_mul_mem (E' i) (c' i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E' i := fun hc => h ((hmem_E' n x hx i).mp hc)
      exact indicator_mul_not_mem (E' i) (c' i) x hx_out

  -- Step 4: For non-empty atoms, the bit-pattern sums are equal
  have hbit_eq : ∀ n : Fin (2^(k+k')), (atom E E' n).Nonempty →
      (∑ i : Fin k, if atomMembership k k' n i = true then c i else 0 : EReal) =
      (∑ i : Fin k', if atomMembership k k' n (k + i) = true then c' i else 0 : EReal) := by
    intro n ⟨x, hx⟩
    rw [← hsum_simp n x hx, ← hsum_simp' n x hx]
    exact hpoint n x hx

  -- Step 5: E_i = union of atoms where bit i = 1
  have hE_decomp : ∀ i : Fin k, E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n :=
    fun i => set_eq_biUnion_atoms E E' i

  -- Step 6: Use finite additivity (this requires showing atoms are disjoint and measurable)
  -- m(E_i) = sum over atoms where bit i = 1 of m(atom)
  have hmes_decomp : ∀ i : Fin k, Lebesgue_measure (E i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
    intro i
    -- Define a modified atom family: atom' n = atom n if bit i is 1, else ∅
    let atom' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n i then atom E E' n else ∅
    -- E i = ⋃ n, atom' n (because atoms with bit 0 contribute nothing)
    have hE_eq : E i = ⋃ n, atom' n := by
      rw [hE_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom'] at hx
        by_cases hn : atomMembership k k' n i
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    -- atom' is pairwise disjoint
    have hdisj' : Set.univ.PairwiseDisjoint atom' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom']
      by_cases h1 : atomMembership k k' i₁ i <;> by_cases h2 : atomMembership k k' i₂ i
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    -- atom' is measurable
    have hmes'_atom : ∀ n, LebesgueMeasurable (atom' n) := by
      intro n
      simp only [atom']
      by_cases h : atomMembership k k' n i
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    -- Apply finite additivity
    calc Lebesgue_measure (E i) = Lebesgue_measure (⋃ n, atom' n) := by rw [hE_eq]
      _ = ∑' n, Lebesgue_measure (atom' n) := Lebesgue_measure.finite_union hmes'_atom hdisj'
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom']
          by_cases h : atomMembership k k' n i
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  have hE'_decomp : ∀ i : Fin k', E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
    fun i => set_eq_biUnion_atoms' E E' i

  have hmes_decomp' : ∀ i : Fin k', Lebesgue_measure (E' i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
    intro i
    let atom'' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n (k + i) then atom E E' n else ∅
    have hE'_eq : E' i = ⋃ n, atom'' n := by
      rw [hE'_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom'', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom''] at hx
        by_cases hn : atomMembership k k' n (k + i)
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    have hdisj'' : Set.univ.PairwiseDisjoint atom'' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom'']
      by_cases h1 : atomMembership k k' i₁ (k + i) <;> by_cases h2 : atomMembership k k' i₂ (k + i)
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    have hmes''_atom : ∀ n, LebesgueMeasurable (atom'' n) := by
      intro n
      simp only [atom'']
      by_cases h : atomMembership k k' n (k + i)
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E' i) = Lebesgue_measure (⋃ n, atom'' n) := by rw [hE'_eq]
      _ = ∑' n, Lebesgue_measure (atom'' n) := Lebesgue_measure.finite_union hmes''_atom hdisj''
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom'' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom'']
          by_cases h : atomMembership k k' n (k + i)
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  -- Step 7: Compute weightedMeasureSum using decomposition
  calc weightedMeasureSum c E
      = ∑ i : Fin k, (c i) * Lebesgue_measure (E i) := rfl
    _ = ∑ i : Fin k, (c i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i; congr 1; exact hmes_decomp i
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), (c i) * (if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i
        -- c i * sum = sum of c i * each term
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n i then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        exact EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c i) (fun n => if atomMembership k k' n i then atomMeas n else 0) hf_nonneg
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        congr 1; ext i; congr 1; ext n
        split_ifs <;> simp
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k, if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k, if atomMembership k k' n i then c i else 0) := by
        congr 1; ext n
        -- Factoring: ∑ i, if p then c i * m else 0 = m * ∑ i, if p then c i else 0
        have hc_nonneg : ∀ i : Fin k, 0 ≤ (if atomMembership k k' n i then c i else 0) := fun i => by
          split_ifs; exact hnonneg i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k (atomMeas n) _ hc_nonneg]
        congr 1; ext i
        split_ifs with h
        · -- c i * atomMeas n = atomMeas n * c i
          exact (EReal.mul_comm (atomMeas n) (c i)).symm
        · simp
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0) := by
        congr 1; ext n
        by_cases h : (atom E E' n).Nonempty
        · congr 1; exact hbit_eq n h
        · -- Empty atom has measure 0, so this term is 0
          rw [Set.not_nonempty_iff_eq_empty] at h
          have hzero : atomMeas n = 0 := by
            simp only [atomMeas, h, Lebesgue_measure.empty]
          simp only [hzero, zero_mul]
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k', if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        congr 1; ext n
        -- Expanding: m * ∑ i, if p then c i else 0 = ∑ i, if p then c i * m else 0
        have hc'_nonneg : ∀ i : Fin k', 0 ≤ (if atomMembership k k' n (k + i) then c' i else 0) := fun i => by
          split_ifs; exact hnonneg' i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k' (atomMeas n) _ hc'_nonneg]
        congr 1; ext i
        split_ifs with h
        · exact EReal.mul_comm (atomMeas n) (c' i)
        · simp
    _ = ∑ i : Fin k', ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin k', (c' i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0) := by
        congr 1; ext i
        -- c' i * sum = sum of c' i * each term, then distribute through conditionals
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n (k + i) then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        rw [EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c' i) _ hf_nonneg]
        congr 1; ext n
        split_ifs <;> simp
    _ = ∑ i : Fin k', (c' i) * Lebesgue_measure (E' i) := by
        congr 1; ext i; congr 1; exact (hmes_decomp' i).symm
    _ = weightedMeasureSum c' E' := rfl

/-- Monotone core lemma: if `∑ cᵢ•ind(Eᵢ) ≤ ∑ c'ⱼ•ind(E'ⱼ)` pointwise outside a null set `N`,
    then the weighted measure sums are `≤`. This is the heart of a.e.-monotonicity of the integral. -/
lemma weightedMeasureSum_le_of_aeLe {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    {N : Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (hN : IsNull N)
    (hle : ∀ x, x ∉ N →
      (∑ i, (c i) • (EReal.indicator (E i))) x ≤ (∑ i, (c' i) • (EReal.indicator (E' i))) x) :
    weightedMeasureSum c E ≤ weightedMeasureSum c' E' := by
  let atomMeas : Fin (2^(k+k')) → EReal := fun n => Lebesgue_measure (atom E E' n)
  have hatom_mes : ∀ n, LebesgueMeasurable (atom E E' n) := atom_measurable hmes hmes'
  -- Pointwise bit-pattern sums, for x in an atom
  have hsum_simp : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k, if atomMembership k k' n i then c i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n i
    · simp only [h]; exact indicator_mul_mem (E i) (c i) x ((hx.1 i).mp h)
    · simp only [h]; exact indicator_mul_not_mem (E i) (c i) x (fun hc => h ((hx.1 i).mpr hc))
  have hsum_simp' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) = ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]; exact indicator_mul_mem (E' i) (c' i) x ((hx.2 i).mp h)
    · simp only [h]; exact indicator_mul_not_mem (E' i) (c' i) x (fun hc => h ((hx.2 i).mpr hc))
  -- Atom decompositions of the measures (copied from weightedMeasureSum_eq_of_eq)
  have hE_decomp : ∀ i : Fin k, E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n :=
    fun i => set_eq_biUnion_atoms E E' i
  have hmes_decomp : ∀ i : Fin k, Lebesgue_measure (E i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
    intro i
    let atom' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n i then atom E E' n else ∅
    have hE_eq : E i = ⋃ n, atom' n := by
      rw [hE_decomp i]; ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩; exact ⟨n, by simp only [atom', hn, ite_true]; exact hx⟩
      · intro ⟨n, hx⟩
        simp only [atom'] at hx
        by_cases hn : atomMembership k k' n i
        · simp only [hn, ite_true] at hx; exact ⟨n, hn, hx⟩
        · simp only [hn] at hx; exact False.elim hx
    have hdisj' : Set.univ.PairwiseDisjoint atom' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom']
      by_cases h1 : atomMembership k k' i₁ i <;> by_cases h2 : atomMembership k k' i₂ i
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]; rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]; rw [Set.disjoint_left]; simp
      · simp only [h1, h2]; rw [Set.disjoint_left]; simp
    have hmes'_atom : ∀ n, LebesgueMeasurable (atom' n) := by
      intro n; simp only [atom']
      by_cases h : atomMembership k k' n i
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E i) = Lebesgue_measure (⋃ n, atom' n) := by rw [hE_eq]
      _ = ∑' n, Lebesgue_measure (atom' n) := Lebesgue_measure.finite_union hmes'_atom hdisj'
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom']
          by_cases h : atomMembership k k' n i
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty
  have hE'_decomp : ∀ i : Fin k', E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
    fun i => set_eq_biUnion_atoms' E E' i
  have hmes_decomp' : ∀ i : Fin k', Lebesgue_measure (E' i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
    intro i
    let atom'' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n (k + i) then atom E E' n else ∅
    have hE'_eq : E' i = ⋃ n, atom'' n := by
      rw [hE'_decomp i]; ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩; exact ⟨n, by simp only [atom'', hn, ite_true]; exact hx⟩
      · intro ⟨n, hx⟩
        simp only [atom''] at hx
        by_cases hn : atomMembership k k' n (k + i)
        · simp only [hn, ite_true] at hx; exact ⟨n, hn, hx⟩
        · simp only [hn] at hx; exact False.elim hx
    have hdisj'' : Set.univ.PairwiseDisjoint atom'' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom'']
      by_cases h1 : atomMembership k k' i₁ (k + i) <;> by_cases h2 : atomMembership k k' i₂ (k + i)
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]; rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]; rw [Set.disjoint_left]; simp
      · simp only [h1, h2]; rw [Set.disjoint_left]; simp
    have hmes''_atom : ∀ n, LebesgueMeasurable (atom'' n) := by
      intro n; simp only [atom'']
      by_cases h : atomMembership k k' n (k + i)
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E' i) = Lebesgue_measure (⋃ n, atom'' n) := by rw [hE'_eq]
      _ = ∑' n, Lebesgue_measure (atom'' n) := Lebesgue_measure.finite_union hmes''_atom hdisj''
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom'' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom'']
          by_cases h : atomMembership k k' n (k + i)
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty
  -- Both sums collapse to ∑ n, atomMeas n * (bit-pattern coefficient sum)
  have hcollapse : ∀ (m : ℕ) (a : Fin m → EReal) (na : ∀ i, a i ≥ 0)
      (sel : Fin (2^(k+k')) → Fin m → Bool),
      (∑ i : Fin m, (a i) * (∑ n : Fin (2^(k+k')), if sel n i then atomMeas n else 0)) =
      ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin m, if sel n i then a i else 0) := by
    intro m a na sel
    calc ∑ i : Fin m, (a i) * (∑ n : Fin (2^(k+k')), if sel n i then atomMeas n else 0)
        = ∑ i : Fin m, ∑ n : Fin (2^(k+k')), (a i) * (if sel n i then atomMeas n else 0) := by
          congr 1; ext i
          have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if sel n i then atomMeas n else 0) := by
            intro n; split_ifs
            · exact Lebesgue_outer_measure.nonneg _
            · rfl
          exact EReal.mul_finset_sum_of_nonneg (2^(k+k')) (a i) _ hf_nonneg
      _ = ∑ i : Fin m, ∑ n : Fin (2^(k+k')), if sel n i then (a i) * atomMeas n else 0 := by
          congr 1; ext i; congr 1; ext n; split_ifs <;> simp
      _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin m, if sel n i then (a i) * atomMeas n else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin m, if sel n i then a i else 0) := by
          congr 1; ext n
          have hc_nonneg : ∀ i : Fin m, 0 ≤ (if sel n i then a i else 0) := fun i => by
            split_ifs; exact na i; rfl
          rw [EReal.mul_finset_sum_of_nonneg m (atomMeas n) _ hc_nonneg]
          congr 1; ext i
          split_ifs with h
          · exact (EReal.mul_comm (atomMeas n) (a i)).symm
          · simp
  have hL : weightedMeasureSum c E
      = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k, if atomMembership k k' n i then c i else 0) := by
    rw [← hcollapse k c hnonneg (fun n i => atomMembership k k' n i)]
    apply Finset.sum_congr rfl; intro i _; rw [hmes_decomp i]
  have hR : weightedMeasureSum c' E'
      = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0) := by
    rw [← hcollapse k' c' hnonneg' (fun n i => atomMembership k k' n (k + i))]
    apply Finset.sum_congr rfl; intro i _; rw [hmes_decomp' i]
  rw [hL, hR]
  apply Finset.sum_le_sum
  intro n _
  -- term-by-term: atomMeas n * bitsum_f ≤ atomMeas n * bitsum_g
  by_cases hz : atomMeas n = 0
  · simp only [hz, zero_mul]; exact le_refl 0
  · -- positive-measure atom is not null, so contains a point outside N
    have hnotnull : ¬ IsNull (atom E E' n) := by
      intro hnull; exact hz hnull
    have hnotsub : ¬ (atom E E' n ⊆ N) := by
      intro hsub
      exact hnotnull (le_antisymm (le_trans (Lebesgue_outer_measure.mono hsub) (le_of_eq hN))
        (Lebesgue_outer_measure.nonneg _))
    obtain ⟨x, hxa, hxN⟩ := Set.not_subset.mp hnotsub
    have hbit : (∑ i : Fin k, if atomMembership k k' n i then c i else 0 : EReal)
        ≤ ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
      rw [← hsum_simp n x hxa, ← hsum_simp' n x hxa]
      have := hle x hxN
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    exact mul_le_mul_of_nonneg_left hbit (Lebesgue_outer_measure.nonneg _)

/-! ## Single-family atoms (k' = 0 specialization)

When working with a single family of sets (no second family to compare against),
we specialize the atom machinery with k' = 0. -/

/-- The atom for a single family of sets, using k' = 0 in the general atom definition -/
def singleAtom {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) : Set X :=
  atom E (fun _ : Fin 0 => ∅) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- Single atoms are pairwise disjoint -/
lemma singleAtom_pairwiseDisjoint {X : Type*} {k : ℕ} (E : Fin k → Set X) :
    Set.univ.PairwiseDisjoint (singleAtom E) := by
  intro i _ j _ hij
  simp only [Function.onFun, singleAtom]
  have hlt_i : i.val < 2^(k+0) := by simp only [add_zero]; exact i.isLt
  have hlt_j : j.val < 2^(k+0) := by simp only [add_zero]; exact j.isLt
  have hij' : (⟨i.val, hlt_i⟩ : Fin (2^(k+0))) ≠ ⟨j.val, hlt_j⟩ := by
    intro h; apply hij; ext; exact Fin.mk.inj h
  exact atom_pairwiseDisjoint E (fun _ : Fin 0 => ∅) (by simp : i ∈ Set.univ) (by simp : j ∈ Set.univ) hij'

/-- Membership in singleAtom is determined by bit pattern -/
lemma mem_singleAtom_iff {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) (x : X) :
    x ∈ singleAtom E n ↔ ∀ i : Fin k, n.val.testBit i.val ↔ x ∈ E i := by
  simp only [singleAtom, atom, Set.mem_setOf_eq]
  constructor
  · intro ⟨h1, _⟩ i
    specialize h1 i
    rw [atomMembership_eq_testBit] at h1
    convert h1 using 1
  · intro h
    constructor
    · intro i
      rw [atomMembership_eq_testBit]
      exact h i
    · intro i; exact Fin.elim0 i

/-- Every point is in exactly one singleAtom -/
lemma exists_unique_singleAtom {X : Type*} [DecidableEq X] {k : ℕ} (E : Fin k → Set X) (x : X) :
    ∃! n : Fin (2^k), x ∈ singleAtom E n := by
  let n : ℕ := atomIndexOf E (fun _ : Fin 0 => ∅) x
  have hn_lt : n < 2^k := by
    have := atomIndexOf_lt E (fun _ : Fin 0 => ∅) x
    simp only [add_zero] at this
    exact this
  use ⟨n, hn_lt⟩
  constructor
  · simp only
    rw [mem_singleAtom_iff]
    intro i
    exact atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x i
  · intro m hm
    ext
    rw [mem_singleAtom_iff] at hm
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · have h1 := hm ⟨j, hj⟩
      have h2 := atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x ⟨j, hj⟩
      by_cases hx : x ∈ E ⟨j, hj⟩
      · rw [h1.mpr hx, h2.mpr hx]
      · have hm_false : (m.val.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h1.mp ht))
        have hn_false : (n.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h2.mp ht))
        rw [hm_false, hn_false]
    · have hm_lt : m.val < 2^k := m.isLt
      have hn_lt' : (atomIndexOf E (fun _ : Fin 0 => ∅) x) < 2^k := hn_lt
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn_lt' (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]

/-- The value on atom n is the sum of coefficients for sets containing that atom -/
noncomputable def atomValue {k : ℕ} (c : Fin k → ℝ) (n : Fin (2^k)) : ℝ :=
  ∑ i : Fin k, if n.val.testBit i.val then c i else 0

end UnsignedSimpleFunction.IntegralWellDef

/-- Lemma 1.3.4 (Well-definedness of simple integral) -/
lemma UnsignedSimpleFunction.integral_eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {k:ℕ} {c: Fin k → EReal}
    {E: Fin k → Set (EuclideanSpace' d)} (hmes: ∀ i, LebesgueMeasurable (E i)) (hnonneg: ∀ i, c i ≥ 0)
    (heq: f = ∑ i, (c i) • (EReal.indicator (E i))) :
    hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) := by
  -- Extract the canonical representation from hf
  -- hf gives: ∃ k', ∃ (c': Fin k' → EReal) (E': Fin k' → Set _), (∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0) ∧ f = ∑...
  -- hf.choose_spec.choose is c', hf.choose_spec.choose_spec.choose is E'
  let k' := hf.choose
  let c' := hf.choose_spec.choose
  let E' := hf.choose_spec.choose_spec.choose
  have hmes'_nonneg : ∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq' : f = ∑ i, (c' i) • (EReal.indicator (E' i)) := hf.choose_spec.choose_spec.choose_spec.2

  -- The canonical representation also equals f
  have hfunc_eq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i)) := by
    rw [← heq, ← heq']

  -- Apply the core lemma: two representations of the same function give the same weighted measure
  have h := IntegralWellDef.weightedMeasureSum_eq_of_eq
    hmes (fun i => (hmes'_nonneg i).1) hnonneg (fun i => (hmes'_nonneg i).2) hfunc_eq

  -- h says: weightedMeasureSum c E = weightedMeasureSum c' E'
  -- Goal: ∑ i, (c' i) * Lebesgue_measure (E' i) = ∑ i, (c i) * Lebesgue_measure (E i)
  simp only [UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum] at h
  exact h.symm

/-- The integral of an unsigned simple function depends only on the function, not the proof. -/
lemma UnsignedSimpleFunction.integ_congr {d:ℕ} {f g: EuclideanSpace' d → EReal}
    (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) (h: f = g) :
    hf.integ = hg.integ := by
  obtain ⟨k, c, E, hmn, heq⟩ := id hg
  rw [hf.integral_eq (fun i => (hmn i).1) (fun i => (hmn i).2) (h.trans heq),
      hg.integral_eq (fun i => (hmn i).1) (fun i => (hmn i).2) heq]

/-- Definition 1.3.5 -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }

lemma UnsignedSimpleFunction.support_measurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  -- Extract the representation: f = ∑ i, c(i) • EReal.indicator(E_i)
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf
  -- Define E' i = E i if c i > 0, else ∅
  let E' : Fin k → Set (EuclideanSpace' d) := fun i => if c i > 0 then E i else ∅
  -- Each E' i is measurable
  have hE'_meas : ∀ i, LebesgueMeasurable (E' i) := fun i => by
    simp only [E']
    split_ifs with h
    · exact (hmes_nonneg i).1
    · exact LebesgueMeasurable.empty
  -- Key: Support f = ⋃ i, E' i
  have h_eq : Support f = ⋃ i, E' i := by
    ext x
    simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion, E']
    constructor
    · -- (⊆) If f(x) ≠ 0, some c_i > 0 and x ∈ E_i
      intro hne
      rw [heq] at hne
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hne
      -- Sum of nonneg terms is nonzero, so some term is nonzero
      have h_exists := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨i, _, hi_ne⟩ := h_exists
      use i
      -- c i * indicator ≠ 0 means c i > 0 and x ∈ E i
      by_cases hc : c i > 0
      · simp only [hc, ↓reduceIte]
        by_cases hx : x ∈ E i
        · exact hx
        · -- If x ∉ E i, then indicator is 0, so c i * 0 = 0, contradiction
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx,
                     EReal.coe_zero, mul_zero] at hi_ne
          exact absurd rfl hi_ne
      · -- c i ≤ 0, but c i ≥ 0, so c i = 0
        have hc_zero : c i = 0 := le_antisymm (le_of_not_gt hc) (hmes_nonneg i).2
        simp only [hc_zero, zero_mul] at hi_ne
        exact absurd rfl hi_ne
    · -- (⊇) If x ∈ E' i for some i, then f(x) ≠ 0
      intro ⟨i, hi⟩
      split_ifs at hi with hc
      · -- c i > 0 and x ∈ E i
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        -- f(x) ≥ c i * indicator(E i)(x) = c i > 0
        have h_term_pos : c i * EReal.indicator (E i) x > 0 := by
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hi,
                     EReal.coe_one, mul_one]
          exact hc
        -- Sum of nonneg terms with one positive term is positive
        have h_sum_nonneg : ∀ j, 0 ≤ c j * EReal.indicator (E j) x := fun j =>
          mul_nonneg (hmes_nonneg j).2 (EReal.indicator_nonneg' (E j) x)
        have h_sum_pos : 0 < ∑ j : Fin k, c j * EReal.indicator (E j) x := by
          calc 0 < c i * EReal.indicator (E i) x := h_term_pos
            _ ≤ ∑ j : Fin k, c j * EReal.indicator (E j) x :=
                Finset.single_le_sum (fun j _ => h_sum_nonneg j) (Finset.mem_univ i)
        exact ne_of_gt h_sum_pos
      · -- hi : x ∈ ∅, contradiction
        exact absurd hi (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hE'_meas

lemma AlmostAlways.ofAlways {d:ℕ} {P: EuclideanSpace' d → Prop} (h: ∀ x, P x) : AlmostAlways P := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If ∀ x, P x, then { x | ¬ P x } = ∅
  unfold AlmostAlways IsNull
  have h_empty : { x | ¬ P x } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

lemma AlmostAlways.mp {d:ℕ} {P Q: EuclideanSpace' d → Prop} (hP: AlmostAlways P) (himp: ∀ x, P x → Q x) : AlmostAlways Q := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If P → Q everywhere, then ¬Q → ¬P (contrapositive), so { x | ¬ Q x } ⊆ { x | ¬ P x }
  unfold AlmostAlways IsNull at *
  -- hP : Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Goal: Lebesgue_outer_measure { x | ¬ Q x } = 0
  have h_subset : { x | ¬ Q x } ⊆ { x | ¬ P x } := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    exact fun hp => hx (himp x hp)
  -- By monotonicity: measure { x | ¬ Q x } ≤ measure { x | ¬ P x } = 0
  have h_le := Lebesgue_outer_measure.mono h_subset
  rw [hP] at h_le
  exact le_antisymm h_le (Lebesgue_outer_measure.nonneg _)

lemma AlmostAlways.countable {d:ℕ} {I: Type*} [Countable I] {P: I → EuclideanSpace' d → Prop} (hP: ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  -- AlmostAlways (fun x ↦ ∀ i, P i x) means IsNull { x | ¬ ∀ i, P i x }
  -- { x | ¬ ∀ i, P i x } = { x | ∃ i, ¬ P i x } = ⋃ᵢ { x | ¬ P i x }
  -- Each { x | ¬ P i x } is null by hP, and a countable union of null sets is null
  unfold AlmostAlways IsNull at *
  -- Goal: Lebesgue_outer_measure { x | ¬ ∀ i, P i x } = 0
  -- hP i : Lebesgue_outer_measure { x | ¬ P i x } = 0
  have h_eq : { x | ¬ ∀ i, P i x } = ⋃ i, { x | ¬ P i x } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
  rw [h_eq]
  -- Need: Lebesgue_outer_measure (⋃ i, { x | ¬ P i x }) = 0
  -- Use countable type I via Encodable
  cases nonempty_encodable I with
  | intro enc =>
    -- Now have Encodable I, can use ℕ-indexed union
    -- Reindex via Encodable.encode
    let E' : ℕ → Set (EuclideanSpace' d) := fun n => match @Encodable.decode I enc n with
      | some i => { x | ¬ P i x }
      | none => ∅
    have h_subset : (⋃ i : I, { x | ¬ P i x }) ⊆ ⋃ n : ℕ, E' n := by
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      use @Encodable.encode I enc i
      simp only [E', @Encodable.encodek I enc]
      exact hi
    have h_le := Lebesgue_outer_measure.mono h_subset
    have h_E'_null : ∀ n, Lebesgue_outer_measure (E' n) = 0 := fun n => by
      simp only [E']
      cases h : @Encodable.decode I enc n with
      | none => exact Lebesgue_outer_measure.of_empty d
      | some i => exact hP i
    -- By countable subadditivity: m(⋃ E'_n) ≤ ∑' n, m(E'_n) = ∑' n, 0 = 0
    have h_sum_zero : ∑' n, Lebesgue_outer_measure (E' n) = 0 := by
      simp only [h_E'_null, tsum_zero]
    have h_union_le := Lebesgue_outer_measure.union_le E'
    have h_bound : Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x }) ≤ 0 :=
      calc Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x })
          ≤ Lebesgue_outer_measure (⋃ n, E' n) := h_le
        _ ≤ ∑' n, Lebesgue_outer_measure (E' n) := h_union_le
        _ = 0 := h_sum_zero
    exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is reflexive -/
lemma AlmostEverywhereEqual.refl {d:ℕ} {X: Type*} (f: EuclideanSpace' d → X) :
    AlmostEverywhereEqual f f :=
  -- {x | f x ≠ f x} = ∅, which is null
  AlmostAlways.ofAlways (fun _ => rfl)

/-- Almost everywhere equality is symmetric -/
lemma AlmostEverywhereEqual.symm {d:ℕ} {X: Type*} {f g: EuclideanSpace' d → X}
    (h: AlmostEverywhereEqual f g) : AlmostEverywhereEqual g f := by
  -- {x | g x ≠ f x} = {x | f x ≠ g x}, same set
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  convert h using 2
  ext x
  exact ne_comm

/-- Almost everywhere equality is transitive -/
lemma AlmostEverywhereEqual.trans {d:ℕ} {X: Type*} {f g h: EuclideanSpace' d → X}
    (hfg: AlmostEverywhereEqual f g) (hgh: AlmostEverywhereEqual g h) :
    AlmostEverywhereEqual f h := by
  -- {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x}
  -- Union of two null sets is null
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  have h_subset : {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra hc
    push_neg at hc
    exact hx (hc.1.trans hc.2)
  -- Express union as ℕ-indexed union for countable subadditivity
  let E : ℕ → Set (EuclideanSpace' d) := fun n =>
    match n with
    | 0 => {x | f x ≠ g x}
    | 1 => {x | g x ≠ h x}
    | _ => ∅
  have h_union_eq : {x | f x ≠ g x} ∪ {x | g x ≠ h x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, E]
    constructor
    · intro hx
      cases hx with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      match n with
      | 0 => exact Or.inl hn
      | 1 => exact Or.inr hn
      | n + 2 => exact absurd hn (Set.notMem_empty x)
  have h_E_null : ∀ n, Lebesgue_outer_measure (E n) = 0 := fun n => by
    match n with
    | 0 => exact hfg
    | 1 => exact hgh
    | n + 2 => exact Lebesgue_outer_measure.of_empty d
  have h_sum_zero : ∑' n, Lebesgue_outer_measure (E n) = 0 := by simp only [h_E_null, tsum_zero]
  have h_union_le := Lebesgue_outer_measure.union_le E
  have h_bound : Lebesgue_outer_measure {x | f x ≠ h x} ≤ 0 :=
    calc Lebesgue_outer_measure {x | f x ≠ h x}
        ≤ Lebesgue_outer_measure (⋃ n, E n) := by rw [← h_union_eq]; exact Lebesgue_outer_measure.mono h_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_union_le
      _ = 0 := h_sum_zero
  exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is an equivalence relation -/
theorem AlmostEverywhereEqual.equivalence {d:ℕ} {X: Type*} :
    Equivalence (@AlmostEverywhereEqual d X) :=
  ⟨refl, symm, trans⟩

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) :
  (hf.add hg).integ = hf.integ + hg.integ := by
  obtain ⟨k₁, c₁, E₁, hmn₁, heq₁⟩ := id hf
  obtain ⟨k₂, c₂, E₂, hmn₂, heq₂⟩ := id hg
  -- representation of hf
  have hf_eq : hf.integ = ∑ i, (c₁ i) * Lebesgue_measure (E₁ i) :=
    hf.integral_eq (fun i => (hmn₁ i).1) (fun i => (hmn₁ i).2) heq₁
  have hg_eq : hg.integ = ∑ i, (c₂ i) * Lebesgue_measure (E₂ i) :=
    hg.integral_eq (fun i => (hmn₂ i).1) (fun i => (hmn₂ i).2) heq₂
  -- concatenated representation of f + g
  set c : Fin (k₁ + k₂) → EReal :=
    fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩ with hc
  set E : Fin (k₁ + k₂) → Set (EuclideanSpace' d) :=
    fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩ with hE
  have hmesE : ∀ i, LebesgueMeasurable (E i) := by
    intro i; simp only [hE]; split_ifs with h
    · exact (hmn₁ ⟨i, h⟩).1
    · exact (hmn₂ ⟨i - k₁, by omega⟩).1
  have hnonnegE : ∀ i, c i ≥ 0 := by
    intro i; simp only [hc]; split_ifs with h
    · exact (hmn₁ ⟨i, h⟩).2
    · exact (hmn₂ ⟨i - k₁, by omega⟩).2
  have hsum_eq : f + g = ∑ i, (c i) • (EReal.indicator (E i)) := by
    ext x
    rw [heq₁, heq₂]
    simp only [hc, hE, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_add]
    congr 1 <;> { apply Finset.sum_congr rfl; intro i _; simp [Fin.is_lt] }
  have hadd_eq : (hf.add hg).integ = ∑ i, (c i) * Lebesgue_measure (E i) :=
    (hf.add hg).integral_eq hmesE hnonnegE hsum_eq
  rw [hadd_eq, hf_eq, hg_eq, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; simp only [hc, hE, Fin.coe_castAdd, Fin.is_lt,
      dif_pos, Fin.eta]
  · apply Finset.sum_congr rfl; intro i _; simp only [hc, hE, Fin.coe_natAdd]
    rw [dif_neg (by omega : ¬ (k₁ + i.val < k₁))]
    congr 2 <;> simp

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {c:EReal} (hc: c ≥ 0) :
  (hf.smul hc).integ = c * hf.integ := by
  obtain ⟨k, c₀, E, hmn, heq⟩ := id hf
  have hf_eq : hf.integ = ∑ i, (c₀ i) * Lebesgue_measure (E i) :=
    hf.integral_eq (fun i => (hmn i).1) (fun i => (hmn i).2) heq
  have hsmul_eq : c • f = ∑ i, (c * c₀ i) • (EReal.indicator (E i)) := by
    rw [heq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k c (fun i => (c₀ i) * EReal.indicator (E i) x)
        (fun i => mul_nonneg (hmn i).2 (EReal.indicator_nonneg' (E i) x))]
    apply Finset.sum_congr rfl; intro i _; rw [mul_assoc]
  have hmesE : ∀ i, LebesgueMeasurable (E i) := fun i => (hmn i).1
  have hnonnegE : ∀ i, c * c₀ i ≥ 0 := fun i => mul_nonneg hc (hmn i).2
  have hsmul_integ : (hf.smul hc).integ = ∑ i, (c * c₀ i) * Lebesgue_measure (E i) :=
    (hf.smul hc).integral_eq hmesE hnonnegE hsmul_eq
  rw [hsmul_integ, hf_eq,
    EReal.mul_finset_sum_of_nonneg k c (fun i => (c₀ i) * Lebesgue_measure (E i))
      (fun i => mul_nonneg (hmn i).2 (Lebesgue_outer_measure.nonneg _))]
  apply Finset.sum_congr rfl; intro i _; rw [mul_assoc]

/-- A finite sum of nonnegative EReals is `< ⊤` iff each term is `< ⊤`. -/
private lemma sum_lt_top_iff_forall_nonneg {k:ℕ} (a : Fin k → EReal) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) < ⊤ ↔ ∀ i, a i < ⊤ := by
  constructor
  · intro h i
    refine Ne.lt_top (fun hi => ?_)
    have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
    rw [hi] at hle
    exact h.ne (le_antisymm le_top hle)
  · intro h
    refine Ne.lt_top (?_ : (∑ i, a i) ≠ ⊤)
    classical
    induction' (Finset.univ : Finset (Fin k)) using Finset.induction with i s his ih
    · simp
    · rw [Finset.sum_insert his]
      exact _root_.EReal.add_ne_top (h i).ne ih

/-- Exercise 1.3.1 (ii) (Finiteness) -/
lemma UnsignedSimpleFunction.integral_finite_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ < ⊤) ↔ (AlmostAlways (fun x ↦ f x < ⊤)) ∧ (Lebesgue_measure (Support f)) < ⊤ := by
  classical
  open UnsignedSimpleFunction.IntegralWellDef in
  -- Canonical representation, converted to disjoint singleAtoms.
  obtain ⟨k, c, E, hmn, heq⟩ := id hf
  set A : Fin (2^k) → Set (EuclideanSpace' d) := singleAtom E with hA
  set V : Fin (2^k) → EReal := fun n => ∑ i : Fin k, if n.val.testBit i.val then c i else 0 with hV
  -- atom values are nonnegative
  have hV_nonneg : ∀ n, 0 ≤ V n := by
    intro n; rw [hV]; apply Finset.sum_nonneg; intro i _; split_ifs
    · exact (hmn i).2
    · exact le_refl 0
  -- atoms are measurable
  have hA_meas : ∀ n, LebesgueMeasurable (A n) := by
    intro n
    simp only [hA, singleAtom]
    exact atom_measurable (fun i => (hmn i).1) (fun i => Fin.elim0 i)
      ⟨n.val, by simp only [add_zero]; exact n.isLt⟩
  -- atoms are disjoint
  have hA_disj : Set.univ.PairwiseDisjoint A := singleAtom_pairwiseDisjoint E
  -- f x = V n when x ∈ A n
  have hfx : ∀ n, ∀ x ∈ A n, f x = V n := by
    intro n x hx
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hV]
    apply Finset.sum_congr rfl
    intro i _
    have hmem := (mem_singleAtom_iff E n x).mp hx i
    by_cases hbit : n.val.testBit i.val
    · simp only [hbit, if_true]
      rw [EReal.indicator_of_mem (hmem.mp hbit), mul_one]
    · simp only [hbit, Bool.false_eq_true, if_false]
      have hxout : x ∉ E i := fun h => hbit (hmem.mpr h)
      rw [EReal.indicator_of_notMem hxout, mul_zero]
  -- disjoint representation of f
  have hfeq2 : f = ∑ n, (V n) • (EReal.indicator (A n)) := by
    ext x
    obtain ⟨n, hn_mem, hn_uniq⟩ := exists_unique_singleAtom E x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfx n x hn_mem]
    rw [Finset.sum_eq_single n]
    · rw [EReal.indicator_of_mem hn_mem, mul_one]
    · intro m _ hm
      have : x ∉ A m := fun h => hm (hn_uniq m h)
      rw [EReal.indicator_of_notMem this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  -- integral = ∑ V n * μ(A n)
  have hinteg : hf.integ = ∑ n, (V n) * Lebesgue_measure (A n) :=
    hf.integral_eq hA_meas hV_nonneg hfeq2
  -- finiteness of integral ↔ each term finite
  rw [hinteg, sum_lt_top_iff_forall_nonneg (fun n => V n * Lebesgue_measure (A n))
    (fun n => mul_nonneg (hV_nonneg n) (Lebesgue_outer_measure.nonneg _))]
  -- μ(Support f) = ∑ n, if V n ≠ 0 then μ(A n) else 0
  have hsuppmeas : Lebesgue_measure (Support f) = ∑ n, if V n ≠ 0 then Lebesgue_measure (A n) else 0 := by
    let A' : Fin (2^k) → Set (EuclideanSpace' d) := fun n => if V n ≠ 0 then A n else ∅
    have hA'_eq : Support f = ⋃ n, A' n := by
      ext x
      simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion, A']
      obtain ⟨n, hn_mem, hn_uniq⟩ := exists_unique_singleAtom E x
      constructor
      · intro hne
        refine ⟨n, ?_⟩
        have hVne : V n ≠ 0 := by rw [← hfx n x hn_mem]; exact hne
        rw [if_pos hVne]; exact hn_mem
      · intro ⟨m, hx⟩
        by_cases hVm : V m ≠ 0
        · rw [if_pos hVm] at hx
          rw [hfx m x hx]; exact hVm
        · rw [if_neg hVm] at hx; exact absurd hx (Set.notMem_empty x)
    have hA'_meas : ∀ n, LebesgueMeasurable (A' n) := by
      intro n; simp only [A']; split_ifs
      · exact hA_meas n
      · exact LebesgueMeasurable.empty
    have hA'_disj : Set.univ.PairwiseDisjoint A' := by
      intro i _ j _ hij
      simp only [Function.onFun, A']
      by_cases h1 : V i ≠ 0 <;> by_cases h2 : V j ≠ 0
      · rw [if_pos h1, if_pos h2]; exact hA_disj (Set.mem_univ i) (Set.mem_univ j) hij
      · rw [if_pos h1, if_neg h2]; rw [Set.disjoint_left]; intro _ _; simp
      · rw [if_neg h1, if_pos h2]; rw [Set.disjoint_left]; simp
      · rw [if_neg h1, if_neg h2]; rw [Set.disjoint_left]; simp
    calc Lebesgue_measure (Support f) = Lebesgue_measure (⋃ n, A' n) := by rw [hA'_eq]
      _ = ∑' n, Lebesgue_measure (A' n) := Lebesgue_measure.finite_union hA'_meas hA'_disj
      _ = ∑ n, Lebesgue_measure (A' n) := tsum_fintype _
      _ = ∑ n, if V n ≠ 0 then Lebesgue_measure (A n) else 0 := by
          apply Finset.sum_congr rfl; intro n _; show Lebesgue_measure (A' n) = _
          simp only [A']; split_ifs
          · rfl
          · exact Lebesgue_measure.empty
  rw [hsuppmeas, sum_lt_top_iff_forall_nonneg
    (fun n => if V n ≠ 0 then Lebesgue_measure (A n) else 0) (by
    intro n; dsimp only; split_ifs
    · exact Lebesgue_outer_measure.nonneg _
    · exact le_refl 0)]
  -- AlmostAlways (f < ⊤) ↔ ∀ n, V n = ⊤ → μ(A n) = 0
  have hae : AlmostAlways (fun x ↦ f x < ⊤) ↔ ∀ n, V n = ⊤ → Lebesgue_measure (A n) = 0 := by
    constructor
    · intro hall n hVtop
      -- the null set {x | ¬ f x < ⊤}; A n ⊆ it when V n = ⊤
      have hsub : A n ⊆ {x | ¬ f x < ⊤} := by
        intro x hx
        simp only [Set.mem_setOf_eq, not_lt]
        rw [hfx n x hx, hVtop]
      have hnull : IsNull (A n) := le_antisymm
        (le_trans (Lebesgue_outer_measure.mono hsub) (le_of_eq hall))
        (Lebesgue_outer_measure.nonneg _)
      exact hnull
    · intro hall
      -- {x | ¬ f x < ⊤} = ⋃ n, (if V n = ⊤ then A n else ∅), each null
      have hset : {x | ¬ (fun x ↦ f x < ⊤) x} = ⋃ n, (if V n = ⊤ then A n else ∅) := by
        ext x
        simp only [Set.mem_setOf_eq, not_lt, Set.mem_iUnion]
        obtain ⟨n, hn_mem, hn_uniq⟩ := exists_unique_singleAtom E x
        constructor
        · intro hge
          refine ⟨n, ?_⟩
          have hVtop : V n = ⊤ := by rw [hfx n x hn_mem] at hge; exact le_antisymm le_top hge
          rw [if_pos hVtop]; exact hn_mem
        · intro ⟨m, hx⟩
          by_cases hVm : V m = ⊤
          · rw [if_pos hVm] at hx
            rw [hfx m x hx, hVm]
          · rw [if_neg hVm] at hx; exact absurd hx (Set.notMem_empty x)
      show IsNull {x | ¬ (fun x ↦ f x < ⊤) x}
      rw [hset]
      have hnull_each : ∀ n, IsNull (if V n = ⊤ then A n else ∅) := by
        intro n; split_ifs with h
        · exact hall n h
        · exact Lebesgue_outer_measure.of_empty d
      -- countable (finite) union of null
      have := AlmostAlways.countable (P := fun n x => x ∉ (if V n = ⊤ then A n else ∅))
        (fun n => by
          show IsNull {x | ¬ x ∉ _}
          have : {x | ¬ x ∉ (if V n = ⊤ then A n else ∅)} = (if V n = ⊤ then A n else ∅) := by
            ext x; simp
          rw [this]; exact hnull_each n)
      show IsNull (⋃ n, (if V n = ⊤ then A n else ∅))
      have heq2 : (⋃ n, (if V n = ⊤ then A n else ∅)) = {x | ¬ ∀ n, x ∉ (if V n = ⊤ then A n else ∅)} := by
        ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_forall, not_not]
      exact heq2 ▸ this
  rw [hae]
  -- Final: combine. ∀n (V n * μ(A n) < ⊤) ↔ (∀n, V n=⊤→μ(A n)=0) ∧ (∀n, V n≠0 → μ(A n)<⊤)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n hVtop
      by_contra hμ
      have hμpos : 0 < Lebesgue_measure (A n) :=
        lt_of_le_of_ne (Lebesgue_outer_measure.nonneg _) (fun he => hμ he.symm)
      have : V n * Lebesgue_measure (A n) = ⊤ := by
        rw [EReal.mul_eq_top]; right; right; left; exact ⟨hVtop, hμpos⟩
      have hn := h n; rw [this] at hn; exact (lt_irrefl ⊤) hn
    · intro n
      split_ifs with hVne
      swap
      · exact EReal.zero_lt_top
      -- V n ≠ 0; show μ(A n) < ⊤
      refine Ne.lt_top (fun hμtop' => ?_)
      by_cases hVtop : V n = ⊤
      · have : V n * Lebesgue_measure (A n) = ⊤ := by
          rw [EReal.mul_eq_top]; right; right; left
          exact ⟨hVtop, by rw [hμtop']; exact EReal.zero_lt_top⟩
        have hn := h n; rw [this] at hn; exact (lt_irrefl ⊤) hn
      · have hVpos : 0 < V n := lt_of_le_of_ne (hV_nonneg n) (fun he => hVne he.symm)
        have : V n * Lebesgue_measure (A n) = ⊤ := by
          rw [EReal.mul_eq_top]; right; right; right
          exact ⟨hVpos, hμtop'⟩
        have hn := h n; rw [this] at hn; exact (lt_irrefl ⊤) hn
  · intro ⟨h1, h2⟩ n
    refine Ne.lt_top (?_ : V n * Lebesgue_measure (A n) ≠ ⊤)
    rw [Ne, EReal.mul_eq_top]
    push_neg
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _; exact Lebesgue_outer_measure.nonneg _
    · intro hneg; exact absurd hneg (not_lt.mpr (hV_nonneg n))
    · intro hVtop
      simp [h1 n hVtop]
    · intro hVpos
      have hVne : V n ≠ 0 := fun he => by rw [he] at hVpos; exact absurd hVpos (lt_irrefl 0)
      have := h2 n
      rw [if_pos hVne] at this
      exact this.ne

/-- Exercise 1.3.1 (iii) (Vanishing) -/
lemma UnsignedSimpleFunction.integral_eq_zero_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ = 0) ↔ AlmostAlways (fun x ↦ f x = 0) := by
  classical
  open UnsignedSimpleFunction.IntegralWellDef in
  obtain ⟨k, c, E, hmn, heq⟩ := id hf
  set A : Fin (2^k) → Set (EuclideanSpace' d) := singleAtom E with hA
  set V : Fin (2^k) → EReal := fun n => ∑ i : Fin k, if n.val.testBit i.val then c i else 0 with hV
  have hV_nonneg : ∀ n, 0 ≤ V n := by
    intro n; rw [hV]; apply Finset.sum_nonneg; intro i _; split_ifs
    · exact (hmn i).2
    · exact le_refl 0
  have hA_meas : ∀ n, LebesgueMeasurable (A n) := by
    intro n
    simp only [hA, singleAtom]
    exact atom_measurable (fun i => (hmn i).1) (fun i => Fin.elim0 i)
      ⟨n.val, by simp only [add_zero]; exact n.isLt⟩
  have hfx : ∀ n, ∀ x ∈ A n, f x = V n := by
    intro n x hx
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hV]
    apply Finset.sum_congr rfl
    intro i _
    have hmem := (mem_singleAtom_iff E n x).mp hx i
    by_cases hbit : n.val.testBit i.val
    · simp only [hbit, if_true]
      rw [EReal.indicator_of_mem (hmem.mp hbit), mul_one]
    · simp only [hbit, Bool.false_eq_true, if_false]
      rw [EReal.indicator_of_notMem (fun h => hbit (hmem.mpr h)), mul_zero]
  have hfeq2 : f = ∑ n, (V n) • (EReal.indicator (A n)) := by
    ext x
    obtain ⟨n, hn_mem, hn_uniq⟩ := exists_unique_singleAtom E x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfx n x hn_mem]
    rw [Finset.sum_eq_single n]
    · rw [EReal.indicator_of_mem hn_mem, mul_one]
    · intro m _ hm
      rw [EReal.indicator_of_notMem (fun h => hm (hn_uniq m h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  have hinteg : hf.integ = ∑ n, (V n) * Lebesgue_measure (A n) :=
    hf.integral_eq hA_meas hV_nonneg hfeq2
  -- integral = 0 iff each term = 0 iff each (V n = 0 ∨ μ(A n) = 0)
  have hsumzero : (∑ n, (V n) * Lebesgue_measure (A n) = 0) ↔ ∀ n, V n = 0 ∨ Lebesgue_measure (A n) = 0 := by
    have hkey := Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset (Fin (2^k))))
      (f := fun n => (V n) * Lebesgue_measure (A n))
      (fun n (_ : n ∈ Finset.univ) => mul_nonneg (hV_nonneg n) (Lebesgue_outer_measure.nonneg (A n)))
    rw [hkey]
    constructor
    · intro h n; exact mul_eq_zero.mp (h n (Finset.mem_univ n))
    · intro h n _; exact mul_eq_zero.mpr (h n)
  rw [hinteg, hsumzero]
  -- AlmostAlways (f = 0) iff Support f null iff ∀ n, V n = 0 ∨ μ(A n) = 0
  constructor
  · intro hall
    -- {x | ¬ f x = 0} = ⋃ n, (if V n ≠ 0 then A n else ∅), each null
    show IsNull {x | ¬ (fun x ↦ f x = 0) x}
    have hset : {x | ¬ (fun x ↦ f x = 0) x} = ⋃ n, (if V n ≠ 0 then A n else ∅) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      obtain ⟨n, hn_mem, hn_uniq⟩ := exists_unique_singleAtom E x
      constructor
      · intro hne
        refine ⟨n, ?_⟩
        have hVne : V n ≠ 0 := by rw [← hfx n x hn_mem]; exact hne
        rw [if_pos hVne]; exact hn_mem
      · intro ⟨m, hx⟩
        by_cases hVm : V m ≠ 0
        · rw [if_pos hVm] at hx; rw [hfx m x hx]; exact hVm
        · rw [if_neg hVm] at hx; exact absurd hx (Set.notMem_empty x)
    rw [hset]
    have hnull_each : ∀ n, IsNull (if V n ≠ 0 then A n else ∅) := by
      intro n; split_ifs with h
      · rcases hall n with hV0 | hμ0
        · exact absurd hV0 h
        · exact hμ0
      · exact Lebesgue_outer_measure.of_empty d
    have hcount := AlmostAlways.countable (P := fun n x => x ∉ (if V n ≠ 0 then A n else ∅))
      (fun n => by
        show IsNull {x | ¬ x ∉ _}
        have : {x | ¬ x ∉ (if V n ≠ 0 then A n else ∅)} = (if V n ≠ 0 then A n else ∅) := by
          ext x; simp
        rw [this]; exact hnull_each n)
    have heq3 : (⋃ n, (if V n ≠ 0 then A n else ∅)) = {x | ¬ ∀ n, x ∉ (if V n ≠ 0 then A n else ∅)} := by
      ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_forall, not_not]
    exact heq3 ▸ hcount
  · intro hall n
    -- if V n ≠ 0 then A n ⊆ {x | f x ≠ 0} (null), so μ(A n) = 0
    by_cases hVn : V n = 0
    · left; exact hVn
    · right
      have hsub : A n ⊆ {x | ¬ f x = 0} := by
        intro x hx
        simp only [Set.mem_setOf_eq]
        rw [hfx n x hx]; exact hVn
      exact le_antisymm
        (le_trans (Lebesgue_outer_measure.mono hsub) (le_of_eq hall))
        (Lebesgue_outer_measure.nonneg _)

/-- Exercise 1.3.1 (v) (Monotonicity) -/
lemma UnsignedSimpleFunction.integral_le_integral_of_aeLe {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostAlways (fun x ↦ f x ≤ g x)) :
  hf.integ ≤ hg.integ := by
  obtain ⟨k, c, E, hmn, heq⟩ := id hf
  obtain ⟨k', c', E', hmn', heq'⟩ := id hg
  have hf_eq : hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) :=
    hf.integral_eq (fun i => (hmn i).1) (fun i => (hmn i).2) heq
  have hg_eq : hg.integ = ∑ i, (c' i) * Lebesgue_measure (E' i) :=
    hg.integral_eq (fun i => (hmn' i).1) (fun i => (hmn' i).2) heq'
  rw [hf_eq, hg_eq]
  -- Apply the monotone core lemma with N = {x | ¬ f x ≤ g x}
  have hN : IsNull {x | ¬ f x ≤ g x} := hae
  have hcore := UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum_le_of_aeLe
    (c := c) (E := E) (c' := c') (E' := E')
    (fun i => (hmn i).1) (fun i => (hmn' i).1) (fun i => (hmn i).2) (fun i => (hmn' i).2)
    hN
    (by
      intro x hx
      simp only [Set.mem_setOf_eq, not_not] at hx
      rw [← heq, ← heq']; exact hx)
  simpa only [UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum] using hcore

/-- Exercise 1.3.1 (iv) (Equivalence) -/
lemma UnsignedSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostEverywhereEqual f g) :
  hf.integ = hg.integ := by
  apply le_antisymm
  · exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hf hg
      (hae.mp (fun x hx => le_of_eq hx))
  · exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hf
      ((AlmostEverywhereEqual.symm hae).mp (fun x hx => le_of_eq hx))

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  refine ⟨1, fun _ => 1, fun _ => E, fun i => ⟨hE, by norm_num⟩, ?_⟩
  ext x
  simp only [Function.comp_apply, Finset.univ_unique, Finset.sum_singleton, one_smul,
    Pi.smul_apply, Finset.sum_const, Finset.card_singleton]
  rfl

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E := by
  have heq : (Real.toEReal ∘ E.indicator') = ∑ _i : Fin 1, (1 : EReal) • (EReal.indicator E) := by
    ext x
    simp only [Function.comp_apply, Finset.univ_unique, Finset.sum_singleton, one_smul]
    rfl
  rw [(UnsignedSimpleFunction.indicator hE).integral_eq (fun _ => hE) (fun _ => by norm_num) heq]
  simp

lemma RealSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ :
      ∃ (n:ℕ) (v: Fin n → ℝ) (A: Fin n → Set (EuclideanSpace' d)),
        (∀ i, LebesgueMeasurable (A i)) ∧ Set.univ.PairwiseDisjoint A ∧
        f = ∑ i, (v i) • (A i).indicator' := by
    classical
    open UnsignedSimpleFunction.IntegralWellDef in
    obtain ⟨k, c, E, hmes, heq⟩ := hf
    refine ⟨2^k, UnsignedSimpleFunction.IntegralWellDef.atomValue c,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E, ?_,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E, ?_⟩
    · intro n
      simp only [UnsignedSimpleFunction.IntegralWellDef.singleAtom]
      exact UnsignedSimpleFunction.IntegralWellDef.atom_measurable hmes (fun i => Fin.elim0 i)
        ⟨n.val, by simp only [add_zero]; exact n.isLt⟩
    · rw [heq]
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have ⟨n, hn_mem, hn_unique⟩ :=
        UnsignedSimpleFunction.IntegralWellDef.exists_unique_singleAtom E x
      have hrhs : (∑ m : Fin (2^k), UnsignedSimpleFunction.IntegralWellDef.atomValue c m *
          (UnsignedSimpleFunction.IntegralWellDef.singleAtom E m).indicator' x) =
          UnsignedSimpleFunction.IntegralWellDef.atomValue c n := by
        rw [Finset.sum_eq_single n]
        · simp only [Set.indicator'_of_mem hn_mem, mul_one]
        · intro m _ hm_ne
          have hx_notin : x ∉ UnsignedSimpleFunction.IntegralWellDef.singleAtom E m :=
            fun h => hm_ne (hn_unique m h)
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ n) h
      rw [hrhs]
      have hn_mem' := (UnsignedSimpleFunction.IntegralWellDef.mem_singleAtom_iff E n x).mp hn_mem
      simp only [UnsignedSimpleFunction.IntegralWellDef.atomValue]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hbit : (n.val.testBit i.val) = true
      · simp only [hbit, ↓reduceIte]
        have hx_in : x ∈ E i := (hn_mem' i).mp hbit
        simp only [Set.indicator'_of_mem hx_in, mul_one]
      · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
        have hx_out : x ∉ E i := fun h => hbit ((hn_mem' i).mpr h)
        simp only [Set.indicator'_of_notMem hx_out, mul_zero, hbit_false, Bool.false_eq_true,
          ↓reduceIte]
  use n, fun i => (|v i|).toEReal, A
  constructor
  · intro i
    exact ⟨hA_meas i, EReal.coe_nonneg.mpr (abs_nonneg (v i))⟩
  · ext x
    simp only [EReal.abs_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx_in : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx_in
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Set.indicator'_of_mem hj, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := fun hx_in_i => by
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (|v i|).toEReal * EReal.indicator (A i) x) =
                  (|v j|).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := fun hx_in_i => by
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hrhs, hlhs]
      simp only [Real.norm_eq_abs]
    · push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Set.indicator'_of_notMem (hx_in i), mul_zero]
      have hrhs : (∑ i : Fin n, (|v i|).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hrhs, hlhs]
      simp

lemma ComplexSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  classical
  -- Convert to a disjoint representation `f = ∑ i, (w i) • (A i).indicator'`.
  obtain ⟨n, w, A, hA_meas, hA_disj, heq⟩ :
      ∃ (n:ℕ) (w: Fin n → ℂ) (A: Fin n → Set (EuclideanSpace' d)),
        (∀ i, LebesgueMeasurable (A i)) ∧ Set.univ.PairwiseDisjoint A ∧
        f = ∑ i, (w i) • (Complex.indicator (A i)) := by
    open UnsignedSimpleFunction.IntegralWellDef in
    obtain ⟨k, c, E, hmes, heq⟩ := hf
    -- complex atom value
    refine ⟨2^k, fun m => ∑ i : Fin k, if m.val.testBit i.val then c i else 0,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E, ?_,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E, ?_⟩
    · intro m
      simp only [UnsignedSimpleFunction.IntegralWellDef.singleAtom]
      exact UnsignedSimpleFunction.IntegralWellDef.atom_measurable hmes (fun i => Fin.elim0 i)
        ⟨m.val, by simp only [add_zero]; exact m.isLt⟩
    · rw [heq]
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have ⟨m, hm_mem, hm_unique⟩ :=
        UnsignedSimpleFunction.IntegralWellDef.exists_unique_singleAtom E x
      have hrhs : (∑ p : Fin (2^k), (∑ i : Fin k, if p.val.testBit i.val then c i else 0) *
          (Complex.indicator (UnsignedSimpleFunction.IntegralWellDef.singleAtom E p) x)) =
          ∑ i : Fin k, if m.val.testBit i.val then c i else 0 := by
        rw [Finset.sum_eq_single m]
        · simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hm_mem,
            Complex.ofReal_one, mul_one]
        · intro p _ hp_ne
          have hx_notin : x ∉ UnsignedSimpleFunction.IntegralWellDef.singleAtom E p :=
            fun h => hp_ne (hm_unique p h)
          simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin,
            Complex.ofReal_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ m) h
      rw [hrhs]
      have hm_mem' := (UnsignedSimpleFunction.IntegralWellDef.mem_singleAtom_iff E m x).mp hm_mem
      apply Finset.sum_congr rfl
      intro i _
      by_cases hbit : (m.val.testBit i.val) = true
      · simp only [hbit, ↓reduceIte]
        have hx_in : x ∈ E i := (hm_mem' i).mp hbit
        simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx_in,
          Complex.ofReal_one, mul_one]
      · have hbit_false : (m.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
        have hx_out : x ∉ E i := fun h => hbit ((hm_mem' i).mpr h)
        simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_out,
          Complex.ofReal_zero, mul_zero, hbit_false, Bool.false_eq_true, ↓reduceIte]
  use n, fun i => (‖w i‖).toEReal, A
  constructor
  · intro i
    exact ⟨hA_meas i, EReal.coe_nonneg.mpr (norm_nonneg (w i))⟩
  · ext x
    simp only [EReal.abs_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx_in : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx_in
      have hlhs : f x = w j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hj,
            Complex.ofReal_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := fun hx_in_i => by
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin,
            Complex.ofReal_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (‖w i‖).toEReal * EReal.indicator (A i) x) =
                  (‖w j‖).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := fun hx_in_i => by
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hrhs, hlhs]
    · push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem (hx_in i),
          Complex.ofReal_zero, mul_zero]
      have hrhs : (∑ i : Fin n, (‖w i‖).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hrhs, hlhs]
      simp

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def RealSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-! ## Disjoint representation for {name}`RealSimpleFunction`

Measure-theory specific lemmas for the disjoint representation of simple functions. -/

namespace RealSimpleFunction.DisjointRepr

open UnsignedSimpleFunction.IntegralWellDef

/-- Single atoms are measurable -/
lemma singleAtom_measurable {d k : ℕ} {E : Fin k → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (n : Fin (2^k)) :
    LebesgueMeasurable (singleAtom E n) := by
  simp only [singleAtom]
  exact atom_measurable hE (fun i => Fin.elim0 i) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- On a point in singleAtom n, the original sum equals atomValue n -/
lemma sum_indicator_eq_atomValue {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d))
    (n : Fin (2^k)) (x : EuclideanSpace' d) (hx : x ∈ singleAtom E n) :
    (∑ i : Fin k, (c i) * (E i).indicator' x) = atomValue c n := by
  simp only [atomValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [mem_singleAtom_iff] at hx
  by_cases hbit : (n.val.testBit i.val) = true
  · simp only [hbit, ↓reduceIte]
    have hx_in : x ∈ E i := (hx i).mp hbit
    simp only [Set.indicator'_of_mem hx_in, mul_one]
  · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit ((hx i).mpr h)
    simp only [Set.indicator'_of_notMem hx_out, mul_zero, hbit_false, Bool.false_eq_true,
      ↓reduceIte]

/-- The original function equals the sum over atoms with atomValue coefficients -/
lemma eq_sum_atomValue_indicator {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (E i).indicator') = ∑ n : Fin (2^k), (atomValue c n) • (singleAtom E n).indicator' := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
  have hrhs : (∑ m : Fin (2^k), atomValue c m * (singleAtom E m).indicator' x) = atomValue c n := by
    rw [Finset.sum_eq_single n]
    · simp only [Set.indicator'_of_mem hn_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ singleAtom E m := fun h => hm_ne (hn_unique m h)
      simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [hrhs]
  exact sum_indicator_eq_atomValue c E n x hn_mem

end RealSimpleFunction.DisjointRepr

/-- Disjoint representation: any {name}`RealSimpleFunction` has an equivalent representation
    with pairwise disjoint, measurable sets. -/
lemma RealSimpleFunction.disjoint_representation {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) :
    ∃ (n:ℕ) (v: Fin n → ℝ) (A: Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      f = ∑ i, (v i) • (A i).indicator' := by
  open UnsignedSimpleFunction.IntegralWellDef in
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use 2^k, UnsignedSimpleFunction.IntegralWellDef.atomValue c,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E
  refine ⟨?_, ?_, ?_⟩
  · exact fun i => DisjointRepr.singleAtom_measurable hmes i
  · exact UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E
  · rw [heq]
    exact DisjointRepr.eq_sum_atomValue_indicator c E

def RealSimpleFunction.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.pos_fun f) := by
  -- Use disjoint representation: f = ∑ i, v_i • A_i.indicator' with disjoint A_i
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  -- The positive part is ∑ i, (max(v_i, 0)).toEReal • EReal.indicator(A_i)
  use n, fun i => (max (v i) 0).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (le_max_right (v i) 0)
  · ext x
    simp only [EReal.pos_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Since atoms are disjoint, x is in at most one atom
    by_cases hx_in : ∃ j, x ∈ A j
    · -- x is in exactly one atom due to disjointness (we use exists version)
      obtain ⟨j, hj⟩ := hx_in
      -- The sum on both sides only has one nonzero term
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Set.indicator'_of_mem hj, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) =
                  (max (v j) 0).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · -- x is not in any atom, so f(x) = 0
      push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Set.indicator'_of_notMem (hx_in i), mul_zero]
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [max_self, EReal.coe_zero]

def RealSimpleFunction.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.neg_fun f) := by
  -- neg_fun f = pos_fun (-f), and -f = (-1) • f is a simple function
  have h : EReal.neg_fun f = EReal.pos_fun ((-1 : ℝ) • f) := by
    ext x; simp only [EReal.neg_fun, EReal.pos_fun, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [h]
  exact (hf.smul (-1)).pos

noncomputable def RealSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : ℝ := (hf.pos).integ.toReal - (hf.neg).integ.toReal

def ComplexSimpleFunction.re {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.re_fun f) := by
  -- If f = ∑ i, c_i • Complex.indicator(E_i), then Re(f) = ∑ i, Re(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).re, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.re_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Goal: (∑ i, c i * Complex.indicator (E i) x).re = ∑ i, (c i).re * (E i).indicator' x
    rw [Complex.re_sum]
    congr 1; ext i
    -- Goal: (c i * Complex.indicator (E i) x).re = (c i).re * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.re_mul_ofReal]

def ComplexSimpleFunction.im {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.im_fun f) := by
  -- If f = ∑ i, c_i • Complex.indicator(E_i), then Im(f) = ∑ i, Im(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).im, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.im_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Goal: (∑ i, c i * Complex.indicator (E i) x).im = ∑ i, (c i).im * (E i).indicator' x
    rw [Complex.im_sum]
    congr 1; ext i
    -- Goal: (c i * Complex.indicator (E i) x).im = (c i).im * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.im_mul_ofReal]

noncomputable def ComplexSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ℂ :=
  hf.re.integ + Complex.I * hf.im.integ

/-- The support of `|f|` equals the support of `f`, for any normed-space-valued `f`. -/
private lemma support_abs_fun_eq {d:ℕ} {Y:Type*} [RCLike Y] (f: EuclideanSpace' d → Y) :
    Support (EReal.abs_fun f) = Support f := by
  ext x
  simp only [Support, Set.mem_setOf_eq, EReal.abs_fun, ne_eq, EReal.coe_eq_zero, norm_eq_zero]

/-- `|f x| < ⊤` everywhere, for normed-space-valued `f`. -/
private lemma abs_fun_lt_top {d:ℕ} {Y:Type*} [RCLike Y] (f: EuclideanSpace' d → Y) (x : EuclideanSpace' d) :
    EReal.abs_fun f x < ⊤ := by
  simp only [EReal.abs_fun]
  exact EReal.coe_lt_top _

lemma RealSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  unfold RealSimpleFunction.AbsolutelyIntegrable
  rw [hf.abs.integral_finite_iff, support_abs_fun_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨AlmostAlways.ofAlways (fun x => abs_fun_lt_top f x), h⟩

lemma ComplexSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  unfold ComplexSimpleFunction.AbsolutelyIntegrable
  rw [hf.abs.integral_finite_iff, support_abs_fun_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨AlmostAlways.ofAlways (fun x => abs_fun_lt_top f x), h⟩

/-- Binary subadditivity of Lebesgue measure. -/
private lemma measure_union_le {d:ℕ} (A B : Set (EuclideanSpace' d)) :
    Lebesgue_measure (A ∪ B) ≤ Lebesgue_measure A + Lebesgue_measure B := by
  let E : ℕ → Set (EuclideanSpace' d) := fun n => match n with | 0 => A | 1 => B | _ => ∅
  have hunion : A ∪ B = ⋃ n, E n := by
    ext x; simp only [Set.mem_union, Set.mem_iUnion, E]
    constructor
    · intro hx; rcases hx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · intro ⟨n, hn⟩
      match n with
      | 0 => exact Or.inl hn
      | 1 => exact Or.inr hn
      | n + 2 => exact absurd hn (Set.notMem_empty x)
  have hsum : ∑' n, Lebesgue_outer_measure (E n) = Lebesgue_measure A + Lebesgue_measure B := by
    rw [tsum_eq_sum (s := {0, 1})]
    · rw [Finset.sum_pair (by norm_num : (0:ℕ) ≠ 1)]; rfl
    · intro n hn
      match n with
      | 0 => simp at hn
      | 1 => simp at hn
      | n + 2 => exact Lebesgue_outer_measure.of_empty d
  rw [hunion]
  calc Lebesgue_measure (⋃ n, E n) ≤ ∑' n, Lebesgue_outer_measure (E n) := Lebesgue_outer_measure.union_le E
    _ = Lebesgue_measure A + Lebesgue_measure B := hsum

/-- If `f + g ≠ 0` at a point, then `f ≠ 0` or `g ≠ 0` there. -/
private lemma support_add_subset {d:ℕ} {Y:Type*} [AddGroup Y] (f g : EuclideanSpace' d → Y) :
    Support (f + g) ⊆ Support f ∪ Support g := by
  intro x hx
  simp only [Support, Set.mem_setOf_eq, Set.mem_union, Pi.add_apply] at *
  by_contra hc
  push_neg at hc
  exact hx (by rw [hc.1, hc.2, add_zero])

lemma RealSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by
  rw [(hf.add hg).absolutelyIntegrable_iff]
  rw [hf.absolutelyIntegrable_iff] at hf_integ
  rw [hg.absolutelyIntegrable_iff] at hg_integ
  calc Lebesgue_measure (Support (f + g))
      ≤ Lebesgue_measure (Support f ∪ Support g) :=
        Lebesgue_outer_measure.mono (support_add_subset f g)
    _ ≤ Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := measure_union_le _ _
    _ < ⊤ := EReal.add_lt_top (ne_of_lt hf_integ) (ne_of_lt hg_integ)

lemma ComplexSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by
  rw [(hf.add hg).absolutelyIntegrable_iff]
  rw [hf.absolutelyIntegrable_iff] at hf_integ
  rw [hg.absolutelyIntegrable_iff] at hg_integ
  calc Lebesgue_measure (Support (f + g))
      ≤ Lebesgue_measure (Support f ∪ Support g) :=
        Lebesgue_outer_measure.mono (support_add_subset f g)
    _ ≤ Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := measure_union_le _ _
    _ < ⊤ := EReal.add_lt_top (ne_of_lt hf_integ) (ne_of_lt hg_integ)

lemma RealSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) :
  (hf.smul a).AbsolutelyIntegrable := by
  unfold RealSimpleFunction.AbsolutelyIntegrable at *
  have hfun : EReal.abs_fun (a • f) = ((|a| : ℝ) : EReal) • EReal.abs_fun f := by
    ext x
    simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
    rw [EReal.coe_mul]
  have habs_smul : UnsignedSimpleFunction (((|a| : ℝ) : EReal) • EReal.abs_fun f) :=
    hf.abs.smul (EReal.coe_nonneg.mpr (abs_nonneg a))
  have hcong : (hf.smul a).abs.integ = habs_smul.integ :=
    UnsignedSimpleFunction.integ_congr _ _ hfun
  rw [hcong, UnsignedSimpleFunction.integral_smul hf.abs (EReal.coe_nonneg.mpr (abs_nonneg a))]
  have hne : ((|a| : ℝ) : EReal) * hf.abs.integ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (EReal.coe_nonneg.mpr (abs_nonneg a)),
      Or.inl (EReal.coe_ne_top _), Or.inr hf_integ.ne⟩
  exact lt_of_le_of_ne le_top hne

lemma ComplexSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) :
  (hf.smul a).AbsolutelyIntegrable := by
  unfold ComplexSimpleFunction.AbsolutelyIntegrable at *
  have hfun : EReal.abs_fun (a • f) = ((‖a‖ : ℝ) : EReal) • EReal.abs_fun f := by
    ext x
    simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul]
    rw [EReal.coe_mul]
  have hcong : (hf.smul a).abs.integ = (hf.abs.smul (EReal.coe_nonneg.mpr (norm_nonneg a))).integ :=
    UnsignedSimpleFunction.integ_congr _ _ hfun
  rw [hcong, UnsignedSimpleFunction.integral_smul hf.abs (EReal.coe_nonneg.mpr (norm_nonneg a))]
  have hne : ((‖a‖ : ℝ) : EReal) * hf.abs.integ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (EReal.coe_nonneg.mpr (norm_nonneg a)),
      Or.inl (EReal.coe_ne_top _), Or.inr hf_integ.ne⟩
  exact lt_of_le_of_ne le_top hne

lemma ComplexSimpleFunction.AbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) :
  (hf.conj).AbsolutelyIntegrable := by
  unfold ComplexSimpleFunction.AbsolutelyIntegrable at *
  have hfun : EReal.abs_fun (Complex.conj_fun f) = EReal.abs_fun f := by
    ext x
    simp only [EReal.abs_fun, Complex.conj_fun, RCLike.norm_conj]
  rw [UnsignedSimpleFunction.integ_congr (hf.conj).abs hf.abs hfun]
  exact hf_integ

/-- The positive part is dominated by the absolute value (pointwise). -/
private lemma pos_fun_le_abs_fun {d:ℕ} (f: EuclideanSpace' d → ℝ) :
    ∀ x, EReal.pos_fun f x ≤ EReal.abs_fun f x := by
  intro x
  simp only [EReal.pos_fun, EReal.abs_fun, Real.norm_eq_abs, EReal.coe_le_coe_iff]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]
  · rw [max_eq_right h]; exact abs_nonneg _

private lemma neg_fun_le_abs_fun {d:ℕ} (f: EuclideanSpace' d → ℝ) :
    ∀ x, EReal.neg_fun f x ≤ EReal.abs_fun f x := by
  intro x
  simp only [EReal.neg_fun, EReal.abs_fun, Real.norm_eq_abs, EReal.coe_le_coe_iff]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_right (by linarith : -f x ≤ 0)]; exact abs_nonneg _
  · rw [max_eq_left (by linarith : 0 ≤ -f x), abs_of_nonpos h]

/-- The positive and negative parts of an absolutely integrable real simple function
have finite integrals. -/
private lemma RealSimpleFunction.pos_integ_lt_top {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f)
    (hf_integ: hf.AbsolutelyIntegrable) : hf.pos.integ < ⊤ :=
  lt_of_le_of_lt
    (UnsignedSimpleFunction.integral_le_integral_of_aeLe hf.pos hf.abs
      (AlmostAlways.ofAlways (pos_fun_le_abs_fun f))) hf_integ

private lemma RealSimpleFunction.neg_integ_lt_top {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f)
    (hf_integ: hf.AbsolutelyIntegrable) : hf.neg.integ < ⊤ :=
  lt_of_le_of_lt
    (UnsignedSimpleFunction.integral_le_integral_of_aeLe hf.neg hf.abs
      (AlmostAlways.ofAlways (neg_fun_le_abs_fun f))) hf_integ

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity) -/
lemma RealSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by
  -- Abbreviations for the six unsigned integrals (all finite).
  set Pfg := (hf.add hg).pos.integ with hPfg
  set Mfg := (hf.add hg).neg.integ with hMfg
  set Pf := hf.pos.integ with hPf
  set Mf := hf.neg.integ with hMf
  set Pg := hg.pos.integ with hPg
  set Mg := hg.neg.integ with hMg
  -- Pointwise identity: pos(f+g) + (neg f + neg g) = neg(f+g) + (pos f + pos g).
  have hpt : EReal.pos_fun (f + g) + (EReal.neg_fun f + EReal.neg_fun g)
      = EReal.neg_fun (f + g) + (EReal.pos_fun f + EReal.pos_fun g) := by
    ext x
    show (EReal.pos_fun (f+g) x) + (EReal.neg_fun f x + EReal.neg_fun g x)
       = (EReal.neg_fun (f+g) x) + (EReal.pos_fun f x + EReal.pos_fun g x)
    have hreal : max (f x + g x) 0 + (max (-f x) 0 + max (-g x) 0)
        = max (-(f x + g x)) 0 + (max (f x) 0 + max (g x) 0) := by
      rcases le_total 0 (f x) with ha | ha <;> rcases le_total 0 (g x) with hb | hb <;>
      rcases le_total 0 (f x + g x) with hab | hab <;>
      simp_all only [max_eq_left, max_eq_right, neg_nonneg, neg_nonpos] <;> ring_nf
    simp only [Pi.add_apply, EReal.pos_fun, EReal.neg_fun]
    exact_mod_cast hreal
  -- Take integrals of both sides via unsigned additivity.
  have hL : (hf.add hg).pos.integ + (hf.neg.integ + hg.neg.integ)
      = (hf.add hg).neg.integ + (hf.pos.integ + hg.pos.integ) := by
    have e1 : ((hf.add hg).pos.add (hf.neg.add hg.neg)).integ
        = ((hf.add hg).neg.add (hf.pos.add hg.pos)).integ :=
      UnsignedSimpleFunction.integ_congr ((hf.add hg).pos.add (hf.neg.add hg.neg))
        ((hf.add hg).neg.add (hf.pos.add hg.pos)) hpt
    have eL : ((hf.add hg).pos.add (hf.neg.add hg.neg)).integ
        = (hf.add hg).pos.integ + (hf.neg.integ + hg.neg.integ) := by
      rw [UnsignedSimpleFunction.integral_add (hf.add hg).pos (hf.neg.add hg.neg),
          UnsignedSimpleFunction.integral_add hf.neg hg.neg]
    have eR : ((hf.add hg).neg.add (hf.pos.add hg.pos)).integ
        = (hf.add hg).neg.integ + (hf.pos.integ + hg.pos.integ) := by
      rw [UnsignedSimpleFunction.integral_add (hf.add hg).neg (hf.pos.add hg.pos),
          UnsignedSimpleFunction.integral_add hf.pos hg.pos]
    rw [eL, eR] at e1
    exact e1
  -- All six integrals are finite; pass to reals.
  have fPfg := (hf.add hg).pos_integ_lt_top (hf_integ.add hg_integ)
  have fMfg := (hf.add hg).neg_integ_lt_top (hf_integ.add hg_integ)
  have fPf := hf.pos_integ_lt_top hf_integ
  have fMf := hf.neg_integ_lt_top hf_integ
  have fPg := hg.pos_integ_lt_top hg_integ
  have fMg := hg.neg_integ_lt_top hg_integ
  -- nonnegativity of each integral
  have nP : ∀ {h : EuclideanSpace' d → EReal} (hh : UnsignedSimpleFunction h), 0 ≤ hh.integ := by
    intro h hh
    apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (hh.choose_spec.choose_spec.choose_spec.1 i).2 (Lebesgue_outer_measure.nonneg _)
  have nb : ∀ (a : EReal), 0 ≤ a → a ≠ ⊥ := fun a ha he => by rw [he] at ha; exact absurd ha (by simp)
  -- ne_bot/ne_top facts for the six integrals
  have bPfg := nb _ (nP (hf.add hg).pos); have bMfg := nb _ (nP (hf.add hg).neg)
  have bPf := nb _ (nP hf.pos); have bMf := nb _ (nP hf.neg)
  have bPg := nb _ (nP hg.pos); have bMg := nb _ (nP hg.neg)
  -- convert hL to a real equation
  have toR : Pfg.toReal + (Mf.toReal + Mg.toReal) = Mfg.toReal + (Pf.toReal + Pg.toReal) := by
    have := congrArg EReal.toReal hL
    rw [EReal.toReal_add (ne_of_lt fPfg) bPfg
          (EReal.add_ne_top (ne_of_lt fMf) (ne_of_lt fMg))
          (nb _ (add_nonneg (nP hf.neg) (nP hg.neg))),
        EReal.toReal_add (ne_of_lt fMfg) bMfg
          (EReal.add_ne_top (ne_of_lt fPf) (ne_of_lt fPg))
          (nb _ (add_nonneg (nP hf.pos) (nP hg.pos))),
        EReal.toReal_add (ne_of_lt fMf) bMf (ne_of_lt fMg) bMg,
        EReal.toReal_add (ne_of_lt fPf) bPf (ne_of_lt fPg) bPg] at this
    exact this
  simp only [RealSimpleFunction.integ, ← hPfg, ← hMfg, ← hPf, ← hMf, ← hPg, ← hMg]
  linarith [toR]

/-- `RealSimpleFunction.integ` depends only on the function, not the membership proof,
and respects equality of functions. -/
private lemma RealSimpleFunction.integ_congr {d:ℕ} {f f': EuclideanSpace' d → ℝ}
    (hf : RealSimpleFunction f) (hf' : RealSimpleFunction f') (h : f = f') : hf.integ = hf'.integ := by
  simp only [RealSimpleFunction.integ]
  rw [UnsignedSimpleFunction.integ_congr hf.pos hf'.pos (by rw [h]),
      UnsignedSimpleFunction.integ_congr hf.neg hf'.neg (by rw [h])]

/-- Re/Im of a sum split additively (as real simple functions, up to the function). -/
private lemma ComplexSimpleFunction.re_fun_add {d:ℕ} (f g: EuclideanSpace' d → ℂ) :
    Complex.re_fun (f + g) = Complex.re_fun f + Complex.re_fun g := by
  ext x; simp only [Complex.re_fun, Pi.add_apply, Complex.add_re]

private lemma ComplexSimpleFunction.im_fun_add {d:ℕ} (f g: EuclideanSpace' d → ℂ) :
    Complex.im_fun (f + g) = Complex.im_fun f + Complex.im_fun g := by
  ext x; simp only [Complex.im_fun, Pi.add_apply, Complex.add_im]

lemma ComplexSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by
  -- absolute integrability of real/imag parts
  have hre_ai : ∀ {h : EuclideanSpace' d → ℂ} (hh : ComplexSimpleFunction h),
      hh.AbsolutelyIntegrable → hh.re.AbsolutelyIntegrable := by
    intro h hh hai
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [hh.absolutelyIntegrable_iff] at hai
    refine lt_of_le_of_lt (Lebesgue_outer_measure.mono ?_) hai
    intro x hx
    simp only [Support, Set.mem_setOf_eq, Complex.re_fun] at *
    intro hc; exact hx (by rw [hc]; simp)
  have him_ai : ∀ {h : EuclideanSpace' d → ℂ} (hh : ComplexSimpleFunction h),
      hh.AbsolutelyIntegrable → hh.im.AbsolutelyIntegrable := by
    intro h hh hai
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [hh.absolutelyIntegrable_iff] at hai
    refine lt_of_le_of_lt (Lebesgue_outer_measure.mono ?_) hai
    intro x hx
    simp only [Support, Set.mem_setOf_eq, Complex.im_fun] at *
    intro hc; exact hx (by rw [hc]; simp)
  -- re/im of f+g equal sums; reduce via Real integ_add and integ_congr
  have hre : (hf.add hg).re.integ = hf.re.integ + hg.re.integ := by
    rw [RealSimpleFunction.integ_congr (hf.add hg).re (hf.re.add hg.re)
        (ComplexSimpleFunction.re_fun_add f g),
        RealSimpleFunction.integ_add (hre_ai hf hf_integ) (hre_ai hg hg_integ)]
  have him : (hf.add hg).im.integ = hf.im.integ + hg.im.integ := by
    rw [RealSimpleFunction.integ_congr (hf.add hg).im (hf.im.add hg.im)
        (ComplexSimpleFunction.im_fun_add f g),
        RealSimpleFunction.integ_add (him_ai hf hf_integ) (him_ai hg hg_integ)]
  simp only [ComplexSimpleFunction.integ, hre, him]
  push_cast
  ring

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity) -/
lemma RealSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) : (hf.smul a).integ = a * hf.integ := by
  -- finiteness and nonnegativity of f's pos/neg integrals
  have nb : ∀ (b : EReal), 0 ≤ b → b ≠ ⊥ := fun b hb he => by rw [he] at hb; exact absurd hb (by simp)
  have nP : ∀ {h : EuclideanSpace' d → EReal} (hh : UnsignedSimpleFunction h), 0 ≤ hh.integ := by
    intro h hh
    apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (hh.choose_spec.choose_spec.choose_spec.1 i).2 (Lebesgue_outer_measure.nonneg _)
  have fPf := hf.pos_integ_lt_top hf_integ
  have fMf := hf.neg_integ_lt_top hf_integ
  -- helper: (↑c * X).toReal = c * X.toReal for finite nonneg X, c ≥ 0
  have hmul : ∀ (c : ℝ) (X : EReal), 0 ≤ c → 0 ≤ X → X < ⊤ → ((c : EReal) * X).toReal = c * X.toReal := by
    intro c X hc hX hXtop
    obtain ⟨r, hr⟩ : ∃ r : ℝ, X = (r : EReal) :=
      ⟨X.toReal, (EReal.coe_toReal (ne_of_lt hXtop) (nb X hX)).symm⟩
    rw [hr, ← EReal.coe_mul, EReal.toReal_coe, EReal.toReal_coe]
  rcases le_total 0 a with ha | ha
  · -- a ≥ 0: pos(a•f)=↑a•pos f, neg(a•f)=↑a•neg f
    have hpos : EReal.pos_fun (a • f) = (a : EReal) • EReal.pos_fun f := by
      ext x
      have hr : max (a * f x) 0 = a * max (f x) 0 := by rw [mul_max_of_nonneg _ _ ha, mul_zero]
      show EReal.pos_fun (a • f) x = (a : EReal) * EReal.pos_fun f x
      simp only [EReal.pos_fun, Pi.smul_apply, smul_eq_mul]
      rw [hr]; exact_mod_cast rfl
    have hneg : EReal.neg_fun (a • f) = (a : EReal) • EReal.neg_fun f := by
      ext x
      have hr : max (-(a * f x)) 0 = a * max (-f x) 0 := by
        rw [← mul_neg, mul_max_of_nonneg _ _ ha, mul_zero]
      show EReal.neg_fun (a • f) x = (a : EReal) * EReal.neg_fun f x
      simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
      rw [hr]; exact_mod_cast rfl
    have ePos : (hf.smul a).pos.integ = (a : EReal) * hf.pos.integ := by
      rw [UnsignedSimpleFunction.integ_congr (hf.smul a).pos (hf.pos.smul (EReal.coe_nonneg.mpr ha)) hpos,
          UnsignedSimpleFunction.integral_smul hf.pos (EReal.coe_nonneg.mpr ha)]
    have eNeg : (hf.smul a).neg.integ = (a : EReal) * hf.neg.integ := by
      rw [UnsignedSimpleFunction.integ_congr (hf.smul a).neg (hf.neg.smul (EReal.coe_nonneg.mpr ha)) hneg,
          UnsignedSimpleFunction.integral_smul hf.neg (EReal.coe_nonneg.mpr ha)]
    simp only [RealSimpleFunction.integ, ePos, eNeg]
    rw [hmul a _ ha (nP hf.pos) fPf, hmul a _ ha (nP hf.neg) fMf]
    ring
  · -- a ≤ 0: write a = -b with b ≥ 0; pos(a•f)=↑b•neg f, neg(a•f)=↑b•pos f
    obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ a = -b := ⟨-a, by linarith, by ring⟩
    have hpos : EReal.pos_fun ((-b) • f) = (b : EReal) • EReal.neg_fun f := by
      ext x
      have hr : max (-b * f x) 0 = b * max (-f x) 0 := by
        rw [mul_max_of_nonneg _ _ hb, mul_zero, mul_neg, neg_mul]
      show EReal.pos_fun ((-b) • f) x = (b : EReal) * EReal.neg_fun f x
      simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
      rw [hr]; exact_mod_cast rfl
    have hneg : EReal.neg_fun ((-b) • f) = (b : EReal) • EReal.pos_fun f := by
      ext x
      have hr : max (-(-b * f x)) 0 = b * max (f x) 0 := by
        rw [mul_max_of_nonneg _ _ hb, mul_zero, neg_mul, neg_neg]
      show EReal.neg_fun ((-b) • f) x = (b : EReal) * EReal.pos_fun f x
      simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
      rw [hr]; exact_mod_cast rfl
    have ePos : (hf.smul (-b)).pos.integ = (b : EReal) * hf.neg.integ := by
      rw [UnsignedSimpleFunction.integ_congr (hf.smul (-b)).pos (hf.neg.smul (EReal.coe_nonneg.mpr hb)) hpos,
          UnsignedSimpleFunction.integral_smul hf.neg (EReal.coe_nonneg.mpr hb)]
    have eNeg : (hf.smul (-b)).neg.integ = (b : EReal) * hf.pos.integ := by
      rw [UnsignedSimpleFunction.integ_congr (hf.smul (-b)).neg (hf.pos.smul (EReal.coe_nonneg.mpr hb)) hneg,
          UnsignedSimpleFunction.integral_smul hf.pos (EReal.coe_nonneg.mpr hb)]
    simp only [RealSimpleFunction.integ, ePos, eNeg]
    rw [hmul b _ hb (nP hf.neg) fMf, hmul b _ hb (nP hf.pos) fPf]
    ring

/-- AbsolutelyIntegrability of the real part of a complex simple function. -/
private lemma ComplexSimpleFunction.re_ai {d:ℕ} {h : EuclideanSpace' d → ℂ} (hh : ComplexSimpleFunction h)
    (hai : hh.AbsolutelyIntegrable) : hh.re.AbsolutelyIntegrable := by
  rw [RealSimpleFunction.absolutelyIntegrable_iff]
  rw [hh.absolutelyIntegrable_iff] at hai
  refine lt_of_le_of_lt (Lebesgue_outer_measure.mono ?_) hai
  intro x hx
  simp only [Support, Set.mem_setOf_eq, Complex.re_fun] at *
  intro hc; exact hx (by rw [hc]; simp)

private lemma ComplexSimpleFunction.im_ai {d:ℕ} {h : EuclideanSpace' d → ℂ} (hh : ComplexSimpleFunction h)
    (hai : hh.AbsolutelyIntegrable) : hh.im.AbsolutelyIntegrable := by
  rw [RealSimpleFunction.absolutelyIntegrable_iff]
  rw [hh.absolutelyIntegrable_iff] at hai
  refine lt_of_le_of_lt (Lebesgue_outer_measure.mono ?_) hai
  intro x hx
  simp only [Support, Set.mem_setOf_eq, Complex.im_fun] at *
  intro hc; exact hx (by rw [hc]; simp)

lemma ComplexSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) : (hf.smul a).integ = a * hf.integ := by
  -- real-simple-function pieces
  have hRf := hf.re; have hIf := hf.im
  have hRf_ai := hf.re_ai hf_integ; have hIf_ai := hf.im_ai hf_integ
  -- re_fun(a•f) = a.re • re_fun f + (-a.im) • im_fun f, pointwise
  have hre : Complex.re_fun (a • f) = a.re • Complex.re_fun f + (-a.im) • Complex.im_fun f := by
    ext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.neg_apply]
    rw [Complex.mul_re]; ring
  have him : Complex.im_fun (a • f) = a.re • Complex.im_fun f + a.im • Complex.re_fun f := by
    ext x
    simp only [Complex.im_fun, Complex.re_fun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.mul_im]
  -- integ of re(a•f)
  have eRe : (hf.smul a).re.integ = a.re * hf.re.integ + (-a.im) * hf.im.integ := by
    rw [RealSimpleFunction.integ_congr (hf.smul a).re
        ((hRf.smul a.re).add (hIf.smul (-a.im))) hre,
        RealSimpleFunction.integ_add (hRf_ai.smul a.re) (hIf_ai.smul (-a.im)),
        RealSimpleFunction.integ_smul hRf_ai, RealSimpleFunction.integ_smul hIf_ai]
  have eIm : (hf.smul a).im.integ = a.re * hf.im.integ + a.im * hf.re.integ := by
    rw [RealSimpleFunction.integ_congr (hf.smul a).im
        ((hIf.smul a.re).add (hRf.smul a.im)) him,
        RealSimpleFunction.integ_add (hIf_ai.smul a.re) (hRf_ai.smul a.im),
        RealSimpleFunction.integ_smul hIf_ai, RealSimpleFunction.integ_smul hRf_ai]
  simp only [ComplexSimpleFunction.integ, eRe, eIm]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
  · push_cast
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im]
    ring

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity) -/
lemma ComplexSimpleFunction.integral_conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) : (hf.conj).integ = (starRingEnd ℂ) hf.integ := by
  have hIf_ai := hf.im_ai hf_integ
  -- re(conj f) = re f
  have hre : Complex.re_fun (Complex.conj_fun f) = Complex.re_fun f := by
    ext x; simp only [Complex.re_fun, Complex.conj_fun, Complex.conj_re]
  -- im(conj f) = (-1) • im f
  have him : Complex.im_fun (Complex.conj_fun f) = (-1 : ℝ) • Complex.im_fun f := by
    ext x
    simp only [Complex.im_fun, Complex.conj_fun, Complex.conj_im, Pi.smul_apply, smul_eq_mul,
      neg_one_mul]
  have eRe : (hf.conj).re.integ = hf.re.integ :=
    RealSimpleFunction.integ_congr (hf.conj).re hf.re hre
  have eIm : (hf.conj).im.integ = -hf.im.integ := by
    rw [RealSimpleFunction.integ_congr (hf.conj).im (hf.im.smul (-1)) him,
        RealSimpleFunction.integ_smul hIf_ai]
    ring
  simp only [ComplexSimpleFunction.integ, eRe, eIm]
  rw [map_add, map_mul]
  push_cast
  simp [Complex.conj_I]

/-- Exercise 1.3.2 (ii) (equivalence) -/
lemma RealSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  have hpos : AlmostEverywhereEqual (EReal.pos_fun f) (EReal.pos_fun g) :=
    h_ae.mp (fun x hx => by simp only [EReal.pos_fun, hx])
  have hneg : AlmostEverywhereEqual (EReal.neg_fun f) (EReal.neg_fun g) :=
    h_ae.mp (fun x hx => by simp only [EReal.neg_fun, hx])
  have hpe := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.pos hg.pos hpos
  have hne := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.neg hg.neg hneg
  simp only [RealSimpleFunction.integ, hpe, hne]

lemma ComplexSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  -- Reduce to real/imaginary parts, then to pos/neg unsigned integrals.
  have hre_ae : AlmostEverywhereEqual (Complex.re_fun f) (Complex.re_fun g) :=
    h_ae.mp (fun x hx => by simp only [Complex.re_fun, hx])
  have him_ae : AlmostEverywhereEqual (Complex.im_fun f) (Complex.im_fun g) :=
    h_ae.mp (fun x hx => by simp only [Complex.im_fun, hx])
  have hre_eq : hf.re.integ = hg.re.integ := by
    have hpos := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.re.pos hg.re.pos
      (hre_ae.mp (fun x hx => by simp only [EReal.pos_fun, hx]))
    have hneg := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.re.neg hg.re.neg
      (hre_ae.mp (fun x hx => by simp only [EReal.neg_fun, hx]))
    simp only [RealSimpleFunction.integ, hpos, hneg]
  have him_eq : hf.im.integ = hg.im.integ := by
    have hpos := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.im.pos hg.im.pos
      (him_ae.mp (fun x hx => by simp only [EReal.pos_fun, hx]))
    have hneg := UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.im.neg hg.im.neg
      (him_ae.mp (fun x hx => by simp only [EReal.neg_fun, hx]))
    simp only [RealSimpleFunction.integ, hpos, hneg]
  simp only [ComplexSimpleFunction.integ, hre_eq, him_eq]

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma RealSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  RealSimpleFunction (E.indicator') := by
  refine ⟨1, fun _ => 1, fun _ => E, fun _ => hE, ?_⟩
  ext x
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]

lemma ComplexSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  ComplexSimpleFunction (Complex.indicator E) := by
  refine ⟨1, fun _ => 1, fun _ => E, fun _ => hE, ?_⟩
  ext x
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma RealSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (RealSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  simp only [RealSimpleFunction.integ]
  -- positive part equals the unsigned indicator
  have hpos_fun : EReal.pos_fun (E.indicator') = (Real.toEReal ∘ E.indicator') := by
    ext x
    simp only [EReal.pos_fun, Function.comp_apply]
    by_cases hx : x ∈ E
    · rw [Set.indicator'_of_mem hx]; norm_num
    · rw [Set.indicator'_of_notMem hx]; norm_num
  have hpos : (RealSimpleFunction.indicator hE).pos.integ = Lebesgue_measure E := by
    rw [UnsignedSimpleFunction.integ_congr (RealSimpleFunction.indicator hE).pos
        (UnsignedSimpleFunction.indicator hE) hpos_fun]
    exact UnsignedSimpleFunction.integral_indicator hE
  -- negative part is the zero function
  have hneg_fun : EReal.neg_fun (E.indicator') = (0:EReal) • EReal.indicator E := by
    ext x
    simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul, zero_mul]
    by_cases hx : x ∈ E
    · rw [Set.indicator'_of_mem hx]; norm_num
    · rw [Set.indicator'_of_notMem hx]; norm_num
  have hneg : (RealSimpleFunction.indicator hE).neg.integ = 0 := by
    rw [UnsignedSimpleFunction.integ_congr (RealSimpleFunction.indicator hE).neg
        ((UnsignedSimpleFunction.indicator hE).smul (le_refl (0:EReal))) hneg_fun,
        UnsignedSimpleFunction.integral_smul (UnsignedSimpleFunction.indicator hE) (le_refl (0:EReal))]
    simp
  rw [hpos, hneg]
  simp

private lemma RealSimpleFunction.integ_of_eq_zero {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealSimpleFunction f) (h: f = 0) : hf.integ = 0 := by
  simp only [RealSimpleFunction.integ]
  have hposeq : EReal.pos_fun f = (0:EReal) • (Real.toEReal ∘ (∅ : Set (EuclideanSpace' d)).indicator') := by
    ext x; simp [EReal.pos_fun, h]
  have hnegeq : EReal.neg_fun f = (0:EReal) • (Real.toEReal ∘ (∅ : Set (EuclideanSpace' d)).indicator') := by
    ext x; simp [EReal.neg_fun, h]
  have hposi : hf.pos.integ = 0 := by
    rw [UnsignedSimpleFunction.integ_congr hf.pos
        ((UnsignedSimpleFunction.indicator (d := d) (E := ∅) LebesgueMeasurable.empty).smul (le_refl (0:EReal))) hposeq,
        UnsignedSimpleFunction.integral_smul (UnsignedSimpleFunction.indicator (d := d) (E := ∅) LebesgueMeasurable.empty) (le_refl (0:EReal))]
    simp
  have hnegi : hf.neg.integ = 0 := by
    rw [UnsignedSimpleFunction.integ_congr hf.neg
        ((UnsignedSimpleFunction.indicator (d := d) (E := ∅) LebesgueMeasurable.empty).smul (le_refl (0:EReal))) hnegeq,
        UnsignedSimpleFunction.integral_smul (UnsignedSimpleFunction.indicator (d := d) (E := ∅) LebesgueMeasurable.empty) (le_refl (0:EReal))]
    simp
  rw [hposi, hnegi]; simp

lemma ComplexSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (ComplexSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  simp only [ComplexSimpleFunction.integ]
  -- real part is the real indicator, imaginary part is zero
  have hre_fun : Complex.re_fun (Complex.indicator E) = E.indicator' := by
    ext x; simp only [Complex.re_fun, Complex.indicator, Real.complex_fun, Complex.ofReal_re]
  have him_fun : Complex.im_fun (Complex.indicator E) = 0 := by
    ext x; simp only [Complex.im_fun, Complex.indicator, Real.complex_fun, Complex.ofReal_im,
      Pi.zero_apply]
  have hre : (ComplexSimpleFunction.indicator hE).re.integ = (Lebesgue_measure E).toReal := by
    rw [RealSimpleFunction.integ_congr (ComplexSimpleFunction.indicator hE).re
        (RealSimpleFunction.indicator hE) hre_fun]
    exact RealSimpleFunction.integral_indicator hE hfin
  have him : (ComplexSimpleFunction.indicator hE).im.integ = 0 :=
    RealSimpleFunction.integ_of_eq_zero (ComplexSimpleFunction.indicator hE).im him_fun
  rw [hre, him]; simp
