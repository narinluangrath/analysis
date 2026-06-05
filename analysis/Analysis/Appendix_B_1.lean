import Mathlib.Tactic

/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers `ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the `OfNat` typeclass.
-/

namespace AppendixB

/- The ten digits, together with the base 10 -/
example : 0 = Nat.zero := rfl
example : 1 = (0:Nat).succ := rfl
example : 2 = (1:Nat).succ := rfl
example : 3 = (2:Nat).succ := rfl
example : 4 = (3:Nat).succ := rfl
example : 5 = (4:Nat).succ := rfl
example : 6 = (5:Nat).succ := rfl
example : 7 = (6:Nat).succ := rfl
example : 8 = (7:Nat).succ := rfl
example : 9 = (8:Nat).succ := rfl
example : 10 = (9:Nat).succ := rfl

/-- Definition B.1.1 -/
def Digit := Fin 10

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩
instance Digit.instOne : One Digit := ⟨1, by decide⟩
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val

instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)
#check (0:Digit)
#check (1:Digit)
#check (2:Digit)
#check (3:Digit)
#check (4:Digit)
#check (5:Digit)
#check (6:Digit)
#check (7:Digit)
#check (8:Digit)
#check (9:Digit)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp +decide

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr

theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  simp_all [List.ext_get_iff]

abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat, Digit.inj]; rfl

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10
#check PosintDecimal.mk' 1 [0] (by decide)

/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)

instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat

example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide

/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  decide

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk']

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind

/-- An operation implicit in the proof of Theorem B.1.4: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero

/-- `toNat` equals Horner (left-fold) evaluation of the digit list. -/
theorem PosintDecimal.toNat_eq_foldl (q : PosintDecimal) :
    q.toNat = q.digits.foldl (fun acc (d : Digit) => acc * 10 + d.toNat) 0 := by
  suffices h : ∀ (L : List Digit) (acc : ℕ),
      L.foldl (fun a (d : Digit) => a * 10 + d.toNat) acc =
      acc * 10 ^ L.length + ∑ i : Fin L.length, (L[L.length - 1 - ↑i]).toNat * 10 ^ (↑i : ℕ)
    from by simp [toNat, h q.digits 0]
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    intro acc; simp only [List.foldl_cons, List.length_cons]
    -- Decompose the Fin (t.length+1) sum: last term is a*10^|t|, rest matches the Fin t.length sum
    have : ∑ x : Fin (t.length + 1), ((a :: t)[t.length - ↑x] : ℕ) * 10 ^ (↑x : ℕ) =
        (∑ x : Fin t.length, (t[t.length - 1 - ↑x] : ℕ) * 10 ^ (↑x : ℕ)) + a * 10 ^ t.length := by
      refine (Fin.sum_univ_castSucc _).trans ?_
      congr 1 <;> grind
    grind

@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  rw [toNat_eq_foldl, toNat_eq_foldl]; simp only [append, mk']
  rw [show p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] from by
    simp [head, ← List.cons_append, List.cons_head_tail]]
  rw [List.foldl_append]; simp [List.foldl]; ring

theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk']
  rw [←p.digits.cons_head_tail p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; grind
  simp [←List.length_pos_iff]; omega

/-- Theorem B.1.4 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply n.case_strong_induction_on
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  obtain hm | hm := lt_or_ge m 9
  . apply ExistsUnique.intro (mk' (.mk (show m+1 < 10 by omega)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    obtain hdl | hdl := lt_or_ge d.digits.length 2
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by omega ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by omega
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := (m+1).mod_add_div 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by grind
  specialize hind s _ _ <;> try linarith
  choose b hb huniq using hind; simp at huniq
  apply ExistsUnique.intro (b.append (.mk hr))
  . simp [←this, hb]
  intro a ha
  obtain hal | hal := lt_or_ge a.digits.length 2
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    observe : a.digits[0].val < 10
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  observe : (b'₀:ℕ) < 10
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at *
  rw [←b'₀.mk_eq_iff hr] at hb'₀r
  rw [huniq b' this.symm, hb'₀r]

@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ q.pos).unique h rfl
  rw [h]


inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide

theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  obtain h | rfl | h := lt_trichotomy n 0
  . generalize e: -n = m
    lift m to Nat using (by omega)
    choose p hp _ using PosintDecimal.exists_unique _ (show 0 < m by omega)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (by omega); simp at h
  choose p hp _ using PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by convert Nat.rec_zero _ _

theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i

abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10

/-- Exercise B.1.1 -/
theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
  p.sum_digit q i < 10 := by
  unfold sum_digit
  have hd1 : (p.digit i : ℕ) < 10 := (p.digit i).isLt
  have hd2 : (q.digit i : ℕ) < 10 := (q.digit i).isLt
  have hc : p.carry q i ≤ 1 := by
    induction i with
    | zero => rw [carry_zero]; omega
    | succ n ih => rw [carry_succ]; split <;> omega
  split <;> omega

/-- Auxiliary: bound on a geometric-style sum of nines. -/
theorem PosintDecimal.geom_lt (n:ℕ) : ∑ i:Fin n, 9 * 10^(i:ℕ) < 10^n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 9 * 10^i)]
  have h : ∑ i ∈ Finset.range n, 9 * 10^i = 10^n - 1 := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; have : 1 ≤ 10^k := Nat.one_le_pow _ _ (by norm_num); ring_nf; omega
  rw [h]; have : 1 ≤ 10^n := Nat.one_le_pow _ _ (by norm_num); omega

/-- `toNat` written as a sum over `digit`. -/
theorem PosintDecimal.toNat_eq_sum_digit (p:PosintDecimal) :
    (p:ℕ) = ∑ i:Fin p.digits.length, (p.digit i:ℕ) * 10^(i:ℕ) := by
  show p.toNat = _
  rw [toNat]
  apply Finset.sum_congr rfl
  intro i _
  have h : (i:ℕ) < p.digits.length := i.isLt
  simp only [digit, dif_pos h]; congr 3; omega

theorem PosintDecimal.toNat_lt (p:PosintDecimal) : (p:ℕ) < 10^p.digits.length := by
  rw [toNat_eq_sum_digit]
  calc ∑ i:Fin p.digits.length, (p.digit i:ℕ) * 10^(i:ℕ)
      ≤ ∑ i:Fin p.digits.length, 9 * 10^(i:ℕ) := by
        apply Finset.sum_le_sum; intro i _
        have h2 : ((p.digit i:ℕ)) < 10 := (p.digit i).isLt; gcongr; omega
    _ < 10^p.digits.length := geom_lt _

/-- The `i`-th `digit` extracts the `i`-th base-10 digit of `toNat`. -/
theorem PosintDecimal.digit_eq_divmod (p:PosintDecimal) (i:ℕ) :
    (p.digit i : ℕ) = (p:ℕ) / 10^i % 10 := by
  by_cases hi : i < p.digits.length
  · rw [toNat_eq_sum_digit]
    set len := p.digits.length
    have hsplit : ∑ j:Fin len, (p.digit j:ℕ) * 10^(j:ℕ)
        = (∑ j ∈ Finset.range i, (p.digit j:ℕ)*10^j)
          + (p.digit i:ℕ)*10^i
          + (∑ j ∈ Finset.Ico (i+1) len, (p.digit j:ℕ)*10^j) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (p.digit j:ℕ) * 10^j) len]
      rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ len by omega)]
      rw [Finset.sum_eq_sum_Ico_succ_bot (show i < len by omega)]
      ring
    rw [hsplit]
    set A := ∑ j ∈ Finset.range i, (p.digit j:ℕ)*10^j with hA
    set B := ∑ j ∈ Finset.Ico (i+1) len, (p.digit j:ℕ)*10^j with hB
    have hAlt : A < 10^i := by
      calc A ≤ ∑ j ∈ Finset.range i, 9*10^j := by
              apply Finset.sum_le_sum; intro j _
              have : ((p.digit j:ℕ)) < 10 := (p.digit j).isLt; gcongr; omega
        _ = ∑ j:Fin i, 9*10^(j:ℕ) := (Fin.sum_univ_eq_sum_range (fun j=>9*10^j) i).symm
        _ < 10^i := geom_lt i
    have hBdvd : 10^(i+1) ∣ B := by
      apply Finset.dvd_sum; intro j hj
      simp only [Finset.mem_Ico] at hj
      exact Dvd.dvd.mul_left (pow_dvd_pow 10 hj.1) _
    obtain ⟨C, hC⟩ := hBdvd
    rw [hC]
    have hdi : (p.digit i:ℕ) < 10 := (p.digit i).isLt
    rw [show A + (p.digit i:ℕ)*10^i + 10^(i+1)*C = A + ((p.digit i:ℕ) + 10*C)*10^i from by ring]
    rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 10^i)]
    rw [Nat.div_eq_of_lt hAlt]
    omega
  · simp only [digit, dif_neg hi]
    have h1 : (p:ℕ) < 10^p.digits.length := p.toNat_lt
    have h2 : 10^p.digits.length ≤ 10^i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (p:ℕ)/10^i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le h1 h2)
    simp [this]

theorem PosintDecimal.carry_eq (p q:PosintDecimal) (i:ℕ) :
    p.carry q i = ((p:ℕ) % 10^i + (q:ℕ) % 10^i) / 10^i := by
  induction i with
  | zero => simp [carry_zero, Nat.mod_one]
  | succ n ih =>
    rw [carry_succ, digit_eq_divmod, digit_eq_divmod, ih]
    set P := (p:ℕ); set Q := (q:ℕ)
    have e1 : P % 10^(n+1) = P % 10^n + (P/10^n%10)*10^n := by
      conv_lhs => rw [pow_succ, Nat.mod_mul]
      ring
    have e2 : Q % 10^(n+1) = Q % 10^n + (Q/10^n%10)*10^n := by
      conv_lhs => rw [pow_succ, Nat.mod_mul]
      ring
    rw [e1, e2]
    have hPn : P % 10^n < 10^n := Nat.mod_lt _ (by positivity)
    have hQn : Q % 10^n < 10^n := Nat.mod_lt _ (by positivity)
    set a := P/10^n%10; set b := Q/10^n%10
    have ha : a < 10 := Nat.mod_lt _ (by norm_num)
    have hb : b < 10 := Nat.mod_lt _ (by norm_num)
    set c := (P%10^n + Q%10^n)/10^n
    have hc : c ≤ 1 := by
      simp only [c]
      have : (P%10^n + Q%10^n)/10^n < 2 := by
        apply Nat.div_lt_of_lt_mul; ring_nf; omega
      omega
    rw [show P % 10^n + a*10^n + (Q%10^n + b*10^n) = (P%10^n + Q%10^n) + (a+b)*10^n from by ring]
    rw [pow_succ]
    set S := P%10^n + Q%10^n with hS
    have hSr : S = c*10^n + S%10^n := by
      simp only [c]; conv_lhs => rw [← Nat.div_add_mod S (10^n)]
      ring
    set r := S % 10^n with hr
    have hSmod : r < 10^n := Nat.mod_lt _ (by positivity)
    rw [show S + (a+b)*10^n = r + (c+a+b)*10^n from by rw [hSr]; ring]
    have hdiv : (r + (c+a+b)*10^n)/(10^n*10) = (c+a+b)/10 := by
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity : 0 < 10^n),
          Nat.div_eq_of_lt hSmod, zero_add]
    rw [hdiv]
    rcases Nat.lt_or_ge (a+b+c) 10 with h | h
    · rw [if_pos h, Nat.div_eq_of_lt (by omega)]
    · rw [if_neg (by omega)]
      have : (c+a+b)/10 = 1 := by
        rw [Nat.div_eq_of_lt_le] <;> omega
      omega

theorem PosintDecimal.div_add_div_carry (p q:PosintDecimal) (i:ℕ) :
    ((p:ℕ)+(q:ℕ))/10^i = (p:ℕ)/10^i + (q:ℕ)/10^i + p.carry q i := by
  rw [carry_eq]
  set P := (p:ℕ); set Q := (q:ℕ)
  conv_lhs => rw [← Nat.div_add_mod P (10^i), ← Nat.div_add_mod Q (10^i)]
  rw [show 10^i*(P/10^i) + P%10^i + (10^i*(Q/10^i)+Q%10^i)
        = (P%10^i + Q%10^i) + (P/10^i + Q/10^i)*10^i from by ring]
  rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 10^i)]
  omega

/-- `sum_digit` is the `i`-th base-10 digit of `p+q`. -/
theorem PosintDecimal.sum_digit_eq (p q:PosintDecimal) (i:ℕ) :
    p.sum_digit q i = ((p:ℕ)+(q:ℕ))/10^i % 10 := by
  unfold sum_digit
  rw [digit_eq_divmod, digit_eq_divmod, div_add_div_carry]
  set P := (p:ℕ); set Q := (q:ℕ)
  have hc : p.carry q i ≤ 1 := by
    rcases i with _ | n
    · rw [carry_zero]; omega
    · rw [carry_succ]; split <;> omega
  set a := P/10^i; set b := Q/10^i; set c := p.carry q i
  have key : (a+b+c)%10 = (a%10 + b%10 + c)%10 := by omega
  rw [key]
  have ha : a%10 < 10 := Nat.mod_lt _ (by norm_num)
  have hb : b%10 < 10 := Nat.mod_lt _ (by norm_num)
  split <;> omega

/-- General base-10 digit decomposition. -/
theorem PosintDecimal.digit_decomp (L:ℕ) : ∀ (M:ℕ), M < 10^L →
    M = ∑ i ∈ Finset.range L, (M/10^i%10)*10^i := by
  induction L with
  | zero => intro M h; simp only [pow_zero, Nat.lt_one_iff] at h; simp [h]
  | succ k ih =>
    intro M h
    rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_succ, Nat.div_one, mul_one]
    have hMk : M/10 < 10^k := by
      have : (10:ℕ)^(k+1) = 10^k*10 := pow_succ 10 k
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
    have hih := ih (M/10) hMk
    have hcong : ∑ i ∈ Finset.range k, (M/(10^i*10)%10)*(10^i*10)
               = (∑ i ∈ Finset.range k, ((M/10)/10^i%10)*10^i) * 10 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [show M/(10^i*10) = M/10/10^i from by
            rw [Nat.div_div_eq_div_mul, Nat.mul_comm]]
      ring
    rw [hcong, ← hih]
    omega

/-- The index of the leading (most significant) digit of `p+q`. -/
def PosintDecimal.sum_digit_top (p q:PosintDecimal) : ℕ := Nat.log 10 ((p:ℕ)+(q:ℕ))

theorem PosintDecimal.leading_nonzero (p q:PosintDecimal) :
    p.sum_digit q (p.sum_digit_top q) ≠ 0 := by
  rw [sum_digit_eq, sum_digit_top]
  set N := (p:ℕ)+(q:ℕ)
  have hN : 0 < N := by have := p.pos; omega
  have h1 : 10^(Nat.log 10 N) ≤ N := Nat.pow_log_le_self 10 (by omega)
  have h2 : N < 10^(Nat.log 10 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hd : 1 ≤ N/10^(Nat.log 10 N) := Nat.le_div_iff_mul_le (by positivity) |>.mpr (by omega)
  have hd2 : N/10^(Nat.log 10 N) < 10 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at h2; omega
  rw [Nat.mod_eq_of_lt hd2]; omega

theorem PosintDecimal.out_of_range_eq_zero (p q:PosintDecimal) :
    ∀ i > ↑(p.sum_digit_top q), p.sum_digit q i = 0 := by
  intro i hi
  rw [sum_digit_eq, sum_digit_top] at *
  set N := (p:ℕ)+(q:ℕ)
  have h2 : N < 10^(Nat.log 10 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have : 10^(Nat.log 10 N + 1) ≤ 10^i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : N/10^i = 0 := Nat.div_eq_of_lt (by omega)
  simp [this]

def PosintDecimal.longAddition (p q : PosintDecimal) : PosintDecimal where
  digits := (List.range (p.sum_digit_top q + 1)).reverse.map
              (fun i => Digit.mk (p.sum_digit_lt q i))
  nonempty := by
    simp [List.length_pos_iff]
  nonzero := by
    rw [List.head_eq_getElem]
    simp only [List.getElem_map, List.getElem_reverse, List.length_range, List.length_map,
      List.getElem_range]
    rw [Ne, Digit.inj, Digit.toNat_mk]
    have : (p.sum_digit_top q + 1 - 1 - 0) = p.sum_digit_top q := by omega
    rw [this]
    exact p.leading_nonzero q

theorem PosintDecimal.longAddition_len (p q:PosintDecimal) :
    (p.longAddition q).digits.length = p.sum_digit_top q + 1 := by
  simp [longAddition]

theorem PosintDecimal.longAddition_digit (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i := by
  rw [digit]
  by_cases hi : i < (p.longAddition q).digits.length
  · rw [dif_pos hi]
    rw [longAddition_len] at hi
    simp only [longAddition, List.getElem_map, List.getElem_reverse, List.length_range,
      List.length_map, List.getElem_range, Digit.toNat_mk, List.length_reverse]
    congr 1
    omega
  · rw [dif_neg hi]
    rw [longAddition_len] at hi
    have : p.sum_digit q i = 0 := p.out_of_range_eq_zero q i (by omega)
    rw [this]; rfl

theorem PosintDecimal.longAddition_toNat (p q:PosintDecimal) :
    (p.longAddition q:ℕ) = (p:ℕ)+(q:ℕ) := by
  rw [toNat_eq_sum_digit, longAddition_len]
  set N := (p:ℕ)+(q:ℕ)
  have hNlt : N < 10^(p.sum_digit_top q + 1) := by
    rw [sum_digit_top]; exact Nat.lt_pow_succ_log_self (by norm_num) N
  rw [digit_decomp _ N hNlt]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((p.longAddition q).digit i:ℕ)*10^i)]
  apply Finset.sum_congr rfl; intro i _
  rw [longAddition_digit, sum_digit_eq]

theorem PosintDecimal.sum_eq (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i ∧ (p.longAddition q:ℕ) = p + q := by
  exact ⟨p.longAddition_digit q i, p.longAddition_toNat q⟩
