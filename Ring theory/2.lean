import Mathlib

/--
For any natural number $n > 1$ that divides 16, $n$ must be one of 2, 4, 8, or 16.
This characterizes all proper divisors of 16 greater than 1.
-/
lemma one_lt_dvd16 {n : ℕ} (one_lt : 1 < n) (hdvd : n ∣ 16) : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
  -- First show n is in the divisors of 16 (which are known to be {1,2,4,8,16})
  have h : n ∈ Nat.divisors 16 := by rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  simp [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at h
  -- Case analysis on possible values of n, eliminating impossible cases using 1 < n
  casesm * _ ∨ _ <;> norm_num [h] at one_lt <;> tauto
/--
For any natural number $n > 2$ that divides 16, $n$ must be one of 4, 8, or 16.
This is a refinement of `one_lt_dvd16` with a stronger lower bound.
-/
lemma two_lt_dvd16 {n : ℕ} (one_lt : 2 < n) (hdvd : n ∣ 16) : n = 4 ∨ n = 8 ∨ n = 16 := by
  -- Similar to previous lemma but with stricter inequality
  have h : n ∈ Nat.divisors 16 := by rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  simp [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at h
  casesm * _ ∨ _ <;> norm_num [h] at one_lt <;> tauto
/--
If three numbers $a,b,c > 1$ multiply to 16, they must be some permutation of (2,2,4).
This characterizes all factorizations of 16 into three integers greater than 1.
-/
theorem two_two_four_of_mul_eq_sixteen {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : a * b * c = 16) :
    (a = 2 ∧ b = 2 ∧ c = 4) ∨
    (a = 2 ∧ b = 4 ∧ c = 2) ∨
    (a = 4 ∧ b = 2 ∧ c = 2) := by
  -- First bound each variable by 16 since they divide 16
  have ha2 : a ≤ 16 := by
    have h1 : a ∣ 16 := by use b * c; linarith
    exact Nat.le_of_dvd (by norm_num) h1
  have hb2 : b ≤ 16 := by
    have h1 : b ∣ 16 := by use a * c; linarith
    exact Nat.le_of_dvd (by norm_num) h1
  have hc2 : c ≤ 16 := by
    have h1 : c ∣ 16 := by use a * b; linarith
    exact Nat.le_of_dvd (by norm_num) h1
  -- Exhaustive case analysis using interval_cases and omega for arithmetic
  interval_cases a <;> interval_cases b <;> omega
/--
If four numbers $a,b,c,d > 1$ multiply to 16, then $d$ must be 2.
This shows that in any factorization of 16 into four integers > 1, one factor must be 2.
-/
lemma eq_two_of_mul_eq_sixteen {a b c d : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (h : a * b * c * d = 16) : d = 2 := by
  -- First use one_lt_dvd16 to get possible values for d
  rcases one_lt_dvd16 hd ⟨a * b * c, by rw [← h]; ac_rfl⟩ with H | H | H | H
  . -- Case d = 2: This is our desired conclusion
    exact H
  . -- Case d = 4: Leads to contradiction since minimal product would be 2*2*2*4=32 > 16
    suffices 32 ≤ 16 by omega
    calc
      _ = 2 * 2 * 2 * 4 := by norm_num
      _ ≤ a * b * c * d := by gcongr; exact ha; exact hb; exact hc; rw[H]
      _ = 16 := h
  . -- Case d = 8: Similarly leads to contradiction (2*2*2*8=64 > 16)
    suffices 64 ≤ 16 by omega
    calc
      _ = 2 * 2 * 2 * 8 := by norm_num
      _ ≤ a * b * c * d := by gcongr; exact ha; exact hb; exact hc; rw [H]
      _ = 16 := h
  . -- Case d = 16: Also leads to contradiction (2*2*2*16=128 > 16)
    suffices 128 ≤ 16 by omega
    calc
      _ = 2 * 2 * 2 * 16 := by norm_num
      _ ≤ a * b * c * d := by gcongr; exact ha; exact hb; exact hc; rw [H]
      _ = 16 := h
/--
A direct sum over the unit type is isomorphic to its single component.
This establishes the trivial case of direct sum decomposition.
-/
def directSumAddEquivProd₁ {f : Unit → Type} [∀ i, AddCommGroup (f i)] :
    DirectSum Unit (fun i => f i) ≃+ f .unit where
  toFun := fun p => p .unit
  invFun := fun p => {
    toFun := fun b => p
    support' := Trunc.mk ⟨Finset.univ.1, fun u => by simp⟩}
  left_inv := fun _ => by ext x; simp
  right_inv := fun _ => by simp
  map_add' := by simp
/--
A direct sum over the boolean type is isomorphic to the product of its two components.
This shows how direct sums over finite index types decompose into products.
-/
def directSumAddEquivProd₂ {f : Bool → Type} [∀ i, AddCommGroup (f i)] :
    DirectSum Bool (fun i => f i) ≃+ f .false × f .true where
  toFun := fun p => (p .false, p .true)
  invFun := fun p => {
    toFun := fun b => match b with
      | .false => p.1
      | .true => p.2
    support' := Trunc.mk ⟨Finset.univ.1, fun b => by simp⟩}
  left_inv := fun _ => by
    ext x
    match x with
    | .false => simp
    | .true => simp
  right_inv := fun _ => by simp
  map_add' := by simp
/-- Custom type with three elements for demonstrating direct sum decompositions. -/
inductive Triple | a | b | c
/-- Triple is a finite type. -/
instance : Fintype Triple :=
  ⟨⟨{.a, .b, .c}, by simp⟩, fun x => by cases x <;> simp⟩
/-- Triple has exactly 3 elements. -/
lemma Fintype.card_triple : Fintype.card Triple = 3 := rfl
/--
A direct sum over Triple is isomorphic to the product of its three components.
This generalizes the previous results to a 3-element index type.
-/
def directSumAddEquivProd₃ {f : Triple → Type} [∀ i, AddCommGroup (f i)] :
    DirectSum Triple (fun i => f i) ≃+ f .a × f .b × f .c where
  toFun := fun p => (p .a, p .b, p .c)
  invFun := fun p => {
    toFun := fun t => match t with
      | .a => p.1
      | .b => p.2.1
      | .c => p.2.2
    support' := Trunc.mk ⟨Finset.univ.1, fun t => by simp⟩}
  left_inv := fun _ => by
    ext x
    match x with
    | .a => simp
    | .b => simp
    | .c => simp
  right_inv := fun _ => by simp
  map_add' := by simp
/-- Custom type with four elements for further direct sum examples. -/
inductive Quadruple | a | b | c | d
/-- Quadruple is a finite type. -/
instance : Fintype Quadruple :=
  ⟨⟨{.a, .b, .c, .d}, by simp⟩, fun x => by cases x <;> simp⟩
/-- Quadruple has exactly 4 elements. -/
lemma Fintype.card_quadruple : Fintype.card Quadruple = 4 := rfl
/--
A direct sum over Quadruple is isomorphic to the product of its four components.
This shows the general pattern for finite index types.
-/
def directSumAddEquivProd₄ {f : Quadruple → Type} [∀ i, AddCommGroup (f i)] :
    DirectSum Quadruple (fun i => f i) ≃+ f .a × f .b × f .c × f .d where
  toFun := fun p => (p .a, p .b, p .c, p .d)
  invFun := fun p => {
    toFun := fun t => match t with
      | .a => p.1
      | .b => p.2.1
      | .c => p.2.2.1
      | .d => p.2.2.2
    support' := Trunc.mk ⟨Finset.univ.1, fun t => by simp⟩}
  left_inv := fun _ => by
    ext x
    match x with
    | .a => simp
    | .b => simp
    | .c => simp
    | .d => simp
  right_inv := fun _ => by simp
  map_add' := by simp


variable {G : Type*} [AddCommGroup G]
/--
Transform a multiplicative subgroup to its additive counterpart while preserving cardinality.
This is used to convert between multiplicative and additive Sylow subgroups.
-/
@[simp] lemma card_toAddSubgroup'_sylow {p : ℕ} {P : Sylow p (Multiplicative G)} :
    (Nat.card <| Subgroup.toAddSubgroup' <| (P : Subgroup (Multiplicative G))) =
    Nat.card P := rfl
variable [Finite G]
open Classical in
/--
Classification theorem for additive abelian groups of order 16.
Any abelian group of order 16 must be isomorphic to one of:
1. The cyclic group ℤ/16ℤ
2. The product ℤ/2ℤ × ℤ/8ℤ
3. The product ℤ/4ℤ × ℤ/2ℤ × ℤ/2ℤ
4. The product (ℤ/2ℤ)^4
5. The product ℤ/4ℤ × ℤ/4ℤ
-/
theorem equiv_of_card_16 (hcard : Nat.card G = 16) :
    Nonempty (G ≃+ ZMod 16) ∨
    Nonempty (G ≃+ (ZMod 2 × ZMod 8)) ∨
    Nonempty (G ≃+ (ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 4 × ZMod 4)) := by
    -- First decompose G into a direct sum of cyclic groups using the structure theorem
    obtain ⟨ι, _, n, hn, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G

    -- Proof that the index set ι cannot be empty
    have card_pos : 0 < (Finset.univ : Finset ι).card := by
      by_contra! h
      have : Fintype.card ι = 0 := le_antisymm h (Nat.zero_le _)
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp this
      have : Unique ((i : ι) → ZMod (n i)) := Pi.uniqueOfIsEmpty _
      suffices 16 = 1 by omega
      calc
        16 = Nat.card G := hcard.symm
        _ = Nat.card ((i : ι) → ZMod (n i)) := Nat.card_congr (f.trans (DirectSum.addEquivProd _))
        _ = 1 := Nat.card_unique
    -- Proof that the index set ι has at most 4 elements
    have card_le_four : (Finset.univ : Finset ι).card ≤ 4 := by
      by_contra! h
      have cardn := Nat.card_congr (f.trans (DirectSum.addEquivProd _)).1
      rw [hcard, Nat.card_pi] at cardn
      suffices 16 < 16 by omega
      calc
        _ = 2 ^ 4 := rfl
        _ < 2 ^ (Finset.univ : Finset ι).card := by gcongr; norm_num
        _ = ∏ i : ι, 2 := by simp
        _ ≤ ∏ i : ι, Nat.card (ZMod (n i)) := by
          apply Finset.prod_le_prod
          . intro i hi; norm_num
          . intro i hi; rw [Nat.card_zmod]; apply hn
        _ = _ := cardn.symm
    -- Case analysis based on the cardinality of ι
    interval_cases hι : (Finset.univ : Finset ι).card

    -- Case 1: ι has 1 element (cyclic case)
    . have fintype_card : Fintype.card ι = 1 := hι
      have card_eq : Fintype.card ι = Fintype.card Unit := by rw [fintype_card, Fintype.card_unit]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Unit (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₁
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_zmod] at cardn
      left
      refine ⟨?_⟩
      apply x.trans
      rw [cardn]
      exact AddEquiv.refl _

    -- Case 2: ι has 2 elements (product of two cyclic groups)
    . have fintype_card : Fintype.card ι = 2 := hι
      have card_eq : Fintype.card ι = Fintype.card Bool := by rw [fintype_card, Fintype.card_bool]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Bool (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₂
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at cardn
      have ha : 1 < n (g.symm .false) := by apply hn
      have hb : 1 < n (g.symm .true) := by apply hn
      rcases one_lt_dvd16 ha (by use n (g.symm .true)) with H | H | H | H
      . right; left
        have Hb : n (g.symm .true) = 8 := by
          rw [← Nat.mul_right_inj (show 2 ≠ 0 by norm_num), show 2 * 8 = 16 by rfl, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        rw [H, Hb]
      . right;right;right;right
        have Hb : n (g.symm .true) = 4 := by
          rw [← Nat.mul_right_inj (show 4 ≠ 0 by norm_num), show 4 * 4 = 16 by rfl, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        rw [H, Hb]
      . right; left
        have Hb : n (g.symm .true) = 2 := by
          rw [← Nat.mul_right_inj (show 8 ≠ 0 by norm_num), show 8 * 2 = 16 by rfl, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        rw [H, Hb]
      . simp [H] at cardn
        rw [cardn] at hb
        contradiction

    -- Case 3: ι has 3 elements (product of three cyclic groups)
    . have fintype_card : Fintype.card ι = 3 := hι
      have card_eq : Fintype.card ι = Fintype.card Triple := by rw [fintype_card, Fintype.card_triple]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Triple (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₃
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
        eq_comm, ← mul_assoc] at cardn
      have ha : 1 < n (g.symm .a) := by apply hn
      have hb : 1 < n (g.symm .b) := by apply hn
      have hc : 1 < n (g.symm .c) := by apply hn
      have hsplit := two_two_four_of_mul_eq_sixteen ha hb hc cardn
      right; right; left
      rcases hsplit with ⟨H1, H2, H3⟩ | ⟨H4, H5, H6⟩ | ⟨H7, H8, H9⟩
      . refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        rw [H1, H2, H3]
      . refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        rw [H4, H5, H6]
      . refine ⟨?_⟩
        apply x.trans
        rw [H7, H8, H9]

    -- Case 4: ι has 4 elements (product of four cyclic groups)
    . have fintype_card : Fintype.card ι = 4 := hι
      have card_eq : Fintype.card ι = Fintype.card Quadruple := by rw [fintype_card, Fintype.card_quadruple]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Quadruple (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₄
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_prod, Nat.card_zmod,
        eq_comm, ← mul_assoc] at cardn
      simp [Nat.card_zmod] at cardn
      have ha : 1 < n (g.symm .a) := by apply hn
      have hb : 1 < n (g.symm .b) := by apply hn
      have hc : 1 < n (g.symm .c) := by apply hn
      have hd : 1 < n (g.symm .d) := by apply hn
      have haeq : n (g.symm .a) = 2 := eq_two_of_mul_eq_sixteen hd hc hb ha (by rw [← cardn]; ac_rfl)
      have hbeq : n (g.symm .b) = 2 := eq_two_of_mul_eq_sixteen hd ha hc hb (by rw [← cardn]; ac_rfl)
      have hceq : n (g.symm .c) = 2 := eq_two_of_mul_eq_sixteen hd hb ha hc (by rw [← cardn]; ac_rfl)
      have hdeq : n (g.symm .d) = 2 := eq_two_of_mul_eq_sixteen ha hb hc hd (by rw [← cardn]; ac_rfl)
      right; right; right; left
      refine ⟨?_⟩
      apply x.trans
      rw[haeq, hbeq, hceq, hdeq]


/--
For any natural number $n > 1$ that divides 625, $n$ must be one of 5, 25, 125, or 625.
This characterizes all proper divisors of 625 greater than 1.
-/
lemma one_lt_dvd625 {n : ℕ} (one_lt : 1 < n) (hdvd : n ∣ 625) : n = 5 ∨ n = 25 ∨ n = 125 ∨ n = 625 := by
  -- First show n is in the divisors of 625 (which are known to be {1,5,25,125,625})
  have h : n ∈ Nat.divisors 625 := by rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  simp [show Nat.divisors 625 = {1, 5, 25, 125, 625} by decide+native] at h
  -- Case analysis on possible values of n, eliminating impossible cases using 1 < n
  casesm * _ ∨ _ <;> norm_num [h] at one_lt <;> tauto

/--
For any natural number $n > 5$ that divides 625, $n$ must be one of 25, 125, or 625.
This is a refinement of `one_lt_dvd625` with a stronger lower bound.
-/
lemma five_lt_dvd625 {n : ℕ} (five_lt : 5 < n) (hdvd : n ∣ 625) : n = 25 ∨ n = 125 ∨ n = 625 := by
  -- Similar to previous lemma but with stricter inequality
  have h : n ∈ Nat.divisors 625 := by rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  simp [show Nat.divisors 625 = {1, 5, 25, 125, 625} by decide+native] at h
  casesm * _ ∨ _ <;> norm_num [h] at five_lt <;> tauto

/--classify the possible values of a, b, c given a * b * c = 625 and a, b, c > 1-/
theorem five_five_twentyfive_of_mul_eq_625 {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : a * b * c = 625) :
    (a = 5 ∧ b = 5 ∧ c = 25) ∨
    (a = 5 ∧ b = 25 ∧ c = 5) ∨
    (a = 25 ∧ b = 5 ∧ c = 5) := by
  -- a, b, c 都整除 625
  have ha_dvd : a ∣ 625 := ⟨b * c, by rw [←mul_assoc, h.symm]⟩
  -- b, c 同理
  have hb_dvd : b ∣ 625 := ⟨a * c, by rw [← mul_assoc, mul_comm, mul_comm b a, mul_comm]; exact h.symm⟩
  -- c 整除 625
  have hc_dvd : c ∣ 625 := ⟨a * b, by rw [mul_comm]; exact h.symm⟩

  -- 确定 a, b, c 的可能值
  have ha_cases := one_lt_dvd625 ha ha_dvd
  -- 同理 b, c
  have hb_cases := one_lt_dvd625 hb hb_dvd
  -- 同理 c
  have hc_cases := one_lt_dvd625 hc hc_dvd

  -- 枚举所有组合，用 omega 排除不满足 a*b*c=625 的情况
  rcases ha_cases with rfl | rfl | rfl | rfl
  · -- a = 5
    rcases hb_cases with rfl | rfl | rfl | rfl
    · left; omega
    · right; left; omega
    · exfalso; omega
    · exfalso; omega
  · -- a = 25
    rcases hb_cases with rfl | rfl | rfl | rfl
    · right; right; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
  · -- a = 125，则 b*c = 5
    exfalso;
    simp_all only [Nat.one_lt_ofNat]
    cases hb_cases with
    | inl h_1 =>
      cases hc_cases with
      | inl h_2 =>
        subst h_2 h_1
        simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
      | inr h_3 =>
        cases h_3 with
        | inl h_2 =>
          subst h_2 h_1
          simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_4 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_3 =>
            subst h_3 h_1
            simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
    | inr h_2 =>
      cases hc_cases with
      | inl h_1 =>
        cases h_2 with
        | inl h_3 =>
          subst h_3 h_1
          simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_4 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_3 =>
            subst h_1 h_3
            simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
      | inr h_3 =>
        cases h_2 with
        | inl h_1 =>
          cases h_3 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_4 =>
            cases h_4 with
            | inl h_2 =>
              subst h_1 h_2
              simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              subst h_1 h_3
              simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_3 with
          | inl h_1 =>
            cases h_4 with
            | inl h_2 =>
              subst h_2 h_1
              simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              subst h_3 h_1
              simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_2 =>
            cases h_4 with
            | inl h_1 =>
              cases h_2 with
              | inl h_3 =>
                subst h_1 h_3
                simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
              | inr h_4 =>
                subst h_4 h_1
                simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              cases h_2 with
              | inl h_1 =>
                subst h_1 h_3
                simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
              | inr h_4 =>
                subst h_4 h_3
                simp_all only [dvd_refl, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]  -- 但 b, c > 1，所以 b*c ≥ 4，矛盾
  · -- a = 625，则 b*c = 1
    exfalso;
    simp_all only [Nat.one_lt_ofNat, dvd_refl]
    cases hb_cases with
    | inl h_1 =>
      cases hc_cases with
      | inl h_2 =>
        subst h_2 h_1
        simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
      | inr h_3 =>
        cases h_3 with
        | inl h_2 =>
          subst h_2 h_1
          simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_4 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_3 =>
            subst h_3 h_1
            simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
    | inr h_2 =>
      cases hc_cases with
      | inl h_1 =>
        cases h_2 with
        | inl h_3 =>
          subst h_3 h_1
          simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_4 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_3 =>
            subst h_3 h_1
            simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
      | inr h_3 =>
        cases h_2 with
        | inl h_1 =>
          cases h_3 with
          | inl h_2 =>
            subst h_2 h_1
            simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_4 =>
            cases h_4 with
            | inl h_2 =>
              subst h_2 h_1
              simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              subst h_3 h_1
              simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
        | inr h_4 =>
          cases h_3 with
          | inl h_1 =>
            cases h_4 with
            | inl h_2 =>
              subst h_2 h_1
              simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              subst h_3 h_1
              simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
          | inr h_2 =>
            cases h_4 with
            | inl h_1 =>
              cases h_2 with
              | inl h_3 =>
                subst h_3 h_1
                simp_all only [Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff]
              | inr h_4 =>
                subst h_4 h_1
                simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
            | inr h_3 =>
              cases h_2 with
              | inl h_1 =>
                subst h_1 h_3
                simp_all only [Nat.one_lt_ofNat, dvd_refl, Nat.reduceMul, Nat.reduceEqDiff]
              | inr h_4 =>
                subst h_3 h_4
                simp_all only [dvd_refl, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceEqDiff] -- 但 b, c > 1，矛盾

/-- If a * b * c * d = 625 and a, b, c, d > 1, then d = 5. -/
lemma eq_five_of_mul_eq_625 {a b c d : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (h : a * b * c * d = 625) : d = 5 := by
  -- d divides 625
  have hd_dvd : d ∣ 625 := ⟨a * b * c, by rw [mul_comm]; exact h.symm⟩
  -- So d ∈ {5, 25, 125, 625}
  have hd_cases := one_lt_dvd625 hd hd_dvd
  rcases hd_cases with rfl | rfl | rfl | rfl
  · rfl  -- d = 5, done
  · -- d = 25, then a*b*c = 25
    exfalso
    have habc : a * b * c = 25 := by omega
    -- a divides 25, and 25 = 5²
    have ha_dvd : a ∣ 25 := ⟨b * c, by rw [←mul_assoc, habc]⟩
    -- So a ∈ {1,5,25}
    have ha_mem : a ∈ Nat.divisors 25 := by
      rw [Nat.mem_divisors]; exact ⟨ha_dvd, by norm_num⟩
    simp [show Nat.divisors 25 = {1, 5, 25} by decide] at ha_mem
    -- a ∈ {1, 5, 25}, but a > 1, so a ∈ {5, 25}
    cases ha_mem with
    | inl h_a => omega  -- a = 1 contradicts a > 1
    | inr ha_mem =>
      cases ha_mem with
      | inl h_a =>
      -- a = 5
        have hbc : b * c = 5 := by
          -- a * b * c = 25 and a = 5, so 5 * (b * c) = 25
          have : a * (b * c) = 25 := by rw [← mul_assoc]; exact habc
          rw [h_a] at this
          -- 5 * (b * c) = 5 * 5
          have : 5 * (b * c) = 5 * 5 := by rw [this];
          exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) this
        -- 5 is prime
        have h5_prime : Nat.Prime 5 := by norm_num
        -- So b divides 5
        have hb_dvd : b ∣ 5 := ⟨c, hbc.symm⟩
        -- Thus b ∈ {1, 5}
        have : b = 1 ∨ b = 5 := Nat.Prime.eq_one_or_self_of_dvd h5_prime b hb_dvd
        cases this with
        | inl h_b => omega
        -- b = 1 contradicts b > 1
        | inr h_b =>
        -- b = 5, so c = 1
          subst h_a h_b
          simp_all only [Nat.one_lt_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, dvd_refl,
            Nat.reduceMul, mul_one, lt_self_iff_false]
            -- contradicts c > 1
      | inr h_a =>
      -- a = 25
        have hbc : b * c = 1 := by
          -- a * b * c = 25 and a = 25, so 25 * (b * c) = 25
          have : a * (b * c) = 25 := by rw [← mul_assoc]; exact habc
          rw [h_a] at this
          -- 25 * (b * c) = 25 * 1
          have : 25 * (b * c) = 25 * 1 := by rw [this];
          exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 25) this
        have : b = 1 := Nat.eq_one_of_mul_eq_one_right hbc
        omega
        -- contradicts b > 1
  · -- d = 125, then a*b*c = 5
    exfalso
    have habc : a * b * c = 5 := by omega
    -- 5 is prime
    have h5_prime : Nat.Prime 5 := by norm_num
    -- So a divides 5
    have ha_dvd : a ∣ 5 := ⟨b * c, by rw [←mul_assoc, habc]⟩
    -- Thus a ∈ {1, 5}
    have : a = 1 ∨ a = 5 := Nat.Prime.eq_one_or_self_of_dvd h5_prime a ha_dvd
    cases this with
    | inl h_a => omega
    -- a = 1 contradicts a > 1
    | inr h_a =>
    -- a = 5, so b*c = 1
      have hbc : b * c = 1 := by
        -- a * b * c = 5 and a = 5, so 5 * (b * c) = 5
        have : a * (b * c) = 5 := by rw [← mul_assoc]; exact habc
        rw [h_a] at this
        -- 5 * (b * c) = 5 * 1
        have : 5 * (b * c) = 5 * 1 := by rw [this];
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) this
      -- b = 1 contradicts b > 1
      have : b = 1 := Nat.eq_one_of_mul_eq_one_right hbc
      omega
  · -- d = 625, then a*b*c = 1
    exfalso
    -- a, b, c > 1
    have habc : a * b * c = 1 := by omega
    -- a =1
    have : a = 1 := by
    -- from a * b * c = 1 and a, b, c > 1, we get a = 1
      have : a * (b * c) = 1 := by rw [← mul_assoc]; exact habc
      exact Nat.eq_one_of_mul_eq_one_right this
    omega



/-- If $n$ divides $25$ and greater than $1$ then $5 \leq n$. -/
lemma five_le_of_dvd_of_one_lt {n : ℕ} (hdvd : n ∣5^4) (one_lt : 1 < n) : 5 ≤ n := by
  rcases one_lt_dvd625 one_lt hdvd with h | h | h | h  <;> norm_num [h]

open Classical in
/--
Classification theorem for additive abelian groups of order 625.
Any abelian group of order 625 must be isomorphic to one of:
1. The cyclic group ℤ/625ℤ
2. The product ℤ/5ℤ × ℤ/125ℤ
3. The product ℤ/25ℤ × ℤ/5ℤ × ℤ/5ℤ
4. The product (ℤ/5ℤ)^4
5. The product ℤ/25ℤ × ℤ/25ℤ
-/
theorem equiv_of_card_625 (hcard : Nat.card G = 625) :
    Nonempty (G ≃+ ZMod 625) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 125)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5)) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 25)) := by
    -- First decompose G into a direct sum of cyclic groups using the structure theorem
    obtain ⟨ι, _, n, hn, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G

    -- Proof that the index set ι cannot be empty
    have card_pos : 0 < (Finset.univ : Finset ι).card := by
      by_contra! h
      have : Fintype.card ι = 0 := le_antisymm h (Nat.zero_le _)
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp this
      have : Unique ((i : ι) → ZMod (n i)) := Pi.uniqueOfIsEmpty _
      suffices 625 = 1 by omega
      calc
        625 = Nat.card G := hcard.symm
        _ = Nat.card ((i : ι) → ZMod (n i)) := Nat.card_congr (f.trans (DirectSum.addEquivProd _))
        _ = 1 := Nat.card_unique

    -- Proof that the index set ι has at most 4 elements
    have card_le_four : (Finset.univ : Finset ι).card ≤ 4 := by
      by_contra! h
      have cardn := Nat.card_congr (f.trans (DirectSum.addEquivProd _)).1
      rw [hcard, Nat.card_pi] at cardn
      suffices 625 < 625 by omega
      calc
        _ = 5 ^ 4 := by norm_num
        _ < 5 ^ (Finset.univ : Finset ι).card := by gcongr; norm_num
        _ = ∏ i : ι, 5 := by simp
        _ ≤ ∏ i : ι, Nat.card (ZMod (n i)) := by
          apply Finset.prod_le_prod
          . intro i hi; norm_num
          . intro i hi; rw [Nat.card_zmod];
            refine five_le_of_dvd_of_one_lt ?_ (by apply hn)
            norm_num
            rw [← Nat.card_zmod (n i), cardn]
            exact Finset.dvd_prod_of_mem (fun i ↦ Nat.card (ZMod (n i))) hi
        _ = _ := cardn.symm

    -- Case analysis based on the cardinality of ι
    interval_cases hι : (Finset.univ : Finset ι).card

    -- Case 1: ι has 1 element (cyclic case)
    . have fintype_card : Fintype.card ι = 1 := hι
      have card_eq : Fintype.card ι = Fintype.card Unit := by rw [fintype_card, Fintype.card_unit]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Unit (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₁
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_zmod] at cardn
      left
      refine ⟨?_⟩
      apply x.trans
      rw [cardn]
      exact AddEquiv.refl _

    -- Case 2: ι has 2 elements (product of two cyclic groups)
    . have fintype_card : Fintype.card ι = 2 := hι
      have card_eq : Fintype.card ι = Fintype.card Bool := by rw [fintype_card, Fintype.card_bool]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Bool (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₂
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at cardn
      have ha : 1 < n (g.symm .false) := by apply hn
      have hb : 1 < n (g.symm .true) := by apply hn
      rcases one_lt_dvd625 ha (by use n (g.symm .true)) with H | H | H | H
      . right; left
        have Hb : n (g.symm .true) = 125 := by
          rw [← Nat.mul_right_inj (show 5 ≠ 0 by norm_num), show 5 * 125 = 625 by norm_num, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        rw [H, Hb]
      . right;right;right;right
        have Hb : n (g.symm .true) = 25 := by
          rw [← Nat.mul_right_inj (show 25 ≠ 0 by norm_num), show 25 * 25 = 625 by norm_num, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        rw [H, Hb]
      . right; left
        have Hb : n (g.symm .true) = 5 := by
          rw [← Nat.mul_right_inj (show 125 ≠ 0 by norm_num), show 125 * 5 = 625 by norm_num, cardn, H]
        refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        rw [H, Hb]
      . simp [H] at cardn
        rw [cardn] at hb
        contradiction

    -- Case 3: ι has 3 elements (product of three cyclic groups)
    . have fintype_card : Fintype.card ι = 3 := hι
      have card_eq : Fintype.card ι = Fintype.card Triple := by rw [fintype_card, Fintype.card_triple]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Triple (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₃
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
        eq_comm, ← mul_assoc] at cardn
      have ha : 1 < n (g.symm .a) := by apply hn
      have hb : 1 < n (g.symm .b) := by apply hn
      have hc : 1 < n (g.symm .c) := by apply hn
      have hsplit := five_five_twentyfive_of_mul_eq_625 ha hb hc cardn
      right; right; left
      rcases hsplit with ⟨H1, H2, H3⟩ | ⟨H4, H5, H6⟩ | ⟨H7, H8, H9⟩
      . refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        rw [H1, H2, H3]
      . refine ⟨?_⟩
        apply x.trans
        apply AddEquiv.prodComm.trans
        apply AddEquiv.prodAssoc.trans
        rw [H4, H5, H6]
      . refine ⟨?_⟩
        apply x.trans
        rw [H7, H8, H9]

    -- Case 4: ι has 4 elements (product of four cyclic groups)
    . have fintype_card : Fintype.card ι = 4 := hι
      have card_eq : Fintype.card ι = Fintype.card Quadruple := by rw [fintype_card, Fintype.card_quadruple]
      rw [Fintype.card_eq] at card_eq
      rcases card_eq with ⟨g⟩
      let x : DirectSum ι (fun i : ι => ZMod (n i)) ≃+ DirectSum Quadruple (fun i => _) :=
        DirectSum.equivCongrLeft g
      let x := x.trans directSumAddEquivProd₄
      let x := f.trans x
      have cardn := Nat.card_congr x.1
      rw [hcard, Nat.card_prod, Nat.card_zmod, Nat.card_prod, Nat.card_zmod,
        eq_comm, ← mul_assoc] at cardn
      simp [Nat.card_zmod] at cardn
      have ha : 1 < n (g.symm .a) := by apply hn
      have hb : 1 < n (g.symm .b) := by apply hn
      have hc : 1 < n (g.symm .c) := by apply hn
      have hd : 1 < n (g.symm .d) := by apply hn
      have haeq : n (g.symm .a) = 5 := eq_five_of_mul_eq_625 hd hc hb ha (by rw [← cardn]; ac_rfl)
      have hbeq : n (g.symm .b) = 5 := eq_five_of_mul_eq_625 hd ha hc hb (by rw [← cardn]; ac_rfl)
      have hceq : n (g.symm .c) = 5 := eq_five_of_mul_eq_625 hd hb ha hc (by rw [← cardn]; ac_rfl)
      have hdeq : n (g.symm .d) = 5 := eq_five_of_mul_eq_625 ha hb hc hd (by rw [← cardn]; ac_rfl)
      right; right; right; left
      refine ⟨?_⟩
      apply x.trans
      rw[haeq, hbeq, hceq, hdeq]
  /-- If $H∩N=1$ and $HN=G$ where $N$ is normal in $G$ then $G$ is isomorphic to semi-direct product of $N$ by $H$. -/
noncomputable def mulEquivSemidirectProduct {G : Type*} [Group G]
    {N H : Subgroup G} (h : Subgroup.Normal N) (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤)
    {φ : H →* MulAut N} (conj : φ = MulAut.conjNormal.restrict H):
    G ≃* N ⋊[φ] H := by
  -- Let $f$ be a map from $N ⋊[φ] H$ to $G$.
  let f : N ⋊[φ] H → G := fun x => x.1 * x.2
  -- $f$ is injective.
  have inj : f.Injective := by
    intro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    -- $y1⁻¹*x1 = y2*x2⁻¹$
    have h12 : (y1 : G)⁻¹ * x1 = y2 * (x2 : G)⁻¹ := by
      rwa [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
    -- $y1⁻¹*x1$ is an element of $N∩H$.
    have h1 : (y1 : G)⁻¹ * x1 ∈ N ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mul_mem (inv_mem <| SetLike.coe_mem y1) (SetLike.coe_mem x1)
      · exact h12 ▸ mul_mem (SetLike.coe_mem y2) (inv_mem <| SetLike.coe_mem x2)
    rw [inf_eq_bot, Subgroup.mem_bot] at h1
    -- $y2*x2⁻¹=1$
    have h2 : y2 * (x2 : G)⁻¹ = 1 := h12 ▸ h1
    rw_mod_cast [inv_mul_eq_one.mp h1, mul_inv_eq_one.mp h2]
  -- $f$ is surjective.
  have surj : f.Surjective := by
    intro x
    -- There exists an element $n$ of $N$, $h$ of $H$ such that $nh=x$.
    obtain ⟨n, hN, h, hH, hyp⟩ : ∃ n ∈ N, ∃ h ∈ H, n * h = x := by
      apply Set.mem_mul.mp
      rw [← Subgroup.normal_mul, sup_eq_top]
      exact Set.mem_univ x
    use ⟨⟨n, hN⟩,⟨h, hH⟩⟩
  refine MulEquiv.ofBijective (MulHom.mk f ?_) ⟨inj, surj⟩ |>.symm
  intro _ _
  simp only [f, conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
    MonoidHom.restrict_apply, MulAut.conjNormal_apply]
  group
/-- If $N∩H=1$ where $N,H$ are normal in $G$ then $nh=hn$ where $n\in N$ and $h\in H$.-/
lemma Subgroup.comm_of_normal_and_inf_eq_bot {G : Type*} [Group G]
    (N H : Subgroup G) (hN : Subgroup.Normal N) (hH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (n : N) (h : H) :
    (n : G) * (h : G) = (h : G) * (n : G) := by
  -- $nhn⁻¹h⁻¹$ is an element of $N∩H$.
  have : (n : G) * h * (n⁻¹ : G) * (h : G)⁻¹ ∈ N ⊓ H := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · -- $nhn⁻¹h⁻¹$ is an element of $N$.
      convert mul_mem (SetLike.coe_mem n) (hN.conj_mem _ (inv_mem (SetLike.coe_mem n)) h) using 1
      group
    · -- $nhn⁻¹h⁻¹$ is an element of $H$.
      exact mul_mem (hH.conj_mem _ (SetLike.coe_mem _) _) (inv_mem (SetLike.coe_mem _))
  rwa [inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul] at this
/-- If $N∩H=1$ where $N,H$ are normal in $G$ and $NH=G$ then $G$ is isomorphic to $N×H$. -/
noncomputable def mulEquivProd {G : Type*} [Group G]
    {N H : Subgroup G} (hN : Subgroup.Normal N) (hH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤) :
    G ≃* N × H := by
  refine MulEquiv.trans (mulEquivSemidirectProduct hN inf_eq_bot sup_eq_top rfl) ?_
  -- Since $H$ is trivial $N$ acts trivial.
  have : MulAut.conjNormal.restrict H = (1 : H →* MulAut N) := by
    ext
    simp [← Subgroup.comm_of_normal_and_inf_eq_bot N H hN hH inf_eq_bot]
  exact this ▸ SemidirectProduct.mulEquivProd
/-- This is an `AddCommGroup` version of `mulEquivProd`.
If $N∩H=1$ where $N,H$ are normal in $G$ and $NH=G$ then $G$ is isomorphic to $N×H$. -/
noncomputable def addEquivProd {N H : AddSubgroup G} (inf_eq_bot : N ⊓ H = ⊥)
    (sup_eq_top : N ⊔ H = ⊤) : G ≃+ N × H :=
  AddEquiv.toMultiplicative.symm ((mulEquivProd (N := N.toSubgroup) (H := H.toSubgroup)
    -- Subgroups in abelian group are normal.
    (by exact Subgroup.normal_of_comm (AddSubgroup.toSubgroup N))
    (by exact Subgroup.normal_of_comm (AddSubgroup.toSubgroup H))
    -- Transform `inf_eq_bot` to `Multiplicative`.
    (by
      rw [show (⊥ : Subgroup (Multiplicative G)) = (⊥ : AddSubgroup G).toSubgroup by simp]
      exact (OrderIso.symm_apply_eq AddSubgroup.toSubgroup).mp inf_eq_bot)
    -- Transform `sup_eq_top` to `Multiplicative`.
    (by
      rw [show (⊤ : Subgroup (Multiplicative G)) = (⊤ : AddSubgroup G).toSubgroup by simp]
      rw [← OrderIso.symm_apply_eq AddSubgroup.toSubgroup, ← sup_eq_top]; simp)).trans
    (by exact (MulEquiv.refl (Multiplicative (↥N × ↥H))).symm))
/--
If $N$ is a subgroup of finite abelian group $G$ with $(|N|, [G:N]) = 1$,
then there exists a complement $H$ with $|H| = |G|/|N|$.
-/
lemma AddSubgroup.exists_left_complement'_of_coprime {G : Type*} [AddCommGroup G] [Finite G]
    {N : AddSubgroup G} (h : (Nat.card N).Coprime N.index) :
    ∃ H : AddSubgroup G, Nat.card H = Nat.card G / Nat.card N := by
  -- Translate the coprime condition to multiplicative subgroups
  have hco : ((Nat.card (AddSubgroup.toSubgroup N)).Coprime (AddSubgroup.toSubgroup N).index) := h
  -- Use the multiplicative version to get a complement
  obtain ⟨H, Hcompl⟩ := Subgroup.exists_left_complement'_of_coprime hco
  use AddSubgroup.toSubgroup.symm H
  -- Verify the cardinality condition
  apply Nat.eq_div_of_mul_eq_left
  . -- $|N|$ is positive since it contains at least 0
    rw [← Nat.pos_iff_ne_zero]
    exact Nat.card_pos
  . -- The product formula $|G| = |N| * |H|$ holds
    exact Hcompl.card_mul
/-- The finite type `Fin n` has exactly $n$ elements. -/
lemma Nat.card_fin (n : ℕ) : Nat.card (Fin n) = n :=
  card_eq_fintype_card (α := Fin n) ▸ Fintype.card_fin n
/--
If every fiber of $f: α → β$ has cardinality $n$, then $|α| = |β| * n$.
This is a cardinality version of the orbit-stabilizer theorem.
-/
lemma Nat.card_eq_mul_card_fiber {α β : Type*} (f : α → β) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ b : β, Nat.card {a // f a = b} = n) :
    Nat.card α = Nat.card β * n := by
  -- Construct bijections between each fiber and `Fin n`
  let φ (b : β) : {a // f a = b} ≃ Fin n := h b ▸ Nat.equivFinOfCardPos (h b ▸ hn)
  -- Construct a bijection between α and β × Fin n
  let F : α ≃ β × Fin n := {
    toFun := fun a => (f a, φ (f a) ⟨a, rfl⟩)
    invFun := fun (b, m) => ((φ b).symm m).val
    left_inv := fun a => by simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply]
    right_inv := fun (b, m) => by
      rw [Prod.mk.injEq]
      -- First component: f maps back to b
      have := ((φ b).invFun m).property
      use this
      -- Second component: φ is inverse to φ⁻¹
      have : (φ b) ((φ b).symm m) = m := (φ b).right_inv m
      convert this using 6
  }
  -- Calculate cardinalities using the bijection
  convert Nat.card_congr F using 1
  rw [Nat.card_prod, Nat.card_fin]
open scoped Pointwise in
/--
If $H ∩ K = 1$ and $|H| * |K| = |G|$, then $HK = G$.
This is a group-theoretic version of the Chinese Remainder Theorem.
-/
@[to_additive "$|H|*|K| = |HK|/|H∩K|$."] lemma Subgroup.card_prod_mul_card_meet {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    Nat.card H * Nat.card K = Nat.card (H * K : Set G) * Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Nat.card_prod]
  -- Let $f$ be a map from `H × K` to `HK`.
  let f : H × K → (H * K : Set G) := fun (h, k) => ⟨h.1 * k.1, Set.mul_mem_mul h.2 k.2⟩
  refine Nat.card_eq_mul_card_fiber f ?_ ?_
  · -- $|H∩K|$ is not $0$.
    exact Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos
  · -- Prove that every element of `HK` has $|H∩K|$ preimages.
    intro ⟨x, hx⟩
    obtain ⟨h, hh, k, hk, hhk⟩ := Set.mem_mul.mp hx
    exact Nat.card_congr {
      toFun := fun a => by
        use h⁻¹ * a.val.1.val
        refine mem_inf.mpr ⟨?_, ?_⟩
        · -- $h⁻¹*a.1$ is an element of $H$.
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) a.val.1.property
        · -- $h⁻¹*a.1$ is an element of $K$.
          convert Subgroup.mul_mem _ hk (Subgroup.inv_mem _ a.val.2.property) using 1
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, hhk]
          exact Subtype.mk.injEq .. ▸ a.property
      invFun := fun i => by
        refine ⟨⟨⟨h * i.val, ?_⟩, ⟨i.val⁻¹ * k, ?_⟩⟩, ?_⟩
        · -- $h⁻¹*i1$ is an element of $H$.
          exact Subgroup.mul_mem _ hh (mem_inf.mp i.property).left
        · -- $h⁻¹*i1$ is an element of $K$.
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_inf.mp i.property).right) hk
        · -- `f` maps $(h*i, i⁻¹*k)$ to $x$.
          rw [Subtype.mk.injEq]
          convert hhk using 1
          group
      left_inv := fun a => by
        rw [Subtype.mk.injEq, Prod.mk.injEq, Subtype.mk.injEq, Subtype.mk.injEq,
          mul_inv_cancel_left, mul_inv_rev, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul, hhk]
        exact ⟨rfl, Subtype.mk.injEq .. ▸ a.property.symm⟩
      right_inv := fun i => by simp
    }
open scoped Pointwise in
/-- If $H∩K = 1$ and $|H|*|K|=|G|$ then $HK=G$. -/
@[to_additive "If $H∩K = 1$ and $|H|*|K|=|G|$ then $HK=G$."] lemma Subgroup.prod_eq_of_inf_eq_bot_and_card {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (h1 : H ⊓ K = ⊥) (h2 : (Nat.card H) * (Nat.card K) = Nat.card G) :
    H * K = (⊤ : Set G) := by
  rw [Subgroup.card_prod_mul_card_meet H K, h1, Subgroup.card_bot, mul_one] at h2
  exact Set.eq_top_of_card_le_of_finite (Nat.le_of_eq h2.symm)
/--
For any additive abelian group $G$ with $|G| = 2^4 × 5^4 = 10000$, there exist subgroups $A$ and $B$
with $|A| = 2^4$ and $|B| = 5^4$ such that $G ≃ A × B$ as additive groups.
-/
lemma exists_addEquiv_prod_10000 {G : Type*} [AddCommGroup G] (hcard : Nat.card G = 2^4 * 5^4) :
    ∃ A : AddSubgroup G, ∃ B : AddSubgroup G, Nat.card A = 2^4 ∧ Nat.card B = 5^4 ∧
      Nonempty (G ≃+ A × B) := by
  -- Instantiate `Finite` for `G` since |G| = 10000 is finite
  have : Finite G := (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).2
  -- Instantiate `Fintype` for `G` to enable cardinality calculations
  have : Fintype G := Fintype.ofFinite G

  -- Fact that 5 is prime
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩

  -- Let Q be the Sylow 5-subgroup of G (of order 625)
  let Q : AddSubgroup G := Subgroup.toAddSubgroup' ((default : Sylow 5 (Multiplicative G)) :
    Subgroup (Multiplicative G))

  -- Proof that |Q| = 625 using Sylow theorems
  have cardQ : Nat.card Q = 5^4 := by
    simp [Q]
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ← Nat.card_eq_fintype_card, hcard]
    decide +native

  -- Proof that [G:Q] = 16 by Lagrange's theorem
  have indexQ : Q.index = 2^4 := by
    rw [← Nat.mul_right_inj (show Nat.card Q ≠ 0 by rw [cardQ]; norm_num),
      AddSubgroup.card_mul_index, hcard, cardQ]
    norm_num

  -- Notice that |Q|=625 and [G:Q]=16 are coprime (gcd(625,16)=1)
  have hco : (Nat.card Q).Coprime Q.index := by rw [cardQ, indexQ]; decide

  -- Apply Schur-Zassenhaus theorem to get a complement N for Q
  obtain ⟨N, hN⟩ := AddSubgroup.exists_left_complement'_of_coprime hco
  rw [hcard, cardQ] at hN
  norm_num at hN
  use N, Q
  refine ⟨hN, cardQ, ?_⟩

  -- Since |N|=16 and |Q|=625 are coprime, N ∩ Q = 0
  have inf_eq_bot : N ⊓ Q = ⊥ := AddSubgroup.inf_eq_bot_of_coprime (by rw [hN, cardQ]; decide)

  -- Since N+Q has order 10000, we must have N + Q = G
  have sup_eq_top : N ⊔ Q = ⊤ := by
    rw [← AddSubgroup.coe_eq_univ, AddSubgroup.normal_add]
    refine AddSubgroup.sum_eq_of_inf_eq_bot_and_card inf_eq_bot ?_
    rw [hN, cardQ, hcard]
    norm_num

  -- Prepare for the product isomorphism by commuting intersections/unions
  rw [inf_comm] at inf_eq_bot
  rw [sup_comm] at sup_eq_top

  -- Construct the isomorphism G ≃ N × Q
  refine ⟨?_⟩
  exact addEquivProd (by rw [← inf_eq_bot, inf_comm]) (by rw [← sup_eq_top, sup_comm])

/--
Classification theorem for additive abelian groups of order 10000.
Any abelian group of order 10000 = 2^4 × 5^4 must be isomorphic to one of 25 types:

For 2^4 part: {16}, {8,2}, {4,4}, {4,2,2}, {2,2,2,2}
For 5^4 part: {625}, {125,5}, {25,25}, {25,5,5}, {5,5,5,5}

This gives 5 × 5 = 25 isomorphism classes.
-/
theorem equiv_of_card_10000 (G : Type*) [AddGroup G]
    (hcomm : Std.Commutative fun x y : G => x + y) (hcard : Nat.card G = 10000) :
    Nonempty (G ≃+ (ZMod 625 × ZMod 16)) ∨
    Nonempty (G ≃+ (ZMod 625 × ZMod 8 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 625 × ZMod 4 × ZMod 4)) ∨
    Nonempty (G ≃+ (ZMod 625 × ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 625 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) ∨

    Nonempty (G ≃+ (ZMod 125 × ZMod 5 × ZMod 16)) ∨
    Nonempty (G ≃+ (ZMod 125 × ZMod 5 × ZMod 8 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 125 × ZMod 5 × ZMod 4 × ZMod 4)) ∨
    Nonempty (G ≃+ (ZMod 125 × ZMod 5 × ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 125 × ZMod 5 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) ∨

    Nonempty (G ≃+ (ZMod 25 × ZMod 25 × ZMod 16)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 25 × ZMod 8 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 25 × ZMod 4 × ZMod 4)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 25 × ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 25 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) ∨

    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5 × ZMod 16)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5 × ZMod 8 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5 × ZMod 4 × ZMod 4)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5 × ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 25 × ZMod 5 × ZMod 5 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) ∨

    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 16)) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 8 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 4 × ZMod 4)) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 4 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃+ (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) := by
  -- Verify G is finite
  have : Finite G := (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).2

  -- Instantiate `AddCommGroup` for `G` from commutativity
  let _ : AddCommGroup G := {
    __ : AddGroup G := ‹_›
    add_comm := by
      intro a b
      exact hcomm.comm _ _
  }

  -- Decompose G as A × B where |A| = 16 and |B| = 625
  obtain ⟨A, B, hA, hB, ⟨f⟩⟩ := exists_addEquiv_prod_10000 (by rw [hcard]; norm_num)

  -- Case analysis on possible structures for B (order 625 = 5^4)
  rcases equiv_of_card_625 hB with ⟨⟨xB⟩⟩ | ⟨⟨xB⟩⟩ | ⟨⟨xB⟩⟩ | ⟨⟨xB⟩⟩ | ⟨⟨xB⟩⟩

  -- When B ≃ ZMod 625
  . rcases equiv_of_card_16 hA with ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩

    -- Case 1: A ≃ ZMod 16, B ≃ ZMod 625
    . left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun (a, b) => (b, a)
        invFun := fun (b, a) => (a, b)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 2: A ≃ ZMod 8 × ZMod 2, B ≃ ZMod 625
    . right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), c) => (c, (b, a))
        invFun := fun (c, (a, b)) => ((b, a), c)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 3: A ≃ ZMod 4 × ZMod 4, B ≃ ZMod 625
    . right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, c)), d) => (d, (a, (b, c)))
        invFun := fun (d, (a, (b, c))) => ((a, (b, c)), d)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 4: A ≃ ZMod 4 × ZMod 2 × ZMod 2, B ≃ ZMod 625
    . right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, (c, d))), e) => (e, (a, (b, (c, d))))
        invFun := fun (e, (a, (b, (c, d)))) => ((a, (b, (c, d))), e)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 3: A ≃ ZMod 4 × ZMod 4, B ≃ ZMod 625
    . right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), c) => (c, (a, b))
        invFun := fun (c, (a, b)) => ((a, b), c)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }
  -- When B ≃ ZMod 125 × ZMod 5
  . rcases equiv_of_card_16 hA with ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩

    -- Case 6: A ≃ ZMod 16, B ≃ ZMod 125 × ZMod 5
    . right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun (a, (b, c)) => (c, (b, a))
        invFun := fun (b, (c, a)) => (a, (c, b))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 7: A ≃ ZMod 8 × ZMod 2, B ≃ ZMod 125 × ZMod 5
    . right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, d)) => (d, (c, (b, a)))
        invFun := fun (c, (d, (a, b))) => ((b, a), (d, c))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 8: A ≃ ZMod 4 × ZMod 4, B ≃ ZMod 125 × ZMod 5
    . right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, c)), (d, e)) => (e, (d, (a, (b, c))))
        invFun := fun (d, (e, (a, (b, c)))) => ((a, (b, c)), (e, d))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 9: A ≃ ZMod 4 × ZMod 2 × ZMod 2, B ≃ ZMod 125 × ZMod 5
    . right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, (c, d))), (e, f)) => (f, (e, (a, (b, (c, d)))))
        invFun := fun (e, (f, (a, (b, (c, d))))) => ((a, (b, (c, d))), (f, e))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 10: A ≃ ZMod 2^4, B ≃ ZMod 125 × ZMod 5
    . right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, d)) => (d, (c, (a, b)))
        invFun := fun (c, (d, (a, b))) => ((a, b), (d, c))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

  -- When B ≃ ZMod 25 × ZMod 25
  . rcases equiv_of_card_16 hA with ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩

    -- Case 11
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun (a, (b, (c, d))) => (b, (c, (d, a)))
        invFun := fun (b, (c, (d, a))) => (a, (b, (c, d)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 12
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, (d, e))) => (c, (d, (e, (b, a))))
        invFun := fun (c, (d, (e, (a, b)))) => ((b, a), (c, (d, e)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 13
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, c)), (d, (e, f))) => (d, (e, (f, (a, (b, c)))))
        invFun := fun (d, (e, (f, (a, (b, c))))) => ((a, (b, c)), (d, (e, f)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 14
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, (c, d))), (e, (f, g))) => (e, (f, (g, (a, (b, (c, d))))))
        invFun := fun (e, (f, (g, (a, (b, (c, d)))))) => ((a, (b, (c, d))), (e, (f, g)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 15
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, (d, e))) => (c, (d, (e, (a, b))))
        invFun := fun (c, (d, (e, (a, b)))) => ((a, b), (c, (d, e)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

  -- When B ≃ ZMod 25 × ZMod 5 × ZMod 5
  . rcases equiv_of_card_16 hA with ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩

    -- Case 16
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun (a, (b, (c, (d, e)))) => (b, (c, (d, (e, a))))
        invFun := fun (b, (c, (d, (e, a)))) => (a, (b, (c, (d, e))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 17
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, (d, (e, f)))) => (c, (d, (e, (f, (b, a)))))
        invFun := fun (c, (d, (e, (f, (a, b))))) => ((b, a), (c, (d, (e, f))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 18
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, c)), (d, (e, (f, g)))) => (d, (e, (f, (g, (a, (b, c))))))
        invFun := fun (d, (e, (f, (g, (a, (b, c)))))) => ((a, (b, c)), (d, (e, (f, g))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 19
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, (c, d))), (e, (f, (g, h)))) => (e, (f, (g, (h, (a, (b, (c, d)))))))
        invFun := fun (e, (f, (g, (h, (a, (b, (c, d))))))) => ((a, (b, (c, d))), (e, (f, (g, h))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 20
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, (d, (e, f)))) => (c, (d, (e, (f, (a, b)))))
        invFun := fun (c, (d, (e, (f, (a, b))))) => ((a, b), (c, (d, (e, f))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }
  -- When B ≃ ZMod 5^4
  . rcases equiv_of_card_16 hA with ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩ | ⟨⟨xA⟩⟩

    -- Case 21
    . right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun (a, (b, c)) => (b, (c, a))
        invFun := fun (b, (c, a)) => (a, (b, c))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 22
    . right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, d)) => (c, (d, (b, a)))
        invFun := fun (c, (d, (a, b))) => ((b, a), (c, d))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 23
    . right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, c)), (d, e)) => (d, (e, (a, (b, c))))
        invFun := fun (d, (e, (a, (b, c)))) => ((a, (b, c)), (d, e))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 24
    . right; right; right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, (b, (c, d))), (e, f)) => (e, (f, (a, (b, (c, d)))))
        invFun := fun (e, (f, (a, (b, (c, d))))) => ((a, (b, (c, d))), (e, f))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }

    -- Case 25
    . right; right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_⟩
      apply f.trans
      apply (AddEquiv.prodCongr xA xB).trans
      exact {
        toFun := fun ((a, b), (c, d)) => (c, (d, (a, b)))
        invFun := fun (c, (d, (a, b))) => ((a, b), (c, d))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
      }