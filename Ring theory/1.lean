import Mathlib

open Ideal
variable {R : Type*} [CommRing R]
/--
If `M` is a maximal ideal and `b ∉ M`, then there exists `c : R`
such that `b * c - 1 ∈ M`.
-/
lemma exists_mul_sub_one_mem_of_maximal
    {M : Ideal R} (hM : M.IsMaximal) {b : R} (hb : b ∉ M) :
    ∃ c : R, b * c - 1 ∈ M := by
  -- `R ⧸ M` is a field.
  have hfield : IsField (R ⧸ M) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient M).mp hM
  -- Supply the field instance for type-class search.
  let π : R →+* R ⧸ M := Ideal.Quotient.mk M
  -- The canonical quotient map.
  -- `π b ≠ 0` since `b ∉ M`.
  have hb_ne : (π b) ≠ 0 := by
    intro h
    exact hb ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  -- Inverse of `π b` in the field.
  obtain ⟨u, hu⟩ := hfield.mul_inv_cancel hb_ne
  -- Pick a representative `c` of `u`.
  obtain ⟨c, rfl⟩ := Quot.exists_rep u
  -- From `π b * u = 1` get `π (b * c) = 1`.
  have hbc : (π (b * c) : R ⧸ M) = 1 := by
    simpa [RingHom.map_mul] using hu
  -- Therefore `π (b * c - 1) = 0`, so the difference lies in `M`.
  have h_mem : b * c - 1 ∈ M := by
    -- Since π(b * c) = 1, this shows π(b * c - 1) = 1 - 1 = 0.
    have : (π (b * c - 1) : R ⧸ M) = 0 := by
      simp [RingHom.map_sub, RingHom.map_one, hbc]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this
  exact ⟨c, h_mem⟩
/--
2. If the result holds for all $r<n$, let $r=n$, with $u p_{1} \ldots p_{n} \in I$, hence $p_{1} \ldots p_{n} \in$ I. Since $p_{1}$ is prime, $\left\langle p_{1}\right\rangle$ is a prime ideal, necessarily maximal by hypothesis. $R\left\langle p_{1}\right\rangle$ is a field. If $b$ belongs to $I$ but not to $\left\langle p_{1}\right\rangle$, show that for some $c \in R$ we have $b c-1 \in\left\langle p_{1}\right\rangle$.
-/
theorem exists_mul_sub_one_mem_span
    {p₁ b : R}
    (hmax : (Ideal.span ({p₁} : Set R)).IsMaximal)
    (hb   : b ∉ Ideal.span ({p₁} : Set R)) :
    ∃ c : R, b * c - 1 ∈ Ideal.span ({p₁} : Set R) := by
  simpa using
    exists_mul_sub_one_mem_of_maximal (R := R)
      (M := Ideal.span ({p₁} : Set R)) hmax hb
variable (R : Type _) [CommRing R] (I : Ideal R)
/--1. If $r=0$, show that $I=\langle 1\rangle=R$.-/
theorem ideal_with_unit_eq_top (h : ∃ u : R, IsUnit u ∧ u ∈ I) : I = ⊤ := by
  -- Unpack the existential hypothesis: get the unit u and its properties
  rcases h with ⟨u, hu, huI⟩
  -- Rewrite the goal I=⊤ to proving 1∈I (by definition of an ideal being the whole ring)
  rw [Ideal.eq_top_iff_one]
  -- Use the unit property to obtain v, the multiplicative inverse of u (v*u = 1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  -- Rewrite the goal 1 as v*u using the inverse property
  rw [←hv]
  -- Since u ∈ I and I is an ideal, for any r ∈ R we have r*u ∈ I.
  -- Specifically when r=v, we get v*u ∈ I which equals 1
  exact I.mul_mem_left v huI

/-- If `p₁ * pRest ∈ I`, `b ∈ I`, `b ∉ ⟨p₁⟩`, and `b c − 1 ∈ ⟨p₁⟩`, then `pRest ∈ I`. -/
theorem product_rest_mem_of_outside_span
    {I : Ideal R} {p₁ pRest b c : R}
    (hp_prod : p₁ * pRest ∈ I)
    (hb     : b ∈ I)
    (hbc    : b * c - 1 ∈ Ideal.span ({p₁} : Set R)) :
    pRest ∈ I := by
  -- Write `b * c - 1 = t * p₁`.
  rcases Ideal.mem_span_singleton.1 hbc with ⟨t, ht⟩
  -- Rearrange to `b * c = 1 + t * p₁`.
  have h_eq : b * c = 1 + t * p₁ := by
    -- Rewrite as (b * c - 1) + 1.
    have : b * c = (b * c - 1) + 1 := by ring
    rw [this, ht]
    ring
  -- Show `b * c ∈ I`.
  have hbc_mem : b * c ∈ I := by
    -- Because `b ∈ I` and ideals are closed under scalar multiplication.
    rw [mul_comm]
    exact I.smul_mem c hb
  -- Show `b * c * pRest ∈ I`.
  have h₁ : b * c * pRest ∈ I := by
    -- Multiplying `b * c ∈ I` by `pRest`.
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using I.smul_mem pRest hbc_mem
  -- Show `t * p₁ * pRest ∈ I`.
  have h₂ : t * p₁ * pRest ∈ I := by
    -- Multiplying `p₁ * pRest ∈ I` by `t`.
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using I.smul_mem t hp_prod
  -- Compute the difference equals `pRest`.
  have h_diff_eq : b * c * pRest - t * p₁ * pRest = pRest := by
    -- Expand using `h_eq` and simplify.
    calc
      b * c * pRest - t * p₁ * pRest
          = (1 + t * p₁) * pRest - t * p₁ * pRest := by simp [h_eq]
      _ = 1 * pRest + t * p₁ * pRest - t * p₁ * pRest := by ring
      _ = pRest := by ring
  -- The difference belongs to `I`.
  have : b * c * pRest - t * p₁ * pRest ∈ I :=
    I.sub_mem h₁ h₂
  -- Conclude `pRest ∈ I`.
  simpa [h_diff_eq] using this
/-- If `p₁ * pRest ∈ I` and `pRest ∉ I`, then every element of `I` lies in ⟨p₁⟩. -/
lemma subset_span_singleton_of_minimal
    {I : Ideal R} {p₁ pRest : R}
    -- `p₁⋯pₙ ∈ I`
    (hp_prod   : p₁ * pRest ∈ I)
    -- minimality: `p₂⋯pₙ ∉ I`
    (hpRest_not : pRest ∉ I)
    -- p₁ is prime
    (hp₁_prime : Prime p₁)
    -- given condition
    (h_max : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal)
    : I ≤ Ideal.span ({p₁} : Set R) := by
  intro x hxI
  by_cases hxSpan : x ∈ Ideal.span ({p₁} : Set R)
  · exact hxSpan
  ·
    -- Show that ⟨p₁⟩ is maximal because it is nonzero prime.
    have hp₁_max : (Ideal.span ({p₁} : Set R)).IsMaximal := by
      apply h_max
      · -- Prove ⟨p₁⟩ is prime.
        rw [Ideal.span_singleton_prime hp₁_prime.ne_zero]
        exact hp₁_prime
      · -- Show ⟨p₁⟩ ≠ ⊥.
        rw [ne_eq, span_singleton_eq_bot]
        exact hp₁_prime.ne_zero
    -- Since x ∉ ⟨p₁⟩, get c with x * c - 1 ∈ ⟨p₁⟩.
    have : pRest ∈ I := by
      obtain ⟨c, hc⟩ := exists_mul_sub_one_mem_of_maximal hp₁_max hxSpan
      -- Applying the key lemma to deduce pRest ∈ I.
      exact product_rest_mem_of_outside_span hp_prod hxI hc
    -- Contradicts pRest ∉ I.
    exact (hpRest_not this).elim
/-- If `I` contains `p₁ * ps.prod` but not `ps.prod`, then `I ⊆ ⟨p₁⟩`. -/
lemma ideal_subset_prime_span_of_minimal_factorization
    {I : Ideal R} {p₁ : R} {ps : List R}
    (hp₁_prime : Prime p₁)
    (h_in_I : p₁ * ps.prod ∈ I)
    -- minimality condition
    (h_minimal : ps.prod ∉ I)
    (h_max : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal) :
    I ≤ Ideal.span ({p₁} : Set R) := by
  exact subset_span_singleton_of_minimal h_in_I h_minimal hp₁_prime h_max
/-- If an ideal contains a product of primes with minimal factorization, it is contained in the span of the first prime. -/
theorem ideal_subset_span_of_minimal_prime_product
    (h_max : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal)
    {I : Ideal R}
    {n : ℕ} (hn_pos : n > 0)
    {p₁ : R} {ps : List R}
    (hp₁_prime : Prime p₁)
    (hps_primes : ∀ p ∈ ps, Prime p)
    (h_in_I : p₁ * ps.prod ∈ I)
    (h_length : ps.length = n - 1)
    (h_minimal : ∀ m < n, ∀ q : R, (∃ qs : List R, qs.length = m ∧
                                   (∀ q ∈ qs, Prime q) ∧ q = qs.prod) → q ∉ I) :
    I ≤ Ideal.span ({p₁} : Set R) := by
  -- ps.prod has length n-1 < n, so by minimality ps.prod ∉ I
  have h_not_in : ps.prod ∉ I := by
    -- Show that ps.prod does not belong to I by minimality assumption.
    apply h_minimal (n - 1) (Nat.sub_lt hn_pos zero_lt_one) ps.prod
    use ps
  -- Apply the main result
  exact subset_span_singleton_of_minimal h_in_I h_not_in hp₁_prime h_max
open Ideal
open scoped Classical
variable {R : Type*} [CommRing R]
/-! ### Two tiny helper lemmas -/
/-- `⟨a⟩ * ⟨b⟩ = ⟨ab⟩`. -/
lemma span_singleton_mul_singleton (a b : R) :
    Ideal.span ({a} : Set R) * Ideal.span ({b} : Set R) =
    Ideal.span ({a * b} : Set R) := by
  -- This follows directly from the `Mathlib` lemma for products of principal ideals.
  simpa using Ideal.span_singleton_mul_span_singleton a b
/-- An ideal that contains `1` is `⊤`, and conversely. -/
lemma one_mem_ideal_iff_top (J : Ideal R) : (1 : R) ∈ J ↔ J = ⊤ := by
  constructor
  · intro h1
    rw[Ideal.eq_top_iff_one]
    exact h1
  · intro hJ
    simp [hJ]
/-! ### The quotient ideal `J = I / p₁` -/
/-- The ideal `{ x | x * p ∈ I }`. -/
def quotientIdeal (I : Ideal R) (p : R) : Ideal R :=
{ carrier   := {x | x * p ∈ I},
  zero_mem' := by simp,
  add_mem'  := by
    intro a b ha hb
    change (a + b) * p ∈ I
    simpa [add_mul] using I.add_mem ha hb,
  smul_mem' := by
    intro c x hx
    change (c * x) * p ∈ I
    simpa [mul_comm, mul_left_comm, mul_assoc] using I.mul_mem_left c hx }


/-- Notation `I / p` for the ideal `{ x | x * p ∈ I }`. -/
notation:75 I " / " p => quotientIdeal I p
/-- `(I / p) * ⟨p⟩ = I` provided `I ⊆ ⟨p⟩`. -/
lemma quotientIdeal_mul_singleton
    {I : Ideal R} {p : R}
    (hI : I ≤ Ideal.span ({p} : Set R)) :
    (I / p) * Ideal.span ({p} : Set R) = I := by
  ext x
  constructor
  · intro hx
    rcases Ideal.mem_mul_span_singleton.1 hx with ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    -- Since `I ⊆ ⟨p⟩`, `x ∈ ⟨p⟩`.
    have h1 : x ∈ span {p} := hI hx
    -- So `p ∣ x`.
    have h2 : p ∣ x := Ideal.mem_span_singleton.1 h1
    -- Write `x = p * y`.
    obtain ⟨y, h3⟩ := dvd_iff_exists_eq_mul_left.1 h2
    -- Show `y ∈ I / p`, i.e., `y * p ∈ I`.
    have hy_in_quot : y ∈ I / p := by
      simp only [quotientIdeal, Set.mem_setOf_eq]
      rwa [h3] at hx
    -- So `x` belongs to the product ideal.
    rw [Ideal.mem_mul_span_singleton]
    exact ⟨y, hy_in_quot, h3.symm⟩
/-! ## Problem 6 – main induction step -/
/-- 6. Since $p_{1} \ldots p_{n}=\left(p_{2} \ldots p_{n}\right) p_{1} \in I$, we have $p_{2} \ldots p_{n} \in J$. Use the induction hypothesis to conclude that $I$ is principal. -/
theorem inductionStep
    -- The ideal we want to show is principal
    {I : Ideal R}
    -- Minimal length
    {n : ℕ} (hn : 0 < n)
    -- The first prime factor
    {p₁ : R} (hp₁ : Prime p₁)
    {ps : List R}
    -- So `p₁ :: ps` has length `n`
    (hlen : ps.length = n - 1)
    -- Every factor is prime
    (hpr : ∀ p ∈ ps, Prime p)
    -- The product belongs to `I`
    (hprod : p₁ * ps.prod ∈ I)
    -- We have `I ⊆ ⟨p₁⟩`
    (hI_le : I ≤ Ideal.span ({p₁} : Set R))
    -- Global minimality assumption for `I`
    (hmin :
      ∀ m, m < n →
        ∀ q : R, (∃ qs : List R,
                    qs.length = m ∧ (∀ r ∈ qs, Prime r) ∧ q = qs.prod) →
        q ∉ I)
    -- Outer induction hypothesis
    (IH :
      ∀ (J : Ideal R) (m : ℕ) (q : R) (qs : List R),
        m < n →
        (∀ r ∈ q :: qs, Prime r) →
        q * qs.prod ∈ J →
        qs.length = m - 1 →
        (∀ k, k < m →
          ∀ r : R, (∃ rs : List R,
                      rs.length = k ∧ (∀ t ∈ rs, Prime t) ∧ r = rs.prod) →
          r ∉ J) →
        ∃ d : R, J = Ideal.span ({d} : Set R)) :
    ∃ d : R, I = Ideal.span ({d} : Set R) := by
  classical
  -- `J = I / p₁`
  let J : Ideal R := I / p₁
  -- ps.prod ∈ J = I / p₁, because p₁ * ps.prod ∈ I
  have h_ps_in_J : ps.prod ∈ J := by
    -- Show that ps.prod * p₁ ∈ I, so ps.prod ∈ {x | x * p₁ ∈ I}
    show ps.prod * p₁ ∈ I
    simpa [mul_comm, quotientIdeal, Set.mem_setOf_eq] using hprod
  -- Split on whether `ps` is empty (= `n = 1`) or not
  cases ps with
  | nil =>
      -- `ps = []`, so `p₁ ∈ I`, hence `1 ∈ J` and `J = ⊤`
      have h_one : (1 : R) ∈ J := by
        change 1 * p₁ ∈ I
        simpa using hprod
      -- If 1 ∈ J, then J = ⊤
      have hJ_top : J = ⊤ := (one_mem_ideal_iff_top J).1 h_one
      -- Now `I = J * ⟨p₁⟩ = ⟨p₁⟩`
      have : I = Ideal.span ({p₁} : Set R) := by
        -- Use the fact that I = (I / p₁) * ⟨p₁⟩
        have hmul := quotientIdeal_mul_singleton (I := I) (p := p₁) hI_le
        -- Rewrite I in terms of (I / p₁)
        rw [←hmul]
        -- Show that (I / p₁) = ⊤, so the product is ⊤ * ⟨p₁⟩
        have h1 : (I / p₁) * span {p₁} = ⊤ * span {p₁} := by
          -- Replace (I / p₁) with ⊤
          congr 1
        -- And ⊤ * ⟨p₁⟩ = ⟨p₁⟩
        rw [h1, Ideal.top_mul]
      exact ⟨p₁, this⟩
  | cons q qs =>
      -- `ps = q :: qs`, so `m := qs.length.succ = n-1`
      set m : ℕ := qs.length.succ
      -- Show that m < n
      have hm_lt : m < n := by
        -- Recall: hlen says (q :: qs).length = n - 1
        have : qs.length.succ = n - 1 := by
          simpa [List.length_cons] using hlen
        -- So qs.length.succ + 1 = n
        have hsucc : qs.length.succ + 1 = n := by
          omega
        -- We have qs.length.succ < qs.length.succ + 1
        have : qs.length.succ < qs.length.succ + 1 := Nat.lt_succ_self _
        -- Therefore m = qs.length.succ < n
        simpa [m, hsucc] using this
      -- Show that qs.length = m - 1
      have hqs_len : qs.length = m - 1 := by
        simp [m]
      -- All primes in `q :: qs`
      have hprime_all : ∀ r ∈ q :: qs, Prime r := by
        intro r hr
        exact hpr r hr
      -- `q * qs.prod` is in `J`
      have hqprod_in_J : q * qs.prod ∈ J := by
        simpa [List.prod_cons, mul_comm] using h_ps_in_J
      -- Minimality for `J`
      have hJ_min :
          ∀ k, k < m →
            ∀ r : R, (∃ rs : List R,
                         rs.length = k ∧ (∀ t ∈ rs, Prime t) ∧ r = rs.prod) →
            r ∉ J := by
        intro k hk r hfac hrJ
        rcases hfac with ⟨rs, hrs_len, hrs_prime, hrs_prod⟩
        -- `r * p₁ ∈ I` with fewer than `n` primes ⇒ contradiction
        have hrp_in_I : r * p₁ ∈ I := by
          change r * p₁ ∈ I
          simpa [quotientIdeal, Set.mem_setOf_eq] using hrJ
        -- Build a factorization of length `k+1`
        have hfac' :
            ∃ qs' : List R,
              qs'.length = k.succ ∧
              (∀ t ∈ qs', Prime t) ∧
              r * p₁ = qs'.prod := by
          refine ⟨p₁ :: rs, ?_, ?_, ?_⟩
          · simp [hrs_len]
          · intro t ht
            rw [List.mem_cons] at ht
            cases ht with
            | inl h => rw [h]; exact hp₁
            | inr h => exact hrs_prime t h
          · simp [hrs_prod, mul_comm]
        -- `k.succ < n` (since `k < m < n`)
        have hk_succ_lt : k.succ < n := by omega
        -- Apply the minimality assumption to get a contradiction
        have hnot := hmin _ hk_succ_lt (r * p₁) hfac'
        exact hnot hrp_in_I
      -- Apply the (outer) induction hypothesis to `J`
      obtain ⟨d, hJ⟩ := IH J m q qs hm_lt hprime_all
        hqprod_in_J hqs_len hJ_min
      -- Finally translate `J = ⟨d⟩` into `I = ⟨d * p₁⟩`
      have hmul := quotientIdeal_mul_singleton (I:=I) (p:=p₁) hI_le
      refine ⟨d * p₁, ?_⟩
      -- `I = (I / p₁) * ⟨p₁⟩ = ⟨d⟩ * ⟨p₁⟩ = ⟨d * p₁⟩`
      simpa [J, hJ, span_singleton_mul_singleton] using hmul.symm







/--
**Main Theorem**: If R is a UFD and every nonzero prime ideal is maximal,
then R is a PID.
-/
theorem isPrincipalIdealRing_of_ufd_and_maximal_primes''
    [IsDomain R] [UniqueFactorizationMonoid R]
    (h_max : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal) :
    IsPrincipalIdealRing R := by
  constructor
  intro I

  by_cases hI_bot : I = ⊥
  · use 0
    simp [hI_bot, ← Ideal.span_zero]
    rfl

  · have h_exists : ∃ a : R, a ∈ I ∧ a ≠ 0 := by
      by_contra h_not
      push_neg at h_not
      have : I = ⊥ := by
        ext x; constructor
        · intro hx; simp [h_not x hx]
        · intro hx; simp at hx; rw [hx]; exact I.zero_mem
      exact hI_bot this

    obtain ⟨a, ha_mem, ha_ne⟩ := h_exists

    obtain ⟨u, hu_primes, ps, ha_eq⟩ :=
      @UniqueFactorizationMonoid.exists_prime_factors R _ (by infer_instance) a ha_ne

    by_cases hps_in : (ps : R) ∈ I
    · have hI_top : I = ⊤ := ideal_with_unit_eq_top R I ⟨(ps : R), Units.isUnit ps, hps_in⟩
      use 1
      rw [hI_top]
      exact (@Ideal.span_singleton_one R (by infer_instance)).symm

    · have hu_nonempty : u ≠ 0 := by
        intro h_empty
        rw [h_empty, Multiset.prod_zero] at ha_eq
        rw [← ha_eq] at ha_mem
        simp at ha_mem
        contradiction

      have hprod_mem : u.prod ∈ I := by
        have : u.prod = (ps⁻¹ : Rˣ) * a := by
          calc u.prod
              = ((ps⁻¹ : Rˣ) : R) * ((ps : Rˣ) : R) * u.prod := by simp
            _ = ((ps⁻¹ : Rˣ) : R) * (u.prod * (ps : Rˣ)) := by ring
            _ = ((ps⁻¹ : Rˣ) : R) * a := by rw [← ha_eq]
        rw [this]
        exact I.mul_mem_left _ ha_mem

      set factors := u.toList with hfactors_def

      have hfactors_prime : ∀ p ∈ factors, Prime p := by
        intro p hp
        have : p ∈ u := by
          rw [← Multiset.mem_toList]
          exact hp
        exact hu_primes p this

      have hfactors_prod : factors.prod = u.prod := by
        simp [factors, Multiset.prod_toList]

      have hfactors_nonempty : factors ≠ [] := by
        intro h
        have : u = 0 := by
          rw [← Multiset.toList_eq_nil]
          exact h
        exact hu_nonempty this

      obtain ⟨p₁, ps_rest, h⟩ := List.exists_cons_of_ne_nil hfactors_nonempty

      have hprod' : p₁ * ps_rest.prod ∈ I := by
        convert hprod_mem using 1
        rw [← hfactors_prod, h, List.prod_cons]

      set n := ps_rest.length.succ with hn_def

      -- Prove by strong induction with case split on minimality
      have main : ∀ (n : ℕ) (I : Ideal R) (p₁ : R) (ps : List R),
          (∀ p ∈ p₁ :: ps, Prime p) →
          p₁ * ps.prod ∈ I →
          ps.length = n - 1 →
          ∃ d : R, I = Ideal.span ({d} : Set R) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n IH =>
            intro I' p₁' ps' hprime hprod hlen

            by_cases hn_zero : n = 0
            · -- Base case: n = 0, so ps' = []
              simp [hn_zero] at hlen
              have hps_empty : ps' = [] := List.length_eq_zero.mp (by exact List.length_eq_zero.mpr hlen)
              subst hps_empty
              simp at hprod


              -- Show I' = ⟨p₁'⟩ using maximality
              have hp₁'_prime : Prime p₁' := hprime p₁' (List.mem_cons_self p₁' [])
              have hp₁'_max : (Ideal.span ({p₁'} : Set R)).IsMaximal := by
                apply h_max
                · rw [Ideal.span_singleton_prime hp₁'_prime.ne_zero]
                  exact hp₁'_prime
                · rw [ne_eq, span_singleton_eq_bot]
                  exact hp₁'_prime.ne_zero

              have h_subset : Ideal.span ({p₁'} : Set R) ≤ I' := by
                rw [Ideal.span_le]
                intro x hx; simp at hx; rw [hx]; exact hprod

              by_cases hI'_top : I' = ⊤
              · use 1
                rw [hI'_top]
                exact Ideal.span_singleton_one.symm
              · -- I' is proper, so by maximality I' = ⟨p₁'⟩
                use p₁'
                refine le_antisymm ?_ h_subset
                by_contra h_not_le
                have : Ideal.span ({p₁'} : Set R) < I' := by
                  constructor; exact h_subset
                  intro h_eq; exact h_not_le (le_of_eq (by
                    have : Ideal.span ({p₁'} : Set R) ≤ I' := by
                      exact h_subset
                    exact False.elim (h_not_le h_eq)
                  ))
                have := hp₁'_max.1.2 I' this
                exact hI'_top this

            · -- Inductive case: n > 0
              have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_zero

              -- Case split on minimality
              by_cases h_minimal : ∀ m < n, ∀ q : R,
                  (∃ qs : List R, qs.length = m ∧ (∀ r ∈ qs, Prime r) ∧ q = qs.prod) → q ∉ I'

              · -- Minimality holds: use inductionStep
                have hI'_subset : I' ≤ Ideal.span ({p₁'} : Set R) := by
                  apply ideal_subset_span_of_minimal_prime_product (R := R) h_max hn_pos
                  · exact hprime p₁' (List.mem_cons_self p₁' ps')
                  · intro p hp; exact hprime p (List.mem_cons_of_mem p₁' hp)
                  · exact hprod
                  · exact hlen
                  · exact h_minimal

                exact inductionStep hn_pos
                  (hprime p₁' (List.mem_cons_self p₁' ps'))
                  hlen
                  (fun p hp => hprime p (List.mem_cons_of_mem p₁' hp))
                  hprod
                  hI'_subset
                  h_minimal
                  (by intros J m q qs hm_lt hqs_prime hq_prod hqs_len h_minimal_J; exact
                    IH m hm_lt J q qs hqs_prime hq_prod hqs_len)

              · -- Minimality fails: there's a shorter factorization in I'
                push_neg at h_minimal
                obtain ⟨m, hm_lt, q, ⟨qs, hqs_len, hqs_prime, hqs_prod⟩, hq_mem⟩ := h_minimal

                -- Apply IH to this shorter element
                cases qs with
                | nil =>
                    -- qs = [], so q = 1 ∈ I', hence I' = ⊤
                    simp at hqs_prod
                    rw [hqs_prod] at hq_mem
                    have : I' = ⊤ := (one_mem_ideal_iff_top I').mp hq_mem
                    use 1
                    rw [this]
                    exact Ideal.span_singleton_one.symm

                | cons q₀ qs_rest =>
                    -- qs = q₀ :: qs_rest, apply IH with the shorter factorization
                    have hqs_rest_len : qs_rest.length = m - 1 := by
                      have : (q₀ :: qs_rest).length = m := by
                        calc (q₀ :: qs_rest).length
                            = (q₀ :: qs_rest).length := by rfl
                          _ = m := hqs_len
                      simp at this
                      omega

                    have hq_prod : q₀ * qs_rest.prod ∈ I' := by
                      have : q = (q₀ :: qs_rest).prod := hqs_prod
                      rw [List.prod_cons] at this
                      rw [← this]
                      exact hq_mem

                    exact IH m hm_lt I' q₀ qs_rest hqs_prime hq_prod hqs_rest_len

      -- Apply main theorem
      have : ∃ d, I = span {d} := by
        exact main n I p₁ ps_rest
          (fun p hp =>
            match hp with
            | List.Mem.head _ => hfactors_prime p (by rw [h]; exact List.mem_cons_self p ps_rest)
            | List.Mem.tail _ hmem =>
                hfactors_prime p (by rw [h]; exact List.mem_cons_of_mem _ hmem))
          hprod'
          (by simp [hn_def])
      exact { principal' := this }
