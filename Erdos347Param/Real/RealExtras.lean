import Mathlib

/-
  ## RealExtras

  Small, stable lemmas for real-analysis facts that are "obvious on paper"
  but verbose in Lean.  These are intended to be reused across Params
  and related files.
-/

lemma sqrt_four : Real.sqrt 4 = 2 := by
  norm_num

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have h0 : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
  have hlt : (3 : ℝ) < (4 : ℝ) := by norm_num
  have h : Real.sqrt (3 : ℝ) < Real.sqrt (4 : ℝ) :=
    Real.sqrt_lt_sqrt h0 hlt
  -- rewrite √4 = 2
  simpa [sqrt_four] using h

lemma sqrt_three_lt_three : Real.sqrt 3 < 3 := by
  calc Real.sqrt 3 < 2 := sqrt_three_lt_two
    _ < 3 := by norm_num

lemma log_two_pos : 0 < Real.log 2 := by
  have h : (1 : ℝ) < 2 := by norm_num
  simpa using Real.log_pos h

lemma log_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma log_div_log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := by
  have hlog := log_mono hx hxy
  have hinv : 0 < (Real.log 2)⁻¹ := inv_pos.mpr log_two_pos
  have := mul_le_mul_of_nonneg_right hlog (le_of_lt hinv)
  simpa [div_eq_mul_inv] using this

lemma log_div_log2_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < Real.log x / Real.log 2 := by
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log 2 ≤ Real.log x := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    exact Real.log_le_log h2pos hx
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le log_two_pos hlogx
  exact div_pos hlogxpos log_two_pos


/-- Toolkit lemma: dividing an inequality by a positive real preserves `≤`.

We keep the proof here (rather than at call sites) so downstream proofs stay mathematical.
-/
lemma div_le_div_of_pos {a b c : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    a / c ≤ b / c := by
  have hinv_nonneg : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have hmul : a * c⁻¹ ≤ b * c⁻¹ := mul_le_mul_of_nonneg_right hab hinv_nonneg
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul


open scoped BigOperators

-- geometric partial sum bound: ∑_{k<n} Q^k ≤ 1/(1-Q) for 0 ≤ Q < 1
lemma geom_sum_le_inv_one_sub (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    ∀ n : ℕ, (∑ k ∈ Finset.range n, Q ^ k) ≤ 1 / (1 - Q) := by
  intro n
  have hden : 0 < (1 - Q) := sub_pos.mpr hQ1

  -- First show the closed form: ∑_{k<n} Q^k = (1 - Q^n)/(1 - Q)
  have hclosed : (∑ k ∈ Finset.range n, Q ^ k) = (1 - Q ^ n) / (1 - Q) := by
    -- use the discrete FTC lemma `sum_range_induction`
    -- with s(n) = (1 - Q^n)/(1 - Q)
    have : (∑ k ∈ Finset.range n, Q ^ k) = (fun m : ℕ => (1 - Q ^ m) / (1 - Q)) n := by
      -- `sum_range_induction (f := ...) (s := ...)`
      refine (Finset.sum_range_induction
        (f := fun k => Q ^ k)
        (s := fun m : ℕ => (1 - Q ^ m) / (1 - Q))
        ?base n ?step)
      · -- base: s 0 = 0
        simp
      · -- step: s(k+1) = s k + f k for k < n
        intro k hk
        -- algebra on the closed form
        -- (1 - Q^(k+1))/(1-Q) = (1 - Q^k)/(1-Q) + Q^k
        -- rewrite Q^(k+1) = Q^k * Q
        have : (1 - Q ^ (k + 1)) / (1 - Q)
            = (1 - Q ^ k) / (1 - Q) + Q ^ k := by
          -- multiply both sides by (1-Q) to avoid division headaches
          have hneq : (1 - Q) ≠ 0 := ne_of_gt hden
          field_simp [hneq]
          -- after field_simp, it's ring arithmetic + pow_succ
          -- note: pow_succ: Q^(k+1)=Q^k*Q
          ring_nf
          -- `ring_nf` will usually finish; if not, add:
          -- simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simpa using this

  -- Now bound: (1 - Q^n)/(1-Q) ≤ 1/(1-Q) since 1 - Q^n ≤ 1
  have hnum : (1 - Q ^ n) ≤ 1 := by
    -- because Q^n ≥ 0
    have hpow : 0 ≤ Q ^ n := by exact pow_nonneg hQ0 n
    linarith
  have hdiv : (1 - Q ^ n) / (1 - Q) ≤ 1 / (1 - Q) :=
    div_le_div_of_pos hden hnum

  simpa [hclosed] using hdiv

/-! ## Natural Number Arithmetic Lemmas -/

/-- For naturals k ≥ 1, squaring preserves or increases: k² ≥ k -/
lemma Nat.sq_ge_self_of_one_le {k : ℕ} (hk : 1 ≤ k) : k ≤ k ^ 2 := by
  calc k = k * 1 := by ring
    _ ≤ k * k := Nat.mul_le_mul_left k hk
    _ = k ^ 2 := by ring

/-- For naturals k ≥ 4, we have k² ≥ 16 -/
lemma Nat.sixteen_le_sq_of_four_le {k : ℕ} (hk : 4 ≤ k) : 16 ≤ k ^ 2 := by
  calc 16 = 4 ^ 2 := by norm_num
    _ ≤ k ^ 2 := Nat.pow_le_pow_left hk 2

/-- For reals k ≥ 4, we have k² ≥ k -/
lemma sq_ge_self_of_four_le {k : ℝ} (hk : 4 ≤ k) : k ≤ k ^ 2 := by
  have h1 : 1 ≤ k := by linarith
  calc k = k * 1 := by ring
    _ ≤ k * k := by
        apply mul_le_mul_of_nonneg_left h1
        linarith
    _ = k ^ 2 := by ring

/-- For reals k ≥ 4, we have k² ≥ 16 -/
lemma sixteen_le_sq_of_four_le {k : ℝ} (hk : 4 ≤ k) : 16 ≤ k ^ 2 := by
  calc 16 = 4 ^ 2 := by norm_num
    _ ≤ k ^ 2 := by
        apply sq_le_sq'
        · linarith
        · exact hk