import AntihydraOrbit.Statements

/-!
# How many start values stop: the density of stopping starts

The counter process of `Defs.lean` can be started at any pair `(x, b)`; Antihydra is the start
`(8, 0)`. This file answers the question "for which fraction of the start values `x` does the
process stop?" as far as it can be answered by counting parity words.

* Section A counts the parity words of length `k` on which the walk from counter `b` stops
  (`stopCount k b`) by a recurrence.
* Section B bounds that count on both sides:
  `q^(b+1) - (4/5)^(b+1) (189/200)^k ≤ stopCount k b / 2^k ≤ q^(b+1)` with `q = (√5 - 1)/2`,
  so the fraction of stopping words tends to `q^(b+1)`.
* Section C transfers the count to start values: among the first `2^k · m` start values exactly
  `m · stopCount k b` stop within `k` steps, and the start values that stop at all have lower
  density at least `q^(b+1)` (at least 61.8% for the counter 0).

Nothing here is about the single start value 8. The statements below are the specification: they
were written before the proofs and are not to be changed.
-/

namespace AntihydraOrbit

open BusyBeaver Filter Topology

/-- The number of parity words of length `k` on which the walk from counter `b` stops. -/
def stopCount (k b : ℕ) : ℕ :=
  ((Finset.univ : Finset (List.Vector Bool k)).filter fun w => wordStops w.toList b = true).card

/-- The constant `q = (√5 - 1)/2 = 0.618…`, the root of `q² + q = 1` between 0 and 1. -/
noncomputable def q : ℝ := (Real.sqrt 5 - 1) / 2

instance instDecidableStopsWithin (k x b : ℕ) : Decidable (StopsWithin k x b) := by
  unfold StopsWithin; infer_instance

/-! ## A. The count of stopping words -/

private theorem card_filter_head_eq (k : ℕ) (P : List Bool → Bool) (a : Bool) :
    (((Finset.univ : Finset (List.Vector Bool (k + 1))).filter fun w => P w.toList = true).filter
        fun w => w.head = a).card =
      ((Finset.univ : Finset (List.Vector Bool k)).filter fun v => P (a :: v.toList) = true).card := by
  apply Finset.card_bij (fun w _ => w.tail)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hcons : List.Vector.cons a w.tail = w := by
      rw [← hw.2, List.Vector.cons_head_tail]
    rw [← List.Vector.toList_cons, hcons]
    exact hw.1
  · intro w₁ hw₁ w₂ hw₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
    rw [← List.Vector.cons_head_tail w₁, ← List.Vector.cons_head_tail w₂, hw₁.2, hw₂.2, h]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨List.Vector.cons a v, ?_, List.Vector.tail_cons a v⟩
    simp [hv]

private theorem card_filter_vector_succ (k : ℕ) (P : List Bool → Bool) :
    ((Finset.univ : Finset (List.Vector Bool (k + 1))).filter fun w => P w.toList = true).card =
      ((Finset.univ : Finset (List.Vector Bool k)).filter fun v => P (true :: v.toList) = true).card +
        ((Finset.univ : Finset (List.Vector Bool k)).filter fun v => P (false :: v.toList) = true).card := by
  set S := (Finset.univ : Finset (List.Vector Bool (k + 1))).filter fun w => P w.toList = true
  rw [← Finset.card_filter_add_card_filter_not (fun w : List.Vector Bool (k + 1) => w.head = true) (s := S)]
  have hnot : (S.filter fun w : List.Vector Bool (k + 1) => ¬ w.head = true) =
      (S.filter fun w : List.Vector Bool (k + 1) => w.head = false) := by
    congr 1; ext w; simp
  rw [hnot, card_filter_head_eq k P true, card_filter_head_eq k P false]

theorem stopCount_zero (b : ℕ) : stopCount 0 b = 0 := by
  unfold stopCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _
  rw [w.eq_nil, List.Vector.toList_nil]
  simp [wordStops]

/-- From counter 0: an odd first term stops at once (`2^k` words), an even one moves to counter 2. -/
theorem stopCount_succ_zero (k : ℕ) : stopCount (k + 1) 0 = stopCount k 2 + 2 ^ k := by
  unfold stopCount
  rw [card_filter_vector_succ k (fun l => wordStops l 0)]
  simp only [wordStops]
  congr 1
  simp [card_vector]

/-- From counter `b + 1`: an even first term moves to `b + 3`, an odd one to `b`. -/
theorem stopCount_succ_succ (k b : ℕ) :
    stopCount (k + 1) (b + 1) = stopCount k (b + 3) + stopCount k b := by
  unfold stopCount
  rw [card_filter_vector_succ k (fun l => wordStops l (b + 1))]
  simp only [wordStops]
  rfl

/-! ## B. The two-sided bound and the limit -/

theorem q_sq : q ^ 2 = 1 - q := by
  unfold q
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  calc ((Real.sqrt 5 - 1) / 2) ^ 2
    _ = (Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1) / 4 := by ring
    _ = 1 - (Real.sqrt 5 - 1) / 2 := by rw [h5]; ring

theorem q_bounds : (618 : ℝ) / 1000 < q ∧ q < 619 / 1000 := by
  unfold q
  have h1 : (2236 : ℝ) / 1000 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt 5 < (2238 : ℝ) / 1000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  constructor <;> linarith

private theorem q_nonneg : 0 ≤ q := by
  linarith [q_bounds.1]

private theorem q_le_four_fifths : q ≤ 4 / 5 := by
  linarith [q_bounds.2]

private theorem q_le_one : q ≤ 1 := by
  linarith [q_bounds.2]

private theorem q_cube_add_one : q ^ 3 + 1 = 2 * q := by
  calc q ^ 3 + 1
    _ = q * q ^ 2 + 1 := by ring
    _ = q * (1 - q) + 1 := by rw [q_sq]
    _ = 1 - q ^ 2 + q := by ring
    _ = 2 * q := by rw [q_sq]; ring

/-- Upper bound: at most the fraction `q^(b+1)` of the words of any length stops. -/
theorem stopCount_le (k b : ℕ) : (stopCount k b : ℝ) ≤ q ^ (b + 1) * 2 ^ k := by
  induction k generalizing b with
  | zero =>
    simp only [stopCount_zero, Nat.cast_zero, pow_zero, mul_one]
    exact pow_nonneg q_nonneg (b + 1)
  | succ k ih =>
    rcases b with _ | b
    · have ih2 : (stopCount k 2 : ℝ) ≤ q ^ 3 * 2 ^ k := ih 2
      calc (stopCount (k + 1) 0 : ℝ)
        _ = (stopCount k 2 : ℝ) + 2 ^ k := by rw [stopCount_succ_zero]; push_cast; rfl
        _ ≤ q ^ 3 * 2 ^ k + 2 ^ k := by linarith [ih2]
        _ = (q ^ 3 + 1) * 2 ^ k := by ring
        _ = (2 * q) * 2 ^ k := by rw [q_cube_add_one]
        _ = q ^ (0 + 1) * 2 ^ (k + 1) := by ring
    · have ih3 : (stopCount k (b + 3) : ℝ) ≤ q ^ (b + 4) * 2 ^ k := ih (b + 3)
      calc (stopCount (k + 1) (b + 1) : ℝ)
        _ = (stopCount k (b + 3) : ℝ) + (stopCount k b : ℝ) := by
            rw [stopCount_succ_succ]; push_cast; rfl
        _ ≤ q ^ (b + 4) * 2 ^ k + q ^ (b + 1) * 2 ^ k := by linarith [ih3, ih b]
        _ = q ^ (b + 1) * (q ^ 3 + 1) * 2 ^ k := by ring
        _ = q ^ (b + 1) * (2 * q) * 2 ^ k := by rw [q_cube_add_one]
        _ = q ^ (b + 1 + 1) * 2 ^ (k + 1) := by ring

/-- Lower bound with an explicit error term that decays geometrically in the length `k`. -/
theorem stopCount_ge (k b : ℕ) :
    (q ^ (b + 1) - (4 / 5 : ℝ) ^ (b + 1) * (189 / 200 : ℝ) ^ k) * 2 ^ k ≤ (stopCount k b : ℝ) := by
  induction k generalizing b with
  | zero =>
    simp only [stopCount_zero, Nat.cast_zero, pow_zero, mul_one]
    have hpow : q ^ (b + 1) ≤ (4 / 5 : ℝ) ^ (b + 1) :=
      pow_le_pow_left₀ q_nonneg q_le_four_fifths (b + 1)
    linarith
  | succ k ih =>
    rcases b with _ | b
    · have hpos : 0 ≤ (189 / 200 : ℝ) ^ k * 2 ^ k := by positivity
      calc (q ^ (0 + 1) - (4 / 5 : ℝ) ^ (0 + 1) * (189 / 200 : ℝ) ^ (k + 1)) * 2 ^ (k + 1)
        _ = (2 * q - (4 / 5 : ℝ) ^ 3 * (189 / 200 : ℝ) ^ k) * 2 ^ k -
              (189 / 200 : ℝ) ^ k * 2 ^ k := by ring
        _ ≤ (2 * q - (4 / 5 : ℝ) ^ 3 * (189 / 200 : ℝ) ^ k) * 2 ^ k := by linarith
        _ = (q ^ 3 + 1 - (4 / 5 : ℝ) ^ 3 * (189 / 200 : ℝ) ^ k) * 2 ^ k := by rw [← q_cube_add_one]
        _ = (q ^ 3 - (4 / 5 : ℝ) ^ 3 * (189 / 200 : ℝ) ^ k) * 2 ^ k + 2 ^ k := by ring
        _ ≤ (stopCount k 2 : ℝ) + 2 ^ k := by linarith [ih 2]
        _ = (stopCount (k + 1) 0 : ℝ) := by rw [stopCount_succ_zero]; push_cast; rfl
    · calc (q ^ (b + 1 + 1) - (4 / 5 : ℝ) ^ (b + 1 + 1) * (189 / 200 : ℝ) ^ (k + 1)) * 2 ^ (k + 1)
        _ = (q ^ (b + 1) * (2 * q) -
              (4 / 5 : ℝ) ^ (b + 1) * ((4 / 5 : ℝ) ^ 3 + 1) * (189 / 200 : ℝ) ^ k) * 2 ^ k := by
            ring
        _ = (q ^ (b + 1) * (q ^ 3 + 1) -
              (4 / 5 : ℝ) ^ (b + 1) * ((4 / 5 : ℝ) ^ 3 + 1) * (189 / 200 : ℝ) ^ k) * 2 ^ k := by
            rw [← q_cube_add_one]
        _ = (q ^ (b + 4) - (4 / 5 : ℝ) ^ (b + 4) * (189 / 200 : ℝ) ^ k) * 2 ^ k +
              (q ^ (b + 1) - (4 / 5 : ℝ) ^ (b + 1) * (189 / 200 : ℝ) ^ k) * 2 ^ k := by ring
        _ ≤ (stopCount k (b + 3) : ℝ) + (stopCount k b : ℝ) := by linarith [ih (b + 3), ih b]
        _ = (stopCount (k + 1) (b + 1) : ℝ) := by rw [stopCount_succ_succ]; push_cast; rfl

/-- The fraction of stopping words of length `k` tends to `q^(b+1)`. -/
theorem tendsto_stopCount (b : ℕ) :
    Tendsto (fun k : ℕ => (stopCount k b : ℝ) / 2 ^ k) atTop (𝓝 (q ^ (b + 1))) := by
  have hg : Tendsto (fun k : ℕ => q ^ (b + 1) - (4 / 5 : ℝ) ^ (b + 1) * (189 / 200 : ℝ) ^ k)
      atTop (𝓝 (q ^ (b + 1))) := by
    have h0 : Tendsto (fun k : ℕ => (189 / 200 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul h0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds (fun k => ?_) (fun k => ?_)
  · exact (le_div_iff₀ (by positivity)).2 (stopCount_ge k b)
  · exact (div_le_iff₀ (by positivity)).2 (stopCount_le k b)

/-! ## C. Start values -/

/-- `StopsWithin` is the finite-horizon form of `CollatzHalts step`, the notion of the bridge
theorem `collatzHalts_step_iff`. -/
theorem collatzHalts_step_iff_stopsWithin (x b : ℕ) :
    CollatzHalts step (x, b) ↔ ∃ k, StopsWithin k x b :=
  Iff.rfl

private theorem periodic_stopsWithin (k b : ℕ) :
    Function.Periodic (fun x => StopsWithin k x b) (2 ^ k) := by
  intro x
  simp only [eq_iff_iff, stopsWithin_iff_wordStops]
  have hpar := parity_of_modEq k (x + 2 ^ k) x (Nat.add_mod_right x (2 ^ k))
  have hmap : ((List.range k).map fun j => decide (H^[j] (x + 2 ^ k) % 2 = 0)) =
      ((List.range k).map fun j => decide (H^[j] x % 2 = 0)) :=
    Aux.pword_congr k (x + 2 ^ k) x hpar
  rw [hmap]

private theorem count_stopsWithin_two_pow (k b : ℕ) :
    Nat.count (fun x => StopsWithin k x b) (2 ^ k) = stopCount k b := by
  rw [Nat.count_eq_card_filter_range]
  unfold stopCount
  rw [← card_stopping_residues k b]
  congr 1
  ext r
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  exact stopsWithin_iff_wordStops k r b

private theorem range_add_eq_union_Ico (a c : ℕ) :
    Finset.range (a + c) = Finset.range a ∪ Finset.Ico a (a + c) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  omega

private theorem disjoint_range_Ico (a c : ℕ) :
    Disjoint (Finset.range a) (Finset.Ico a (a + c)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2
  omega

/-- Among the first `2^k · m` start values, exactly `m · stopCount k b` stop within `k` steps from
counter `b`. -/
theorem card_stopsWithin_range (k b m : ℕ) :
    ((Finset.range (2 ^ k * m)).filter fun x => StopsWithin k x b).card = m * stopCount k b := by
  induction m with
  | zero => simp
  | succ m ih =>
    have heq : 2 ^ k * (m + 1) = 2 ^ k * m + 2 ^ k := by ring
    rw [heq, range_add_eq_union_Ico, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (disjoint_range_Ico _ _)),
      ih, Nat.filter_Ico_card_eq_of_periodic _ _ _ (periodic_stopsWithin k b),
      count_stopsWithin_two_pow]
    ring

open Classical in
/-- **Lower density of the stopping start values.** For every `ε > 0`, from some `N₀` on, at least
`(q^(b+1) - ε) · N` of the start values `x < N` stop from counter `b`. For `b = 0` this is at least
61.8% of all start values. -/
theorem lower_density_stopping (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (q ^ (b + 1) - ε) * (N : ℝ) ≤
        (((Finset.range N).filter fun x => CollatzHalts step (x, b)).card : ℝ) := by
  by_cases hq : q ^ (b + 1) - ε / 2 ≤ 0
  · refine ⟨0, fun N _ => ?_⟩
    have h1 : (q ^ (b + 1) - ε) * (N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)
    have h2 : (0 : ℝ) ≤ (((Finset.range N).filter fun x => CollatzHalts step (x, b)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · push Not at hq
    set C : ℝ := (4 / 5 : ℝ) ^ (b + 1)
    have hC : 0 < C := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (ε / 2) / C by positivity)
      (show (189 / 200 : ℝ) < 1 by norm_num)
    have hk' : C * (189 / 200 : ℝ) ^ k < ε / 2 := by
      have := (lt_div_iff₀ hC).1 hk
      linarith
    have hsc : (q ^ (b + 1) - ε / 2) * (2 : ℝ) ^ k ≤ (stopCount k b : ℝ) := by
      have hge := stopCount_ge k b
      have hle : (q ^ (b + 1) - ε / 2) * (2 : ℝ) ^ k ≤
          (q ^ (b + 1) - C * (189 / 200 : ℝ) ^ k) * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hq1 : q ^ (b + 1) ≤ 1 := by
      calc q ^ (b + 1)
        _ ≤ 1 ^ (b + 1) := pow_le_pow_left₀ q_nonneg q_le_one (b + 1)
        _ = 1 := one_pow (b + 1)
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((2 : ℝ) ^ k / (ε / 2))
    refine ⟨N₀, fun N hN => ?_⟩
    have hN_real : (2 : ℝ) ^ k ≤ (ε / 2) * (N : ℝ) := by
      have hle : (2 : ℝ) ^ k / (ε / 2) ≤ (N : ℝ) := by
        calc (2 : ℝ) ^ k / (ε / 2)
          _ ≤ (N₀ : ℝ) := le_of_lt hN₀
          _ ≤ (N : ℝ) := Nat.cast_le.2 hN
      have := (div_le_iff₀ (by linarith : 0 < ε / 2)).1 hle
      linarith
    set m := N / 2 ^ k
    have hcard_nat : m * stopCount k b ≤
        ((Finset.range N).filter fun x => CollatzHalts step (x, b)).card := by
      rw [← card_stopsWithin_range k b m]
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      refine ⟨lt_of_lt_of_le hx.1 (Nat.mul_div_le N (2 ^ k)), ?_⟩
      rw [collatzHalts_step_iff_stopsWithin]
      exact ⟨k, hx.2⟩
    have hcard : (m : ℝ) * (stopCount k b : ℝ) ≤
        (((Finset.range N).filter fun x => CollatzHalts step (x, b)).card : ℝ) := by
      exact_mod_cast hcard_nat
    have hdiv_nat : N ≤ 2 ^ k * m + 2 ^ k := by
      have h1 : N % 2 ^ k + 2 ^ k * m = N := Nat.mod_add_div N (2 ^ k)
      have h2 : N % 2 ^ k < 2 ^ k := Nat.mod_lt N (by positivity)
      omega
    have hdiv : (N : ℝ) - (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * (m : ℝ) := by
      have hcast : (N : ℝ) ≤ (2 : ℝ) ^ k * (m : ℝ) + (2 : ℝ) ^ k := by exact_mod_cast hdiv_nat
      linarith
    have hm_sc : (q ^ (b + 1) - ε / 2) * ((2 : ℝ) ^ k * (m : ℝ)) ≤ (m : ℝ) * (stopCount k b : ℝ) := by
      calc (q ^ (b + 1) - ε / 2) * ((2 : ℝ) ^ k * (m : ℝ))
        _ = (m : ℝ) * ((q ^ (b + 1) - ε / 2) * (2 : ℝ) ^ k) := by ring
        _ ≤ (m : ℝ) * (stopCount k b : ℝ) :=
            mul_le_mul_of_nonneg_left hsc (Nat.cast_nonneg m)
    have hstep1 : (q ^ (b + 1) - ε / 2) * ((N : ℝ) - (2 : ℝ) ^ k) ≤
        (q ^ (b + 1) - ε / 2) * ((2 : ℝ) ^ k * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (le_of_lt hq)
    have hstep2 : (q ^ (b + 1) - ε / 2) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k := by
      calc (q ^ (b + 1) - ε / 2) * (2 : ℝ) ^ k
        _ ≤ 1 * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (2 : ℝ) ^ k := one_mul _
    linarith

end AntihydraOrbit
