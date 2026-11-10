import AntihydraOrbit.Defs
import AntihydraOrbit.Bridge

/-!
# Helper lemmas for sections B and D of `Statements.lean`
-/

namespace AntihydraOrbit.Aux


theorem H_add_two_mul (x s : ℕ) : H (x + 2 * s) = H x + 3 * s := by
  unfold H; omega

theorem H_iterate_add (k x t : ℕ) : H^[k] (x + 2 ^ k * t) = H^[k] x + 3 ^ k * t := by
  induction k generalizing x t with
  | zero => simp
  | succ k ih =>
    have e : x + 2 ^ (k + 1) * t = x + 2 * (2 ^ k * t) := by ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, e, H_add_two_mul,
      show H x + 3 * (2 ^ k * t) = H x + 2 ^ k * (3 * t) by ring, ih]
    ring

theorem H_iterate_zero (k : ℕ) : H^[k] 0 = 0 :=
  Function.iterate_fixed (by simp [H]) k

theorem H_iterate_one (k : ℕ) : H^[k] 1 = 1 :=
  Function.iterate_fixed (by simp [H]) k

theorem parity_mod (k x : ℕ) : ∀ j < k, H^[j] x % 2 = H^[j] (x % 2 ^ k) % 2 := by
  intro j hj
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d + 1 := ⟨k - j - 1, by omega⟩
  have e : x = x % 2 ^ (j + d + 1) + 2 ^ j * (2 ^ (d + 1) * (x / 2 ^ (j + d + 1))) := by
    have := Nat.mod_add_div x (2 ^ (j + d + 1))
    have h2 : 2 ^ (j + d + 1) = 2 ^ j * 2 ^ (d + 1) := by ring
    rw [h2] at this ⊢
    nlinarith [this]
  conv_lhs => rw [e]
  rw [H_iterate_add]
  have : 2 ∣ 3 ^ j * (2 ^ (d + 1) * (x / 2 ^ (j + d + 1))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _
  omega

theorem parity_of_modEq (k x y : ℕ) (h : x % 2 ^ k = y % 2 ^ k) :
    ∀ j < k, H^[j] x % 2 = H^[j] y % 2 := by
  intro j hj
  rw [parity_mod k x j hj, parity_mod k y j hj, h]

theorem modEq_of_parity (k x y : ℕ) (h : ∀ j < k, H^[j] x % 2 = H^[j] y % 2) :
    x % 2 ^ k = y % 2 ^ k := by
  induction k generalizing x y with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have h0 := h 0 (by omega)
    simp only [Function.iterate_zero, id] at h0
    have h1 : H x % 2 ^ k = H y % 2 ^ k := by
      apply ih
      intro j hj
      have := h (j + 1) (by omega)
      simpa [Function.iterate_succ_apply] using this
    have hx : H x = 3 * (x / 2) + x % 2 := by unfold H; omega
    have hy : H y = 3 * (y / 2) + y % 2 := by unfold H; omega
    rw [hx, hy, h0] at h1
    have h2 : 3 * (x / 2) ≡ 3 * (y / 2) [MOD 2 ^ k] := by
      have := Nat.ModEq.add_right_cancel' (y % 2) h1
      exact this
    have h3 : x / 2 ≡ y / 2 [MOD 2 ^ k] :=
      Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h2
    have h4 := Nat.ModEq.mul_left' 2 h3
    have h5 : x % 2 ^ (k + 1) = y % 2 ^ (k + 1) := by
      have hxe : x = 2 * (x / 2) + x % 2 := by omega
      have hye : y = 2 * (y / 2) + y % 2 := by omega
      have h6 := Nat.ModEq.add_right (x % 2) h4
      have e1 : 2 * (y / 2) + x % 2 = y := by omega
      rw [← hxe, e1] at h6
      rw [pow_succ, mul_comm]
      exact h6
    exact h5



theorem H_iterate_two_pow_mul (k m : ℕ) : H^[k] (2 ^ k * m) = 3 ^ k * m := by
  have := H_iterate_add k 0 m
  simpa [H_iterate_zero] using this

theorem H_iterate_two_pow_mul_add_one (k m : ℕ) : H^[k] (2 ^ k * m + 1) = 3 ^ k * m + 1 := by
  have := H_iterate_add k 1 m
  rw [H_iterate_one] at this
  rw [add_comm (2 ^ k * m) 1, this]
  ring

theorem Z_succ (n : ℕ) : Z (n + 1) = M (Z n) := by
  simp [Z, Function.iterate_succ_apply']

theorem X_eq_Z_add_one (n : ℕ) : X n = Z n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [X_succ, Z_succ, ih]; unfold H M; omega

theorem X_bounds (n : ℕ) : 7 * 3 ^ n ≤ 2 ^ n * (X n - 1) ∧ 2 ^ n * X n ≤ 8 * 3 ^ n := by
  induction n with
  | zero => simp [X_zero]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hx : X n - 1 = Z n := by have := X_eq_Z_add_one n; omega
    have hx' : X (n + 1) - 1 = Z (n + 1) := by have := X_eq_Z_add_one (n + 1); omega
    rw [hx] at ih1
    rw [hx']
    constructor
    · have h1 : 3 * Z n ≤ 2 * Z (n + 1) := by rw [Z_succ]; unfold M; omega
      have := Nat.mul_le_mul_left (2 ^ n) h1
      rw [pow_succ, pow_succ]; nlinarith
    · have h1 : 2 * X (n + 1) ≤ 3 * X n := by rw [X_succ]; unfold H; omega
      have := Nat.mul_le_mul_left (2 ^ n) h1
      rw [pow_succ, pow_succ]; nlinarith

theorem exists_even_within (n : ℕ) : ∃ k ≤ Nat.log 2 (X n), X (n + k) % 2 = 0 := by
  by_contra hne
  push Not at hne
  have hX := X_ge n
  set L := Nat.log 2 (X n) with hL
  have hlt : X n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hpar : ∀ j < L + 1, H^[j] (X n) % 2 = H^[j] 1 % 2 := by
    intro j hj
    have := hne j (by omega)
    have e : X (n + j) = H^[j] (X n) := by
      unfold X; rw [add_comm, Function.iterate_add_apply]
    rw [H_iterate_one, ← e]; omega
  have := modEq_of_parity (L + 1) _ _ hpar
  have h1 : 1 % 2 ^ (L + 1) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [h1, Nat.mod_eq_of_lt hlt] at this
  omega

theorem exists_odd_within (n : ℕ) : ∃ k ≤ Nat.log 2 (X n), X (n + k) % 2 = 1 := by
  by_contra hne
  push Not at hne
  have hX := X_ge n
  set L := Nat.log 2 (X n) with hL
  have hlt : X n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hpar : ∀ j < L + 1, H^[j] (X n) % 2 = H^[j] 0 % 2 := by
    intro j hj
    have := hne j (by omega)
    have e : X (n + j) = H^[j] (X n) := by
      unfold X; rw [add_comm, Function.iterate_add_apply]
    rw [H_iterate_zero, ← e]; omega
  have := modEq_of_parity (L + 1) _ _ hpar
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hlt] at this
  omega



/-- parity word -/
def pword (k r : ℕ) : List Bool := (List.range k).map fun j => decide (H^[j] r % 2 = 0)

theorem pword_zero (r : ℕ) : pword 0 r = [] := rfl

theorem pword_succ (k r : ℕ) : pword (k + 1) r = decide (r % 2 = 0) :: pword k (H r) := by
  unfold pword
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ List.cons rfl (List.map_congr_left fun j _ => ?_)
  show decide (H^[j + 1] r % 2 = 0) = decide (H^[j] (H r) % 2 = 0)
  rw [Function.iterate_succ_apply]

theorem stopsWithin_iff_wordStops (k r b : ℕ) :
    StopsWithin k r b ↔ wordStops ((List.range k).map fun j => decide (H^[j] r % 2 = 0)) b = true := by
  show StopsWithin k r b ↔ wordStops (pword k r) b = true
  induction k generalizing r b with
  | zero => simp [StopsWithin, pword_zero, wordStops]
  | succ k ih =>
    unfold StopsWithin at ih ⊢
    rw [Function.iterate_succ_apply, pword_succ]
    by_cases he : r % 2 = 0
    · have : step (r, b) = some (H r, b + 2) := by simp [step, he]
      simp [this, he, wordStops]
      simpa using ih (H r) (b + 2)
    · rcases b with _ | b
      · have : step (r, 0) = none := by simp [step, he]
        simp [this, he, wordStops]
      · have : step (r, b + 1) = some (H r, b) := by simp [step, he]
        simp [this, he, wordStops]
        simpa using ih (H r) b

theorem card_stopping_residues (k b : ℕ) :
    ((Finset.range (2 ^ k)).filter fun r =>
        wordStops ((List.range k).map fun j => decide (H^[j] r % 2 = 0)) b = true).card =
      ((Finset.univ : Finset (List.Vector Bool k)).filter fun w => wordStops w.toList b = true).card := by
  let g : Fin (2 ^ k) → List.Vector Bool k := fun r => ⟨pword k r.val, by simp [pword]⟩
  have hinj : Function.Injective g := by
    intro r r' h
    have h1 : pword k r.val = pword k r'.val := congrArg Subtype.val h
    have h2 : ∀ j < k, H^[j] r.val % 2 = H^[j] r'.val % 2 := by
      intro j hj
      have := congrArg (fun l => l[j]?) h1
      simp [pword, hj] at this
      omega
    have h3 := modEq_of_parity k _ _ h2
    rw [Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] at h3
    exact Fin.ext h3
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, by simp⟩
  apply Finset.card_bij (fun r hr => g ⟨r, Finset.mem_range.1 (Finset.mem_filter.1 hr).1⟩)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.1 hr).2
  · intro r hr r' hr' h
    have := hinj h
    simpa using this
  · intro w hw
    obtain ⟨r, rfl⟩ := hbij.2 w
    refine ⟨r.val, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨r.2, hw⟩


/-! ### Section E -/

theorem lt_H (x : ℕ) (hx : 2 ≤ x) : x < H x := by
  unfold H; omega

theorem le_H (x : ℕ) : x ≤ H x := by
  unfold H; omega

theorem le_iterate_H (r u : ℕ) : u ≤ H^[r] u := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply']; exact le_trans ih (le_H _)

theorem lt_iterate_H (u r : ℕ) (hu : 2 ≤ u) (hr : 0 < r) : u < H^[r] u := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact lt_of_le_of_lt (le_iterate_H r' u) (lt_H _ (le_trans hu (le_iterate_H r' u)))

theorem eq_of_parity_window (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ j < k, H^[j] x % 2 = H^[j] y % 2) : x = y := by
  have := modEq_of_parity k x y h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem not_eventually_periodic (x : ℕ) (hx : 2 ≤ x) :
    ¬ ∃ m r, 0 < r ∧ ∀ k, H^[m + k] x % 2 = H^[m + r + k] x % 2 := by
  rintro ⟨m, r, hr, h⟩
  set u := H^[m] x with hu
  have hv : H^[m + r] x = H^[r] u := by
    rw [hu, add_comm m r, Function.iterate_add_apply]
  have hpar : ∀ j, H^[j] u % 2 = H^[j] (H^[r] u) % 2 := by
    intro j
    have := h j
    have e1 : H^[m + j] x = H^[j] u := by
      rw [hu, add_comm m j, Function.iterate_add_apply]
    have e2 : H^[m + r + j] x = H^[j] (H^[r] u) := by
      rw [← hv, add_comm (m + r) j, Function.iterate_add_apply]
    rwa [e1, e2] at this
  have hu2 : 2 ≤ u := le_trans hx (le_iterate_H m x)
  have hlt := lt_iterate_H u r hu2 hr
  have hn : H^[r] u < 2 ^ (H^[r] u) := Nat.lt_two_pow_self
  have := eq_of_parity_window (H^[r] u) u (H^[r] u) (lt_trans hlt hn) hn (fun j _ => hpar j)
  omega

theorem stopsWithin_two_pow_mul_add_one (b m : ℕ) :
    StopsWithin (b + 1) (2 ^ (b + 1) * m + 1) b := by
  unfold StopsWithin
  suffices h : ∀ b m, (Option.bind · step)^[b + 1] (some (2 ^ (b + 1) * m + 1, b)) = none by
    rw [h]; rfl
  intro b
  induction b with
  | zero =>
    intro m
    have : step (2 * m + 1, 0) = none := by simp [step]
    simp [this]
  | succ b ih =>
    intro m
    have h1 : 2 ^ (b + 1 + 1) * m = 2 * (2 ^ (b + 1) * m) := by ring
    have h2 : 2 ^ (b + 1) * (3 * m) = 3 * (2 ^ (b + 1) * m) := by ring
    have hs : step (2 ^ (b + 1 + 1) * m + 1, b + 1) = some (2 ^ (b + 1) * (3 * m) + 1, b) := by
      rw [h1, h2]
      have : ¬ (2 * (2 ^ (b + 1) * m) + 1) % 2 = 0 := by omega
      simp only [step, this, ite_false, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
      simp only [H]
      congr 2
      omega
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some, hs]
    exact ih (3 * m)

/-! Words -/

theorem wordStops_replicate_false (b : ℕ) : ∀ L, b < L → wordStops (List.replicate L false) b = true := by
  induction b with
  | zero =>
    intro L hL
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    simp [List.replicate_succ, wordStops]
  | succ b ih =>
    intro L hL
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    simp only [List.replicate_succ, wordStops]
    exact ih L' (by omega)

theorem wordStops_append_replicate (L : ℕ) (w : List Bool) :
    ∀ b, b + 2 * w.length < L → wordStops (w ++ List.replicate L false) b = true := by
  induction w with
  | nil => intro b hb; simpa using wordStops_replicate_false b L (by simpa using hb)
  | cons a w ih =>
    intro b hb
    simp only [List.length_cons] at hb
    cases a with
    | true => simp only [List.cons_append, wordStops]; exact ih (b + 2) (by omega)
    | false =>
      cases b with
      | zero => simp [wordStops]
      | succ b => simp only [List.cons_append, wordStops]; exact ih b (by omega)

theorem pword_getElem? (n x j : ℕ) :
    (pword n x)[j]? = if j < n then some (decide (H^[j] x % 2 = 0)) else none := by
  unfold pword
  rw [List.getElem?_map]
  by_cases hj : j < n
  · simp [hj]
  · simp [hj]

theorem pword_length (n x : ℕ) : (pword n x).length = n := by simp [pword]

theorem pword_congr (n x y : ℕ) (h : ∀ j < n, H^[j] x % 2 = H^[j] y % 2) :
    pword n x = pword n y := by
  unfold pword
  refine List.map_congr_left fun j hj => ?_
  have := h j (List.mem_range.1 hj)
  simp [this]

theorem parity_of_pword_eq (n x y : ℕ) (h : pword n x = pword n y) :
    ∀ j < n, H^[j] x % 2 = H^[j] y % 2 := by
  intro j hj
  have := congrArg (fun l => l[j]?) h
  simp only [pword_getElem?, hj, ite_true, Option.some.injEq, decide_eq_decide] at this
  omega

theorem pword_surj (n : ℕ) (w : List Bool) (hw : w.length = n) : ∃ ρ < 2 ^ n, pword n ρ = w := by
  let g : Fin (2 ^ n) → List.Vector Bool n := fun r => ⟨pword n r.val, by simp [pword]⟩
  have hinj : Function.Injective g := by
    intro r r' h
    have h1 : pword n r.val = pword n r'.val := congrArg Subtype.val h
    have h3 := modEq_of_parity n _ _ (parity_of_pword_eq n _ _ h1)
    rw [Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] at h3
    exact Fin.ext h3
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, by simp⟩
  obtain ⟨r, hr⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨r.val, r.2, congrArg Subtype.val hr⟩

theorem exists_stopping_in_residue_class (M r b : ℕ) (hM : 0 < M) :
    ∃ x n, x % M = r % M ∧ StopsWithin n x b := by
  obtain ⟨k, M', hM', hMk⟩ := Nat.exists_eq_two_pow_mul_odd (n := M) (by omega)
  set L := b + 2 * k + 1 with hL
  obtain ⟨ρ, -, hρ⟩ := pword_surj (k + L) (pword k r ++ List.replicate L false)
    (by simp [pword_length])
  have cop : Nat.Coprime (2 ^ (k + L)) M' :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM')
  obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder cop ρ r
  have hxρ : pword (k + L) x = pword (k + L) ρ :=
    pword_congr _ _ _ (parity_of_modEq _ _ _ hx1)
  -- the first `k` parities of `ρ` and `r` agree
  have hρr : ∀ j < k, H^[j] ρ % 2 = H^[j] r % 2 := by
    intro j hj
    have hj' : j < (pword k r).length := by rw [pword_length]; exact hj
    have h3 : (pword (k + L) ρ)[j]? = (pword k r ++ List.replicate L false)[j]? :=
      congrArg (fun l => l[j]?) hρ
    rw [List.getElem?_append_left hj', pword_getElem?, pword_getElem?] at h3
    simp only [show j < k + L by omega, hj, ite_true, Option.some.injEq, decide_eq_decide] at h3
    omega
  have h2k : x ≡ r [MOD 2 ^ k] := by
    have a1 : x ≡ ρ [MOD 2 ^ k] := Nat.ModEq.of_dvd (pow_dvd_pow 2 (by omega)) hx1
    have a2 : ρ ≡ r [MOD 2 ^ k] := modEq_of_parity k ρ r hρr
    exact a1.trans a2
  have hcop2 : Nat.Coprime (2 ^ k) M' := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM')
  have hM : x ≡ r [MOD M] := by
    rw [hMk]; exact (Nat.modEq_and_modEq_iff_modEq_mul hcop2).1 ⟨h2k, hx2⟩
  refine ⟨x, k + L, hM, ?_⟩
  rw [stopsWithin_iff_wordStops]
  show wordStops (pword (k + L) x) b = true
  rw [hxρ, hρ]
  exact wordStops_append_replicate L _ b (by rw [pword_length]; omega)

end AntihydraOrbit.Aux
