import AntihydraOrbit.Defs
import AntihydraOrbit.Bridge
import AntihydraOrbit.Lemmas
import AntihydraOrbit.Horizon

/-!
# The Antihydra orbit: statements

The statements below are the specification. They were written before the proofs (each proof was a
placeholder then) and have not been changed since. All are proved. The proofs use `Bridge.lean`,
`Lemmas.lean` and `Horizon.lean`; `Audit.lean` prints the axioms each theorem depends on.
-/

namespace AntihydraOrbit

open BusyBeaver
open BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA (target next start)

/-! ## A. The bridge: the machine halts iff the orbit has an odd-heavy prefix -/

/-- The DeepMind acceleration `next` from `P(0,3,1)` stops iff the counter process stops from `(8, 0)`. -/
theorem collatzHalts_next_iff_step : CollatzHalts next start ↔ CollatzHalts step (8, 0) := by
  have hs : CollatzHalts step (8, 0) ↔ ∃ n, 2 * evens n < odds n := step_halts_iff_bad
  rw [hs]
  constructor
  · rintro ⟨n, hn⟩
    by_contra hb
    push Not at hb
    exact never_none hb n (Option.isNone_iff_eq_none.1 hn)
  · intro hb
    obtain ⟨m, hm⟩ := halts_of_bad hb
    exact ⟨m, by rw [← it, hm]; rfl⟩

/-- The counter process stops from `(8, 0)` iff some prefix of the orbit has more than twice as
many odd terms as even terms. -/
theorem collatzHalts_step_iff : CollatzHalts step (8, 0) ↔ ∃ n, 2 * evens n < odds n := by
  exact step_halts_iff_bad

/-- **Antihydra halts iff the orbit of 8 under `x ↦ ⌊3x/2⌋` has a prefix with more than twice as
many odd terms as even terms.** -/
theorem antihydra_isHalt_iff : IsHalt target ↔ ∃ n, 2 * evens n < odds n := by
  exact BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.isHalt_iff_acceleration.trans
    (collatzHalts_next_iff_step.trans collatzHalts_step_iff)

/-- The same statement for non-halting. -/
theorem antihydra_isNotHalt_iff : IsNotHalt target ↔ ∀ n, odds n ≤ 2 * evens n := by
  have h : IsNotHalt target ↔ ¬ IsHalt target := by
    unfold IsNotHalt IsHalt
    constructor
    · rintro h ⟨cfg, hc, hn⟩
      have := h cfg hc
      rw [Option.isNone_iff_eq_none.1 hn] at this
      simp at this
    · intro h cfg hc
      by_contra hs
      exact h ⟨cfg, hc, by simpa using hs⟩
  rw [h, antihydra_isHalt_iff]
  push Not
  rfl

/-! ## B. Structure of the map -/

theorem H_iterate_add (k x t : ℕ) : H^[k] (x + 2 ^ k * t) = H^[k] x + 3 ^ k * t := by
  exact Aux.H_iterate_add k x t

/-- The parities of the first `k` iterates depend only on `x mod 2^k` … -/
theorem parity_of_modEq (k x y : ℕ) (h : x % 2 ^ k = y % 2 ^ k) :
    ∀ j < k, H^[j] x % 2 = H^[j] y % 2 := by
  exact Aux.parity_of_modEq k x y h

/-- … and determine it: the map from residues mod `2^k` to parity words of length `k` is a bijection. -/
theorem modEq_of_parity (k x y : ℕ) (h : ∀ j < k, H^[j] x % 2 = H^[j] y % 2) :
    x % 2 ^ k = y % 2 ^ k := by
  exact Aux.modEq_of_parity k x y h

/-- A run of even terms: `2^k · m ↦ 3^k · m` in `k` steps. -/
theorem H_iterate_two_pow_mul (k m : ℕ) : H^[k] (2 ^ k * m) = 3 ^ k * m := by
  exact Aux.H_iterate_two_pow_mul k m

/-- A run of odd terms: `2^k · m + 1 ↦ 3^k · m + 1` in `k` steps. -/
theorem H_iterate_two_pow_mul_add_one (k m : ℕ) : H^[k] (2 ^ k * m + 1) = 3 ^ k * m + 1 := by
  exact Aux.H_iterate_two_pow_mul_add_one k m

theorem X_eq_Z_add_one (n : ℕ) : X n = Z n + 1 := by
  exact Aux.X_eq_Z_add_one n

/-- Size: `7 · (3/2)^n ≤ X n - 1` and `X n ≤ 8 · (3/2)^n`. -/
theorem X_bounds (n : ℕ) : 7 * 3 ^ n ≤ 2 ^ n * (X n - 1) ∧ 2 ^ n * X n ≤ 8 * 3 ^ n := by
  exact Aux.X_bounds n

/-- From any point of the orbit the next even term comes within `log₂ (X n)` steps … -/
theorem exists_even_within (n : ℕ) : ∃ k ≤ Nat.log 2 (X n), X (n + k) % 2 = 0 := by
  exact Aux.exists_even_within n

/-- … and so does the next odd term. -/
theorem exists_odd_within (n : ℕ) : ∃ k ≤ Nat.log 2 (X n), X (n + k) % 2 = 1 := by
  exact Aux.exists_odd_within n

/-! ## C. A kernel-checked horizon

Replace `1000` by the largest horizon the Lean kernel can check in reasonable time
(no `native_decide`). -/

theorem no_stop_upto : ∀ n ≤ 1000, odds n ≤ 2 * evens n := by
  intro n hn
  exact Aux.noStop_sound 10 (by decide +kernel) n (le_trans hn (by norm_num))

/-- The same, for the first `65536 = 2^16` steps: the kernel checks this in about 20 seconds
(`decide +kernel`, no `native_decide`). The same check for `2^17` did not finish in ten minutes. -/
theorem no_stop_upto_65536 : ∀ n ≤ 65536, odds n ≤ 2 * evens n := by
  intro n hn
  exact Aux.noStop_sound 16 (by decide +kernel) n (le_trans hn (by norm_num))

/-! ## D. Which starting values stop early (a Terras-type count)

Among the `2^k` residues `r` mod `2^k`, the number for which the counter process from `(r, b)` stops
within `k` steps equals the number of parity words of length `k` on which the walk stops. -/

theorem stopsWithin_iff_wordStops (k r b : ℕ) :
    StopsWithin k r b ↔ wordStops ((List.range k).map fun j => decide (H^[j] r % 2 = 0)) b = true := by
  exact Aux.stopsWithin_iff_wordStops k r b

theorem card_stopping_residues (k b : ℕ) :
    ((Finset.range (2 ^ k)).filter fun r =>
        wordStops ((List.range k).map fun j => decide (H^[j] r % 2 = 0)) b = true).card =
      ((Finset.univ : Finset (List.Vector Bool k)).filter fun w => wordStops w.toList b = true).card := by
  exact Aux.card_stopping_residues k b

/-! ## E. Aperiodicity and barriers -/

/-- From 2 on, the map strictly increases. -/
theorem lt_H (x : ℕ) (hx : 2 ≤ x) : x < H x := by
  exact Aux.lt_H x hx

/-- A window of `k` parities determines a start value below `2^k`. -/
theorem eq_of_parity_window (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ j < k, H^[j] x % 2 = H^[j] y % 2) : x = y := by
  exact Aux.eq_of_parity_window k x y hx hy h

/-- The parity sequence of any start `x ≥ 2` is not eventually periodic. -/
theorem not_eventually_periodic (x : ℕ) (hx : 2 ≤ x) :
    ¬ ∃ m r, 0 < r ∧ ∀ k, H^[m + k] x % 2 = H^[m + r + k] x % 2 := by
  exact Aux.not_eventually_periodic x hx

/-- Barrier 1: at every counter value there are stopping starts of every size:
`2^(b+1) · m + 1` stops within `b + 1` steps from counter `b`. -/
theorem stopsWithin_two_pow_mul_add_one (b m : ℕ) :
    StopsWithin (b + 1) (2 ^ (b + 1) * m + 1) b := by
  exact Aux.stopsWithin_two_pow_mul_add_one b m

/-- Barrier 2: no congruence condition on the start value protects from stopping. Every residue
class contains, for every counter value, a start from which the process stops. -/
theorem exists_stopping_in_residue_class (M r b : ℕ) (hM : 0 < M) :
    ∃ x n, x % M = r % M ∧ StopsWithin n x b := by
  exact Aux.exists_stopping_in_residue_class M r b hM

end AntihydraOrbit
