import Mathlib
import BusyBeaver.BB6.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

/-!
# The machine `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`: the halting criterion

DeepMind's `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart = E(0, 1)`
(`isHalt_iff_highLevel_acceleration`). Its states are `E(b, d)` with `b, d` natural numbers.

This file records the structure of that map that decides halting. It is the structure of the
machines of `Line322.lean`, `Line487.lean` and `Line167.lean`, with the parity of `d` as the phase.

* **Odd phase.** For `d` odd the step never halts and the new `d` is odd, with one exception:
  the coincidence `d = 2 b + 1`, where the state `E(b, 2b + 1)` goes to `E(0, 4 b + 6)`
  (`odd_step`).
* **Excursion.** From `E(0, 4 b + 6)` the chain `E(b_i, d_i)` with `b_i + 4 = 4 · 2^i` and
  `d_{i+1} = d_i - 2 b_i - 6` runs while `d` is even (two things can end it: the state leaves
  to an odd `d`, or `d = 2 b_i` and the state restarts at `E(0, 4 b_i + 4)`). It halts if and
  only if `b = SW j = 4^j - j - 4` with `2 ≤ j`, for every `b` (`excursion_halts`,
  `excursion_ends`), and otherwise it ends at an odd `d`.
* **Criterion.** The machine halts if and only if the orbit reaches a coincidence state
  `E(SW j, 2 SW j + 1)` with `2 ≤ j` (`isHalt_iff_E_SW`). Whether that happens is open.
-/

namespace AntihydraOrbit.Line594

open BusyBeaver
open BusyBeaver.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
  (target HighLevelState highLevelNext highLevelStart isHalt_iff_highLevel_acceleration)

/-! ### Definitions (the trusted base) -/

/-- `n` steps of the high-level acceleration (`none` once it halted). -/
def it (n : ℕ) (o : Option HighLevelState) : Option HighLevelState :=
  (Option.bind · highLevelNext)^[n] o

/-- The state of the high-level acceleration after `t` steps (`none` once the machine halted). -/
def orbit (t : ℕ) : Option HighLevelState :=
  it t (some highLevelStart)

/-- The entry values `b` of the coincidence `E(b, 2b + 1)` that halt: `4^j - j - 4`. -/
def SW (j : ℕ) : ℕ := 4 ^ j - j - 4

/-- The chain from `E(b, d)` halts at a stage `i`: `d = 2 b_i + 2` with `b_i + 4 = (b + 4) 2^i`. -/
def Hal (b d : ℕ) : Prop := ∃ i, d + 2 * (b + 4) + 2 * i + 6 = 4 * (b + 4) * 2 ^ i

/-- The chain from `E(b, d)` restarts at a stage `i`: `d = 2 b_i`, and the state becomes
`E(0, 4 b_i + 4)`. -/
def Res (b d : ℕ) : Prop := ∃ i, d + 2 * (b + 4) + 2 * i + 8 = 4 * (b + 4) * 2 ^ i

/-! ### Sanity anchors -/

example : orbit 0 = some (.E 0 1) := rfl
example : SW 2 = 10 ∧ SW 3 = 57 ∧ SW 4 = 248 ∧ SW 5 = 1015 := by decide
example : highLevelNext (.E 114 229) = some (.E 0 462) := by decide
example : highLevelNext (.E 10 21) = some (.E 0 46) := by decide
example : highLevelNext (.E 0 46) = some (.E 4 40) := by decide
example : highLevelNext (.E 4 40) = some (.E 12 26) := by decide
example : highLevelNext (.E 12 26) = none := by decide
example : orbit 220 = some (.E 114 229) := by decide +kernel

/-! ### Iterating the step -/

theorem it_zero (o : Option HighLevelState) : it 0 o = o := rfl

theorem it_succ_some (n : ℕ) (s : HighLevelState) :
    it (n + 1) (some s) = it n (highLevelNext s) := by
  simp [it, Function.iterate_succ_apply]

theorem it_none (n : ℕ) : it n none = none :=
  Function.iterate_fixed (f := fun o : Option HighLevelState => Option.bind o highLevelNext)
    (by rfl) n

theorem it_add (m n : ℕ) (o : Option HighLevelState) : it (m + n) o = it m (it n o) :=
  Function.iterate_add_apply _ m n o

theorem orbit_add (t j : ℕ) : orbit (j + t) = it j (orbit t) := by
  simp only [orbit]
  exact it_add j t _

theorem it_one {s s1 : HighLevelState} (h : highLevelNext s = some s1) :
    it 1 (some s) = some s1 := by
  simp [it_succ_some, h, it_zero]

theorem it_two {s s1 s2 : HighLevelState} (h1 : highLevelNext s = some s1)
    (h2 : highLevelNext s1 = some s2) : it 2 (some s) = some s2 := by
  simp [it_succ_some, h1, h2, it_zero]

theorem it_trans {s s' : HighLevelState} {j : ℕ} (j' : ℕ) (h : it j (some s) = some s') :
    it (j' + j) (some s) = it j' (some s') := by
  rw [it_add, h]

/-! ### The step in each case -/

theorem next_def (b d : ℕ) : highLevelNext (.E b d) =
    if b > d / 2 then
      (if b = d / 2 + 1 then some (.E 0 (2 * (d + 1) + 3))
        else if b = d / 2 + 2 then some (.E 2 (2 * (d + 1) + 1))
        else some (.E (b - d / 2 - 3) (2 * (d + 1) + 5)))
    else
      (if d + 1 - 2 * b ≤ 2 then some (.E 0 (2 * (d + 1) + 2))
        else if d + 1 - 2 * b = 3 then none
        else if d + 1 - 2 * b ≤ 6 then some (.E (2 * b + 2) (2 * (d + 1 - 2 * b) - 7))
        else some (.E (2 * b + 4) (d + 1 - 2 * b - 7))) := rfl

/-- The coincidence: `E(b, 2b + 1)` goes to `E(0, 4b + 6)`. -/
theorem next_coincidence (b : ℕ) : highLevelNext (.E b (2 * b + 1)) = some (.E 0 (4 * b + 6)) := by
  rw [next_def]
  split_ifs <;>
  first
    | (exfalso; omega)
    | (simp only [Option.some.injEq, HighLevelState.E.injEq, true_and]; omega)

/-- The state `E(b, d)` with `d = 2b + 2` halts. -/
theorem next_halt (b : ℕ) : highLevelNext (.E b (2 * b + 2)) = none := by
  rw [next_def]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The state `E(b, 2b)` restarts at `E(0, 4b + 4)`. -/
theorem next_restart (b : ℕ) : highLevelNext (.E b (2 * b)) = some (.E 0 (4 * b + 4)) := by
  rw [next_def]
  split_ifs <;>
  first
    | (exfalso; omega)
    | (simp only [Option.some.injEq, HighLevelState.E.injEq, true_and]; omega)

/-- The state `E(b, 2b + 4)` leaves to `E(2b + 2, 3)`. -/
theorem next_five (b : ℕ) : highLevelNext (.E b (2 * b + 4)) = some (.E (2 * b + 2) 3) := by
  rw [next_def]
  split_ifs <;>
  first
    | (exfalso; omega)
    | (simp only [Option.some.injEq, HighLevelState.E.injEq, true_and]; omega)

/-- The chain step: `E(b, d)` with `d ≥ 2b + 6` goes to `E(2b + 4, d - 2b - 6)`. -/
theorem next_chain (b d : ℕ) (h : 2 * b + 6 ≤ d) :
    highLevelNext (.E b d) = some (.E (2 * b + 4) (d - 2 * b - 6)) := by
  rw [next_def]
  split_ifs <;>
  first
    | (exfalso; omega)
    | (simp only [Option.some.injEq, HighLevelState.E.injEq, true_and]; omega)

/-- `b` above `d / 2`: the new `d` is odd. -/
theorem next_gt (b d : ℕ) (h : d / 2 < b) :
    ∃ x y, highLevelNext (.E b d) = some (.E x y) ∧ y % 2 = 1 := by
  rw [next_def]
  split_ifs <;> first | (exfalso; omega) | exact ⟨_, _, rfl, by omega⟩

/-! ### The odd phase -/

/-- The odd phase never halts, and its `d` stays odd except at the coincidence `d = 2b + 1`. -/
theorem odd_step (b d : ℕ) (hd : d % 2 = 1) :
    ∃ b' d', highLevelNext (.E b d) = some (.E b' d') ∧
      (d' % 2 = 1 ∨ (d = 2 * b + 1 ∧ b' = 0 ∧ d' = 4 * b + 6)) := by
  rw [next_def]
  split_ifs <;> first | (exfalso; omega) | exact ⟨_, _, rfl, by omega⟩

/-! ### Closed forms -/

theorem SW_add (j : ℕ) (hj : 2 ≤ j) : SW j + j + 4 = 4 ^ j := by
  have h : j + 4 ≤ 4 ^ j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  unfold SW
  omega

theorem bound_aux (b d i k : ℕ) (hk : k ≤ 8)
    (h : d + 2 * (b + 4) + 2 * i + k = 4 * (b + 4) * 2 ^ i) :
    (i = 0 ∧ d + k = 2 * (b + 4)) ∨ (1 ≤ i ∧ 2 * b + 6 ≤ d) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · left
    simp at h
    omega
  · right
    refine ⟨hpos, ?_⟩
    have h1 : i + 1 ≤ 2 ^ i := Nat.lt_two_pow_self
    have h4 : (b + 4) * (i + 1) ≤ (b + 4) * 2 ^ i := Nat.mul_le_mul_left _ h1
    have h5 : 4 * i + b + 4 ≤ (b + 4) * 2 ^ i := by nlinarith [h4, Nat.zero_le (b * i)]
    have e : 4 * (b + 4) * 2 ^ i = 4 * ((b + 4) * 2 ^ i) := by ring
    omega

theorem Hal_bound {b d : ℕ} (h : Hal b d) : d = 2 * b + 2 ∨ 2 * b + 6 ≤ d := by
  obtain ⟨i, hi⟩ := h
  rcases bound_aux b d i 6 (by norm_num) hi with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem Res_bound {b d : ℕ} (h : Res b d) : d = 2 * b ∨ 2 * b + 6 ≤ d := by
  obtain ⟨i, hi⟩ := h
  rcases bound_aux b d i 8 (by norm_num) hi with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem Hal_rec {b d : ℕ} (h : 2 * b + 6 ≤ d) : Hal b d ↔ Hal (2 * b + 4) (d - 2 * b - 6) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases bound_aux b d i 6 (by norm_num) hi with ⟨_, h2⟩ | ⟨hpos, _⟩
    · omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine ⟨i', ?_⟩
      have e1 : 4 * (b + 4) * 2 ^ (i' + 1) = 2 * (4 * (b + 4) * 2 ^ i') := by ring
      have e2 : 4 * (2 * b + 4 + 4) * 2 ^ i' = 2 * (4 * (b + 4) * 2 ^ i') := by ring
      omega
  · rintro ⟨i, hi⟩
    refine ⟨i + 1, ?_⟩
    have e1 : 4 * (b + 4) * 2 ^ (i + 1) = 2 * (4 * (b + 4) * 2 ^ i) := by ring
    have e2 : 4 * (2 * b + 4 + 4) * 2 ^ i = 2 * (4 * (b + 4) * 2 ^ i) := by ring
    omega

theorem Res_rec {b d : ℕ} (h : 2 * b + 6 ≤ d) : Res b d ↔ Res (2 * b + 4) (d - 2 * b - 6) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases bound_aux b d i 8 (by norm_num) hi with ⟨_, h2⟩ | ⟨hpos, _⟩
    · omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine ⟨i', ?_⟩
      have e1 : 4 * (b + 4) * 2 ^ (i' + 1) = 2 * (4 * (b + 4) * 2 ^ i') := by ring
      have e2 : 4 * (2 * b + 4 + 4) * 2 ^ i' = 2 * (4 * (b + 4) * 2 ^ i') := by ring
      omega
  · rintro ⟨i, hi⟩
    refine ⟨i + 1, ?_⟩
    have e1 : 4 * (b + 4) * 2 ^ (i + 1) = 2 * (4 * (b + 4) * 2 ^ i) := by ring
    have e2 : 4 * (2 * b + 4 + 4) * 2 ^ i = 2 * (4 * (b + 4) * 2 ^ i) := by ring
    omega

/-- The halting values: `Hal 0 (4b + 6)` iff `b = SW j` for some `j ≥ 2`. -/
theorem Hal_zero_iff (b : ℕ) : Hal 0 (4 * b + 6) ↔ ∃ j, 2 ≤ j ∧ b = SW j := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
    · have e : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
      rw [e] at hi
      have e2 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [pow_zero] at hi
        omega
      · refine ⟨k + 1, by omega, ?_⟩
        have := SW_add (k + 1) (by omega)
        omega
    · have e : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
      rw [e] at hi
      omega
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    refine ⟨2 * k, ?_⟩
    have e : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
    have e2 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
    have := SW_add (k + 1) hj
    rw [e]
    omega

/-- A restart state `E(0, D)` with `D + 12 = 16 · 2^i` neither halts nor restarts again. -/
theorem restart_not_hal (i D : ℕ) (h : D + 12 = 16 * 2 ^ i) : ¬ Hal 0 D ∧ ¬ Res 0 D := by
  have key : ∀ i' k : ℕ, k ≤ 8 → 6 ≤ k → D + 8 + 2 * i' + k = 16 * 2 ^ i' → False := by
    intro i' k hk hk2 hi'
    have hY := Nat.lt_two_pow_self (n := i')
    rcases Nat.lt_or_ge i i' with hlt | hge
    · have : 2 ^ (i + 1) ≤ 2 ^ i' := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this
      omega
    · have : 2 ^ i' ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge
      omega
  constructor
  · rintro ⟨i', hi'⟩
    exact key i' 6 (by norm_num) (by norm_num) (by omega)
  · rintro ⟨i', hi'⟩
    exact key i' 8 (by norm_num) (by norm_num) (by omega)

/-! ### The excursion -/

/-- The excursion law for every even `d` and every `b`: the chain halts iff `Hal b d`; otherwise
it ends, after at least one step, at an odd `d` or at a restart `E(0, D)`. -/
theorem stage : ∀ d b : ℕ, d % 2 = 0 →
    (Hal b d → ∃ n, it n (some (.E b d)) = none) ∧
    (¬ Hal b d → ∃ n, 1 ≤ n ∧
      ((∃ x y, it n (some (.E b d)) = some (.E x y) ∧ y % 2 = 1) ∨
       (∃ i D, d + 2 * (b + 4) + 2 * i + 8 = 4 * (b + 4) * 2 ^ i ∧ D + 12 = 4 * (b + 4) * 2 ^ i ∧
         it n (some (.E b d)) = some (.E 0 D)))) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro b hd
    by_cases hgt : d / 2 < b
    · -- b > d / 2: the new d is odd
      obtain ⟨x, y, hxy, hy⟩ := next_gt b d hgt
      refine ⟨fun h => ?_, fun _ => ⟨1, le_refl _, Or.inl ⟨x, y, it_one hxy, hy⟩⟩⟩
      rcases Hal_bound h with h | h <;> omega
    · by_cases h0 : d = 2 * b
      · -- d = 2b: restart at E(0, 4b + 4)
        subst h0
        refine ⟨fun h => ?_, fun _ => ⟨1, le_refl _, Or.inr ⟨0, 4 * b + 4, ?_, ?_,
          it_one (next_restart b)⟩⟩⟩
        · rcases Hal_bound h with h | h <;> omega
        · simp only [pow_zero]; omega
        · simp only [pow_zero]; omega
      · by_cases h2 : d = 2 * b + 2
        · -- d = 2b + 2: the halting state
          subst h2
          have hH : Hal b (2 * b + 2) := ⟨0, by simp only [pow_zero]; omega⟩
          refine ⟨fun _ => ⟨1, ?_⟩, fun h => absurd hH h⟩
          simp [it_succ_some, next_halt, it_zero]
        · by_cases h4 : d = 2 * b + 4
          · subst h4
            refine ⟨fun h => ?_, fun _ => ⟨1, le_refl _, Or.inl ⟨2 * b + 2, 3,
              it_one (next_five b), by norm_num⟩⟩⟩
            rcases Hal_bound h with h | h <;> omega
          · -- d ≥ 2b + 6: one step of the chain
            have h6 : 2 * b + 6 ≤ d := by omega
            have e1 := next_chain b d h6
            obtain ⟨ih1, ih2⟩ := ih (d - 2 * b - 6) (by omega) (2 * b + 4) (by omega)
            have hrec : Hal b d ↔ Hal (2 * b + 4) (d - 2 * b - 6) := Hal_rec h6
            refine ⟨fun h => ?_, fun h => ?_⟩
            · obtain ⟨n, hn⟩ := ih1 (hrec.mp h)
              exact ⟨n + 1, by rw [it_trans n (it_one e1), hn]⟩
            · obtain ⟨n, hn1, hn⟩ := ih2 (fun h' => h (hrec.mpr h'))
              refine ⟨n + 1, by omega, ?_⟩
              rcases hn with ⟨x, y, hxy, hy⟩ | ⟨i, D, hi, hD, hs⟩
              · exact Or.inl ⟨x, y, by rw [it_trans n (it_one e1), hxy], hy⟩
              · refine Or.inr ⟨i + 1, D, ?_, ?_, by rw [it_trans n (it_one e1), hs]⟩
                · have e1' : 4 * (b + 4) * 2 ^ (i + 1) = 2 * (4 * (b + 4) * 2 ^ i) := by ring
                  have e2' : 4 * (2 * b + 4 + 4) * 2 ^ i = 2 * (4 * (b + 4) * 2 ^ i) := by ring
                  omega
                · have e1' : 4 * (b + 4) * 2 ^ (i + 1) = 2 * (4 * (b + 4) * 2 ^ i) := by ring
                  have e2' : 4 * (2 * b + 4 + 4) * 2 ^ i = 2 * (4 * (b + 4) * 2 ^ i) := by ring
                  omega

/-- The excursion from the coincidence, for every `b`: it halts if `b = SW j` with `2 ≤ j`. -/
theorem excursion_halts (b j : ℕ) (hj : 2 ≤ j) (hb : b = SW j) :
    ∃ n, it n (some (.E 0 (4 * b + 6))) = none :=
  (stage (4 * b + 6) 0 (by omega)).1 ((Hal_zero_iff b).mpr ⟨j, hj, hb⟩)

/-- ... and otherwise it ends, after at least one step, at an odd `d`. -/
theorem excursion_ends (b : ℕ) (hb : ∀ j, 2 ≤ j → b ≠ SW j) :
    ∃ n, 1 ≤ n ∧ ∃ x y, it n (some (.E 0 (4 * b + 6))) = some (.E x y) ∧ y % 2 = 1 := by
  have hnh : ¬ Hal 0 (4 * b + 6) := fun h => by
    obtain ⟨j, hj, hj'⟩ := (Hal_zero_iff b).mp h
    exact hb j hj hj'
  obtain ⟨n, hn1, hn⟩ := (stage (4 * b + 6) 0 (by omega)).2 hnh
  rcases hn with ⟨x, y, hxy, hy⟩ | ⟨i, D, hi, hD, hs⟩
  · exact ⟨n, hn1, x, y, hxy, hy⟩
  · have hD' : D + 12 = 16 * 2 ^ i := by simpa using hD
    obtain ⟨hn2, hr⟩ := restart_not_hal i D hD'
    obtain ⟨m, hm1, hm⟩ := (stage D 0 (by omega)).2 hn2
    refine ⟨m + n, by omega, ?_⟩
    rcases hm with ⟨x, y, hxy, hy⟩ | ⟨i2, D2, hi2, _, _⟩
    · exact ⟨x, y, by rw [it_trans m hs, hxy], hy⟩
    · exact absurd ⟨i2, by simpa using hi2⟩ hr

/-- From an odd-`d` state (a *waypoint*) the orbit reaches the next odd-`d` state, unless the
state is a coincidence `E(SW j, 2 SW j + 1)`. -/
theorem next_waypoint (b d : ℕ) (hd : d % 2 = 1) :
    (∃ j, 2 ≤ j ∧ b = SW j ∧ d = 2 * b + 1) ∨
      ∃ n, 1 ≤ n ∧ ∃ x y, it n (some (.E b d)) = some (.E x y) ∧ y % 2 = 1 := by
  obtain ⟨b', d', hs, hcase⟩ := odd_step b d hd
  rcases hcase with h | ⟨hd2, rfl, rfl⟩
  · exact Or.inr ⟨1, le_refl _, b', d', it_one hs, h⟩
  · by_cases hb : ∃ j, 2 ≤ j ∧ b = SW j
    · obtain ⟨j, hj, hbj⟩ := hb
      exact Or.inl ⟨j, hj, hbj, hd2⟩
    · push Not at hb
      obtain ⟨n, hn1, x, y, hxy, hy⟩ := excursion_ends b hb
      exact Or.inr ⟨n + 1, by omega, x, y, by rw [it_trans n (it_one hs), hxy], hy⟩

/-! ### The criterion -/

/-- The machine halts if and only if the orbit reaches a coincidence `E(SW j, 2 SW j + 1)`. -/
theorem isHalt_iff_E_SW :
    IsHalt target ↔ ∃ t j, 2 ≤ j ∧ orbit t = some (.E (SW j) (2 * SW j + 1)) := by
  rw [isHalt_iff_highLevel_acceleration]
  constructor
  · rintro ⟨n, hn⟩
    have key : ∀ n : ℕ, ∀ b d t : ℕ, d % 2 = 1 → orbit t = some (.E b d) →
        (it n (some (.E b d))).isNone →
          ∃ t j, 2 ≤ j ∧ orbit t = some (.E (SW j) (2 * SW j + 1)) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro b d t hd ht hnone
        rcases next_waypoint b d hd with ⟨j, hj, rfl, rfl⟩ | ⟨j, hj, x, y, hs, hy⟩
        · exact ⟨t, j, hj, ht⟩
        · have hnone' : it n (some (.E b d)) = none := Option.isNone_iff_eq_none.mp hnone
          have hlt : j < n := by
            by_contra hge
            have hj' : j = (j - n) + n := by omega
            rw [hj', it_add, hnone', it_none] at hs
            exact absurd hs (by simp)
          have h3 := it_trans (n - j) hs
          rw [show n - j + j = n by omega] at h3
          have h2 : (it (n - j) (some (.E x y))).isNone := by
            rw [← h3]
            exact hnone
          exact ih (n - j) (by omega) x y (j + t) hy (by rw [orbit_add, ht, hs]) h2
    exact key n 0 1 0 (by norm_num) rfl hn
  · rintro ⟨t, j, hj, ht⟩
    obtain ⟨m, hm⟩ := excursion_halts (SW j) j hj rfl
    refine ⟨m + 1 + t, ?_⟩
    have h : orbit (m + 1 + t) = none := by
      rw [orbit_add, ht, it_succ_some, next_coincidence]
      exact hm
    change (orbit (m + 1 + t)).isNone
    rw [h]
    rfl

end AntihydraOrbit.Line594
