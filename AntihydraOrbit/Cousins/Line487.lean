import Mathlib
import BusyBeaver.BB6.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

/-!
# The machine `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`: the halting criterion

DeepMind's `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart = D(0, 1)`
(`isHalt_iff_highLevel_acceleration`). Its states are `D(a, w)` with `a, w` natural numbers; the
step is described in the doc comment of that file (the drain chain is `evalK2`).

This file records the structure of that map that decides halting. It is the same structure as for
the machine of `Line322.lean`.

* **Two phases.** In the *even phase* the number `w` is odd; in the *odd phase* the state is
  `D(0, W)` with `W` even. Every state on the orbit is in one of the two phases (`Inv`,
  `inv_orbit`), and no state of the even phase halts (`highLevelNext_ne_none_of_odd`).
* **Entry.** The even phase leads into the odd phase only through the coincidence `a = ⌊w/2⌋`,
  after which the state is `D(0, 2 w + 2)` (or `D(0, 2 w + 6)` at a later stage of the chain).
* **Excursion.** From `D(0, W)` the next step halts if and only if `W` is one of
  `SW k = 12 · 2^k - 2 k - 10` (`highLevelNext_D_zero_eq_none_iff`), for every `W`.
* **Criterion.** The machine halts if and only if the orbit reaches `D(0, SW k)` for some `k`
  (`isHalt_iff_D_SW`). Whether that happens is open.

In the variables of the Cubic Cap macro map, `D(a, w)` is the state `(w + 1, 0, a + 1)`, an entry
is a state with `a = 2c` and `b' = b + a`, and `SW k = 2 b'` with `b' = 6 · 2^k - k - 5`.
-/

namespace AntihydraOrbit.Line487

open BusyBeaver
open BusyBeaver.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
  (target HighLevelState highLevelNext highLevelStart evalK2
    isHalt_iff_highLevel_acceleration)

/-! ### Definitions (the trusted base) -/

/-- The state of the high-level acceleration after `t` steps (`none` once the machine halted). -/
def orbit (t : ℕ) : Option HighLevelState :=
  (Option.bind · highLevelNext)^[t] (some highLevelStart)

/-- The even phase: `w` is odd. -/
def EvenPhase : HighLevelState → Prop
  | .D _ w => w % 2 = 1

/-- The odd phase: the state is `D(0, W)` with `W` even. -/
def OddPhase : HighLevelState → Prop
  | .D a w => a = 0 ∧ w % 2 = 0

/-- The invariant of the orbit: every state is in one of the two phases. -/
def Inv (s : HighLevelState) : Prop := EvenPhase s ∨ OddPhase s

/-- The entry values `W` of the odd phase that halt: `12 · 2^k - 2 k - 10`. -/
def SW (k : ℕ) : ℕ := 12 * 2 ^ k - 2 * k - 10

/-! ### Sanity anchors: the first steps of the orbit -/

example : orbit 0 = some (.D 0 1) := rfl
example : orbit 1 = some (.D 0 4) := by decide
example : orbit 2 = some (.D 2 3) := by decide
example : orbit 3 = some (.D 0 9) := by decide
example : highLevelNext (.D 0 13) = some (.D 8 1) := by
  simp [highLevelNext, evalK2]
example : highLevelNext (.D 0 2) = none := by
  simp [highLevelNext]
example : highLevelNext (.D 0 12) = none := by
  simp [highLevelNext, evalK2]
example : [SW 0, SW 1, SW 2, SW 3, SW 4] = [2, 12, 34, 80, 174] := by decide

/-! ### Elementary facts -/

private theorem orbit_succ (t : ℕ) : orbit (t + 1) = (orbit t).bind highLevelNext := by
  unfold orbit
  exact Function.iterate_succ_apply' _ _ _

private theorem lt_two_pow (j : ℕ) : j < 2 ^ j := Nat.lt_two_pow_self

/-- `SW k + 2 k + 10 = 12 · 2^k`. -/
theorem SW_add (k : ℕ) : SW k + 2 * k + 10 = 12 * 2 ^ k := by
  have h := lt_two_pow k
  unfold SW
  omega

/-- Every `SW k` is even. -/
theorem SW_even (k : ℕ) : SW k % 2 = 0 := by
  have h := SW_add k
  omega

/-! ### A. The phase invariant -/

/-- Every step of a drain chain lands in one of the two phases. -/
theorem inv_evalK2 (a w : ℕ) (s' : HighLevelState) (h : evalK2 a w = some s') : Inv s' := by
  induction w using Nat.strong_induction_on generalizing a s' with
  | _ w ih =>
    rw [evalK2] at h
    by_cases c1 : a > w / 2
    · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w + 7) % 2 = 1
      omega
    by_cases c2 : a = w / 2
    · simp only [c1, eq_true c2, ↓reduceIte, Option.some.injEq] at h
      subst h
      right
      exact ⟨rfl, by omega⟩
    by_cases c3 : w = 2 * a + 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte] at h
      cases h
    by_cases c4 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, eq_true c4, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w - 4 * a - 5) % 2 = 1
      omega
    · simp only [c1, c2, c3, c4, ↓reduceIte] at h
      exact ih (w - 2 * a - 6) (by omega) (2 * a + 4) s' h

/-- Every step lands in one of the two phases, whatever the state it starts from. -/
theorem inv_highLevelNext (s s' : HighLevelState) (h : highLevelNext s = some s') : Inv s' := by
  rcases s with ⟨a, w⟩
  unfold highLevelNext at h
  dsimp only at h
  by_cases c1 : a > w / 2
  · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
    subst h
    left
    change (2 * w + 3) % 2 = 1
    omega
  by_cases c2 : a = w / 2
  · simp only [c1, eq_true c2, ↓reduceIte, Option.some.injEq] at h
    subst h
    right
    exact ⟨rfl, by omega⟩
  by_cases c3 : w = 2 * a + 2
  · simp only [c1, c2, eq_true c3, ↓reduceIte] at h
    cases h
  by_cases c4 : w ≤ 2 * a + 5
  · simp only [c1, c2, c3, eq_true c4, ↓reduceIte, Option.some.injEq] at h
    subst h
    left
    change (2 * w - 4 * a - 5) % 2 = 1
    omega
  · simp only [c1, c2, c3, c4, ↓reduceIte] at h
    exact inv_evalK2 _ _ s' h

theorem inv_start : Inv highLevelStart := Or.inl rfl

/-- Every state on the orbit is in the even or in the odd phase. -/
theorem inv_orbit (t : ℕ) (s : HighLevelState) (h : orbit t = some s) : Inv s := by
  induction t generalizing s with
  | zero =>
    have h' : some highLevelStart = some s := h
    have : highLevelStart = s := Option.some.inj h'
    subst this
    exact inv_start
  | succ t ih =>
    rw [orbit_succ] at h
    rcases hs : orbit t with _ | s0
    · rw [hs] at h
      simp at h
    · rw [hs] at h
      exact inv_highLevelNext s0 s h

/-- A halt needs an even `w`: a chain of `evalK2` from an odd `w` never halts. -/
theorem evalK2_ne_none_of_odd (a w : ℕ) (hw : w % 2 = 1) : evalK2 a w ≠ none := by
  induction w using Nat.strong_induction_on generalizing a with
  | _ w ih =>
    rw [evalK2]
    by_cases c1 : a > w / 2
    · simp only [eq_true c1, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c2 : a = w / 2
    · simp only [c1, eq_true c2, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c3 : w = 2 * a + 2
    · exfalso
      omega
    by_cases c4 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, eq_true c4, ↓reduceIte]
      exact Option.some_ne_none _
    · simp only [c1, c2, c3, c4, ↓reduceIte]
      exact ih (w - 2 * a - 6) (by omega) (2 * a + 4) (by omega)

/-- A state in the even phase never halts. -/
theorem highLevelNext_ne_none_of_odd (s : HighLevelState) (h : EvenPhase s) :
    highLevelNext s ≠ none := by
  rcases s with ⟨a, w⟩
  have hw : w % 2 = 1 := h
  unfold highLevelNext
  dsimp only
  by_cases c1 : a > w / 2
  · simp only [eq_true c1, ↓reduceIte]
    exact Option.some_ne_none _
  by_cases c2 : a = w / 2
  · simp only [c1, eq_true c2, ↓reduceIte]
    exact Option.some_ne_none _
  by_cases c3 : w = 2 * a + 2
  · exfalso
    omega
  by_cases c4 : w ≤ 2 * a + 5
  · simp only [c1, c2, c3, eq_true c4, ↓reduceIte]
    exact Option.some_ne_none _
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    exact evalK2_ne_none_of_odd _ _ (by omega)

/-- The value of the entry: from `D(a, w)` with `a = ⌊w/2⌋` the step lands on `D(0, 2 w + 2)`. -/
theorem entry_direct_value (a w : ℕ) (_hw : w % 2 = 1) (ha : a = w / 2) :
    highLevelNext (.D a w) = some (.D 0 (2 * w + 2)) := by
  have c1 : ¬ (a > w / 2) := by omega
  unfold highLevelNext
  dsimp only
  simp only [c1, eq_true ha, ↓reduceIte]

/-- The entry: from `D(a, w)` with `w` odd and no drain chain (`w ≤ 2 a + 5`) the step goes
from the even phase into the odd phase if and only if `a = ⌊w/2⌋`. The entries that come out of
a drain chain are the same coincidence at a later stage of the chain of `evalK2` (see the
translation in the README). -/
theorem entry_direct (a w : ℕ) (hw : w % 2 = 1) (hw' : w ≤ 2 * a + 5) :
    (∃ s', highLevelNext (.D a w) = some s' ∧ OddPhase s') ↔ a = w / 2 := by
  constructor
  · rintro ⟨s', h, hs'⟩
    unfold highLevelNext at h
    dsimp only at h
    by_cases c1 : a > w / 2
    · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
      subst h
      have := hs'.2
      change (2 * w + 3) % 2 = 0 at this
      omega
    by_cases c2 : a = w / 2
    · exact c2
    by_cases c3 : w = 2 * a + 2
    · omega
    · simp only [c1, c2, c3, hw', ↓reduceIte, Option.some.injEq] at h
      subst h
      have := hs'.2
      change (2 * w - 4 * a - 5) % 2 = 0 at this
      omega
  · intro h
    exact ⟨_, entry_direct_value a w hw h, rfl, by omega⟩

/-! ### B. The excursion law -/

/-- The closed form of the chain: the chain from `(a, w)` reaches the halting test after exactly
`j` rounds when `w + 2 j + 6 + 2 (a + 4) = (a + 4) 2^(j+2)`. -/
private def Chain (j a w : ℕ) : Prop := w + 2 * j + 6 + 2 * (a + 4) = (a + 4) * 2 ^ (j + 2)

private theorem evalK2_none_of_chain (j : ℕ) :
    ∀ a w : ℕ, Chain j a w → evalK2 a w = none := by
  induction j with
  | zero =>
    intro a w h
    unfold Chain at h
    have h4 : (a + 4) * 2 ^ (0 + 2) = 4 * a + 16 := by ring
    have hw : w = 2 * a + 2 := by omega
    subst hw
    rw [evalK2]
    have c1 : ¬ (a > (2 * a + 2) / 2) := by omega
    have c2 : ¬ (a = (2 * a + 2) / 2) := by omega
    simp only [c1, c2, ↓reduceIte]
  | succ j ih =>
    intro a w h
    unfold Chain at h
    have hj := lt_two_pow j
    have hX : (a + 4) * 2 ^ (j + 1 + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
    have hge : (a + 4) * 2 ^ j ≥ (a + 4) * (j + 1) := Nat.mul_le_mul_left _ hj
    have hge2 : (a + 4) * (j + 1) = a * j + a + 4 * j + 4 := by ring
    have hw : w ≥ 2 * a + 6 := by omega
    rw [evalK2]
    have c1 : ¬ (a > w / 2) := by omega
    have c2 : ¬ (a = w / 2) := by omega
    have c3 : ¬ (w = 2 * a + 2) := by omega
    have c4 : ¬ (w ≤ 2 * a + 5) := by omega
    simp only [c1, c2, c3, c4, ↓reduceIte]
    apply ih
    unfold Chain
    have e1 : (2 * a + 4 + 4) * 2 ^ (j + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
    omega

private theorem chain_of_evalK2_none (a w : ℕ) (h : evalK2 a w = none) :
    ∃ j, Chain j a w := by
  induction w using Nat.strong_induction_on generalizing a with
  | _ w ih =>
    rw [evalK2] at h
    by_cases c1 : a > w / 2
    · simp only [eq_true c1, ↓reduceIte] at h
      cases h
    by_cases c2 : a = w / 2
    · simp only [c1, eq_true c2, ↓reduceIte] at h
      cases h
    by_cases c3 : w = 2 * a + 2
    · refine ⟨0, ?_⟩
      unfold Chain
      have h4' : (a + 4) * 2 ^ (0 + 2) = 4 * a + 16 := by ring
      omega
    by_cases c4 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, eq_true c4, ↓reduceIte] at h
      cases h
    · simp only [c1, c2, c3, c4, ↓reduceIte] at h
      obtain ⟨j, hj⟩ := ih (w - 2 * a - 6) (by omega) (2 * a + 4) h
      refine ⟨j + 1, ?_⟩
      unfold Chain at hj ⊢
      have e1 : (2 * a + 4 + 4) * 2 ^ (j + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
      have e2 : (a + 4) * 2 ^ (j + 1 + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
      omega

/-- The excursion law: for every `W` (not only on the orbit), `D(0, W)` halts if and only if
`W = SW k` for a `k`. -/
theorem highLevelNext_D_zero_eq_none_iff (W : ℕ) :
    highLevelNext (.D 0 W) = none ↔ ∃ k, W = SW k := by
  unfold highLevelNext
  dsimp only
  by_cases c1 : 0 > W / 2
  · exfalso
    omega
  by_cases c2 : 0 = W / 2
  · simp only [c1, eq_true c2, ↓reduceIte]
    constructor
    · intro h
      cases h
    · rintro ⟨k, hk⟩
      have h := SW_add k
      have := lt_two_pow k
      omega
  by_cases c3 : W = 2 * 0 + 2
  · simp only [c1, c2, eq_true c3, ↓reduceIte]
    exact ⟨fun _ => ⟨0, by unfold SW; omega⟩, fun _ => trivial⟩
  by_cases c4 : W ≤ 2 * 0 + 5
  · simp only [c1, c2, c3, eq_true c4, ↓reduceIte]
    constructor
    · intro h
      cases h
    · rintro ⟨k, hk⟩
      have h := SW_add k
      have h2 := SW_even k
      rcases k with _ | k
      · unfold SW at hk
        omega
      · have h3 := lt_two_pow k
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    have hW : W ≥ 6 := by omega
    constructor
    · intro h
      obtain ⟨j, hj⟩ := chain_of_evalK2_none _ _ h
      refine ⟨j + 1, ?_⟩
      unfold Chain at hj
      have e : (2 * 0 + 2 + 4) * 2 ^ (j + 2) = 24 * 2 ^ j := by ring
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      have := SW_add (j + 1)
      omega
    · rintro ⟨k, hk⟩
      have h := SW_add k
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this
        unfold SW at hk
        omega
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      apply evalK2_none_of_chain j
      unfold Chain
      have e : (2 * 0 + 2 + 4) * 2 ^ (j + 2) = 24 * 2 ^ j := by ring
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      omega

/-- A state of the two phases halts if and only if it is `D(0, SW k)` (in the odd phase). -/
theorem highLevelNext_eq_none_iff (s : HighLevelState) (hs : Inv s) :
    highLevelNext s = none ↔ ∃ k, s = .D 0 (SW k) := by
  rcases s with ⟨a, w⟩
  rcases hs with hs | ⟨ha, hw⟩
  · constructor
    · intro h
      exact absurd h (highLevelNext_ne_none_of_odd _ hs)
    · rintro ⟨k, hk⟩
      simp only [HighLevelState.D.injEq] at hk
      have h1 : w % 2 = 1 := hs
      have h2 := SW_even k
      omega
  · subst ha
    rw [highLevelNext_D_zero_eq_none_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]⟩
    · rintro ⟨k, hk⟩
      simp only [HighLevelState.D.injEq] at hk
      exact ⟨k, hk.2⟩

/-- The excursion ends: the next state is in the even phase or in the odd phase again (the second
coincidence). -/
theorem excursion_ends (W : ℕ) (s' : HighLevelState)
    (h : highLevelNext (.D 0 W) = some s') : EvenPhase s' ∨ OddPhase s' :=
  inv_highLevelNext _ s' h

/-! ### C. The criterion -/

private theorem exists_halt_step (h : CollatzHalts highLevelNext highLevelStart) :
    ∃ t s, orbit t = some s ∧ highLevelNext s = none := by
  obtain ⟨n, hn⟩ := h
  change (orbit n).isNone at hn
  induction n with
  | zero => simp [orbit] at hn
  | succ n ih =>
    by_cases hn' : (orbit n).isNone
    · exact ih hn'
    · rcases hcur : orbit n with _ | s
      · rw [hcur] at hn'
        simp at hn'
      · refine ⟨n, s, hcur, ?_⟩
        rw [orbit_succ, hcur] at hn
        exact Option.isNone_iff_eq_none.mp hn

/-- The halting criterion: the machine halts if and only if the orbit of the high-level
acceleration ever reaches `D(0, W)` with `W = SW k` for a `k`. -/
theorem isHalt_iff_D_SW :
    IsHalt target ↔ ∃ t k, orbit t = some (.D 0 (SW k)) := by
  rw [isHalt_iff_highLevel_acceleration]
  constructor
  · intro h
    obtain ⟨t, s, ht, hs⟩ := exists_halt_step h
    obtain ⟨k, hk⟩ := (highLevelNext_eq_none_iff s (inv_orbit t s ht)).1 hs
    exact ⟨t, k, by rw [ht, hk]⟩
  · rintro ⟨t, k, ht⟩
    refine ⟨t + 1, ?_⟩
    change (orbit (t + 1)).isNone
    rw [orbit_succ, ht]
    have : highLevelNext (.D 0 (SW k)) = none :=
      (highLevelNext_D_zero_eq_none_iff _).2 ⟨k, rfl⟩
    simp [this]

end AntihydraOrbit.Line487
