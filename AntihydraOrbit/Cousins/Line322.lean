import Mathlib
import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

/-!
# The machine `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`: the halting criterion

DeepMind's `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart = D_0(0, 3)`
(`isHalt_iff_highLevel_acceleration`). Its states are `D_p(a, w)` with `p` a bit and `a, w`
natural numbers, and the step is described in the doc comment of that file.

This file records the structure of that map that decides halting.

* **Two phases.** In the *even phase* the number `w` is odd; in the *odd phase* the state is
  `D_1(1, W)` with `W` even. Every state on the orbit is in one of the two phases
  (`Inv`, `inv_orbit`), and no state of the even phase halts (`highLevelNext_ne_none_of_odd`).
* **Entry.** The even phase leads into the odd phase only through the coincidence `a = ⌊w/2⌋`,
  after which the state is `D_1(1, W)`.
* **Excursion.** From `D_1(1, W)` the next step is `drainJ1 1 W`, and it halts if and only if
  `W` is one of `SW j = 20 · 2^j - 2 j - 16` (`drainJ1_one_eq_none_iff`).
* **Criterion.** The machine halts if and only if the orbit reaches `D_1(1, SW j)` for some `j`
  (`isHalt_iff_D_SW`). Whether that happens is open.

In the variables of the Cubic Cap macro map, `D_p(a, w)` is the state `(w + 1, p + 1, a + 1)`, an
entry is a state with `a = 2c` and `b' = b + a`, and `SW j = 2 (b' - 2)` with
`b' = 5 · 2^(j+1) - (j + 1) - 5`.
-/

namespace AntihydraOrbit.Line322

open BusyBeaver
open BusyBeaver.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
  (target HighLevelState highLevelNext highLevelStart drainJ1
    isHalt_iff_highLevel_acceleration)

/-! ### Definitions (the trusted base) -/

/-- The state of the high-level acceleration after `t` steps (`none` once the machine halted). -/
def orbit (t : ℕ) : Option HighLevelState :=
  (Option.bind · highLevelNext)^[t] (some highLevelStart)

/-- The even phase: `w` is odd. -/
def EvenPhase : HighLevelState → Prop
  | .D _ _ w => w % 2 = 1

/-- The odd phase: the state is `D_1(1, W)` with `W` even. -/
def OddPhase : HighLevelState → Prop
  | .D p a w => p = true ∧ a = 1 ∧ w % 2 = 0

/-- The invariant of the orbit: every state is in one of the two phases. -/
def Inv (s : HighLevelState) : Prop := EvenPhase s ∨ OddPhase s

/-- The entry values `W` of the odd phase that halt: `20 · 2^j - 2 j - 16`. -/
def SW (j : ℕ) : ℕ := 20 * 2 ^ j - 2 * j - 16

/-! ### Sanity anchors: the first steps of the orbit -/

example : orbit 0 = some (.D false 0 3) := rfl
example : orbit 1 = some (.D false 2 1) := by decide
example : orbit 2 = some (.D false 0 7) := by decide
/-- One step of the orbit, from a state given by a hypothesis. -/
private theorem orbit_succ_of {t : ℕ} {s s' : HighLevelState} (h : orbit t = some s)
    (hs : highLevelNext s = some s') : orbit (t + 1) = some s' := by
  simp only [orbit] at h ⊢
  rw [Function.iterate_succ_apply', h]
  exact hs

/-- The anchor at step 8: the first state of the odd phase on the orbit. The orbit is followed
step by step because `decide` cannot evaluate the well-founded `drainJ1`. -/
example : orbit 8 = some (.D true 1 24) := by
  have h3 : orbit 3 = some (.D false 1 9) :=
    orbit_succ_of (by decide : orbit 2 = some (.D false 0 7)) (by simp [highLevelNext, drainJ1])
  have h4 : orbit 4 = some (.D false 3 9) := orbit_succ_of h3 (by simp [highLevelNext, drainJ1])
  have h5 : orbit 5 = some (.D false 8 1) := orbit_succ_of h4 (by simp [highLevelNext])
  have h6 : orbit 6 = some (.D false 6 7) := orbit_succ_of h5 (by simp [highLevelNext])
  have h7 : orbit 7 = some (.D false 1 19) := orbit_succ_of h6 (by simp [highLevelNext])
  exact orbit_succ_of h7 (by simp [highLevelNext, drainJ1])
example : highLevelNext (.D false 1 19) = some (.D true 1 24) := by
  simp [highLevelNext, drainJ1]
example : highLevelNext (.D true 1 24) = some (.D false 15 3) := by
  simp [highLevelNext, drainJ1]
example : highLevelNext (.D true 1 4) = none := by
  simp [highLevelNext, drainJ1]
example : highLevelNext (.D true 1 22) = none := by
  simp [highLevelNext, drainJ1]
example : [SW 0, SW 1, SW 2, SW 3, SW 4] = [4, 22, 60, 138, 296] := by decide

/-! ### Elementary facts -/

private theorem orbit_succ (t : ℕ) : orbit (t + 1) = (orbit t).bind highLevelNext := by
  unfold orbit
  exact Function.iterate_succ_apply' _ _ _

/-- `j < 2^j`, in the form used below. -/
private theorem lt_two_pow (j : ℕ) : j < 2 ^ j := Nat.lt_two_pow_self

/-- `SW j + 2 j + 16 = 20 · 2^j`. -/
theorem SW_add (j : ℕ) : SW j + 2 * j + 16 = 20 * 2 ^ j := by
  have h := lt_two_pow j
  unfold SW
  omega

/-- Every `SW j` is even. -/
theorem SW_even (j : ℕ) : SW j % 2 = 0 := by
  have h := SW_add j
  omega

/-! ### A. The phase invariant -/

/-- Every step of a drain chain lands in one of the two phases. -/
theorem inv_drainJ1 (a w : ℕ) (s' : HighLevelState) (h : drainJ1 a w = some s') : Inv s' := by
  induction w using Nat.strong_induction_on generalizing a s' with
  | _ w ih =>
    rw [drainJ1] at h
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w + 7) % 2 = 1
      omega
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w + 3) % 2 = 1
      omega
    by_cases c3 : a = w / 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte, Option.some.injEq] at h
      subst h
      right
      exact ⟨rfl, rfl, by omega⟩
    by_cases c4 : w = 2 * a + 2
    · simp only [c1, c2, c3, eq_true c4, ↓reduceIte] at h
      cases h
    by_cases c5 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, c4, eq_true c5, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w - 4 * a - 5) % 2 = 1
      omega
    · simp only [c1, c2, c3, c4, c5, ↓reduceIte] at h
      exact ih (w - 2 * a - 6) (by omega) (2 * a + 4) s' h

/-- Every step lands in one of the two phases, whatever the state it starts from. -/
theorem inv_highLevelNext (s s' : HighLevelState) (h : highLevelNext s = some s') : Inv s' := by
  rcases s with ⟨p, a, w⟩
  cases p with
  | true => exact inv_drainJ1 a w s' h
  | false =>
    unfold highLevelNext at h
    dsimp only at h
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w + 5) % 2 = 1
      omega
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w + 1) % 2 = 1
      omega
    by_cases c3 : a = w / 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte, Option.some.injEq] at h
      subst h
      right
      exact ⟨rfl, rfl, by omega⟩
    by_cases c4 : w = 2 * a + 2
    · simp only [c1, c2, c3, eq_true c4, ↓reduceIte] at h
      cases h
    by_cases c5 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, c4, eq_true c5, ↓reduceIte, Option.some.injEq] at h
      subst h
      left
      change (2 * w - 4 * a - 5) % 2 = 1
      omega
    · simp only [c1, c2, c3, c4, c5, ↓reduceIte] at h
      exact inv_drainJ1 _ _ s' h

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

/-- A halt needs an even `w`: a chain of `drainJ1` from an odd `w` never halts. -/
theorem drainJ1_ne_none_of_odd (a w : ℕ) (hw : w % 2 = 1) : drainJ1 a w ≠ none := by
  induction w using Nat.strong_induction_on generalizing a with
  | _ w ih =>
    rw [drainJ1]
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c3 : a = w / 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c4 : w = 2 * a + 2
    · exfalso
      omega
    by_cases c5 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, c4, eq_true c5, ↓reduceIte]
      exact Option.some_ne_none _
    · simp only [c1, c2, c3, c4, c5, ↓reduceIte]
      exact ih (w - 2 * a - 6) (by omega) (2 * a + 4) (by omega)

/-- A state in the even phase never halts. -/
theorem highLevelNext_ne_none_of_odd (s : HighLevelState) (h : EvenPhase s) :
    highLevelNext s ≠ none := by
  rcases s with ⟨p, a, w⟩
  have hw : w % 2 = 1 := h
  cases p with
  | true => exact drainJ1_ne_none_of_odd a w hw
  | false =>
    unfold highLevelNext
    dsimp only
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c3 : a = w / 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte]
      exact Option.some_ne_none _
    by_cases c4 : w = 2 * a + 2
    · exfalso
      omega
    by_cases c5 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, c4, eq_true c5, ↓reduceIte]
      exact Option.some_ne_none _
    · simp only [c1, c2, c3, c4, c5, ↓reduceIte]
      exact drainJ1_ne_none_of_odd _ _ (by omega)

/-- The value of the entry: from `D_0(a, w)` with `w` odd and `a = ⌊w/2⌋` the step lands on
`D_1(1, 2 w)`. -/
theorem entry_direct_value (a w : ℕ) (_hw : w % 2 = 1) (ha : a = w / 2) :
    highLevelNext (.D false a w) = some (.D true 1 (2 * w)) := by
  unfold highLevelNext
  dsimp only
  simp [ha]

/-- The entry: from `D_0(a, w)` with `w` odd and no drain chain (`w ≤ 2 a + 5`) the step goes
from the even phase into the odd phase if and only if `a = ⌊w/2⌋`. The entries that come out of
a drain chain are the same coincidence at a later stage of the chain of `drainJ1` (see the
translation in the README). -/
theorem entry_direct (a w : ℕ) (hw : w % 2 = 1) (hw' : w ≤ 2 * a + 5) :
    (∃ s', highLevelNext (.D false a w) = some s' ∧ OddPhase s') ↔ a = w / 2 := by
  constructor
  · rintro ⟨s', h, hs'⟩
    unfold highLevelNext at h
    dsimp only at h
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact absurd hs'.1 (by simp)
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte, Option.some.injEq] at h
      subst h
      have := hs'.2.2
      change (2 * w + 1) % 2 = 0 at this
      omega
    by_cases c3 : a = w / 2
    · exact c3
    by_cases c4 : w = 2 * a + 2
    · omega
    · simp only [c1, c2, c3, c4, hw', ↓reduceIte, Option.some.injEq] at h
      subst h
      exact absurd hs'.1 (by simp)
  · intro h
    exact ⟨_, entry_direct_value a w hw h, rfl, rfl, by omega⟩

/-! ### B. The excursion law -/

/-- The closed form of the chain: the chain from `(a, w)` reaches the halting test after exactly
`j` rounds when `w + 2 j + 6 + 2 (a + 4) = (a + 4) 2^(j+2)`. -/
private def Chain (j a w : ℕ) : Prop := w + 2 * j + 6 + 2 * (a + 4) = (a + 4) * 2 ^ (j + 2)

private theorem drainJ1_none_of_chain (j : ℕ) :
    ∀ a w : ℕ, Chain j a w → drainJ1 a w = none := by
  induction j with
  | zero =>
    intro a w h
    unfold Chain at h
    have h4 : (a + 4) * 2 ^ (0 + 2) = 4 * a + 16 := by ring
    have hw : w = 2 * a + 2 := by omega
    subst hw
    rw [drainJ1]
    have c1 : ¬ (a ≥ (2 * a + 2) / 2 + 2) := by omega
    have c2 : ¬ (a = (2 * a + 2) / 2 + 1) := by omega
    have c3 : ¬ (a = (2 * a + 2) / 2) := by omega
    simp only [c1, c2, c3, ↓reduceIte]
  | succ j ih =>
    intro a w h
    unfold Chain at h
    have hj := lt_two_pow j
    have hX : (a + 4) * 2 ^ (j + 1 + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
    have hge : (a + 4) * 2 ^ j ≥ (a + 4) * (j + 1) := Nat.mul_le_mul_left _ hj
    have hge2 : (a + 4) * (j + 1) = a * j + a + 4 * j + 4 := by ring
    have hw : w ≥ 2 * a + 6 := by omega
    rw [drainJ1]
    have c1 : ¬ (a ≥ w / 2 + 2) := by omega
    have c2 : ¬ (a = w / 2 + 1) := by omega
    have c3 : ¬ (a = w / 2) := by omega
    have c4 : ¬ (w = 2 * a + 2) := by omega
    have c5 : ¬ (w ≤ 2 * a + 5) := by omega
    simp only [c1, c2, c3, c4, c5, ↓reduceIte]
    apply ih
    unfold Chain
    have e1 : (2 * a + 4 + 4) * 2 ^ (j + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
    omega

private theorem chain_of_drainJ1_none (a w : ℕ) (h : drainJ1 a w = none) :
    ∃ j, Chain j a w := by
  induction w using Nat.strong_induction_on generalizing a with
  | _ w ih =>
    rw [drainJ1] at h
    by_cases c1 : a ≥ w / 2 + 2
    · simp only [eq_true c1, ↓reduceIte] at h
      cases h
    by_cases c2 : a = w / 2 + 1
    · simp only [c1, eq_true c2, ↓reduceIte] at h
      cases h
    by_cases c3 : a = w / 2
    · simp only [c1, c2, eq_true c3, ↓reduceIte] at h
      cases h
    by_cases c4 : w = 2 * a + 2
    · refine ⟨0, ?_⟩
      unfold Chain
      have h4' : (a + 4) * 2 ^ (0 + 2) = 4 * a + 16 := by ring
      omega
    by_cases c5 : w ≤ 2 * a + 5
    · simp only [c1, c2, c3, c4, eq_true c5, ↓reduceIte] at h
      cases h
    · simp only [c1, c2, c3, c4, c5, ↓reduceIte] at h
      obtain ⟨j, hj⟩ := ih (w - 2 * a - 6) (by omega) (2 * a + 4) h
      refine ⟨j + 1, ?_⟩
      unfold Chain at hj ⊢
      have e1 : (2 * a + 4 + 4) * 2 ^ (j + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
      have e2 : (a + 4) * 2 ^ (j + 1 + 2) = 8 * ((a + 4) * 2 ^ j) := by ring
      omega

/-- The excursion law: for every `W` (not only on the orbit), `D_1(1, W)` halts if and only if
`W = SW j` for a `j`. -/
theorem drainJ1_one_eq_none_iff (W : ℕ) : drainJ1 1 W = none ↔ ∃ j, W = SW j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := chain_of_drainJ1_none 1 W h
    refine ⟨j, ?_⟩
    unfold Chain at hj
    have e : (1 + 4) * 2 ^ (j + 2) = 20 * 2 ^ j := by ring
    have := SW_add j
    omega
  · rintro ⟨j, rfl⟩
    apply drainJ1_none_of_chain j
    unfold Chain
    have e : (1 + 4) * 2 ^ (j + 2) = 20 * 2 ^ j := by ring
    have := SW_add j
    omega

theorem highLevelNext_D_true_one_eq_none_iff (W : ℕ) :
    highLevelNext (.D true 1 W) = none ↔ ∃ j, W = SW j :=
  drainJ1_one_eq_none_iff W

/-- A state of the two phases halts if and only if it is `D_1(1, SW j)` (in the odd phase). -/
theorem highLevelNext_eq_none_iff (s : HighLevelState) (hs : Inv s) :
    highLevelNext s = none ↔ ∃ j, s = .D true 1 (SW j) := by
  rcases s with ⟨p, a, w⟩
  rcases hs with hs | ⟨hp, ha, hw⟩
  · constructor
    · intro h
      exact absurd h (highLevelNext_ne_none_of_odd _ hs)
    · rintro ⟨j, hj⟩
      simp only [HighLevelState.D.injEq] at hj
      have h1 : w % 2 = 1 := hs
      have h2 := SW_even j
      omega
  · subst hp
    subst ha
    rw [highLevelNext_D_true_one_eq_none_iff]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hj]⟩
    · rintro ⟨j, hj⟩
      simp only [HighLevelState.D.injEq] at hj
      exact ⟨j, hj.2.2⟩

/-- Away from `SW`, the excursion ends: the next state is in the even phase, or it is again an
odd-phase state `D_1(1, W')` (the second coincidence). -/
theorem excursion_ends (W : ℕ) (s' : HighLevelState)
    (h : drainJ1 1 W = some s') : EvenPhase s' ∨ OddPhase s' :=
  inv_drainJ1 1 W s' h

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
acceleration ever reaches `D_1(1, W)` with `W = SW j` for a `j`. -/
theorem isHalt_iff_D_SW :
    IsHalt target ↔ ∃ t j, orbit t = some (.D true 1 (SW j)) := by
  rw [isHalt_iff_highLevel_acceleration]
  constructor
  · intro h
    obtain ⟨t, s, ht, hs⟩ := exists_halt_step h
    obtain ⟨j, hj⟩ := (highLevelNext_eq_none_iff s (inv_orbit t s ht)).1 hs
    exact ⟨t, j, by rw [ht, hj]⟩
  · rintro ⟨t, j, ht⟩
    refine ⟨t + 1, ?_⟩
    change (orbit (t + 1)).isNone
    rw [orbit_succ, ht]
    have : highLevelNext (.D true 1 (SW j)) = none :=
      (highLevelNext_D_true_one_eq_none_iff _).2 ⟨j, rfl⟩
    simp [this]

end AntihydraOrbit.Line322
