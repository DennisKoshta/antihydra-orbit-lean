import Mathlib
import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

/-!
# The machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`: the halting criterion

DeepMind's `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart = P_1(2, 1)`
(`isHalt_iff_highLevel_acceleration`). Its states are `P_1(a, c)` with `a, c` natural numbers;
the countdown `evalP2` collapses the inner loop.

This file records the structure of that map that decides halting. The idea is the same as for
the machine of `Line322.lean`, but here the excursion takes several steps of `highLevelNext`.

* **Waypoints.** A *waypoint* is a state `P_1(a, c)` with `c` odd (the *odd-`c` phase*) or
  with `a = 2` and `c` even (an *entry* of the even-`c` phase). The odd-`c` phase never halts
  (`m_step`) and leaves its parity only through `P_1(a, 1) -> P_1(a + 2, 0)`, which goes on to
  the entry `P_1(2, a + 3)` (`entry_two_steps`).
* **Excursion.** From an entry `P_1(2, c0)` with `c0` even, the states `P_1(a_i, c_i)` with
  `a_i + 12 = 14 · 2^i` and `c_{i+1} = c_i - a_i - 10` follow each other (two steps of
  `highLevelNext` each) until the chain ends. It halts, at `P_1(a_i, 4)`, if and only if `c0` is
  one of `SW k = 14 · 2^k - 2 k - 10` (`excursion_halts`, `excursion_ends`), and otherwise it
  stops at the next waypoint, for every `c0`.
* **Criterion.** The machine halts if and only if the orbit reaches `P_1(2, SW k)` for some `k`
  (`isHalt_iff_P_SW`). Whether that happens is open.

In the variables of the Cubic Cap macro map, an entry `P_1(2, c0)` is the state `(c0 - 1, 1, 1)`
that follows the macro step with `a = 2c` and `b' = b + a`, and `SW k = 2 (b' + 1)` with
`b' = 7 · 2^k - k - 6`.
-/

namespace AntihydraOrbit.Line167

open BusyBeaver
open BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
  (target HighLevelState highLevelNext highLevelStart evalP2
    isHalt_iff_highLevel_acceleration)

/-! ### Definitions (the trusted base) -/

/-- `n` steps of the high-level acceleration (`none` once it halted). -/
def it (n : ℕ) (o : Option HighLevelState) : Option HighLevelState :=
  (Option.bind · highLevelNext)^[n] o

/-- The state of the high-level acceleration after `t` steps (`none` once the machine halted). -/
def orbit (t : ℕ) : Option HighLevelState :=
  it t (some highLevelStart)

/-- A waypoint: `c` odd, or an entry `P_1(2, c)` with `c` even. -/
def Wp : HighLevelState → Prop
  | .P_1 a c => c % 2 = 1 ∨ (a = 2 ∧ c % 2 = 0)

/-- The entry values `c0` that halt: `14 · 2^k - 2 k - 10`. -/
def SW (k : ℕ) : ℕ := 14 * 2 ^ k - 2 * k - 10

/-! ### Sanity anchors: the first steps of the orbit -/

example : orbit 0 = some (.P_1 2 1) := rfl
example : highLevelNext (.P_1 5 3) = some (.P_1 8 1) := by
  simp [highLevelNext, evalP2]
example : highLevelNext (.P_1 2 4) = some (.P_1 5 2) := by simp [highLevelNext]
example : highLevelNext (.P_1 5 2) = none := by simp [highLevelNext]
example : SW 0 = 4 ∧ SW 1 = 16 ∧ SW 2 = 42 ∧ SW 3 = 96 := by decide

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

theorem next_c0 (a : ℕ) : highLevelNext (.P_1 a 0) = some (.P_1 2 (a + 1)) := by
  simp [highLevelNext]

theorem next_c1 (a : ℕ) : highLevelNext (.P_1 a 1) = some (.P_1 (a + 2) 0) := by
  simp [highLevelNext]

theorem next_even (a c : ℕ) (h : a % 2 = 0) :
    highLevelNext (.P_1 a (c + 2)) = some (.P_1 (a + 3) c) := by
  simp [highLevelNext, h]

theorem next_halt (a : ℕ) (h : a % 2 = 1) : highLevelNext (.P_1 a 2) = none := by
  simp [highLevelNext, h]

theorem next_three (a : ℕ) (h : a % 2 = 1) :
    highLevelNext (.P_1 a 3) = some (evalP2 (a / 2) 1) := by
  simp [highLevelNext, h]

theorem next_big (a c : ℕ) (h : a % 2 = 1) :
    highLevelNext (.P_1 a (c + 4)) = some (evalP2 (a / 2 + 1) (c + 2)) := by
  simp [highLevelNext, h]

/-! ### The countdown `evalP2` -/

theorem evalP2_hi (k c : ℕ) (h : 2 * k + 2 ≤ c) :
    evalP2 k c = .P_1 (4 * k + 4) (c - 2 * k - 2) := by
  have h1 : 2 * k ≤ c := by omega
  have h2 : ¬ c ≤ 2 * k + 1 := by omega
  rw [evalP2]
  simp [h1, h2]

theorem evalP2_mid (k c : ℕ) (h1 : 2 * k ≤ c) (h2 : c ≤ 2 * k + 1) :
    evalP2 k c = .P_1 0 (2 * c + 3) := by
  rw [evalP2]
  simp [h1, h2]

theorem evalP2_lo (k c : ℕ) (h : c < 2 * k) :
    evalP2 k c = evalP2 (k - c / 2 - 1) (2 * c + 3) := by
  have h1 : ¬ 2 * k ≤ c := by omega
  rw [evalP2]
  simp [h1]

/-- With an odd second argument the countdown returns a state with `c` odd. -/
theorem evalP2_odd : ∀ k c : ℕ, c % 2 = 1 → ∃ x y, evalP2 k c = .P_1 x y ∧ y % 2 = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro c hc
    by_cases h1 : 2 * k ≤ c
    · by_cases h2 : c ≤ 2 * k + 1
      · exact ⟨0, 2 * c + 3, evalP2_mid k c h1 h2, by omega⟩
      · exact ⟨4 * k + 4, c - 2 * k - 2, evalP2_hi k c (by omega), by omega⟩
    · have h3 : c < 2 * k := by omega
      rw [evalP2_lo k c h3]
      exact ih _ (by omega) _ (by omega)

example : orbit 1 = some (.P_1 4 0) := it_one (next_c1 2)
example : orbit 2 = some (.P_1 2 5) := it_two (next_c1 2) (next_c0 4)

/-! ### The odd-`c` phase -/

/-- From an odd `c` other than 1 the step lands again on an odd `c`: this phase never halts. -/
theorem m_step (a c : ℕ) (hc : c % 2 = 1) (h1 : c ≠ 1) :
    ∃ x y, highLevelNext (.P_1 a c) = some (.P_1 x y) ∧ y % 2 = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 3 := ⟨c - 3, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · exact ⟨a + 3, d + 1, next_even a (d + 1) ha, by omega⟩
  · rcases d with _ | _ | e
    · obtain ⟨x, y, hx, hy⟩ := evalP2_odd (a / 2) 1 (by omega)
      exact ⟨x, y, (next_three a ha).trans (by rw [hx]), hy⟩
    · omega
    · have e1 : highLevelNext (.P_1 a (e + 2 + 3)) = some (evalP2 (a / 2 + 1) (e + 1 + 2)) :=
        next_big a (e + 1) ha
      obtain ⟨x, y, hx, hy⟩ := evalP2_odd (a / 2 + 1) (e + 1 + 2) (by omega)
      exact ⟨x, y, e1.trans (by rw [hx]), hy⟩

theorem m_no_halt (a c : ℕ) (hc : c % 2 = 1) : highLevelNext (.P_1 a c) ≠ none := by
  by_cases h1 : c = 1
  · subst h1
    rw [next_c1]
    simp
  · obtain ⟨x, y, hx, _⟩ := m_step a c hc h1
    rw [hx]
    simp

/-- The only exit of the odd-`c` phase: `P_1(a, 1)` with `a` odd reaches the entry
`P_1(2, a + 3)` (and with `a` even it reaches `P_1(2, a + 3)`, again with `c` odd). -/
theorem entry_two_steps (a : ℕ) : it 2 (some (.P_1 a 1)) = some (.P_1 2 (a + 3)) := by
  apply it_two (s1 := .P_1 (a + 2) 0)
  · exact next_c1 a
  · rw [next_c0]

/-! ### The closed form of the excursion -/

/-- `Hal a c`: the chain from `P_1(a, c)` ends at `P_1(a_i, 4)` for some stage `i`. -/
def Hal (a c : ℕ) : Prop := ∃ i, c + (a + 12) + 2 * i = (a + 12) * 2 ^ i + 4

theorem SW_add (k : ℕ) : SW k + 2 * k + 10 = 14 * 2 ^ k := by
  have h := Nat.lt_two_pow_self (n := k)
  unfold SW
  omega

theorem Hal_two_iff (c : ℕ) : Hal 2 c ↔ ∃ k, c = SW k := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have := SW_add i
    omega
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    have := SW_add k
    omega

theorem Hal_bound {a c : ℕ} (h : Hal a c) : c = 4 ∨ a + 14 ≤ c := by
  obtain ⟨i, hi⟩ := h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · left
    simp at hi
    omega
  · right
    have h1 : i + 1 ≤ 2 ^ i := Nat.lt_two_pow_self
    have h2 : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hpos
    nlinarith [Nat.mul_le_mul_left a h2]

theorem Hal_rec {a c c' : ℕ} (h : c = c' + a + 10) : Hal a c ↔ Hal (2 * a + 12) c' := by
  subst h
  constructor
  · rintro ⟨i, hi⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp at hi
      omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine ⟨i', ?_⟩
      have e1 : (a + 12) * 2 ^ (i' + 1) = 2 * ((a + 12) * 2 ^ i') := by ring
      have e2 : (2 * a + 12 + 12) * 2 ^ i' = 2 * ((a + 12) * 2 ^ i') := by ring
      omega
  · rintro ⟨i, hi⟩
    refine ⟨i + 1, ?_⟩
    have e1 : (a + 12) * 2 ^ (i + 1) = 2 * ((a + 12) * 2 ^ i) := by ring
    have e2 : (2 * a + 12 + 12) * 2 ^ i = 2 * ((a + 12) * 2 ^ i) := by ring
    omega

/-! ### The excursion from an even `a` and an even `c` -/

/-- The excursion law for every even pair `(a, c)` with `a` even and at least 2: either the
chain halts (exactly when `Hal a c`), or it reaches a waypoint after at least one step. -/
theorem stage : ∀ c a : ℕ, a % 2 = 0 → 2 ≤ a → c % 2 = 0 →
    (Hal a c → ∃ j, it j (some (.P_1 a c)) = none) ∧
    (¬ Hal a c → ∃ j, 1 ≤ j ∧ ∃ s', it j (some (.P_1 a c)) = some s' ∧ Wp s') := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a ha ha2 hc
    obtain rfl | rfl | rfl | h6 : c = 0 ∨ c = 2 ∨ c = 4 ∨ 6 ≤ c := by omega
    · refine ⟨fun h => ?_, fun _ => ⟨1, le_refl _, .P_1 2 (a + 1), it_one (next_c0 a), ?_⟩⟩
      · rcases Hal_bound h with h | h <;> omega
      · left; omega
    · refine ⟨fun h => ?_, fun _ => ⟨2, by norm_num, .P_1 2 (a + 4), ?_, ?_⟩⟩
      · rcases Hal_bound h with h | h <;> omega
      · exact it_two (s1 := .P_1 (a + 3) 0) (next_even a 0 ha) (next_c0 (a + 3))
      · right; exact ⟨rfl, by omega⟩
    · have hH : Hal a 4 := ⟨0, by simp only [pow_zero, mul_one, mul_zero]; omega⟩
      refine ⟨fun _ => ⟨3, ?_⟩, fun h => absurd hH h⟩
      have e1 : highLevelNext (.P_1 a 4) = some (.P_1 (a + 3) 2) := next_even a 2 ha
      have e2 : highLevelNext (.P_1 (a + 3) 2) = none := next_halt _ (by omega)
      simp [it_succ_some, e1, e2, it_none]
    · -- c = e + 6: two steps and then the countdown
      obtain ⟨e, rfl⟩ : ∃ e, c = e + 6 := ⟨c - 6, by omega⟩
      have e1 : highLevelNext (.P_1 a (e + 6)) = some (.P_1 (a + 3) (e + 4)) :=
        next_even a (e + 4) ha
      have e2 : highLevelNext (.P_1 (a + 3) (e + 4)) = some (evalP2 (a / 2 + 2) (e + 2)) := by
        have := next_big (a + 3) e (by omega)
        rw [show (a + 3) / 2 + 1 = a / 2 + 2 by omega] at this
        exact this
      by_cases hhi : a + 6 ≤ e + 2
      · -- the chain goes on with a' = 2a + 12 and c' = c - a - 10
        have e3 : evalP2 (a / 2 + 2) (e + 2) = .P_1 (2 * a + 12) (e - a - 4) := by
          have := evalP2_hi (a / 2 + 2) (e + 2) (by omega)
          rw [this]
          congr 1 <;> omega
        have h2 : it 2 (some (.P_1 a (e + 6))) = some (.P_1 (2 * a + 12) (e - a - 4)) :=
          it_two e1 (by rw [e2, e3])
        obtain ⟨ih1, ih2⟩ := ih (e - a - 4) (by omega) (2 * a + 12) (by omega) (by omega)
          (by omega)
        have hrec : Hal a (e + 6) ↔ Hal (2 * a + 12) (e - a - 4) := Hal_rec (by omega)
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨j, hj⟩ := ih1 (hrec.mp h)
          exact ⟨j + 2, by rw [it_trans j h2, hj]⟩
        · obtain ⟨j, hj1, s', hs, hwp⟩ := ih2 (fun h' => h (hrec.mpr h'))
          exact ⟨j + 2, by omega, s', by rw [it_trans j h2, hs], hwp⟩
      · -- the chain ends here: the countdown returns a waypoint
        have hnot : ¬ Hal a (e + 6) := by
          intro h
          rcases Hal_bound h with h | h <;> omega
        refine ⟨fun h => absurd h hnot, fun _ => ?_⟩
        by_cases hmid : e + 2 = a + 4
        · have e3 : evalP2 (a / 2 + 2) (e + 2) = .P_1 0 (2 * (e + 2) + 3) :=
            evalP2_mid _ _ (by omega) (by omega)
          refine ⟨2, by norm_num, .P_1 0 (2 * (e + 2) + 3), ?_, ?_⟩
          · exact it_two e1 (by rw [e2, e3])
          · left; omega
        · have hlt : e + 2 < 2 * (a / 2 + 2) := by omega
          obtain ⟨x, y, hxy, hy⟩ := evalP2_odd (a / 2 + 2 - (e + 2) / 2 - 1)
            (2 * (e + 2) + 3) (by omega)
          have e3 : evalP2 (a / 2 + 2) (e + 2) = .P_1 x y := by
            rw [evalP2_lo _ _ hlt, hxy]
          refine ⟨2, by norm_num, .P_1 x y, ?_, ?_⟩
          · exact it_two e1 (by rw [e2, e3])
          · left; exact hy

/-- The excursion law at an entry, for every even `c0`: it halts if `c0` is one of the `SW k`. -/
theorem excursion_halts (c0 : ℕ) (hc : c0 % 2 = 0) (hk : ∃ k, c0 = SW k) :
    ∃ j, it j (some (.P_1 2 c0)) = none :=
  (stage c0 2 rfl le_rfl hc).1 ((Hal_two_iff c0).mpr hk)

/-- ... and otherwise it ends, after at least one step, at the next waypoint. -/
theorem excursion_ends (c0 : ℕ) (hc : c0 % 2 = 0) (hk : ¬ ∃ k, c0 = SW k) :
    ∃ j, 1 ≤ j ∧ ∃ s', it j (some (.P_1 2 c0)) = some s' ∧ Wp s' :=
  (stage c0 2 rfl le_rfl hc).2 (fun h => hk ((Hal_two_iff c0).mp h))

/-! ### From waypoint to waypoint -/

/-- Every waypoint is an entry that halts, or reaches the next waypoint after at least one
step (and, since `it` stays `none` once it is `none`, without halting on the way). -/
theorem next_waypoint (a c : ℕ) (h : Wp (.P_1 a c)) :
    (a = 2 ∧ ∃ k, c = SW k) ∨
      ∃ j, 1 ≤ j ∧ ∃ s', it j (some (.P_1 a c)) = some s' ∧ Wp s' := by
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · -- c even: then a = 2
    have ha : a = 2 := by
      rcases h with h | h
      · omega
      · exact h.1
    subst ha
    by_cases hk : ∃ k, c = SW k
    · exact Or.inl ⟨rfl, hk⟩
    · exact Or.inr (excursion_ends c hc hk)
  · right
    by_cases h1 : c = 1
    · subst h1
      refine ⟨2, by norm_num, .P_1 2 (a + 3), entry_two_steps a, ?_⟩
      change (a + 3) % 2 = 1 ∨ (2 = 2 ∧ (a + 3) % 2 = 0)
      omega
    · obtain ⟨x, y, hx, hy⟩ := m_step a c hc h1
      exact ⟨1, le_refl _, .P_1 x y, it_one hx, Or.inl hy⟩

/-! ### The criterion -/

theorem Wp_start : Wp highLevelStart := Or.inl (by decide)

/-- The machine halts if and only if the orbit reaches an entry `P_1(2, SW k)`. -/
theorem isHalt_iff_P_SW : IsHalt target ↔ ∃ t k, orbit t = some (.P_1 2 (SW k)) := by
  rw [isHalt_iff_highLevel_acceleration]
  constructor
  · rintro ⟨n, hn⟩
    have key : ∀ n : ℕ, ∀ a c t : ℕ, Wp (.P_1 a c) → orbit t = some (.P_1 a c) →
        (it n (some (.P_1 a c))).isNone → ∃ t k, orbit t = some (.P_1 2 (SW k)) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro a c t hwp ht hnone
        rcases next_waypoint a c hwp with ⟨rfl, k, rfl⟩ | ⟨j, hj, ⟨x, y⟩, hs, hwp'⟩
        · exact ⟨t, k, ht⟩
        · have hnone' : it n (some (.P_1 a c)) = none := Option.isNone_iff_eq_none.mp hnone
          have hlt : j < n := by
            by_contra hge
            have hj' : j = (j - n) + n := by omega
            rw [hj', it_add, hnone', it_none] at hs
            exact absurd hs (by simp)
          have h3 := it_trans (n - j) hs
          rw [show n - j + j = n by omega] at h3
          have h2 : (it (n - j) (some (.P_1 x y))).isNone := by
            rw [← h3]
            exact hnone
          exact ih (n - j) (by omega) x y (j + t) hwp' (by rw [orbit_add, ht, hs]) h2
    exact key n 2 1 0 Wp_start rfl hn
  · rintro ⟨t, k, ht⟩
    have hev : SW k % 2 = 0 := by
      have := SW_add k
      omega
    obtain ⟨j, hj⟩ := excursion_halts (SW k) hev ⟨k, rfl⟩
    refine ⟨j + t, ?_⟩
    have h : orbit (j + t) = none := by rw [orbit_add, ht]; exact hj
    change (orbit (j + t)).isNone
    rw [h]
    rfl

end AntihydraOrbit.Line167
