import Mathlib
import BusyBeaver.BB6.Accelerations.M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD
import AntihydraOrbit.Cousins.Line439Base

/-!
# The machine `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD`: explicit stack map and exposure law

DeepMind's `cryptids` module for this machine (Halving Tower family, Problem S4 sibling) exports
only `machine`, `target`, and `has_stack_reduction : HasStackReduction target`, keeping its
separator configurations and seven transition rules `private`. Using
`AntihydraOrbit.Cousins.Line439Base` (which exposes those rule lemmas in
`AntihydraOrbit.Line439.Base`), this file establishes:

1. **Bridge (`is_valid_next439_acceleration`, `isHalt_iff_next439`):** An explicit two-mode,
   two-stack state type `State439`, initial state `start439 = .D [3] [0]`, and 7-rule step function
   `next439`, proved to be a valid acceleration of DeepMind's `target`, giving
   `IsHalt target ↔ CollatzHalts next439 start439`.
2. **Exposure law (`exposure_even_step`, `exposure_odd_step`, `exposure_halt_of_powerOfTwo`,
   `exposure_reaches_D_of_not_powerOfTwo`, `exposure_halts_before_D_iff`):** Call `.AL L [x]` an
   *exposure* of value `x`. Writing `y = x + 2`, each even exposure with `x ≥ 2` steps in `x / 2`
   transitions to a new exposure of value `x / 2 - 1` (halving `y ↦ y / 2`), whereas an odd
   exposure steps in `(x + 1) / 2` transitions into mode `D`. Consequently `AL L [x]` halts before
   its next `D` configuration if and only if `x = 0` or `x + 2 = 2 ^ k` with `2 ≤ k`.
3. **Only way to halt and global criterion (`orbitInv_start439`, `orbitInv_step`,
   `halt_after_exposure_two`, `isHalt_iff_exposure_powerOfTwo`):** On the orbit from `start439`,
   `D [] []` is unreachable (`OrbitInv`), so every halting state `AL L (0 :: R)` has `R = []` and
   is reached one step after an exposure `AL L' [2]`. Therefore `target` halts from the blank tape
   if and only if the `next439`-orbit from `start439` ever reaches an exposure `AL L [x]` with
   `x + 2 = 2 ^ k` (`2 ≤ k`).

Whether `target` halts remains open: nothing in this file decides whether `IsHalt target` holds.
-/

namespace AntihydraOrbit.Line439

open BusyBeaver
open BusyBeaver.Stack (bumpHead encStack encStack2)
open BusyBeaver.M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD (target)

/-! ### Definitions (the trusted base) -/

/-- Explicit separator state of the machine:
- `D L R`: state `D` reading `0` between `encStack2 L` and `encStack R`.
- `AL L R`: state `A` reading `0` between `(encStack2 L).tail` and `encStack R`. -/
inductive State439
  | D (L R : List ℕ)
  | AL (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Separator state reached from the blank tape after 23 raw TM steps (`D [3] [0]`). -/
def start439 : State439 := .D [3] [0]

/-- Tape configuration encoded by a separator state. -/
def encode439 : State439 → Cfg (Fin 2) (Fin 6)
  | .D L R => Base.cfg_D L R
  | .AL L R => Base.cfg_AL L R

/-- Head digit of a left stack under `.tail` (`0` if empty, `a` if `a :: _`). -/
def tailWeight : List ℕ → ℕ
  | [] => 0
  | a :: _ => a

/-- One step of the explicit 7-rule separator map. `none` means the machine halts on that
separator transition. -/
def next439 : State439 → Option State439
  | .D [] R => some (.AL [] (bumpHead R))
  | .D (a :: L) R => some (.D L (a :: bumpHead R))
  | .AL L [] => some (.D L.tail [tailWeight L + 2])
  | .AL _ (0 :: _) => none
  | .AL L (1 :: R) => some (.D ((tailWeight L + 2) :: L.tail) R)
  | .AL L (2 :: R) => some (.AL (0 :: tailWeight L :: L.tail) (bumpHead R))
  | .AL L ((d + 3) :: R) => some (.AL ((tailWeight L + 1) :: L.tail) ((d + 1) :: bumpHead R))

/-- Left stack produced by `t` consecutive even exposure halvings of value `2^t * q - 2`. -/
def exposureHalveL : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, L => L
  | t + 1, q, L =>
    exposureHalveL t q (0 :: (tailWeight L + (2 ^ t * q - 2)) :: L.tail)

/-- Number of `next439` steps in the exposure phase starting at `AL L [x]`:
`x + 2 - ν` steps to `none` when `x + 2 = 2^ν`, or `x + 2 - (q + 1) / 2 - ν` steps to the first
`D` configuration when `x + 2 = 2^ν * q` with `q ≥ 3` odd. -/
def exposureSteps (x : ℕ) : ℕ :=
  let y := x + 2
  let ν := padicValNat 2 y
  let q := y / 2 ^ ν
  if q = 1 then y - ν else y - (q + 1) / 2 - ν

/-- Inductive invariant holding on every state reachable from `start439 = D [3] [0]`:
mode `D` never has both stacks empty. -/
def OrbitInv : State439 → Prop
  | .D L R => L ≠ [] ∨ R ≠ []
  | .AL _ _ => True

instance (s : State439) : Decidable (OrbitInv s) := by
  cases s <;> unfold OrbitInv <;> infer_instance

/-! ### Concrete sanity anchors (`decide`) -/

-- First exposures along the orbit from `start439 = D [3] [0]`
example : OrbitInv start439 := by decide
example : (Option.bind · next439)^[4] (some start439) = some (.AL [0, 1] [3]) := by decide
example : (Option.bind · next439)^[6] (some start439) = some (.D [3, 1] [0]) := by decide
example : (Option.bind · next439)^[30] (some start439) = some (.AL [0, 4, 1] [9]) := by decide
example : (Option.bind · next439)^[48] (some start439) = some (.AL [0, 4, 2, 0] [9]) := by decide

-- Even exposure halving (`x = 56 -> 27` in `28` steps, `x + 2 : 58 -> 29`)
example :
    (Option.bind · next439)^[28] (some (.AL [0, 35] [56])) = some (.AL [0, 27, 35] [27]) := by
  decide

-- Power-of-two exposures halt (`x = 2, 6, 14`, i.e. `x + 2 = 4, 8, 16`, in `2, 5, 12` steps)
example : (Option.bind · next439)^[2] (some (.AL [5] [2])) = none := by decide
example : (Option.bind · next439)^[5] (some (.AL [5] [6])) = none := by decide
example : (Option.bind · next439)^[12] (some (.AL [] [14])) = none := by decide

-- Non-power-of-two even exposure (`x = 4`, `x + 2 = 6 = 2 * 3`) enters `D` in `3` steps
example : (Option.bind · next439)^[3] (some (.AL [5] [4])) = some (.D [2, 6] []) := by decide

/-! ### A. Bridge to DeepMind's `target` -/

private theorem base_target_eq : Base.target = target := rfl

private theorem base_tailWeight_eq (L : List ℕ) : Base.tailWeight L = tailWeight L := by
  cases L <;> rfl

/-- `start439`, `encode439`, and `next439` form a valid acceleration of DeepMind's `target`. -/
theorem is_valid_next439_acceleration :
    IsValidAcceleration target start439 encode439 next439 :=
  { init_reaches := by
      simpa only [start439, encode439, base_target_eq] using Base.init_to_cfg_D.to_star
    step_some := fun s s' hnext => by
      cases s with
      | D L R =>
        rcases L with _ | ⟨a, L'⟩
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq] using Base.rule_D_nil R
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq] using Base.rule_D_cons a L' R
      | AL L R =>
        rcases R with _ | ⟨_ | _ | _ | d, R'⟩
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq, base_tailWeight_eq] using Base.rule_AL_nil L
        · simp [next439] at hnext
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq, base_tailWeight_eq] using Base.rule_AL_one L R'
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq, base_tailWeight_eq] using Base.rule_AL_two L R'
        · simp only [next439, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode439, base_target_eq, base_tailWeight_eq] using Base.rule_AL_ge3 d L R'
    step_none := fun s hnext => by
      cases s with
      | D L R =>
        rcases L with _ | ⟨a, L'⟩ <;> simp [next439] at hnext
      | AL L R =>
        rcases R with _ | ⟨_ | _ | _ | d, R'⟩
        · simp [next439] at hnext
        · obtain ⟨hstep, hnone⟩ := Base.rule_AL_zero L R'
          exact ⟨Base.cfg_Halt_AL L R',
            by simpa only [encode439, base_target_eq] using hstep.to_star,
            by simpa only [base_target_eq] using hnone⟩
        · simp [next439] at hnext
        · simp [next439] at hnext
        · simp [next439] at hnext }

/-- The machine halts from the blank tape if and only if `next439` halts from `start439`. -/
theorem isHalt_iff_next439 : IsHalt target ↔ CollatzHalts next439 start439 := by
  exact is_valid_next439_acceleration.isHalt_iff

/-! ### B. Exposure law (arbitrary left stack `L`) -/

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def it (n : ℕ) (o : Option State439) : Option State439 :=
  (Option.bind · next439)^[n] o

private theorem it_zero (o : Option State439) : it 0 o = o := rfl

private theorem it_succ_front (n : ℕ) (o : Option State439) :
    it (n + 1) o = it n (o.bind next439) :=
  Function.iterate_succ_apply _ n o

private theorem it_succ_back (n : ℕ) (o : Option State439) :
    it (n + 1) o = (it n o).bind next439 :=
  Function.iterate_succ_apply' _ n o

private theorem it_add (m n : ℕ) (o : Option State439) :
    it (m + n) o = it n (it m o) := by
  unfold it
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem it_none (n : ℕ) : it n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [it_succ_front]; exact ih

private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

private theorem odd_part_properties (V : ℕ) (hV : 1 ≤ V) :
    let ν := padicValNat 2 V
    let q := V / 2 ^ ν
    V = 2 ^ ν * q ∧ 0 < q ∧ q % 2 = 1 ∧ (q = 1 ↔ ∃ p, V = 2 ^ p) := by
  intro ν q
  have hdvd : 2 ^ ν ∣ V := pow_padicValNat_dvd
  have hndvd : ¬ 2 ^ (ν + 1) ∣ V := pow_succ_padicValNat_not_dvd (by omega)
  have hV_eq : V = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hq_pos : 0 < q := by
    rcases q with _ | q'
    · simp [hV_eq] at hV
    · omega
  have hq_odd : q % 2 = 1 := by
    by_contra hnot
    obtain ⟨r, hr⟩ : ∃ r, q = 2 * r := ⟨q / 2, by omega⟩
    have h2 : 2 ^ (ν + 1) ∣ V := ⟨r, by rw [hV_eq, hr, pow_succ]; ring⟩
    exact hndvd h2
  refine ⟨hV_eq, hq_pos, hq_odd, ?_⟩
  constructor
  · intro hq1
    exact ⟨ν, by rw [hV_eq, hq1, mul_one]⟩
  · rintro ⟨p, hp⟩
    have hν_eq : ν = p := by
      unfold ν
      rw [hp]
      exact padicValNat.prime_pow p
    have hpow_pos : 0 < 2 ^ ν := by positivity
    have hmul : 2 ^ ν * q = 2 ^ ν * 1 := by rw [← hV_eq, hp, hν_eq, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpow_pos hmul

private theorem al_peel_loop (k r₀ : ℕ) :
    ∀ (a e : ℕ) (L₁ : List ℕ) (j : ℕ), j ≤ k →
      it j (some (.AL (a :: L₁) [2 * k + r₀ + 1, e])) =
        some (.AL ((a + j) :: L₁) [2 * (k - j) + r₀ + 1, e + j]) := by
  induction k with
  | zero =>
    intro a e L₁ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [it_zero]
  | succ k ih =>
    intro a e L₁ j hj
    rcases j with _ | j
    · simp [it_zero]
    · have hstep :
          next439 (.AL (a :: L₁) [2 * (k + 1) + r₀ + 1, e]) =
            some (.AL ((a + 1) :: L₁) [2 * k + r₀ + 1, e + 1]) := by
        rw [show 2 * (k + 1) + r₀ + 1 = (2 * k + r₀) + 3 by omega]
        rfl
      rw [it_succ_front, Option.bind_some, hstep, ih (a + 1) (e + 1) L₁ j (by omega),
        show a + 1 + j = a + (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega,
        show e + 1 + j = e + (j + 1) by omega]

/-- Even exposure step: for every `L` and even `x ≥ 2`, `x / 2` steps from `AL L [x]` reach the
halved exposure `AL (0 :: (tailWeight L + (x / 2 - 1)) :: L.tail) [x / 2 - 1]` without visiting
mode `D`. -/
theorem exposure_even_step (L : List ℕ) (x : ℕ) (hx2 : 2 ≤ x) (hx_ev : x % 2 = 0) :
    (Option.bind · next439)^[x / 2] (some (.AL L [x])) =
        some (.AL (0 :: (tailWeight L + (x / 2 - 1)) :: L.tail) [x / 2 - 1]) ∧
      ∀ t < x / 2, ∀ L' R',
        (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L' R') := by
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 2 := ⟨x / 2 - 1, by omega⟩
  have hdiv : (2 * m + 2) / 2 = m + 1 := by omega
  have hsub : (2 * m + 2) / 2 - 1 = m := by omega
  rw [hsub, hdiv]
  change it (m + 1) (some (.AL L [2 * m + 2])) =
      some (.AL (0 :: (tailWeight L + m) :: L.tail) [m]) ∧
    ∀ t < m + 1, ∀ L' R', it t (some (.AL L [2 * m + 2])) ≠ some (.D L' R')
  rcases m with _ | k
  · refine ⟨?_, ?_⟩
    · simp [it_succ_front, it_zero, next439, bumpHead]
    · intro t ht L' R'
      have ht0 : t = 0 := by omega
      subst ht0
      simp [it_zero]
  · have h1 :
        it 1 (some (.AL L [2 * (k + 1) + 2])) =
          some (.AL ((tailWeight L + 1) :: L.tail) [2 * k + 1 + 1, 0]) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 1) + 3 by omega, it_succ_front, it_zero]
      rfl
    have hpeel := al_peel_loop k 1 (tailWeight L + 1) 0 L.tail k (le_refl k)
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add,
      show tailWeight L + 1 + k = tailWeight L + (k + 1) by omega] at hpeel
    have hend :
        it 1 (some (.AL ((tailWeight L + (k + 1)) :: L.tail) [2, k])) =
          some (.AL (0 :: (tailWeight L + (k + 1)) :: L.tail) [k + 1]) := rfl
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 1 = 1 + k + 1 by omega, it_add (1 + k) 1, it_add 1 k, h1, hpeel, hend]
    · intro t ht L' R'
      rcases t with _ | t'
      · simp [it_zero]
      · rw [show t' + 1 = 1 + t' by omega, it_add 1 t', h1,
          al_peel_loop k 1 (tailWeight L + 1) 0 L.tail t' (by omega)]
        simp

/-- Odd exposure step: for every `L` and odd `x`, `(x + 1) / 2` steps from `AL L [x]` enter mode
`D` at `D ((tailWeight L + x / 2 + 2) :: L.tail) (if x = 1 then [] else [x / 2 - 1])`, with no
earlier `D` configuration. -/
theorem exposure_odd_step (L : List ℕ) (x : ℕ) (hx_odd : x % 2 = 1) :
    (Option.bind · next439)^[(x + 1) / 2] (some (.AL L [x])) =
        some (.D ((tailWeight L + x / 2 + 2) :: L.tail) (if x = 1 then [] else [x / 2 - 1])) ∧
      ∀ t < (x + 1) / 2, ∀ L' R',
        (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L' R') := by
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 1 := ⟨x / 2, by omega⟩
  have hsteps : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hsteps, hdiv]
  change it (m + 1) (some (.AL L [2 * m + 1])) =
      some (.D ((tailWeight L + m + 2) :: L.tail) (if 2 * m + 1 = 1 then [] else [m - 1])) ∧
    ∀ t < m + 1, ∀ L' R', it t (some (.AL L [2 * m + 1])) ≠ some (.D L' R')
  rcases m with _ | k
  · refine ⟨rfl, ?_⟩
    intro t ht L' R'
    have ht0 : t = 0 := by omega
    subst ht0
    simp [it_zero]
  · have h1 :
        it 1 (some (.AL L [2 * (k + 1) + 1])) =
          some (.AL ((tailWeight L + 1) :: L.tail) [2 * k + 0 + 1, 0]) := by
      rw [show 2 * (k + 1) + 1 = (2 * k) + 3 by omega, it_succ_front, it_zero]
      rfl
    have hpeel := al_peel_loop k 0 (tailWeight L + 1) 0 L.tail k (le_refl k)
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add,
      show tailWeight L + 1 + k = tailWeight L + (k + 1) by omega] at hpeel
    have hend :
        it 1 (some (.AL ((tailWeight L + (k + 1)) :: L.tail) [1, k])) =
          some (.D ((tailWeight L + (k + 1) + 2) :: L.tail) [k]) := rfl
    have hne1 : ¬ 2 * (k + 1) + 1 = 1 := by omega
    refine ⟨?_, ?_⟩
    · simp only [hne1, ↓reduceIte, Nat.add_sub_cancel]
      rw [show k + 1 + 1 = 1 + k + 1 by omega, it_add (1 + k) 1, it_add 1 k, h1, hpeel, hend]
    · intro t ht L' R'
      rcases t with _ | t'
      · simp [it_zero]
      · rw [show t' + 1 = 1 + t' by omega, it_add 1 t', h1,
          al_peel_loop k 0 (tailWeight L + 1) 0 L.tail t' (by omega)]
        simp

/-- Halting exposure chain: if `x + 2 = 2 ^ k` (covering `x = 0` at `k = 1` and all `2 ≤ k`), then
`AL L [x]` halts (`none`) in `2 ^ k - k` steps without visiting mode `D`. -/
theorem exposure_halt_of_powerOfTwo (L : List ℕ) (x k : ℕ) (hx : x + 2 = 2 ^ k) :
    (Option.bind · next439)^[2 ^ k - k] (some (.AL L [x])) = none ∧
      ∀ t < 2 ^ k - k, ∀ L' R',
        (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L' R') := by
  change it (2 ^ k - k) (some (.AL L [x])) = none ∧
    ∀ t < 2 ^ k - k, ∀ L' R', it t (some (.AL L [x])) ≠ some (.D L' R')
  induction k generalizing L x with
  | zero => omega
  | succ k ih =>
    rcases k with _ | m
    · have hx0 : x = 0 := by omega
      subst hx0
      refine ⟨rfl, ?_⟩
      intro t ht L' R'
      have ht0 : t = 0 := by omega
      subst ht0
      simp [it_zero]
    · have hpow_le := succ_le_two_pow (m + 1)
      have hpow_succ : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      have hx2 : 2 ≤ x := by omega
      have hx_ev : x % 2 = 0 := by omega
      obtain ⟨heven, hnoD_ev⟩ := exposure_even_step L x hx2 hx_ev
      change it (x / 2) (some (.AL L [x])) = _ at heven
      set L₁ := 0 :: (tailWeight L + (x / 2 - 1)) :: L.tail
      have hx' : (x / 2 - 1) + 2 = 2 ^ (m + 1) := by omega
      obtain ⟨hrec, hnoD_rec⟩ := ih L₁ (x / 2 - 1) hx'
      have hsplit : 2 ^ (m + 1 + 1) - (m + 1 + 1) = x / 2 + (2 ^ (m + 1) - (m + 1)) := by omega
      refine ⟨?_, ?_⟩
      · rw [hsplit, it_add, heven, hrec]
      · intro t ht L' R'
        rw [hsplit] at ht
        by_cases hlt : t < x / 2
        · exact hnoD_ev t hlt L' R'
        · rw [show t = x / 2 + (t - x / 2) by omega, it_add, heven]
          exact hnoD_rec (t - x / 2) (by omega) L' R'

private theorem exposure_halve_chain (t q : ℕ) (hq3 : 3 ≤ q) (hq_odd : q % 2 = 1) :
    ∀ L : List ℕ,
      it (2 ^ t * q - q - t) (some (.AL L [2 ^ t * q - 2])) =
          some (.AL (exposureHalveL t q L) [q - 2]) ∧
        ∀ k < 2 ^ t * q - q - t, ∀ L₁ R₁,
          it k (some (.AL L [2 ^ t * q - 2])) ≠ some (.D L₁ R₁) := by
  let _ := hq_odd
  induction t with
  | zero =>
    intro L
    simp only [pow_zero, one_mul, Nat.sub_self, exposureHalveL, it_zero]
    refine ⟨trivial, ?_⟩
    intro k hk
    omega
  | succ t ih =>
    intro L
    set P := 2 ^ t
    have hP_le : t + 1 ≤ P := succ_le_two_pow t
    have hPq_ge : q + t ≤ P * q := by nlinarith
    have hP_succ : 2 ^ (t + 1) * q = 2 * (P * q) := by
      change 2 ^ (t + 1) * q = 2 * (2 ^ t * q)
      rw [pow_succ]
      ring
    set x := 2 ^ (t + 1) * q - 2
    have hx2 : 2 ≤ x := by omega
    have hx_ev : x % 2 = 0 := by omega
    have hx_div : x / 2 = P * q - 1 := by omega
    have hx_sub : x / 2 - 1 = P * q - 2 := by omega
    obtain ⟨heven, hnoD_ev⟩ := exposure_even_step L x hx2 hx_ev
    change it (x / 2) (some (.AL L [x])) = _ at heven
    rw [hx_sub, hx_div] at heven
    rw [hx_div] at hnoD_ev
    set L₁ := 0 :: (tailWeight L + (P * q - 2)) :: L.tail
    obtain ⟨hrec, hnoD_rec⟩ := ih L₁
    have hsplit : 2 ^ (t + 1) * q - q - (t + 1) = (P * q - 1) + (P * q - q - t) := by omega
    refine ⟨?_, ?_⟩
    · rw [hsplit, it_add, heven]
      exact hrec
    · intro k hk L₂ R₂
      rw [hsplit] at hk
      by_cases hlt : k < P * q - 1
      · exact hnoD_ev k hlt L₂ R₂
      · rw [show k = (P * q - 1) + (k - (P * q - 1)) by omega, it_add, heven]
        exact hnoD_rec (k - (P * q - 1)) (by omega) L₂ R₂

/-- Non-halting exposure chain: if `x + 2` is not a power of two, let `ν = padicValNat 2 (x + 2)`
and odd part `q = (x + 2) / 2 ^ ν` (`q ≥ 3` odd); then `AL L [x]` halves `ν` times to
`AL (exposureHalveL ν q L) [q - 2]` in `x + 2 - q - ν` steps and enters mode `D` at step
`exposureSteps x = x + 2 - (q + 1) / 2 - ν`, with no earlier `D` configuration. -/
theorem exposure_reaches_D_of_not_powerOfTwo (L : List ℕ) (x : ℕ)
    (hnp : ¬ ∃ k, x + 2 = 2 ^ k) :
    let ν := padicValNat 2 (x + 2)
    let q := (x + 2) / 2 ^ ν
    let L' := exposureHalveL ν q L
    (Option.bind · next439)^[x + 2 - q - ν] (some (.AL L [x])) = some (.AL L' [q - 2]) ∧
      (Option.bind · next439)^[exposureSteps x] (some (.AL L [x])) =
        some (.D ((tailWeight L' + (q - 2) / 2 + 2) :: L'.tail)
          (if q = 3 then [] else [(q - 2) / 2 - 1])) ∧
      ∀ t < exposureSteps x, ∀ L₁ R₁,
        (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L₁ R₁) := by
  intro ν q L'
  obtain ⟨hy_eq, hq_pos, hq_odd, hq1_iff⟩ := odd_part_properties (x + 2) (by omega)
  have hy_eq' : x + 2 = 2 ^ ν * q := hy_eq
  have hq_pos' : 0 < q := hq_pos
  have hq_odd' : q % 2 = 1 := hq_odd
  have hq_ne1 : q ≠ 1 := fun h1 => hnp (hq1_iff.mp h1)
  have hq3 : 3 ≤ q := by omega
  have hν_le : ν + 1 ≤ 2 ^ ν := succ_le_two_pow ν
  have hy_ge : q + ν ≤ x + 2 := by nlinarith
  have hx_eq : x = 2 ^ ν * q - 2 := by omega
  obtain ⟨hchain, hnoD_chain⟩ := exposure_halve_chain ν q hq3 hq_odd' L
  rw [← hx_eq, ← hy_eq'] at hchain hnoD_chain
  obtain ⟨hodd_step, hnoD_odd⟩ := exposure_odd_step L' (q - 2) (by omega)
  change it ((q - 2 + 1) / 2) (some (.AL L' [q - 2])) = _ at hodd_step
  have hexp_steps : exposureSteps x = (x + 2 - q - ν) + ((q - 2 + 1) / 2) := by
    unfold exposureSteps
    change (if q = 1 then x + 2 - ν else x + 2 - (q + 1) / 2 - ν) = _
    simp only [hq_ne1, ↓reduceIte]
    omega
  have hcond_eq :
      (if q - 2 = 1 then ([] : List ℕ) else [(q - 2) / 2 - 1]) =
        (if q = 3 then [] else [(q - 2) / 2 - 1]) := by
    by_cases hq3_eq : q = 3
    · rw [hq3_eq]
      rfl
    · have hne : q - 2 ≠ 1 := by omega
      simp [hq3_eq, hne]
  refine ⟨hchain, ?_, ?_⟩
  · change it (exposureSteps x) (some (.AL L [x])) = _
    rw [hexp_steps, it_add, hchain, hodd_step, hcond_eq]
  · intro t ht L₁ R₁
    change it t (some (.AL L [x])) ≠ some (.D L₁ R₁)
    rw [hexp_steps] at ht
    by_cases hlt : t < x + 2 - q - ν
    · exact hnoD_chain t hlt L₁ R₁
    · rw [show t = (x + 2 - q - ν) + (t - (x + 2 - q - ν)) by omega, it_add, hchain]
      exact hnoD_odd (t - (x + 2 - q - ν)) (by omega) L₁ R₁

/-- Exposure law: for every `L` and `x`, starting from `AL L [x]` the map `next439` halts (`none`)
before visiting any `D` configuration if and only if `x = 0` or `x + 2 = 2 ^ k` with `2 ≤ k`. -/
theorem exposure_halts_before_D_iff (L : List ℕ) (x : ℕ) :
    (∃ T, (Option.bind · next439)^[T] (some (.AL L [x])) = none ∧
        ∀ t < T, ∀ L' R',
          (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L' R')) ↔
      (x = 0 ∨ ∃ k, 2 ≤ k ∧ x + 2 = 2 ^ k) := by
  have hpow_iff : (x = 0 ∨ ∃ k, 2 ≤ k ∧ x + 2 = 2 ^ k) ↔ ∃ k, x + 2 = 2 ^ k := by
    constructor
    · rintro (rfl | ⟨k, _, hk⟩)
      · exact ⟨1, rfl⟩
      · exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | _ | k'
      · omega
      · exact Or.inl (by omega)
      · exact Or.inr ⟨k' + 2, by omega, hk⟩
  rw [hpow_iff]
  constructor
  · rintro ⟨T, hT, hnoD⟩
    by_contra hnp
    obtain ⟨_, hD, _⟩ := exposure_reaches_D_of_not_powerOfTwo L x hnp
    set S := exposureSteps x
    by_cases hST : S < T
    · exact hnoD S hST _ _ hD
    · change it T (some (.AL L [x])) = none at hT
      change it S (some (.AL L [x])) = _ at hD
      rw [show S = T + (S - T) by omega, it_add, hT, it_none] at hD
      simp at hD
  · rintro ⟨k, hk⟩
    obtain ⟨hhalt, hnoD⟩ := exposure_halt_of_powerOfTwo L x k hk
    exact ⟨2 ^ k - k, hhalt, hnoD⟩

/-! ### C. Orbit invariant, only way to halt, and global halting criterion -/

/-- The initial state `start439 = D [3] [0]` satisfies `OrbitInv`. -/
theorem orbitInv_start439 : OrbitInv start439 := by
  exact Or.inl (List.cons_ne_nil _ _)

/-- Every non-halting step of `next439` preserves `OrbitInv` (`D [] []` is never reached). -/
theorem orbitInv_step (s s' : State439) (hinv : OrbitInv s) (hstep : next439 s = some s') :
    OrbitInv s' := by
  let _ := hinv
  cases s with
  | D L R =>
    rcases L with _ | ⟨a, L'⟩
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      trivial
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      exact Or.inr (List.cons_ne_nil _ _)
  | AL L R =>
    rcases R with _ | ⟨_ | _ | _ | d, R'⟩
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      exact Or.inr (List.cons_ne_nil _ _)
    · simp [next439] at hstep
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      exact Or.inl (List.cons_ne_nil _ _)
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      trivial
    · simp only [next439, Option.some.injEq] at hstep
      subst hstep
      trivial

private theorem orbitInv_of_reach (t : ℕ) :
    ∀ s : State439, it t (some start439) = some s → OrbitInv s := by
  induction t with
  | zero =>
    intro s h
    simp only [it_zero, Option.some.injEq] at h
    subst h
    exact orbitInv_start439
  | succ t ih =>
    intro s h
    rw [it_succ_back] at h
    rcases ht : it t (some start439) with _ | s₀
    · simp [ht] at h
    · rw [ht, Option.bind_some] at h
      exact orbitInv_step s₀ s (ih s₀ ht) h

/-- Every halting configuration `AL L (0 :: R)` on the orbit from `start439` has `R = []` and is
reached one step after an exposure `AL L' [2]` (so `none` occurs two steps after `AL L' [2]`). -/
theorem halt_after_exposure_two (t : ℕ) (L R : List ℕ)
    (h : (Option.bind · next439)^[t] (some start439) = some (.AL L (0 :: R))) :
    1 ≤ t ∧ R = [] ∧
      ∃ L', L = 0 :: tailWeight L' :: L'.tail ∧
        (Option.bind · next439)^[t - 1] (some start439) = some (.AL L' [2]) := by
  change it t (some start439) = some (.AL L (0 :: R)) at h
  rcases t with _ | t'
  · simp [it_zero, start439] at h
  · rw [it_succ_back] at h
    rcases ht' : it t' (some start439) with _ | s
    · simp [ht'] at h
    · rw [ht', Option.bind_some] at h
      have hinv : OrbitInv s := orbitInv_of_reach t' s ht'
      cases s with
      | D L₀ R₀ =>
        rcases L₀ with _ | ⟨a, L₁⟩
        · rcases R₀ with _ | ⟨d, R₁⟩
          · simp [OrbitInv] at hinv
          · simp [next439, bumpHead] at h
        · simp [next439] at h
      | AL L₀ R₀ =>
        rcases R₀ with _ | ⟨_ | _ | _ | d, R₁⟩
        · simp [next439] at h
        · simp [next439] at h
        · simp [next439] at h
        · rcases R₁ with _ | ⟨e, R₂⟩
          · change some (State439.AL (0 :: tailWeight L₀ :: L₀.tail) [0]) =
                some (State439.AL L (0 :: R)) at h
            injection h with h1
            injection h1 with hL hR
            injection hR with _ hR_nil
            exact ⟨by omega, hR_nil.symm, L₀, hL.symm, ht'⟩
          · simp [next439, bumpHead] at h
        · simp [next439] at h

/-- Global halting criterion: the machine halts from the blank tape if and only if the
`next439`-orbit from `start439` ever reaches an exposure `AL L [x]` with `x + 2 = 2 ^ k`
(`2 ≤ k`). -/
theorem isHalt_iff_exposure_powerOfTwo :
    IsHalt target ↔
      ∃ t L x, (Option.bind · next439)^[t] (some start439) = some (.AL L [x]) ∧
        ∃ k, 2 ≤ k ∧ x + 2 = 2 ^ k := by
  rw [isHalt_iff_next439]
  constructor
  · rintro ⟨T, hT⟩
    rw [Option.isNone_iff_eq_none] at hT
    have hex_halt :
        ∃ m L R, it m (some start439) = some (.AL L (0 :: R)) := by
      change it T (some start439) = none at hT
      induction T with
      | zero => simp [it_zero] at hT
      | succ n ih =>
        rw [it_succ_back] at hT
        rcases hn : it n (some start439) with _ | s
        · exact ih hn
        · rw [hn, Option.bind_some] at hT
          cases s with
          | D L R =>
            rcases L with _ | ⟨a, L'⟩ <;> simp [next439] at hT
          | AL L R =>
            rcases R with _ | ⟨_ | _ | _ | d, R'⟩
            · simp [next439] at hT
            · exact ⟨n, L, R', hn⟩
            · simp [next439] at hT
            · simp [next439] at hT
            · simp [next439] at hT
    obtain ⟨m, L, R, hm⟩ := hex_halt
    obtain ⟨_, _, L', _, hprev⟩ := halt_after_exposure_two m L R hm
    exact ⟨m - 1, L', 2, hprev, 2, le_refl 2, rfl⟩
  · rintro ⟨t, L, x, ht, k, _, hx⟩
    have hhalt := (exposure_halt_of_powerOfTwo L x k hx).1
    refine ⟨t + (2 ^ k - k), ?_⟩
    rw [Option.isNone_iff_eq_none]
    change it (t + (2 ^ k - k)) (some start439) = none
    rw [it_add]
    change it (2 ^ k - k) ((Option.bind · next439)^[t] (some start439)) = none
    rw [ht]
    exact hhalt

end AntihydraOrbit.Line439
