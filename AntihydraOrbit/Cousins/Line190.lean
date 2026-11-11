import Mathlib
import BusyBeaver.BB6.Accelerations.M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF
import AntihydraOrbit.Cousins.Line190Base

/-!
# The machine `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF`: explicit stack map and exposure law

DeepMind's `cryptids` module for this machine (Problem S4, Halving Tower family) exports only
`machine`, `target`, and `has_stack_reduction : HasStackReduction target`, keeping its separator
configurations, its 3-mode transition rules (`C`, `D`, `D00`), and its inner double-zero sub-system
(`C₀`, `D₀`, `D00₀`) `private`. Using `AntihydraOrbit.Cousins.Line190Base` (which exposes those
lemmas in `AntihydraOrbit.Line190.Base`), this file establishes:

1. **Bridge (`is_valid_next190_acceleration`, `isHalt_iff_next190`):** An explicit 3-mode,
   2-stack state type `State190` (`C`, `D`, `D00`), initial state `start190 = .D [2] []` (reached
   after 5 raw TM steps), and total step function `next190` (contracting the inner double-zero
   sub-system `C L (0 :: 0 :: R)` into one computable step `innerStep L R`), proved to be a valid
   acceleration of DeepMind's `target`, giving `IsHalt target ↔ CollatzHalts next190 start190`.
2. **Exposure law (`exposure_odd_step`, `exposure_even_step`, `exposure_halt_of_powerOfTwo`,
   `exposure_reaches_C_of_not_powerOfTwo`, `exposure_halts_before_C_iff`):** Call `.D00 [x] R` an
   *exposure* of value `x`. Writing `y = x + 1`, each odd exposure (`x ≥ 1`, `y` even) steps in
   `(x + 1) / 2` transitions to the halved exposure `.D00 [x / 2] ((x / 2) :: R)`, whereas each
   even exposure (`x ≥ 2`, `y` odd) enters mode `C` at `.C [x / 2 + 1, x / 2 - 1] R` in `x / 2`
   steps. Hence `.D00 [x] R` halts before its next `C` configuration if and only if `x + 1 = 2 ^ k`.
3. **Shield invariant and global criterion (`shieldInv_start190`, `shieldInv_step`,
   `shieldInv_excludes_hazards`, `halt_after_exposure_three`, `isHalt_iff_exposure_powerOfTwo`):**
   On the orbit from `start190`, `ShieldInv` rules out `D (0 :: L) R` halts, non-singleton
   `D00 (0 :: b :: L) R` halts, and all `C L (0 :: e :: R)` transitions (so the inner sub-system is
   never entered). Every halting state on the orbit is `.D00 [0] (0 :: 1 :: R')`, reached three
   steps after `.D00 [3] R'`. Therefore `target` halts from the blank tape if and only if the
   `next190`-orbit from `start190` ever reaches an exposure `.D00 [x] R` with `x + 1 = 2 ^ k`
   (`2 ≤ k`).

Whether `target` halts remains open: nothing in this file decides whether `IsHalt target` holds.
-/

namespace AntihydraOrbit.Line190

open BusyBeaver
open BusyBeaver.Stack (bumpHead encStack)
open BusyBeaver.M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF (target)

/-! ### Definitions (the trusted base) -/

/-- Explicit 3-mode separator state of the machine:
- `C L R`: state `C` reading `0` between `encStack L` and `encStack R`.
- `D L R`: state `D` reading `0` between `encStack L` and `encStack R`.
- `D00 L R`: state `D` reading `0` between `encStack L` and `0 :: encStack R`. -/
inductive State190
  | C (L R : List ℕ)
  | D (L R : List ℕ)
  | D00 (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Separator state reached from the blank tape after 5 raw TM steps (`D [2] []`). -/
def start190 : State190 := .D [2] []

/-- Tape configuration encoded by a separator state. -/
def encode190 : State190 → Cfg (Fin 2) (Fin 6)
  | .C L R => Base.cfg_C L R
  | .D L R => Base.cfg_D L R
  | .D00 L R => Base.cfg_D00 L R

/-- Sweep an inner `C₀` stack of positive digits `(d + 1)` onto `L`, returning the left stack of
the resulting `D` configuration upon re-entry into the main system. -/
def innerC0Sweep (L : List ℕ) : List ℕ → List ℕ
  | [] => bumpHead L
  | d :: R_pos => innerC0Sweep (d :: bumpHead L) R_pos

/-- Resolve `D00₀(R, [a + 2], R_pos.map (· + 1))` using structural fuel (`a < fuel`). -/
def innerD00Single : ℕ → ℕ → List ℕ → List ℕ → Option State190
  | 0, _, _, _ => none
  | _ + 1, 0, R_pos, R => some (.D (innerC0Sweep [2, 0] R_pos) R)
  | _ + 1, 1, _, _ => none
  | _ + 1, 2, R_pos, R => some (.D (innerC0Sweep [3, 1] R_pos) R)
  | fuel + 1, ap + 3, R_pos, R =>
    if ap % 2 = 1 then
      some (.D (innerC0Sweep [ap / 2 + 4, ap / 2 + 2] R_pos) R)
    else
      innerD00Single fuel (ap / 2) ((1 + ap / 2) :: R_pos) R

/-- Resolve `D00₀(R, (a + 2) :: L_tail, R_pos.map (· + 1))` by recursion on `L_tail`. -/
def innerD00List : List ℕ → ℕ → List ℕ → List ℕ → Option State190
  | [], a, R_pos, R => innerD00Single (a + 1) a R_pos R
  | b :: L'', 0, R_pos, R => some (.D (innerC0Sweep (2 :: (b + 1) :: L'') R_pos) R)
  | b :: L'', ap + 1, R_pos, R =>
    if ap % 2 = 1 then
      some (.D (innerC0Sweep ((ap / 2 + 3) :: (b + ap / 2 + 2) :: L'') R_pos) R)
    else
      innerD00List L'' (b + ap / 2) ((ap / 2) :: R_pos) R

/-- Contracted transition for `C L (0 :: 0 :: R)` through the inner double-zero sub-system. -/
def innerStep (L R : List ℕ) : Option State190 :=
  match L with
  | [] => none
  | a :: L_tail => innerD00List L_tail a [] R

/-- One step of the explicit 3-mode separator map (`none` = halt). -/
def next190 : State190 → Option State190
  | .C L [] => some (.D (bumpHead L) [])
  | .C L [0] => some (.C (1 :: bumpHead L) [])
  | .C L (0 :: 0 :: R) => innerStep L R
  | .C L (0 :: (e + 1) :: R) => some (.D00 (bumpHead (bumpHead L)) (e :: R))
  | .C L ((d + 1) :: R) => some (.C (d :: bumpHead L) R)
  | .D [] [] => some (.C [0, 0] [])
  | .D [] (d :: R) => some (.C ((d + 1) :: [0]) R)
  | .D (0 :: _) _ => none
  | .D (1 :: L) R => some (.D00 (bumpHead L) (bumpHead R))
  | .D (2 :: L) [] => some (.C (2 :: bumpHead L) [])
  | .D (2 :: L) (d :: R) => some (.C ((d + 3) :: bumpHead L) R)
  | .D ((a + 3) :: L) R => some (.D ((a + 1) :: bumpHead L) (bumpHead R))
  | .D00 [] R => some (.C [0, 0] R)
  | .D00 (0 :: _) _ => none
  | .D00 (1 :: L) R => some (.D00 (bumpHead L) (0 :: R))
  | .D00 (2 :: L) R => some (.C (2 :: bumpHead L) R)
  | .D00 ((a + 3) :: L) R => some (.D ((a + 1) :: bumpHead L) (0 :: R))

/-- Right stack produced by `t` consecutive odd exposure halvings starting from
`D00 [2 ^ t * q - 1] R`. -/
def exposureHalveR : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, R => R
  | t + 1, q, R => exposureHalveR t q ((2 ^ t * q - 1) :: R)

/-- Number of `next190` steps in the exposure phase starting at `D00 [x] R`:
`x + 1` steps to `none` when `x + 1 = 2 ^ ν`, or `x + 1 - (q + 1) / 2` steps to the first `C`
configuration when `x + 1 = 2 ^ ν * q` with `q ≥ 3` odd. -/
def exposureSteps (x : ℕ) : ℕ :=
  let y := x + 1
  let ν := padicValNat 2 y
  let q := y / 2 ^ ν
  if q = 1 then y else y - (q + 1) / 2

/-- Every entry except possibly the final entry is at least `1` (`0` may appear only last). -/
def AtMostLastZero : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => 1 ≤ a ∧ AtMostLastZero (b :: xs)

instance instDecidableAtMostLastZero : (xs : List ℕ) → Decidable (AtMostLastZero xs)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: xs =>
    @instDecidableAnd _ _ (Nat.decLe 1 a) (instDecidableAtMostLastZero (b :: xs))

/-- Inductive shield invariant holding on the entire orbit from `start190 = D [2] []`:
excludes empty-left states, `D (0 :: L) R` halts, non-singleton `D00 (0 :: b :: L) R` halts,
`C [0, 0] R`, and all `C L (0 :: e :: R)` transitions (including the inner sub-system). -/
def ShieldInv : State190 → Prop
  | .C L R => 2 ≤ L.length ∧ L ≠ [0, 0] ∧ AtMostLastZero L.tail ∧ AtMostLastZero R
  | .D L R =>
    (L = [2] ∧ R = []) ∨
      (2 ≤ L.length ∧ 1 ≤ L.headI ∧ AtMostLastZero L.tail ∧ AtMostLastZero R.tail)
  | .D00 L R =>
    L = [0] ∨ L = [1] ∨
      (1 ≤ L.length ∧ 2 ≤ L.headI ∧ AtMostLastZero L.tail ∧ AtMostLastZero R)

instance (s : State190) : Decidable (ShieldInv s) := by
  cases s <;> unfold ShieldInv <;> infer_instance

/-! ### Concrete sanity anchors (`decide`) -/

-- First exposures along the orbit from `start190 = D [2] []`
example : ShieldInv start190 := by decide
example : (Option.bind · next190)^[4] (some start190) = some (.D00 [2] [1]) := by decide
example : (Option.bind · next190)^[20] (some start190) = some (.D00 [6] [3, 1]) := by decide
example : (Option.bind · next190)^[45] (some start190) = some (.D00 [8] [5, 3, 1]) := by decide

-- Odd exposure halving (`x = 25 -> 12` in `13` steps, `x + 1 : 26 -> 13`) and even exit to `C`
example :
    (Option.bind · next190)^[13] (some (.D00 [25] [14, 15])) =
      some (.D00 [12] [12, 14, 15]) := by decide
example :
    (Option.bind · next190)^[3] (some (.D00 [6] [3, 1])) = some (.C [4, 2] [3, 1]) := by decide

-- Power-of-two exposures halt (`x = 1, 3, 7`, i.e. `x + 1 = 2, 4, 8`, in `2, 4, 8` steps)
example : (Option.bind · next190)^[2] (some (.D00 [1] [5])) = none := by decide
example : (Option.bind · next190)^[4] (some (.D00 [3] [5])) = none := by decide
example : (Option.bind · next190)^[8] (some (.D00 [7] [])) = none := by decide

-- Contracted inner double-zero rule (unreachable on the orbit, total on `State190`)
example : next190 (.C [1] [0, 0, 2]) = none := by decide
example : next190 (.C [2] [0, 0, 2]) = some (.D [4, 1] [2]) := by decide

/-! ### A. Bridge to DeepMind's `target` -/

private theorem base_target_eq : Base.target = target := rfl

private def StepValid (c : Cfg (Fin 2) (Fin 6)) : Option State190 → Prop
  | some s' => ReachesPlus target c (encode190 s')
  | none => ∃ cfg', ReachesStar target c cfg' ∧ (step target cfg').isNone

private theorem stepValid_of_plus {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : Option State190}
    (h₁ : ReachesPlus target c₁ c₂) (h₂ : StepValid c₂ res) :
    StepValid c₁ res := by
  cases res with
  | some s' => exact h₁.trans h₂
  | none =>
    obtain ⟨cfg', hstar, hnone⟩ := h₂
    exact ⟨cfg', h₁.to_star.trans hstar, hnone⟩

private theorem stepValid_of_star {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : Option State190}
    (h₁ : ReachesStar target c₁ c₂) (h₂ : StepValid c₂ res) :
    StepValid c₁ res := by
  cases res with
  | some s' => exact h₁.trans_plus h₂
  | none =>
    obtain ⟨cfg', hstar, hnone⟩ := h₂
    exact ⟨cfg', h₁.trans hstar, hnone⟩

private theorem innerC0Sweep_reaches (R R_pos L : List ℕ) :
    ReachesPlus target (Base.cfg_C0 R L (R_pos.map (· + 1)))
      (encode190 (.D (innerC0Sweep L R_pos) R)) := by
  induction R_pos generalizing L with
  | nil =>
    simpa only [List.map_nil, innerC0Sweep, encode190, base_target_eq] using Base.rule_C0_nil R L
  | cons d R_pos' ih =>
    have h1 : ReachesPlus target (Base.cfg_C0 R L ((d + 1) :: R_pos'.map (· + 1)))
        (Base.cfg_C0 R (d :: bumpHead L) (R_pos'.map (· + 1))) := by
      simpa only [base_target_eq] using Base.rule_C0_succ_cons R L (R_pos'.map (· + 1)) d
    simpa only [List.map_cons, innerC0Sweep] using h1.trans (ih (d :: bumpHead L))

private theorem innerD0_ge3_loop (R : List ℕ) (k r₀ : ℕ) :
    ∀ (b₀ : ℕ) (L'' : List ℕ) (d : ℕ) (R_pos : List ℕ),
      ReachesStar target
        (Base.cfg_D0 R ((2 * k + r₀ + 1) :: (b₀ + 1) :: L'') (d :: R_pos.map (· + 1)))
        (Base.cfg_D0 R ((r₀ + 1) :: (b₀ + k + 1) :: L'') ((d + k) :: R_pos.map (· + 1))) := by
  induction k with
  | zero =>
    intro b₀ L'' d R_pos
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    intro b₀ L'' d R_pos
    have h1 : ReachesPlus target
        (Base.cfg_D0 R ((2 * (k + 1) + r₀ + 1) :: (b₀ + 1) :: L'') (d :: R_pos.map (· + 1)))
        (Base.cfg_D0 R ((2 * k + r₀ + 1) :: (b₀ + 1 + 1) :: L'')
          ((d + 1) :: R_pos.map (· + 1))) := by
      rw [show 2 * (k + 1) + r₀ + 1 = (2 * k + r₀) + 3 by omega]
      simpa only [bumpHead, base_target_eq] using
        Base.rule_D0_ge3_cons R ((b₀ + 1) :: L'') (R_pos.map (· + 1)) (2 * k + r₀) d
    refine h1.to_star.trans ?_
    simpa only [show b₀ + 1 + k + 1 = b₀ + (k + 1) + 1 by omega,
      show d + 1 + k = d + (k + 1) by omega] using ih (b₀ + 1) L'' (d + 1) R_pos

private theorem innerD0_peel_odd (R : List ℕ) (ap b₀ : ℕ) (L'' : List ℕ) (d : ℕ)
    (R_pos : List ℕ) (hap : ap % 2 = 1) :
    ReachesPlus target
      (Base.cfg_D0 R ((ap + 1) :: (b₀ + 1) :: L'') (d :: R_pos.map (· + 1)))
      (encode190 (.D (innerC0Sweep
        ((d + ap / 2 + 3) :: (b₀ + ap / 2 + 2) :: L'') R_pos) R)) := by
  set k := ap / 2
  have hap_eq : ap = 2 * k + 1 := by omega
  have hloop := innerD0_ge3_loop R k 1 b₀ L'' d R_pos
  rw [← hap_eq] at hloop
  have htwo : ReachesPlus target
      (Base.cfg_D0 R (2 :: (b₀ + k + 1) :: L'') ((d + k) :: R_pos.map (· + 1)))
      (Base.cfg_C0 R ((d + k + 3) :: (b₀ + k + 2) :: L'') (R_pos.map (· + 1))) := by
    simpa only [bumpHead, base_target_eq] using
      Base.rule_D0_two_cons R ((b₀ + k + 1) :: L'') (R_pos.map (· + 1)) (d + k)
  exact hloop.trans_plus (htwo.trans (innerC0Sweep_reaches R R_pos _))

private theorem innerD0_peel_even (R : List ℕ) (ap b₀ : ℕ) (L'' : List ℕ) (d : ℕ)
    (R_pos : List ℕ) (hap : ¬ ap % 2 = 1) :
    ReachesPlus target
      (Base.cfg_D0 R ((ap + 1) :: (b₀ + 1) :: L'') (d :: R_pos.map (· + 1)))
      (Base.cfg_D00_0 R ((b₀ + ap / 2 + 2) :: L'') (((d + ap / 2) :: R_pos).map (· + 1))) := by
  set k := ap / 2
  have hap_eq : ap = 2 * k := by omega
  have hloop := innerD0_ge3_loop R k 0 b₀ L'' d R_pos
  simp only [Nat.add_zero] at hloop
  rw [← hap_eq] at hloop
  have hone : ReachesPlus target
      (Base.cfg_D0 R (1 :: (b₀ + k + 1) :: L'') ((d + k) :: R_pos.map (· + 1)))
      (Base.cfg_D00_0 R ((b₀ + k + 2) :: L'') (((d + k) :: R_pos).map (· + 1))) := by
    simpa only [bumpHead, List.map_cons, base_target_eq] using
      Base.rule_D0_one_cons R ((b₀ + k + 1) :: L'') (R_pos.map (· + 1)) (d + k)
  exact hloop.trans_plus hone

private theorem innerD00Single_valid (R : List ℕ) (fuel : ℕ) :
    ∀ (a : ℕ) (R_pos : List ℕ), a < fuel →
      StepValid (Base.cfg_D00_0 R [a + 2] (R_pos.map (· + 1)))
        (innerD00Single fuel a R_pos R) := by
  induction fuel with
  | zero =>
    intro a _ ha
    omega
  | succ fuel ih =>
    intro a R_pos ha
    rcases a with _ | _ | _ | ap
    · have h1 : ReachesPlus target (Base.cfg_D00_0 R [2] (R_pos.map (· + 1)))
          (Base.cfg_C0 R [2, 0] (R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using Base.rule_D00_0_two R [] (R_pos.map (· + 1))
      exact h1.trans (innerC0Sweep_reaches R R_pos [2, 0])
    · have h1 : ReachesPlus target (Base.cfg_D00_0 R [3] (R_pos.map (· + 1)))
          (Base.cfg_D0 R [1, 0] (0 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using Base.rule_D00_0_ge3 R [] (R_pos.map (· + 1)) 0
      have h2 : ReachesPlus target (Base.cfg_D0 R [1, 0] (0 :: R_pos.map (· + 1)))
          (Base.cfg_D00_0 R [1] (1 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D0_one_cons R [0] (R_pos.map (· + 1)) 0
      obtain ⟨h3, hnone⟩ := Base.rule_D00_0_one_nil_halt R (1 :: R_pos.map (· + 1))
      exact ⟨Base.cfg_Halt_D00_0 R (1 :: R_pos.map (· + 1)),
        ((h1.trans h2).trans (by simpa only [base_target_eq] using h3)).to_star,
        by simpa only [base_target_eq] using hnone⟩
    · have h1 : ReachesPlus target (Base.cfg_D00_0 R [4] (R_pos.map (· + 1)))
          (Base.cfg_D0 R [2, 0] (0 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using Base.rule_D00_0_ge3 R [] (R_pos.map (· + 1)) 1
      have h2 : ReachesPlus target (Base.cfg_D0 R [2, 0] (0 :: R_pos.map (· + 1)))
          (Base.cfg_C0 R [3, 1] (R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D0_two_cons R [0] (R_pos.map (· + 1)) 0
      exact (h1.trans h2).trans (innerC0Sweep_reaches R R_pos [3, 1])
    · rw [innerD00Single]
      have h1 : ReachesPlus target (Base.cfg_D00_0 R [ap + 3 + 2] (R_pos.map (· + 1)))
          (Base.cfg_D0 R ((ap + 3) :: [0]) (0 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D00_0_ge3 R [] (R_pos.map (· + 1)) (ap + 2)
      have h2 : ReachesPlus target (Base.cfg_D0 R ((ap + 3) :: [0]) (0 :: R_pos.map (· + 1)))
          (Base.cfg_D0 R ((ap + 1) :: [1]) (1 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D0_ge3_cons R [0] (R_pos.map (· + 1)) ap 0
      refine stepValid_of_plus (h1.trans h2) ?_
      by_cases hap : ap % 2 = 1
      · simp only [hap, ↓reduceIte, StepValid]
        simpa only [show 1 + ap / 2 + 3 = ap / 2 + 4 by omega, Nat.zero_add] using
          innerD0_peel_odd R ap 0 [] 1 R_pos hap
      · simp only [hap, ↓reduceIte]
        have hev := innerD0_peel_even R ap 0 [] 1 R_pos hap
        simp only [Nat.zero_add] at hev
        exact stepValid_of_plus hev (ih (ap / 2) ((1 + ap / 2) :: R_pos) (by omega))

private theorem innerD00List_valid (R L_tail : List ℕ) :
    ∀ (a : ℕ) (R_pos : List ℕ),
      StepValid (Base.cfg_D00_0 R ((a + 2) :: L_tail) (R_pos.map (· + 1)))
        (innerD00List L_tail a R_pos R) := by
  induction L_tail with
  | nil =>
    intro a R_pos
    exact innerD00Single_valid R (a + 1) a R_pos (by omega)
  | cons b L'' ih =>
    intro a R_pos
    rcases a with _ | ap
    · have h1 : ReachesPlus target (Base.cfg_D00_0 R (2 :: b :: L'') (R_pos.map (· + 1)))
          (Base.cfg_C0 R (2 :: (b + 1) :: L'') (R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D00_0_two R (b :: L'') (R_pos.map (· + 1))
      exact h1.trans (innerC0Sweep_reaches R R_pos (2 :: (b + 1) :: L''))
    · rw [innerD00List]
      have h1 : ReachesPlus target
          (Base.cfg_D00_0 R ((ap + 1 + 2) :: b :: L'') (R_pos.map (· + 1)))
          (Base.cfg_D0 R ((ap + 1) :: (b + 1) :: L'') (0 :: R_pos.map (· + 1))) := by
        simpa only [bumpHead, base_target_eq] using
          Base.rule_D00_0_ge3 R (b :: L'') (R_pos.map (· + 1)) ap
      refine stepValid_of_plus h1 ?_
      by_cases hap : ap % 2 = 1
      · simp only [hap, ↓reduceIte, StepValid]
        simpa only [Nat.zero_add] using innerD0_peel_odd R ap b L'' 0 R_pos hap
      · simp only [hap, ↓reduceIte]
        have hev := innerD0_peel_even R ap b L'' 0 R_pos hap
        simp only [Nat.zero_add] at hev
        exact stepValid_of_plus hev (ih (b + ap / 2) ((ap / 2) :: R_pos))

private theorem innerStep_valid (L R : List ℕ) :
    StepValid (Base.cfg_C L (0 :: 0 :: R)) (innerStep L R) := by
  have h0 : ReachesPlus target (Base.cfg_C L (0 :: 0 :: R))
      (Base.cfg_D00_0 R (bumpHead (bumpHead L)) []) := by
    simpa only [base_target_eq] using Base.rule_C_zero_zero_to_D00_0 L R
  refine stepValid_of_plus h0 ?_
  cases L with
  | nil =>
    obtain ⟨h1, hnone⟩ := Base.rule_D00_0_one_nil_halt R []
    have h1' : ReachesPlus target (Base.cfg_D00_0 R (bumpHead (bumpHead [])) [])
        (Base.cfg_Halt_D00_0 R []) := by
      simpa only [bumpHead, base_target_eq] using h1
    exact ⟨Base.cfg_Halt_D00_0 R [], h1'.to_star, by simpa only [base_target_eq] using hnone⟩
  | cons a L_tail =>
    simpa only [bumpHead, innerStep, List.map_nil] using innerD00List_valid R L_tail a []

/-- `start190`, `encode190`, and `next190` form a valid acceleration of DeepMind's `target`. -/
theorem is_valid_next190_acceleration :
    IsValidAcceleration target start190 encode190 next190 := by
  refine IsValidAcceleration.of_step ?_ (fun s => ?_)
  · simpa only [start190, encode190, base_target_eq] using Base.init_to_cfg_D.to_star
  · suffices h : StepValid (encode190 s) (next190 s) by
      cases hnx : next190 s <;> simpa only [hnx, StepValid] using h
    cases s with
    | C L R =>
      rcases R with _ | ⟨_ | d, R'⟩
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_C_nil L
      · rcases R' with _ | ⟨_ | e, R''⟩
        · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_C_zero_nil L
        · exact innerStep_valid L R''
        · simpa only [next190, StepValid, encode190, base_target_eq] using
            Base.rule_C_zero_succ_cons L R'' e
      · simpa only [next190, StepValid, encode190, base_target_eq] using
          Base.rule_C_succ_cons L R' d
    | D L R =>
      rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · rcases R with _ | ⟨d, R'⟩
        · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D_nil_nil
        · simpa only [next190, StepValid, encode190, base_target_eq] using
            Base.rule_D_nil_cons R' d
      · obtain ⟨h1, hnone⟩ := Base.rule_D_zero L' R
        exact ⟨Base.cfg_Halt_D L' R,
          by simpa only [encode190, base_target_eq] using h1.to_star,
          by simpa only [base_target_eq] using hnone⟩
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D_one L' R
      · rcases R with _ | ⟨d, R'⟩
        · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D_two_nil L'
        · simpa only [next190, StepValid, encode190, base_target_eq] using
            Base.rule_D_two_cons L' R' d
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D_ge3 L' R a
    | D00 L R =>
      rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D00_nil R
      · obtain ⟨h1, hnone⟩ := Base.rule_D00_zero L' R
        exact ⟨Base.cfg_Halt_D00 L' R,
          by simpa only [encode190, base_target_eq] using h1.to_star,
          by simpa only [base_target_eq] using hnone⟩
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D00_one L' R
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D00_two L' R
      · simpa only [next190, StepValid, encode190, base_target_eq] using Base.rule_D00_ge3 L' R a

/-- The machine halts from the blank tape if and only if `next190` halts from `start190`. -/
theorem isHalt_iff_next190 : IsHalt target ↔ CollatzHalts next190 start190 := by
  exact is_valid_next190_acceleration.isHalt_iff

/-! ### B. Exposure law (arbitrary right stack `R`) -/

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def it (n : ℕ) (o : Option State190) : Option State190 :=
  (Option.bind · next190)^[n] o

private theorem it_zero (o : Option State190) : it 0 o = o := rfl

private theorem it_succ_front (n : ℕ) (o : Option State190) :
    it (n + 1) o = it n (o.bind next190) :=
  Function.iterate_succ_apply _ n o

private theorem it_succ_back (n : ℕ) (o : Option State190) :
    it (n + 1) o = (it n o).bind next190 :=
  Function.iterate_succ_apply' _ n o

private theorem it_add (m n : ℕ) (o : Option State190) :
    it (m + n) o = it n (it m o) := by
  unfold it
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem it_none (n : ℕ) : it n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [it_succ_front]; exact ih

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

private theorem d_peel_loop (k r₀ : ℕ) :
    ∀ (b e : ℕ) (R : List ℕ) (j : ℕ), j ≤ k →
      it j (some (.D [2 * k + r₀ + 1, b] (e :: R))) =
        some (.D [2 * (k - j) + r₀ + 1, b + j] ((e + j) :: R)) := by
  induction k with
  | zero =>
    intro b e R j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [it_zero]
  | succ k ih =>
    intro b e R j hj
    rcases j with _ | j
    · simp [it_zero]
    · have hstep :
          next190 (.D [2 * (k + 1) + r₀ + 1, b] (e :: R)) =
            some (.D [2 * k + r₀ + 1, b + 1] ((e + 1) :: R)) := by
        rw [show 2 * (k + 1) + r₀ + 1 = (2 * k + r₀) + 3 by omega]
        rfl
      rw [it_succ_front, Option.bind_some, hstep, ih (b + 1) (e + 1) R j (by omega),
        show b + 1 + j = b + (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega,
        show e + 1 + j = e + (j + 1) by omega]

/-- Odd exposure step: for every `R` and odd `x ≥ 1`, `(x + 1) / 2` steps from `D00 [x] R` reach
the halved exposure `D00 [x / 2] ((x / 2) :: R)` without visiting mode `C`. -/
theorem exposure_odd_step (R : List ℕ) (x : ℕ) (hx1 : 1 ≤ x) (hx_odd : x % 2 = 1) :
    (Option.bind · next190)^[(x + 1) / 2] (some (.D00 [x] R)) =
        some (.D00 [x / 2] ((x / 2) :: R)) ∧
      ∀ t < (x + 1) / 2, ∀ L' R',
        (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L' R') := by
  let _ := hx1
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 1 := ⟨x / 2, by omega⟩
  have hsteps : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hsteps, hdiv]
  change it (m + 1) (some (.D00 [2 * m + 1] R)) = some (.D00 [m] (m :: R)) ∧
    ∀ t < m + 1, ∀ L' R', it t (some (.D00 [2 * m + 1] R)) ≠ some (.C L' R')
  rcases m with _ | k
  · refine ⟨rfl, ?_⟩
    intro t ht L' R'
    have ht0 : t = 0 := by omega
    subst ht0
    simp [it_zero]
  · have h1 : it 1 (some (.D00 [2 * (k + 1) + 1] R)) =
        some (.D [2 * k + 0 + 1, 0] (0 :: R)) := by
      rw [show 2 * (k + 1) + 1 = (2 * k) + 3 by omega, it_succ_front, it_zero]
      rfl
    have hpeel := d_peel_loop k 0 0 0 R k (le_refl k)
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hpeel
    have hend : it 1 (some (.D [1, k] (k :: R))) = some (.D00 [k + 1] ((k + 1) :: R)) := rfl
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 1 = 1 + k + 1 by omega, it_add (1 + k) 1, it_add 1 k, h1, hpeel, hend]
    · intro t ht L' R'
      rcases t with _ | t'
      · simp [it_zero]
      · rw [show t' + 1 = 1 + t' by omega, it_add 1 t', h1,
          d_peel_loop k 0 0 0 R t' (by omega)]
        simp

/-- Even exposure step: for every `R` and even `x ≥ 2`, `x / 2` steps from `D00 [x] R` enter mode
`C` at `C [x / 2 + 1, x / 2 - 1] R`, with no earlier `C` configuration. -/
theorem exposure_even_step (R : List ℕ) (x : ℕ) (hx2 : 2 ≤ x) (hx_ev : x % 2 = 0) :
    (Option.bind · next190)^[x / 2] (some (.D00 [x] R)) =
        some (.C [x / 2 + 1, x / 2 - 1] R) ∧
      ∀ t < x / 2, ∀ L' R',
        (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L' R') := by
  obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 2 := ⟨x / 2 - 1, by omega⟩
  have hadd : (2 * m + 2) / 2 + 1 = m + 2 := by omega
  have hsub : (2 * m + 2) / 2 - 1 = m := by omega
  have hdiv : (2 * m + 2) / 2 = m + 1 := by omega
  rw [hadd, hsub, hdiv]
  change it (m + 1) (some (.D00 [2 * m + 2] R)) = some (.C [m + 2, m] R) ∧
    ∀ t < m + 1, ∀ L' R', it t (some (.D00 [2 * m + 2] R)) ≠ some (.C L' R')
  rcases m with _ | k
  · refine ⟨rfl, ?_⟩
    intro t ht L' R'
    have ht0 : t = 0 := by omega
    subst ht0
    simp [it_zero]
  · have h1 : it 1 (some (.D00 [2 * (k + 1) + 2] R)) =
        some (.D [2 * k + 1 + 1, 0] (0 :: R)) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 1) + 3 by omega, it_succ_front, it_zero]
      rfl
    have hpeel := d_peel_loop k 1 0 0 R k (le_refl k)
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hpeel
    have hend : it 1 (some (.D [2, k] (k :: R))) = some (.C [k + 3, k + 1] R) := by
      simp [it_succ_front, it_zero, next190, bumpHead]
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 1 = 1 + k + 1 by omega, it_add (1 + k) 1, it_add 1 k, h1, hpeel, hend,
        show k + 1 + 2 = k + 3 by omega]
    · intro t ht L' R'
      rcases t with _ | t'
      · simp [it_zero]
      · rw [show t' + 1 = 1 + t' by omega, it_add 1 t', h1,
          d_peel_loop k 1 0 0 R t' (by omega)]
        simp

/-- Halting exposure chain: if `x + 1 = 2 ^ k`, then `D00 [x] R` halts (`none`) in `2 ^ k` steps
without visiting mode `C`. -/
theorem exposure_halt_of_powerOfTwo (R : List ℕ) (x k : ℕ) (hx : x + 1 = 2 ^ k) :
    (Option.bind · next190)^[2 ^ k] (some (.D00 [x] R)) = none ∧
      ∀ t < 2 ^ k, ∀ L' R',
        (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L' R') := by
  change it (2 ^ k) (some (.D00 [x] R)) = none ∧
    ∀ t < 2 ^ k, ∀ L' R', it t (some (.D00 [x] R)) ≠ some (.C L' R')
  induction k generalizing R x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    refine ⟨rfl, ?_⟩
    intro t ht L' R'
    have ht0 : t = 0 := by omega
    subst ht0
    simp [it_zero]
  | succ k ih =>
    have hpow_pos : 0 < 2 ^ k := by positivity
    have hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hx1 : 1 ≤ x := by omega
    have hx_odd : x % 2 = 1 := by omega
    obtain ⟨hodd, hnoC_odd⟩ := exposure_odd_step R x hx1 hx_odd
    change it ((x + 1) / 2) (some (.D00 [x] R)) = _ at hodd
    have hsteps_eq : (x + 1) / 2 = 2 ^ k := by omega
    rw [hsteps_eq] at hodd hnoC_odd
    have hx' : x / 2 + 1 = 2 ^ k := by omega
    obtain ⟨hrec, hnoC_rec⟩ := ih ((x / 2) :: R) (x / 2) hx'
    have hsplit : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    refine ⟨?_, ?_⟩
    · rw [hsplit, it_add, hodd, hrec]
    · intro t ht L' R'
      rw [hsplit] at ht
      by_cases hlt : t < 2 ^ k
      · exact hnoC_odd t hlt L' R'
      · rw [show t = 2 ^ k + (t - 2 ^ k) by omega, it_add, hodd]
        exact hnoC_rec (t - 2 ^ k) (by omega) L' R'

private theorem exposure_halve_chain (t q : ℕ) (hq3 : 3 ≤ q) (hq_odd : q % 2 = 1) :
    ∀ R : List ℕ,
      it (2 ^ t * q - q) (some (.D00 [2 ^ t * q - 1] R)) =
          some (.D00 [q - 1] (exposureHalveR t q R)) ∧
        ∀ k < 2 ^ t * q - q, ∀ L₁ R₁,
          it k (some (.D00 [2 ^ t * q - 1] R)) ≠ some (.C L₁ R₁) := by
  let _ := hq_odd
  induction t with
  | zero =>
    intro R
    simp only [pow_zero, one_mul, Nat.sub_self, exposureHalveR, it_zero]
    refine ⟨trivial, ?_⟩
    intro k hk
    omega
  | succ t ih =>
    intro R
    set P := 2 ^ t
    have hP_pos : 0 < P := by positivity
    have hPq_ge : q ≤ P * q := by nlinarith
    have hP_succ : 2 ^ (t + 1) * q = 2 * (P * q) := by
      change 2 ^ (t + 1) * q = 2 * (2 ^ t * q)
      rw [pow_succ]
      ring
    set x := 2 ^ (t + 1) * q - 1
    have hx1 : 1 ≤ x := by omega
    have hx_odd : x % 2 = 1 := by omega
    have hx_steps : (x + 1) / 2 = P * q := by omega
    have hx_div : x / 2 = P * q - 1 := by omega
    obtain ⟨hodd, hnoC_odd⟩ := exposure_odd_step R x hx1 hx_odd
    change it ((x + 1) / 2) (some (.D00 [x] R)) = _ at hodd
    rw [hx_steps, hx_div] at hodd
    rw [hx_steps] at hnoC_odd
    obtain ⟨hrec, hnoC_rec⟩ := ih ((P * q - 1) :: R)
    have hsplit : 2 ^ (t + 1) * q - q = P * q + (P * q - q) := by omega
    refine ⟨?_, ?_⟩
    · rw [hsplit, it_add, hodd]
      exact hrec
    · intro k hk L₁ R₁
      rw [hsplit] at hk
      by_cases hlt : k < P * q
      · exact hnoC_odd k hlt L₁ R₁
      · rw [show k = P * q + (k - P * q) by omega, it_add, hodd]
        exact hnoC_rec (k - P * q) (by omega) L₁ R₁

/-- Non-halting exposure chain: if `x + 1` is not a power of two, let `ν = padicValNat 2 (x + 1)`
and odd part `q = (x + 1) / 2 ^ ν` (`q ≥ 3` odd); then `D00 [x] R` halves `ν` times to
`D00 [q - 1] (exposureHalveR ν q R)` in `x + 1 - q` steps and enters mode `C` at step
`exposureSteps x = x + 1 - (q + 1) / 2`, with no earlier `C` configuration. -/
theorem exposure_reaches_C_of_not_powerOfTwo (R : List ℕ) (x : ℕ)
    (hnp : ¬ ∃ k, x + 1 = 2 ^ k) :
    let ν := padicValNat 2 (x + 1)
    let q := (x + 1) / 2 ^ ν
    let R' := exposureHalveR ν q R
    (Option.bind · next190)^[x + 1 - q] (some (.D00 [x] R)) = some (.D00 [q - 1] R') ∧
      (Option.bind · next190)^[exposureSteps x] (some (.D00 [x] R)) =
        some (.C [(q + 1) / 2, (q - 3) / 2] R') ∧
      ∀ t < exposureSteps x, ∀ L₁ R₁,
        (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L₁ R₁) := by
  intro ν q R'
  obtain ⟨hy_eq, hq_pos, hq_odd, hq1_iff⟩ := odd_part_properties (x + 1) (by omega)
  have hy_eq' : x + 1 = 2 ^ ν * q := hy_eq
  have hq_pos' : 0 < q := hq_pos
  have hq_odd' : q % 2 = 1 := hq_odd
  have hq_ne1 : q ≠ 1 := fun h1 => hnp (hq1_iff.mp h1)
  have hq3 : 3 ≤ q := by omega
  have hν_pos : 0 < 2 ^ ν := by positivity
  have hy_ge : q ≤ x + 1 := by nlinarith
  have hx_eq : x = 2 ^ ν * q - 1 := by omega
  obtain ⟨hchain, hnoC_chain⟩ := exposure_halve_chain ν q hq3 hq_odd' R
  rw [← hx_eq, ← hy_eq'] at hchain hnoC_chain
  obtain ⟨heven_step, hnoC_ev⟩ := exposure_even_step R' (q - 1) (by omega) (by omega)
  change it ((q - 1) / 2) (some (.D00 [q - 1] R')) = _ at heven_step
  have hexp_steps : exposureSteps x = (x + 1 - q) + (q - 1) / 2 := by
    unfold exposureSteps
    change (if q = 1 then x + 1 else x + 1 - (q + 1) / 2) = _
    simp only [hq_ne1, ↓reduceIte]
    omega
  refine ⟨hchain, ?_, ?_⟩
  · change it (exposureSteps x) (some (.D00 [x] R)) = _
    rw [hexp_steps, it_add, hchain, heven_step,
      show (q - 1) / 2 + 1 = (q + 1) / 2 by omega,
      show (q - 1) / 2 - 1 = (q - 3) / 2 by omega]
  · intro t ht L₁ R₁
    change it t (some (.D00 [x] R)) ≠ some (.C L₁ R₁)
    rw [hexp_steps] at ht
    by_cases hlt : t < x + 1 - q
    · exact hnoC_chain t hlt L₁ R₁
    · rw [show t = (x + 1 - q) + (t - (x + 1 - q)) by omega, it_add, hchain]
      exact hnoC_ev (t - (x + 1 - q)) (by omega) L₁ R₁

/-- Exposure law: for every `R` and `x`, starting from `D00 [x] R` the map `next190` halts (`none`)
before visiting any `C` configuration if and only if `x + 1 = 2 ^ k`. -/
theorem exposure_halts_before_C_iff (R : List ℕ) (x : ℕ) :
    (∃ T, (Option.bind · next190)^[T] (some (.D00 [x] R)) = none ∧
        ∀ t < T, ∀ L' R',
          (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L' R')) ↔
      ∃ k, x + 1 = 2 ^ k := by
  constructor
  · rintro ⟨T, hT, hnoC⟩
    by_contra hnp
    obtain ⟨_, hC, _⟩ := exposure_reaches_C_of_not_powerOfTwo R x hnp
    set S := exposureSteps x
    by_cases hST : S < T
    · exact hnoC S hST _ _ hC
    · change it T (some (.D00 [x] R)) = none at hT
      change it S (some (.D00 [x] R)) = _ at hC
      rw [show S = T + (S - T) by omega, it_add, hT, it_none] at hC
      simp at hC
  · rintro ⟨k, hk⟩
    obtain ⟨hhalt, hnoC⟩ := exposure_halt_of_powerOfTwo R x k hk
    exact ⟨2 ^ k, hhalt, hnoC⟩

/-! ### C. Shield invariant, only way to halt, and global halting criterion -/

private theorem length_bumpHead_pos (xs : List ℕ) : 1 ≤ (bumpHead xs).length := by
  cases xs <;> simp [bumpHead]

private theorem length_bumpHead_of_pos {xs : List ℕ} (h : 1 ≤ xs.length) :
    (bumpHead xs).length = xs.length := by
  cases xs with
  | nil => simp at h
  | cons _ _ => rfl

private theorem atMostLastZero_tail {xs : List ℕ} (h : AtMostLastZero xs) :
    AtMostLastZero xs.tail := by
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩
  · trivial
  · trivial
  · exact h.2

private theorem atMostLastZero_bumpHead {xs : List ℕ} (h : AtMostLastZero xs.tail) :
    AtMostLastZero (bumpHead xs) := by
  rcases xs with _ | ⟨a, _ | ⟨b, ys⟩⟩
  · trivial
  · trivial
  · exact ⟨by omega, h⟩

/-- The initial state `start190 = D [2] []` satisfies `ShieldInv`. -/
theorem shieldInv_start190 : ShieldInv start190 := by
  exact Or.inl ⟨rfl, rfl⟩

/-- Every non-halting step of `next190` preserves `ShieldInv`. -/
theorem shieldInv_step (s s' : State190) (hinv : ShieldInv s) (hstep : next190 s = some s') :
    ShieldInv s' := by
  cases s with
  | C L R =>
    obtain ⟨hL2, _, hLtail, hR⟩ := hinv
    rcases R with _ | ⟨_ | d, R'⟩
    · simp only [next190, Option.some.injEq] at hstep
      subst hstep
      rcases L with _ | ⟨a, _ | ⟨b, L''⟩⟩
      · simp at hL2
      · simp at hL2
      · exact Or.inr ⟨by simp [bumpHead], by simp [bumpHead], hLtail, trivial⟩
    · rcases R' with _ | ⟨e, R''⟩
      · simp only [next190, Option.some.injEq] at hstep
        subst hstep
        have hlen := length_bumpHead_pos L
        refine ⟨by simp; omega, ?_, atMostLastZero_bumpHead hLtail, trivial⟩
        intro hc
        injection hc with h0
        omega
      · simp [AtMostLastZero] at hR
    · simp only [next190, Option.some.injEq] at hstep
      subst hstep
      have hlen : (bumpHead L).length = L.length := length_bumpHead_of_pos (by omega)
      refine ⟨by simp [hlen]; omega, ?_, atMostLastZero_bumpHead hLtail, atMostLastZero_tail hR⟩
      intro hc
      have hclen := congrArg List.length hc
      simp [hlen] at hclen
      omega
  | D L R =>
    rcases hinv with ⟨rfl, rfl⟩ | ⟨hL2, hLhead, hLtail, hRtail⟩
    · simp only [next190, Option.some.injEq] at hstep
      subst hstep
      decide
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL2
      · simp at hLhead
      · simp only [next190, Option.some.injEq] at hstep
        subst hstep
        rcases L' with _ | ⟨_ | b, L''⟩
        · simp at hL2
        · rcases L'' with _ | ⟨c, L'''⟩
          · exact Or.inr (Or.inl rfl)
          · simp [AtMostLastZero] at hLtail
        · exact Or.inr (Or.inr ⟨by simp [bumpHead], by simp [bumpHead],
            atMostLastZero_tail (xs := (b + 1) :: L'') hLtail,
            atMostLastZero_bumpHead hRtail⟩)
      · rcases R with _ | ⟨d, R'⟩
        · simp only [next190, Option.some.injEq] at hstep
          subst hstep
          have hlen := length_bumpHead_pos L'
          refine ⟨by simp; omega, ?_, atMostLastZero_bumpHead (atMostLastZero_tail hLtail), trivial⟩
          intro hc
          injection hc with h0
          omega
        · simp only [next190, Option.some.injEq] at hstep
          subst hstep
          have hlen := length_bumpHead_pos L'
          refine ⟨by simp; omega, ?_, atMostLastZero_bumpHead (atMostLastZero_tail hLtail), hRtail⟩
          intro hc
          injection hc with h0
          omega
      · simp only [next190, Option.some.injEq] at hstep
        subst hstep
        have hlen := length_bumpHead_pos L'
        have hR' : AtMostLastZero (bumpHead R).tail := by
          cases R with
          | nil => trivial
          | cons _ _ => exact hRtail
        exact Or.inr ⟨by simp; omega, by simp,
          atMostLastZero_bumpHead (atMostLastZero_tail hLtail), hR'⟩
  | D00 L R =>
    rcases hinv with rfl | rfl | ⟨hL1, hLhead, hLtail, hR⟩
    · simp [next190] at hstep
    · simp only [next190, Option.some.injEq] at hstep
      subst hstep
      exact Or.inl rfl
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL1
      · simp at hLhead
      · simp at hLhead
      · simp only [next190, Option.some.injEq] at hstep
        subst hstep
        have hlen := length_bumpHead_pos L'
        refine ⟨by simp; omega, ?_, atMostLastZero_bumpHead (atMostLastZero_tail hLtail), hR⟩
        intro hc
        injection hc with h0
        omega
      · simp only [next190, Option.some.injEq] at hstep
        subst hstep
        have hlen := length_bumpHead_pos L'
        exact Or.inr ⟨by simp; omega, by simp,
          atMostLastZero_bumpHead (atMostLastZero_tail hLtail), hR⟩

/-- `ShieldInv` excludes `C L (0 :: e :: R)` (in particular the inner double-zero sub-system
`C L (0 :: 0 :: R)`), `D (0 :: L) R` halts, and non-singleton `D00 (0 :: b :: L) R` halts. -/
theorem shieldInv_excludes_hazards (s : State190) (hinv : ShieldInv s) :
    (∀ L e R, s ≠ .C L (0 :: e :: R)) ∧
      (∀ L R, s ≠ .D (0 :: L) R) ∧
      (∀ b L R, s ≠ .D00 (0 :: b :: L) R) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro L e R rfl
    obtain ⟨_, _, _, hR⟩ := hinv
    simp [AtMostLastZero] at hR
  · rintro L R rfl
    rcases hinv with ⟨h, _⟩ | ⟨_, hhead, _, _⟩
    · injection h with h0
      omega
    · simp at hhead
  · rintro b L R rfl
    rcases hinv with h | h | ⟨_, hhead, _, _⟩
    · injection h with _ hnil
      simp at hnil
    · injection h with h0
      omega
    · simp at hhead

private theorem shieldInv_of_reach (t : ℕ) :
    ∀ s : State190, it t (some start190) = some s → ShieldInv s := by
  induction t with
  | zero =>
    intro s h
    simp only [it_zero, Option.some.injEq] at h
    subst h
    exact shieldInv_start190
  | succ t ih =>
    intro s h
    rw [it_succ_back] at h
    rcases ht : it t (some start190) with _ | s₀
    · simp [ht] at h
    · rw [ht, Option.bind_some] at h
      exact shieldInv_step s₀ s (ih s₀ ht) h

private theorem pred_of_D00_zero {s : State190} {R₀ : List ℕ} (hinv : ShieldInv s)
    (hstep : next190 s = some (.D00 [0] R₀)) :
    ∃ R₁, s = .D00 [1] R₁ ∧ R₀ = 0 :: R₁ := by
  cases s with
  | C L R =>
    obtain ⟨_, _, _, hR⟩ := hinv
    rcases R with _ | ⟨_ | d, _ | ⟨e, R''⟩⟩
    · simp [next190] at hstep
    · simp [next190] at hstep
    · simp [AtMostLastZero] at hR
    · simp [next190] at hstep
    · simp [next190] at hstep
  | D L R =>
    rcases hinv with ⟨rfl, rfl⟩ | ⟨hL2, _, _, _⟩
    · simp [next190] at hstep
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL2
      · simp [next190] at hstep
      · rcases L' with _ | ⟨b, L''⟩
        · simp at hL2
        · simp [next190, bumpHead] at hstep
      · cases R <;> simp [next190] at hstep
      · simp [next190] at hstep
  | D00 L R =>
    rcases hinv with rfl | rfl | ⟨hL1, hLhead, _, _⟩
    · simp [next190] at hstep
    · simp only [next190, bumpHead, Option.some.injEq, State190.D00.injEq, true_and] at hstep
      exact ⟨R, rfl, hstep.symm⟩
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL1
      · simp at hLhead
      · simp at hLhead
      · simp [next190] at hstep
      · simp [next190] at hstep

private theorem pred_of_D00_one {s : State190} {R₁ : List ℕ} (hinv : ShieldInv s)
    (hstep : next190 s = some (.D00 [1] R₁)) :
    ∃ R₂, s = .D [1, 0] R₂ ∧ R₁ = bumpHead R₂ := by
  cases s with
  | C L R =>
    obtain ⟨_, _, _, hR⟩ := hinv
    rcases R with _ | ⟨_ | d, _ | ⟨e, R''⟩⟩
    · simp [next190] at hstep
    · simp [next190] at hstep
    · simp [AtMostLastZero] at hR
    · simp [next190] at hstep
    · simp [next190] at hstep
  | D L R =>
    rcases hinv with ⟨rfl, rfl⟩ | ⟨hL2, _, _, _⟩
    · simp [next190] at hstep
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL2
      · simp [next190] at hstep
      · simp only [next190, Option.some.injEq, State190.D00.injEq] at hstep
        obtain ⟨hL', hR'⟩ := hstep
        rcases L' with _ | ⟨_ | b, _ | ⟨c, L'''⟩⟩
        · simp [bumpHead] at hL'
        · exact ⟨R, rfl, hR'.symm⟩
        · simp [bumpHead] at hL'
        · simp [bumpHead] at hL'
        · simp [bumpHead] at hL'
      · cases R <;> simp [next190] at hstep
      · simp [next190] at hstep
  | D00 L R =>
    rcases hinv with rfl | rfl | ⟨hL1, hLhead, _, _⟩
    · simp [next190] at hstep
    · simp [next190, bumpHead] at hstep
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL1
      · simp at hLhead
      · simp at hLhead
      · simp [next190] at hstep
      · simp [next190] at hstep

private theorem pred_of_D_one_zero {s : State190} {R₂ : List ℕ} (hinv : ShieldInv s)
    (hstep : next190 s = some (.D [1, 0] R₂)) :
    ∃ R', s = .D00 [3] R' ∧ R₂ = 0 :: R' := by
  cases s with
  | C L R =>
    obtain ⟨_, hLne00, _, hR⟩ := hinv
    rcases R with _ | ⟨_ | d, _ | ⟨e, R''⟩⟩
    · simp only [next190, Option.some.injEq, State190.D.injEq] at hstep
      obtain ⟨hL', _⟩ := hstep
      rcases L with _ | ⟨_ | a, _ | ⟨b, L''⟩⟩
      · simp [bumpHead] at hL'
      · simp [bumpHead] at hL'
      · simp only [bumpHead, List.cons.injEq, true_and] at hL'
        obtain ⟨rfl, rfl⟩ := hL'
        exact absurd rfl hLne00
      · simp [bumpHead] at hL'
      · simp [bumpHead] at hL'
    · simp [next190] at hstep
    · simp [AtMostLastZero] at hR
    · simp [next190] at hstep
    · simp [next190] at hstep
  | D L R =>
    rcases hinv with ⟨rfl, rfl⟩ | ⟨hL2, _, _, _⟩
    · simp [next190] at hstep
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL2
      · simp [next190] at hstep
      · simp [next190] at hstep
      · cases R <;> simp [next190] at hstep
      · simp only [next190, Option.some.injEq, State190.D.injEq] at hstep
        obtain ⟨hL', _⟩ := hstep
        injection hL' with ha hbump
        have ha0 : a = 0 := by omega
        subst ha0
        rcases L' with _ | ⟨b, L''⟩
        · simp at hL2
        · simp [bumpHead] at hbump
  | D00 L R =>
    rcases hinv with rfl | rfl | ⟨hL1, hLhead, _, _⟩
    · simp [next190] at hstep
    · simp [next190] at hstep
    · rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp at hL1
      · simp at hLhead
      · simp at hLhead
      · simp [next190] at hstep
      · simp only [next190, Option.some.injEq, State190.D.injEq] at hstep
        obtain ⟨hL', hR'⟩ := hstep
        injection hL' with ha hbump
        have ha0 : a = 0 := by omega
        subst ha0
        rcases L' with _ | ⟨b, L''⟩
        · exact ⟨R, rfl, hR'.symm⟩
        · simp [bumpHead] at hbump

/-- Every halting state `s` (`next190 s = none`) on the orbit from `start190` has the form
`D00 [0] (0 :: 1 :: R')` and is reached three steps after an exposure `D00 [3] R'` (so `none`
occurs four steps after `D00 [3] R'`). -/
theorem halt_after_exposure_three (t : ℕ) (s : State190)
    (hreach : (Option.bind · next190)^[t] (some start190) = some s)
    (hhalt : next190 s = none) :
    3 ≤ t ∧ ∃ R', s = .D00 [0] (0 :: 1 :: R') ∧
      (Option.bind · next190)^[t - 3] (some start190) = some (.D00 [3] R') := by
  change it t (some start190) = some s at hreach
  have hinv : ShieldInv s := shieldInv_of_reach t s hreach
  obtain ⟨hnoC, hnoD, hnoD00⟩ := shieldInv_excludes_hazards s hinv
  have hs0 : ∃ R₀, s = .D00 [0] R₀ := by
    cases s with
    | C L R =>
      rcases R with _ | ⟨_ | d, _ | ⟨e, R''⟩⟩
      · simp [next190] at hhalt
      · simp [next190] at hhalt
      · exact absurd rfl (hnoC L e R'')
      · simp [next190] at hhalt
      · simp [next190] at hhalt
    | D L R =>
      rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · cases R <;> simp [next190] at hhalt
      · exact absurd rfl (hnoD L' R)
      · simp [next190] at hhalt
      · cases R <;> simp [next190] at hhalt
      · simp [next190] at hhalt
    | D00 L R =>
      rcases L with _ | ⟨_ | _ | _ | a, L'⟩
      · simp [next190] at hhalt
      · rcases L' with _ | ⟨b, L''⟩
        · exact ⟨R, rfl⟩
        · exact absurd rfl (hnoD00 b L'' R)
      · simp [next190] at hhalt
      · simp [next190] at hhalt
      · simp [next190] at hhalt
  obtain ⟨R₀, rfl⟩ := hs0
  rcases t with _ | t₁
  · simp [it_zero, start190] at hreach
  · rw [it_succ_back] at hreach
    rcases ht₁ : it t₁ (some start190) with _ | s₁
    · simp [ht₁] at hreach
    · rw [ht₁, Option.bind_some] at hreach
      obtain ⟨R₁, rfl, rfl⟩ := pred_of_D00_zero (shieldInv_of_reach t₁ s₁ ht₁) hreach
      rcases t₁ with _ | t₂
      · simp [it_zero, start190] at ht₁
      · rw [it_succ_back] at ht₁
        rcases ht₂ : it t₂ (some start190) with _ | s₂
        · simp [ht₂] at ht₁
        · rw [ht₂, Option.bind_some] at ht₁
          obtain ⟨R₂, rfl, rfl⟩ := pred_of_D00_one (shieldInv_of_reach t₂ s₂ ht₂) ht₁
          rcases t₂ with _ | t₃
          · simp [it_zero, start190] at ht₂
          · rw [it_succ_back] at ht₂
            rcases ht₃ : it t₃ (some start190) with _ | s₃
            · simp [ht₃] at ht₂
            · rw [ht₃, Option.bind_some] at ht₂
              obtain ⟨R', rfl, rfl⟩ := pred_of_D_one_zero (shieldInv_of_reach t₃ s₃ ht₃) ht₂
              exact ⟨by omega, R', rfl, ht₃⟩

/-- Global halting criterion: the machine halts from the blank tape if and only if the
`next190`-orbit from `start190` ever reaches an exposure `D00 [x] R` with `x + 1 = 2 ^ k`
(`2 ≤ k`). -/
theorem isHalt_iff_exposure_powerOfTwo :
    IsHalt target ↔
      ∃ t R x, (Option.bind · next190)^[t] (some start190) = some (.D00 [x] R) ∧
        ∃ k, 2 ≤ k ∧ x + 1 = 2 ^ k := by
  rw [isHalt_iff_next190]
  constructor
  · rintro ⟨T, hT⟩
    rw [Option.isNone_iff_eq_none] at hT
    have hex_halt : ∃ m s, it m (some start190) = some s ∧ next190 s = none := by
      change it T (some start190) = none at hT
      induction T with
      | zero => simp [it_zero] at hT
      | succ n ih =>
        rw [it_succ_back] at hT
        rcases hn : it n (some start190) with _ | s
        · exact ih hn
        · rw [hn, Option.bind_some] at hT
          exact ⟨n, s, hn, hT⟩
    obtain ⟨m, s, hm, hhalt⟩ := hex_halt
    obtain ⟨_, R', _, hprev⟩ := halt_after_exposure_three m s hm hhalt
    exact ⟨m - 3, R', 3, hprev, 2, le_refl 2, rfl⟩
  · rintro ⟨t, R, x, ht, k, _, hx⟩
    have hhalt := (exposure_halt_of_powerOfTwo R x k hx).1
    refine ⟨t + 2 ^ k, ?_⟩
    rw [Option.isNone_iff_eq_none]
    change it (t + 2 ^ k) (some start190) = none
    rw [it_add]
    change it (2 ^ k) ((Option.bind · next190)^[t] (some start190)) = none
    rw [ht]
    exact hhalt

end AntihydraOrbit.Line190
