import Mathlib
import BusyBeaver.BB6.Accelerations.M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF
import AntihydraOrbit.Cousins.Line505Base

/-!
# The machine `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`: explicit two-stack map and single-sum law

DeepMind's `cryptids` module for this machine exports only `machine`, `target`, and the existential
`has_stack_reduction : HasStackReduction target`, keeping its separator configurations and local
rules `private`. Using `AntihydraOrbit.Cousins.Line505Base` (which exposes those rule lemmas in
`AntihydraOrbit.Line505.Base`), this file establishes:

1. **Bridge (`is_valid_next505_acceleration`, `isHalt_iff_next505`):** An explicit two-mode,
   two-stack state type `State505`, initial state `start505 = .D [2] []`, and 11-rule step function
   `next505`, proved to be a valid acceleration of DeepMind's original `target`,
   giving `IsHalt target ↔ CollatzHalts next505 start505` with no extra hypotheses.
2. **Single-sum law:** On any left stack `L`, the dyadic weighted sum
   `W L = ∑_{r=1}^{|L|} 2^(r-1) * (L[r-1] + 1)` halves on each odd `D`-peel (`W_oddPeel`), the
   number of consecutive odd peels equals `padicValNat 2 (W L)` (`oddPeelDepth_eq_padicValNat`) with
   closed-form end states both when the sweep stops inside `L` (`oddSweep_stops_inside`) and when it
   reaches the singleton fresh start `[W L / 2^(|L|-1) - 1]` (`oddSweep_reaches_singleton`,
   `oddSweep_singleton_end`), and for any odd-top `D`-state other than `.D [1] []` the sweep halts
   if and only if `W L` is a power of two (`oddSweep_halts_iff_powerOfTwo`,
   `fullSweep_halts_iff_powerOfTwo`, `singleton_halts_iff_powerOfTwo`).
3. **Global reduction (`isHalt_iff_D_powerOfTwo`, `isHalt_iff_oddTop_powerOfTwo`):** Every state on
   the `next505`-orbit from `start505` satisfies the inductive invariant `OrbitInv`, ruling out
   empty left stacks, unreachable even-top interior halts, and the `.D [1] []` exception. Therefore
   `target` halts from the blank tape if and only if the `next505`-orbit of `start505` ever reaches
   a `D`-state (equivalently, an odd-top `D`-sweep start) whose `W L` is a power of two.

Whether `target` halts remains open: nothing in this file decides whether `IsHalt target` holds.
-/

namespace AntihydraOrbit.Line505

open BusyBeaver
open BusyBeaver.Stack (bumpHead encStack)
open BusyBeaver.M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF (target)

/-! ### Definitions (the trusted base) -/

/-- Explicit separator state of the machine:
- `D L R`: state `D` reading `0` between `encStack L` and `0 :: encStack R`.
- `FR a L R`: state `F` reading `0` between `encStack (a :: L)` and `0 :: (encStack R).tail`
  (an empty left stack in mode `FR` is unrepresentable). -/
inductive State505
  | D (L R : List ℕ)
  | FR (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Separator state reached from the blank tape after 3 raw TM steps (`D [2] []`). -/
def start505 : State505 := .D [2] []

/-- Tape configuration encoded by a separator state. -/
def encode505 : State505 → Cfg (Fin 2) (Fin 6)
  | .D L R => Base.cfg_D L R
  | .FR a L R => Base.cfg_FR (a :: L) R

/-- One step of the explicit 11-rule separator map. `none` means the machine
halts on that separator transition. -/
def next505 : State505 → Option State505
  | .D [] _ => none
  | .D (0 :: L) [] => some (.D (bumpHead^[3] L) [])
  | .D (0 :: L) [0] => some (.D (bumpHead^[6] L) [])
  | .D (0 :: _) (0 :: _ :: _) => none
  | .D (0 :: L) (1 :: R) => some (.D (bumpHead^[4] L) (bumpHead R))
  | .D (0 :: L) ((d + 2) :: R) => some (.FR d (bumpHead^[4] L) (bumpHead R))
  | .D (1 :: L) R => some (.D (bumpHead L) (0 :: R))
  | .D ((a + 2) :: L) R => some (.FR a (bumpHead L) (0 :: R))
  | .FR a L [] => some (.D (a :: L) [0])
  | .FR a L (0 :: R) => some (.D (a :: L) (bumpHead R))
  | .FR a L ((d + 1) :: R) => some (.FR d (a :: L) (bumpHead R))

/-- Dyadic left-stack weighted sum `∑_{r=1}^{|L|} 2^(r-1) * (L[r-1] + 1)`. -/
def W : List ℕ → ℕ
  | [] => 0
  | a :: L => (a + 1) + 2 * W L

/-- Structural helper for `singletonPeelDepth`: at most `n` odd singleton halvings `b ↦ b / 2`. -/
def singletonPeelDepthAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b => if b % 2 = 1 then singletonPeelDepthAux n (b / 2) + 1 else 0

/-- Number of consecutive odd singleton peels `b ↦ (b - 1) / 2` before reaching an even value. -/
def singletonPeelDepth (b : ℕ) : ℕ :=
  singletonPeelDepthAux b b

/-- Structural helper for `oddPeelDepth`: peels odd head `a` onto the remaining stack `L`. -/
def oddPeelDepthAux : List ℕ → ℕ → ℕ
  | [], b => singletonPeelDepth b
  | c :: L, a => if a % 2 = 1 then oddPeelDepthAux L (c + (a + 1) / 2) + 1 else 0

/-- Number of consecutive odd `D`-peels from left stack `L` before reaching an even top entry. -/
def oddPeelDepth : List ℕ → ℕ
  | [] => 0
  | a :: L => oddPeelDepthAux L a

/-- Top entry of the left stack after `j` consecutive odd peels (`0 ≤ j ≤ padicValNat 2 (W L)`). -/
def peelTop (L : List ℕ) (j : ℕ) : ℕ :=
  W (L.take (j + 1)) / 2 ^ j - 1

/-- Right stack after `d` consecutive odd peels from `D L R`. -/
def oddSweepR (L R : List ℕ) : ℕ → List ℕ
  | 0 => R
  | d + 1 => 0 :: bumpHead^[peelTop L d / 2] (oddSweepR L R d)

/-- Number of `next505` steps taken by `d` consecutive odd peels from `D L R`. -/
def oddSweepSteps (L : List ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => oddSweepSteps L d + peelTop L d

/-- Total `next505` steps for a complete `D`-sweep from `D L R`: all `v₂(W L)` odd peels followed by
the terminal even peel and its `0`-top transition. -/
def fullSweepSteps (L : List ℕ) : ℕ :=
  let ν := padicValNat 2 (W L)
  oddSweepSteps L ν + peelTop L ν + 1

/-- Inductive invariant holding on every separator state reachable from `start505 = D [2] []`. -/
def OrbitInv : State505 → Prop
  | .D L R =>
    L ≠ [] ∧
    (R = [] → 2 ≤ L.headI) ∧
    (L = [0] → 2 ≤ R.length ∧ R.headI = 0) ∧
    (2 ≤ L.length ∧ L.headI = 0 → ¬ (2 ≤ R.length ∧ R.headI = 0))
  | .FR _ L _ =>
    L ≠ []

instance (s : State505) : Decidable (OrbitInv s) := by
  cases s <;> unfold OrbitInv <;> infer_instance

/-! ### Concrete sanity anchors (`decide`) -/

-- First steps of the blank-tape orbit (`start505` to first fresh start `D [11] [0, 1]` at t = 29)
example : OrbitInv start505 := by decide
example : (Option.bind · next505)^[3] (some start505) = some (.D [6] []) := by decide
example : (Option.bind · next505)^[12] (some start505) = some (.D [12] []) := by decide
example : (Option.bind · next505)^[29] (some start505) = some (.D [11] [0, 1]) := by decide

-- Inside-stack sweep stop: `L = [1, 3, 2]`, `W L = 22`, `v₂(W L) = 1 < 2`
example : W [1, 3, 2] = 22 ∧ oddPeelDepth [1, 3, 2] = 1 := by decide
example :
    (Option.bind · next505)^[oddSweepSteps [1, 3, 2] 1] (some (.D [1, 3, 2] [5])) =
      some (.D [4, 2] [0, 5]) := by decide

-- Singleton fresh-start reach (non-halting): `L = [3, 5, 2]`, `W L = 28 = 4 * 7`, `v₂(W L) = 2`
example : W [3, 5, 2] = 28 ∧ oddPeelDepth [3, 5, 2] = 2 := by decide
example :
    (Option.bind · next505)^[oddSweepSteps [3, 5, 2] 2] (some (.D [3, 5, 2] [5])) =
      some (.D [6] [0, 3, 6]) := by decide
example :
    ((Option.bind · next505)^[oddSweepSteps [3, 5, 2] 2 + peelTop [3, 5, 2] 2 + 1]
      (some (.D [3, 5, 2] [5]))).isNone = false := by decide

-- Power-of-two sweep halt: `L = [1, 2]`, `W L = 8 = 2^3`, `v₂(W L) = 3`
example : W [1, 2] = 8 ∧ oddPeelDepth [1, 2] = 3 := by decide
example :
    (Option.bind · next505)^[oddSweepSteps [1, 2] 1] (some (.D [1, 2] [5])) =
      some (.D [3] [0, 5]) := by decide
example :
    (Option.bind · next505)^[oddSweepSteps [1, 2] 3] (some (.D [1, 2] [5])) =
      some (.D [0] [0, 0, 1, 5]) := by decide
example :
    (Option.bind · next505)^[oddSweepSteps [1, 2] 3 + peelTop [1, 2] 3 + 1]
      (some (.D [1, 2] [5])) = none := by decide

-- The unique right-stack underflow exception: `D [1] []` (`W [1] = 2`, `R = []`) does not halt
example :
    (Option.bind · next505)^[oddSweepSteps [1] 1 + peelTop [1] 1 + 1]
      (some (.D [1] [])) = some (.D [5] []) := by decide

/-! ### Bridge to DeepMind's `target` -/

private theorem base_target_eq : Base.target = target := rfl

/-- `start505`, `encode505`, and `next505` form a valid acceleration of DeepMind's `target`. -/
theorem is_valid_next505_acceleration :
    IsValidAcceleration target start505 encode505 next505 where
  init_reaches := by
    simpa only [start505, encode505, base_target_eq] using Base.init_to_cfg_D.to_star
  step_some s s' hnext := by
    cases s with
    | D L R =>
      rcases L with _ | ⟨_ | _ | a, L'⟩
      · simp [next505] at hnext
      · rcases R with _ | ⟨_ | _ | d, R'⟩
        · simp only [next505, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode505, base_target_eq, Function.iterate_succ_apply',
            Function.iterate_zero_apply] using Base.rule_D_zero_nil L'
        · rcases R' with _ | ⟨e, R''⟩
          · simp only [next505, Option.some.injEq] at hnext
            subst hnext
            simpa only [encode505, base_target_eq, Function.iterate_succ_apply',
              Function.iterate_zero_apply] using Base.rule_D_zero_zero_nil L'
          · simp [next505] at hnext
        · simp only [next505, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode505, base_target_eq, Function.iterate_succ_apply',
            Function.iterate_zero_apply] using Base.rule_D_zero_one L' R'
        · simp only [next505, Option.some.injEq] at hnext
          subst hnext
          simpa only [encode505, base_target_eq, Function.iterate_succ_apply',
            Function.iterate_zero_apply] using Base.rule_D_zero_ge2 L' R' d
      · simp only [next505, Option.some.injEq] at hnext
        subst hnext
        simpa only [encode505, base_target_eq] using Base.rule_D_one L' R
      · simp only [next505, Option.some.injEq] at hnext
        subst hnext
        simpa only [encode505, base_target_eq] using Base.rule_D_ge2 L' R a
    | FR a L R =>
      rcases R with _ | ⟨_ | d, R'⟩
      · simp only [next505, Option.some.injEq] at hnext
        subst hnext
        simpa only [encode505, base_target_eq] using Base.rule_FR_cons_nil L a
      · simp only [next505, Option.some.injEq] at hnext
        subst hnext
        simpa only [encode505, base_target_eq] using Base.rule_FR_cons_zero L R' a
      · simp only [next505, Option.some.injEq] at hnext
        subst hnext
        simpa only [encode505, base_target_eq] using Base.rule_FR_cons_succ L R' a d
  step_none s hnext := by
    cases s with
    | D L R =>
      rcases L with _ | ⟨_ | _ | a, L'⟩
      · obtain ⟨hstep, hnone⟩ := Base.rule_D_nil R
        exact ⟨Base.cfg_Halt_D_nil R,
          by simpa only [encode505, base_target_eq] using hstep.to_star,
          by simpa only [base_target_eq] using hnone⟩
      · rcases R with _ | ⟨_ | _ | d, R'⟩
        · simp [next505] at hnext
        · rcases R' with _ | ⟨e, R''⟩
          · simp [next505] at hnext
          · obtain ⟨hstep, hnone⟩ := Base.rule_D_zero_zero_cons L' R'' e
            exact ⟨Base.cfg_Halt_D_zero L' e R'',
              by simpa only [encode505, base_target_eq] using hstep.to_star,
              by simpa only [base_target_eq] using hnone⟩
        · simp [next505] at hnext
        · simp [next505] at hnext
      · simp [next505] at hnext
      · simp [next505] at hnext
    | FR a L R =>
      rcases R with _ | ⟨_ | d, R'⟩ <;> simp [next505] at hnext

/-- The machine halts from the blank tape if and only if `next505` halts from `start505`. -/
theorem isHalt_iff_next505 : IsHalt target ↔ CollatzHalts next505 start505 :=
  is_valid_next505_acceleration.isHalt_iff

/-! ### Single-sum law and global halting reduction -/

private def it (n : ℕ) (o : Option State505) : Option State505 :=
  (Option.bind · next505)^[n] o

private theorem it_zero (o : Option State505) : it 0 o = o := rfl

private theorem it_succ_front (n : ℕ) (o : Option State505) :
    it (n + 1) o = it n (o.bind next505) :=
  Function.iterate_succ_apply _ n o

private theorem it_add (m n : ℕ) (o : Option State505) :
    it (m + n) o = it n (it m o) := by
  unfold it
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem it_none (n : ℕ) : it n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [it_succ_front]; exact ih

private theorem bumpHead_iter_cons (k a : ℕ) (L : List ℕ) :
    bumpHead^[k] (a :: L) = (a + k) :: L := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [bumpHead]
    rw [ih (a + 1)]
    ring_nf

private theorem bumpHead_iter_nil_succ (k : ℕ) :
    bumpHead^[k + 1] [] = [k] := by
  rw [Function.iterate_succ_apply]
  simp only [bumpHead]
  simpa using bumpHead_iter_cons k 0 []

private theorem bumpHead_ne_nil (L : List ℕ) : bumpHead L ≠ [] := by
  cases L <;> simp [bumpHead]

private theorem bumpHead_iter_succ_ne_nil (k : ℕ) (L : List ℕ) :
    bumpHead^[k + 1] L ≠ [] := by
  cases L with
  | nil => rw [bumpHead_iter_nil_succ]; simp
  | cons a L' => rw [bumpHead_iter_cons]; simp

/-- Every non-empty left stack has positive weighted sum `W L > 0`. -/
theorem W_pos_of_ne_nil (L : List ℕ) (hL : L ≠ []) : 0 < W L := by
  cases L with
  | nil => contradiction
  | cons a L' =>
    simp only [W]
    omega

/-- Lower bound `2 ^ |L| - 1 ≤ W L` on any left stack `L`. -/
theorem two_pow_sub_one_le_W (L : List ℕ) : 2 ^ L.length - 1 ≤ W L := by
  induction L with
  | nil => simp [W]
  | cons a L' ih =>
    have hpow : 0 < 2 ^ L'.length := by positivity
    simp only [W, List.length_cons, pow_succ']
    omega

/-- Splitting identity `W (L₁ ++ L₂) = W L₁ + 2 ^ |L₁| * W L₂`. -/
theorem W_append (L₁ L₂ : List ℕ) : W (L₁ ++ L₂) = W L₁ + 2 ^ L₁.length * W L₂ := by
  induction L₁ with
  | nil => simp [W]
  | cons a L₁ ih =>
    simp only [List.cons_append, W, ih, List.length_cons, pow_succ']
    ring

private theorem peelPairs_reaches (k r : ℕ) (L R : List ℕ) :
    it (2 * k) (some (.D ((2 * k + r) :: L) R)) =
      some (.D (r :: bumpHead^[k] L) (bumpHead^[k] R)) := by
  induction k generalizing r L R with
  | zero => simp [it]
  | succ k ih =>
    have hsplit : 2 * (k + 1) = 2 + 2 * k := by omega
    have htop : 2 + 2 * k + r = (2 * k + r) + 2 := by omega
    rw [hsplit, htop, it_add]
    have h2 : it 2 (some (.D (((2 * k + r) + 2) :: L) R)) =
        some (.D ((2 * k + r) :: bumpHead L) (bumpHead R)) := rfl
    rw [h2, ih r (bumpHead L) (bumpHead R)]
    simp only [Function.iterate_succ_apply]

/-- Intra-peel two-step move: lowering a top entry `a + 2` by `2` reaches
`D (a :: bumpHead L) (bumpHead R)` in `2` steps of `next505`. -/
theorem stepTwo_reaches (a : ℕ) (L R : List ℕ) :
    (Option.bind · next505)^[2] (some (.D ((a + 2) :: L) R)) =
      some (.D (a :: bumpHead L) (bumpHead R)) :=
  rfl

/-- Intra-peel invariance of `W`: the two-step move lowering a top entry by `2` leaves `W`
unchanged, for both even and odd `a` and both empty and non-empty `L`. -/
theorem W_stepTwo (a : ℕ) (L : List ℕ) :
    W ((a + 2) :: L) = W (a :: bumpHead L) := by
  cases L with
  | nil =>
    simp only [bumpHead, W, Nat.mul_zero, Nat.add_zero]
  | cons b L' =>
    simp only [bumpHead, W]
    omega

/-- Clause 1a (resulting state of one odd peel): when `a` is odd, `a` steps of `next505` from
`D (a :: L) R` reach `D (bumpHead^[(a + 1) / 2] L) (0 :: bumpHead^[a / 2] R)`. -/
theorem oddPeel_reaches (a : ℕ) (L R : List ℕ) (ha : a % 2 = 1) :
    (Option.bind · next505)^[a] (some (.D (a :: L) R)) =
      some (.D (bumpHead^[(a + 1) / 2] L) (0 :: bumpHead^[a / 2] R)) := by
  change it a (some (.D (a :: L) R)) = _
  set k := a / 2
  have ha_eq : a = 2 * k + 1 := by omega
  have hk1 : (a + 1) / 2 = k + 1 := by omega
  rw [hk1]
  conv_lhs => rw [ha_eq]
  rw [it_add (2 * k) 1, peelPairs_reaches k 1 L R]
  simp [it, next505, Function.iterate_succ_apply']

/-- Clause 1b (odd peel halves `W`): one odd peel divides `W` by `2`, both for interior peels
(`L ≠ []`) and singleton peels (`L = []`). -/
theorem W_oddPeel (a : ℕ) (L : List ℕ) (ha : a % 2 = 1) :
    W (bumpHead^[(a + 1) / 2] L) = W (a :: L) / 2 := by
  set k := a / 2
  have ha_eq : a = 2 * k + 1 := by omega
  have hk1 : (a + 1) / 2 = k + 1 := by omega
  rw [hk1, ha_eq]
  cases L with
  | nil =>
    rw [bumpHead_iter_nil_succ]
    simp only [W]
    omega
  | cons b L' =>
    rw [bumpHead_iter_cons]
    simp only [W]
    omega

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem padicValNat_two_mul {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
  rw [padicValNat.mul (by omega) hm, padicValNat_self, add_comm]

private theorem singletonPeelDepthAux_eq (n b : ℕ) (hb : b ≤ n) :
    singletonPeelDepthAux n b = padicValNat 2 (b + 1) := by
  induction n generalizing b with
  | zero =>
    have hb0 : b = 0 := by omega
    subst hb0
    simp [singletonPeelDepthAux]
  | succ n ih =>
    unfold singletonPeelDepthAux
    by_cases hodd : b % 2 = 1
    · simp only [hodd, ↓reduceIte]
      rw [ih (b / 2) (by omega)]
      have h2 : b + 1 = 2 * (b / 2 + 1) := by omega
      rw [h2, padicValNat_two_mul (by omega)]
    · simp only [hodd, ↓reduceIte]
      symm
      exact padicValNat.eq_zero_of_not_dvd (by omega)

private theorem oddPeelDepthAux_eq (L : List ℕ) (a : ℕ) :
    oddPeelDepthAux L a = padicValNat 2 (W (a :: L)) := by
  induction L generalizing a with
  | nil =>
    simp only [oddPeelDepthAux, singletonPeelDepth, W, Nat.mul_zero, Nat.add_zero]
    exact singletonPeelDepthAux_eq a a le_rfl
  | cons c L' ih =>
    unfold oddPeelDepthAux
    by_cases hodd : a % 2 = 1
    · simp only [hodd, ↓reduceIte, ih]
      have hW : W (a :: c :: L') = 2 * W ((c + (a + 1) / 2) :: L') := by
        simp only [W]
        omega
      have hpos : W ((c + (a + 1) / 2) :: L') ≠ 0 := by
        have := W_pos_of_ne_nil ((c + (a + 1) / 2) :: L') (by simp)
        omega
      rw [hW, padicValNat_two_mul hpos]
    · simp only [hodd, ↓reduceIte]
      symm
      apply padicValNat.eq_zero_of_not_dvd
      simp only [W]
      omega

/-- Clause 2a (sweep depth is the 2-adic valuation): the number of consecutive odd `D`-peels from
`L` equals `padicValNat 2 (W L)`. -/
theorem oddPeelDepth_eq_padicValNat (L : List ℕ) :
    oddPeelDepth L = padicValNat 2 (W L) := by
  cases L with
  | nil => simp [oddPeelDepth, W]
  | cons a L' => exact oddPeelDepthAux_eq L' a

private theorem list_take_succ_eq_append (L : List ℕ) (d : ℕ) (hd : d < L.length) :
    L.take (d + 1) = L.take d ++ [L[d]'hd] := by
  induction L generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    rcases d with _ | d
    · rfl
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hd
      change x :: xs.take (d + 1) = x :: (xs.take d ++ [xs[d]'hd])
      rw [ih d hd]

private theorem list_drop_eq_cons (L : List ℕ) (d : ℕ) (hd : d < L.length) :
    L.drop d = (L[d]'hd) :: L.drop (d + 1) := by
  induction L generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    rcases d with _ | d
    · rfl
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hd
      change xs.drop d = xs[d]'hd :: xs.drop (d + 1)
      exact ih d hd

private theorem W_eq_take_add_drop (L : List ℕ) (m : ℕ) :
    ∃ t, W L = W (L.take m) + 2 ^ m * t := by
  by_cases hlen : m ≤ L.length
  · refine ⟨W (L.drop m), ?_⟩
    conv_lhs => rw [← List.take_append_drop m L, W_append]
    rw [List.length_take_of_le hlen]
  · refine ⟨0, ?_⟩
    rw [List.take_of_length_le (by omega)]
    omega

private theorem pow_dvd_W_take_iff (L : List ℕ) (m k : ℕ) (hk : k ≤ m) :
    2 ^ k ∣ W (L.take m) ↔ 2 ^ k ∣ W L := by
  obtain ⟨t, hsplit⟩ := W_eq_take_add_drop L m
  have hmul : 2 ^ k ∣ 2 ^ m * t :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hk) t
  rw [hsplit]
  exact Nat.dvd_add_iff_left hmul

private theorem take_succ_ne_nil (L : List ℕ) (hL : L ≠ []) (d : ℕ) :
    L.take (d + 1) ≠ [] := by
  cases L with
  | nil => contradiction
  | cons a L' => simp

private theorem peelTop_odd_and_half (L : List ℕ) (hL : L ≠ []) (d : ℕ)
    (hd : d + 1 ≤ padicValNat 2 (W L)) :
    peelTop L d % 2 = 1 ∧
    (peelTop L d + 1) / 2 = W (L.take (d + 1)) / 2 ^ (d + 1) ∧
    1 ≤ W (L.take (d + 1)) / 2 ^ (d + 1) := by
  have hWpos : 0 < W L := W_pos_of_ne_nil L hL
  have hdvdW : 2 ^ (d + 1) ∣ W L :=
    (padicValNat_dvd_iff_le (by omega)).mpr hd
  have hdvd : 2 ^ (d + 1) ∣ W (L.take (d + 1)) :=
    (pow_dvd_W_take_iff L (d + 1) (d + 1) le_rfl).mpr hdvdW
  have htake_pos : 0 < W (L.take (d + 1)) :=
    W_pos_of_ne_nil _ (take_succ_ne_nil L hL d)
  set q := W (L.take (d + 1)) / 2 ^ (d + 1)
  have hq_eq : W (L.take (d + 1)) = 2 ^ (d + 1) * q := (Nat.mul_div_cancel' hdvd).symm
  have hq_pos : 1 ≤ q :=
    Nat.div_pos (Nat.le_of_dvd htake_pos hdvd) (by positivity)
  have hpow : 0 < 2 ^ d := by positivity
  have hdiv : W (L.take (d + 1)) / 2 ^ d = 2 * q := by
    have hmul : W (L.take (d + 1)) = 2 ^ d * (2 * q) := by
      rw [hq_eq, pow_succ]
      ring
    rw [hmul, Nat.mul_div_cancel_left _ hpow]
  unfold peelTop
  rw [hdiv]
  omega

private theorem oddSweep_at_depth (L R : List ℕ) (hL : L ≠ []) (d : ℕ)
    (hd : d ≤ padicValNat 2 (W L)) :
    it (oddSweepSteps L d) (some (.D L R)) =
      some (.D (peelTop L d :: L.drop (d + 1)) (oddSweepR L R d)) := by
  induction d with
  | zero =>
    cases L with
    | nil => contradiction
    | cons a L' =>
      simp only [oddSweepSteps, oddSweepR, it_zero, peelTop, List.take, W,
        Nat.mul_zero, Nat.add_zero, pow_zero, Nat.div_one, Nat.add_sub_cancel, List.drop]
  | succ d ih =>
    have hd_le : d ≤ padicValNat 2 (W L) := by omega
    obtain ⟨hodd, hhalf, hq_pos⟩ := peelTop_odd_and_half L hL d hd
    simp only [oddSweepSteps]
    rw [it_add, ih hd_le]
    have hstep : it (peelTop L d)
        (some (.D (peelTop L d :: L.drop (d + 1)) (oddSweepR L R d))) =
        some (.D (bumpHead^[(peelTop L d + 1) / 2] (L.drop (d + 1)))
          (0 :: bumpHead^[peelTop L d / 2] (oddSweepR L R d))) :=
      oddPeel_reaches (peelTop L d) (L.drop (d + 1)) (oddSweepR L R d) hodd
    rw [hstep]
    congr 2
    rw [hhalf]
    set q := W (L.take (d + 1)) / 2 ^ (d + 1)
    by_cases hlt : d + 1 < L.length
    · rw [list_drop_eq_cons L (d + 1) hlt, bumpHead_iter_cons]
      congr 1
      have htake : L.take (d + 2) = L.take (d + 1) ++ [L[d + 1]'hlt] :=
        list_take_succ_eq_append L (d + 1) hlt
      have hdvdW : 2 ^ (d + 1) ∣ W L :=
        (padicValNat_dvd_iff_le (by have := W_pos_of_ne_nil L hL; omega)).mpr hd
      have hdvd : 2 ^ (d + 1) ∣ W (L.take (d + 1)) :=
        (pow_dvd_W_take_iff L (d + 1) (d + 1) le_rfl).mpr hdvdW
      have hq_eq : W (L.take (d + 1)) = 2 ^ (d + 1) * q :=
        (Nat.mul_div_cancel' hdvd).symm
      have hlen : (L.take (d + 1)).length = d + 1 :=
        List.length_take_of_le (by omega)
      have hW2 : W (L.take (d + 2)) = 2 ^ (d + 1) * (q + L[d + 1]'hlt + 1) := by
        rw [htake, W_append, hlen, hq_eq]
        simp only [W, Nat.mul_zero, Nat.add_zero]
        ring
      have hpow : 0 < 2 ^ (d + 1) := by positivity
      unfold peelTop
      rw [hW2, Nat.mul_div_cancel_left _ hpow]
      omega
    · have hdrop1 : L.drop (d + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have hdrop2 : L.drop (d + 2) = [] := List.drop_eq_nil_of_le (by omega)
      have htake1 : L.take (d + 1) = L := List.take_of_length_le (by omega)
      have htake2 : L.take (d + 2) = L := List.take_of_length_le (by omega)
      rw [hdrop1, hdrop2]
      have hq_succ : q = (q - 1) + 1 := by omega
      rw [hq_succ, bumpHead_iter_nil_succ]
      congr 1
      unfold peelTop
      rw [htake2]
      have hq_def : q = W L / 2 ^ (d + 1) := by simp [q, htake1]
      omega

private theorem peelTop_padicValNat_even (L : List ℕ) (hL : L ≠ []) :
    let ν := padicValNat 2 (W L)
    peelTop L ν % 2 = 0 ∧ 1 ≤ W (L.take (ν + 1)) / 2 ^ ν := by
  intro ν
  have hWpos : 0 < W L := W_pos_of_ne_nil L hL
  have hdvdW : 2 ^ ν ∣ W L := pow_padicValNat_dvd
  have hndvdW : ¬ 2 ^ (ν + 1) ∣ W L := pow_succ_padicValNat_not_dvd (by omega)
  have hdvd : 2 ^ ν ∣ W (L.take (ν + 1)) :=
    (pow_dvd_W_take_iff L (ν + 1) ν (by omega)).mpr hdvdW
  have hndvd : ¬ 2 ^ (ν + 1) ∣ W (L.take (ν + 1)) := by
    intro h
    exact hndvdW ((pow_dvd_W_take_iff L (ν + 1) (ν + 1) le_rfl).mp h)
  have htake_pos : 0 < W (L.take (ν + 1)) :=
    W_pos_of_ne_nil _ (take_succ_ne_nil L hL ν)
  set m := W (L.take (ν + 1)) / 2 ^ ν
  have hm_eq : W (L.take (ν + 1)) = 2 ^ ν * m := (Nat.mul_div_cancel' hdvd).symm
  have hm_pos : 1 ≤ m :=
    Nat.div_pos (Nat.le_of_dvd htake_pos hdvd) (by positivity)
  have hm_odd : m % 2 = 1 := by
    by_contra hnotodd
    obtain ⟨r, hr⟩ : ∃ r, m = 2 * r := ⟨m / 2, by omega⟩
    apply hndvd
    refine ⟨r, ?_⟩
    rw [hm_eq, hr, pow_succ]
    ring
  refine ⟨?_, hm_pos⟩
  unfold peelTop
  change (m - 1) % 2 = 0
  omega

/-- Clause 2b (sweep stops inside the stack): when `padicValNat 2 (W L) + 1 < L.length`, the
`ν = padicValNat 2 (W L)` odd peels stop inside `L` at
`D (peelTop L ν :: L.drop (ν + 1)) (oddSweepR L R ν)` with an even top entry and non-empty tail. -/
theorem oddSweep_stops_inside (L R : List ℕ) (h : padicValNat 2 (W L) + 1 < L.length) :
    let ν := padicValNat 2 (W L)
    (Option.bind · next505)^[oddSweepSteps L ν] (some (.D L R)) =
      some (.D (peelTop L ν :: L.drop (ν + 1)) (oddSweepR L R ν)) ∧
    peelTop L ν % 2 = 0 ∧
    L.drop (ν + 1) ≠ [] := by
  intro ν
  have hL : L ≠ [] := by
    intro hnil
    subst hnil
    simp at h
  refine ⟨oddSweep_at_depth L R hL ν le_rfl, (peelTop_padicValNat_even L hL).1, ?_⟩
  intro hdrop
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_nil] at hlen
  omega

/-- Clause 2c (sweep reaches the singleton fresh start): when `L ≠ []` and
`L.length - 1 ≤ padicValNat 2 (W L)`, the first `L.length - 1` odd peels reach the singleton fresh
start `D [W L / 2 ^ (L.length - 1) - 1] (oddSweepR L R (L.length - 1))` whose `b + 1` value equals
`W L / 2 ^ (L.length - 1)`. -/
theorem oddSweep_reaches_singleton (L R : List ℕ) (hL : L ≠ [])
    (h : L.length - 1 ≤ padicValNat 2 (W L)) :
    (Option.bind · next505)^[oddSweepSteps L (L.length - 1)] (some (.D L R)) =
      some (.D [W L / 2 ^ (L.length - 1) - 1] (oddSweepR L R (L.length - 1))) ∧
    (W L / 2 ^ (L.length - 1) - 1) + 1 = W L / 2 ^ (L.length - 1) := by
  have hlen_pos : 1 ≤ L.length := List.length_pos_iff_ne_nil.mpr hL
  have hreach := oddSweep_at_depth L R hL (L.length - 1) h
  have h1 : L.length - 1 + 1 = L.length := by omega
  have htake : L.take (L.length - 1 + 1) = L := by rw [h1, List.take_length]
  have hdrop : L.drop (L.length - 1 + 1) = [] := by rw [h1, List.drop_length]
  have htop : peelTop L (L.length - 1) = W L / 2 ^ (L.length - 1) - 1 := by
    unfold peelTop
    rw [htake]
  rw [htop, hdrop] at hreach
  refine ⟨hreach, ?_⟩
  have hWpos : 0 < W L := W_pos_of_ne_nil L hL
  have hdvd : 2 ^ (L.length - 1) ∣ W L :=
    (padicValNat_dvd_iff_le (by omega)).mpr h
  have hq_pos : 1 ≤ W L / 2 ^ (L.length - 1) :=
    Nat.div_pos (Nat.le_of_dvd hWpos hdvd) (by positivity)
  omega

/-- Clause 2d (end of the singleton sweep): when `L ≠ []` and
`L.length - 1 ≤ padicValNat 2 (W L)`, all `ν = padicValNat 2 (W L)` odd peels reach the even
singleton `D [W L / 2 ^ ν - 1] (oddSweepR L R ν)`. -/
theorem oddSweep_singleton_end (L R : List ℕ) (hL : L ≠ [])
    (h : L.length - 1 ≤ padicValNat 2 (W L)) :
    let ν := padicValNat 2 (W L)
    (Option.bind · next505)^[oddSweepSteps L ν] (some (.D L R)) =
      some (.D [W L / 2 ^ ν - 1] (oddSweepR L R ν)) ∧
    (W L / 2 ^ ν - 1) % 2 = 0 := by
  intro ν
  have hlen_le : L.length ≤ ν + 1 := by omega
  have hreach := oddSweep_at_depth L R hL ν le_rfl
  have htake : L.take (ν + 1) = L := List.take_of_length_le hlen_le
  have hdrop : L.drop (ν + 1) = [] := List.drop_eq_nil_of_le hlen_le
  have htop : peelTop L ν = W L / 2 ^ ν - 1 := by
    unfold peelTop
    rw [htake]
  have hev := (peelTop_padicValNat_even L hL).1
  change peelTop L ν % 2 = 0 at hev
  rw [htop] at hreach hev
  rw [hdrop] at hreach
  exact ⟨hreach, hev⟩

private theorem padicValNat_pos_of_odd_top (a : ℕ) (L : List ℕ) (ha : a % 2 = 1) :
    1 ≤ padicValNat 2 (W (a :: L)) := by
  have hWpos : 0 < W (a :: L) := W_pos_of_ne_nil (a :: L) (by simp)
  have hdvd : 2 ^ 1 ∣ W (a :: L) := by
    simp only [pow_one, W]
    omega
  exact (padicValNat_dvd_iff_le (by omega)).mp hdvd

private theorem peelTop_eq_zero_iff_pow2 (a : ℕ) (L : List ℕ) (ha : a % 2 = 1) :
    peelTop (a :: L) (padicValNat 2 (W (a :: L))) = 0 ↔
      ∃ k, W (a :: L) = 2 ^ k := by
  set ν := padicValNat 2 (W (a :: L))
  have hL : a :: L ≠ [] := by simp
  have hν_pos : 1 ≤ ν := padicValNat_pos_of_odd_top a L ha
  have hdvdW : 2 ^ ν ∣ W (a :: L) := pow_padicValNat_dvd
  have hdvd : 2 ^ ν ∣ W ((a :: L).take (ν + 1)) :=
    (pow_dvd_W_take_iff (a :: L) (ν + 1) ν (by omega)).mpr hdvdW
  have htake_pos : 0 < W ((a :: L).take (ν + 1)) :=
    W_pos_of_ne_nil _ (take_succ_ne_nil (a :: L) hL ν)
  have hm_pos : 1 ≤ W ((a :: L).take (ν + 1)) / 2 ^ ν :=
    Nat.div_pos (Nat.le_of_dvd htake_pos hdvd) (by positivity)
  constructor
  · intro hzero
    unfold peelTop at hzero
    have hm1 : W ((a :: L).take (ν + 1)) / 2 ^ ν = 1 := by omega
    have hW_eq : W ((a :: L).take (ν + 1)) = 2 ^ ν := by
      have := (Nat.mul_div_cancel' hdvd).symm
      rw [hm1, Nat.mul_one] at this
      exact this
    by_cases hlen : ν + 1 ≤ (a :: L).length
    · have hlen_take : ((a :: L).take (ν + 1)).length = ν + 1 :=
        List.length_take_of_le hlen
      have hlow := two_pow_sub_one_le_W ((a :: L).take (ν + 1))
      rw [hlen_take, hW_eq, pow_succ'] at hlow
      have hpow2 : 2 ≤ 2 ^ ν := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hν_pos
      omega
    · rw [List.take_of_length_le (by omega)] at hW_eq
      exact ⟨ν, hW_eq⟩
  · rintro ⟨k, hk⟩
    have hν_eq : ν = k := by
      change padicValNat 2 (W (a :: L)) = k
      rw [hk, padicValNat.prime_pow]
    have hlen_lt : (a :: L).length ≤ k := by
      have hk1 : 1 ≤ k := by omega
      have hg2 : 2 ≤ 2 ^ k := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hk1
      have hlow := two_pow_sub_one_le_W (a :: L)
      rw [hk] at hlow
      by_contra hgt
      have hk_le : k + 1 ≤ (a :: L).length := by omega
      have hpow_le : 2 ^ (k + 1) ≤ 2 ^ (a :: L).length :=
        Nat.pow_le_pow_right (by omega) hk_le
      rw [pow_succ'] at hpow_le
      omega
    unfold peelTop
    rw [hν_eq, List.take_of_length_le (by omega), hk, Nat.div_self (by positivity)]

private theorem oddSweepR_pow2_shape (a : ℕ) (L R : List ℕ)
    (ha : a % 2 = 1) (hR : a :: L ≠ [1] ∨ R ≠ [])
    (hk : W (a :: L) = 2 ^ padicValNat 2 (W (a :: L))) :
    ∃ e R', oddSweepR (a :: L) R (padicValNat 2 (W (a :: L))) = 0 :: e :: R' := by
  set ν := padicValNat 2 (W (a :: L))
  have hν_pos : 1 ≤ ν := padicValNat_pos_of_odd_top a L ha
  rcases ν with _ | d
  · omega
  · rcases d with _ | d'
    · -- `ν = 1`, so `W (a :: L) = 2`
      have hW2 : W (a :: L) = 2 := by simpa using hk
      have ha1 : a = 1 ∧ L = [] := by
        cases L with
        | nil =>
          simp only [W, Nat.mul_zero, Nat.add_zero] at hW2
          exact ⟨by omega, rfl⟩
        | cons b L' =>
          simp only [W] at hW2
          omega
      rcases hR with hne | hRne
      · exfalso; exact hne (by rw [ha1.1, ha1.2])
      · cases R with
        | nil => contradiction
        | cons r₀ R₀ =>
          have htop0 : peelTop (a :: L) 0 / 2 = 0 := by
            rw [ha1.1, ha1.2]
            rfl
          simp only [oddSweepR, htop0, Function.iterate_zero_apply]
          exact ⟨r₀, R₀, rfl⟩
    · -- `ν = d' + 2 ≥ 2`
      simp only [oddSweepR]
      rw [bumpHead_iter_cons]
      exact ⟨0 + peelTop (a :: L) (d' + 1) / 2,
        bumpHead^[peelTop (a :: L) d' / 2] (oddSweepR (a :: L) R d'), rfl⟩

/-- Clause 3a (halting at the end of the odd-peel chain): from any odd-top `D`-state `D (a :: L) R`
with `a :: L ≠ [1] ∨ R ≠ []`, the step immediately after the `padicValNat 2 (W (a :: L))` odd peels
halts (`none`) if and only if `W (a :: L)` is a power of two. -/
theorem oddSweep_halts_iff_powerOfTwo (a : ℕ) (L R : List ℕ)
    (ha : a % 2 = 1) (hR : a :: L ≠ [1] ∨ R ≠ []) :
    ((Option.bind · next505)^[oddSweepSteps (a :: L) (padicValNat 2 (W (a :: L))) + 1]
      (some (.D (a :: L) R))).isNone ↔
      ∃ k, W (a :: L) = 2 ^ k := by
  change (it (oddSweepSteps (a :: L) (padicValNat 2 (W (a :: L))) + 1)
    (some (.D (a :: L) R))).isNone ↔ _
  set ν := padicValNat 2 (W (a :: L))
  have hL : a :: L ≠ [] := by simp
  rw [it_add, oddSweep_at_depth (a :: L) R hL ν le_rfl]
  by_cases hpow : ∃ k, W (a :: L) = 2 ^ k
  · simp only [hpow, iff_true]
    have htop0 : peelTop (a :: L) ν = 0 := (peelTop_eq_zero_iff_pow2 a L ha).mpr hpow
    obtain ⟨k, hk⟩ := hpow
    have hν_eq : ν = k := by
      change padicValNat 2 (W (a :: L)) = k
      rw [hk, padicValNat.prime_pow]
    have hk' : W (a :: L) = 2 ^ ν := by rw [hν_eq]; exact hk
    obtain ⟨e, R', hRshape⟩ := oddSweepR_pow2_shape a L R ha hR hk'
    rw [htop0, hRshape]
    rfl
  · simp only [hpow, iff_false, Bool.not_eq_true]
    have hne0 : peelTop (a :: L) ν ≠ 0 :=
      mt (peelTop_eq_zero_iff_pow2 a L ha).mp hpow
    have hev : peelTop (a :: L) ν % 2 = 0 := (peelTop_padicValNat_even (a :: L) hL).1
    have hge2 : peelTop (a :: L) ν = (peelTop (a :: L) ν - 2) + 2 := by omega
    rw [hge2]
    rfl

/-- Clause 3b (halting across the full `D`-sweep including the terminal even peel): from any
odd-top `D`-state `D (a :: L) R` with `a :: L ≠ [1] ∨ R ≠ []`, the full `D`-sweep of
`fullSweepSteps (a :: L)` steps halts (`none`) if and only if `W (a :: L)` is a power of two. -/
theorem fullSweep_halts_iff_powerOfTwo (a : ℕ) (L R : List ℕ)
    (ha : a % 2 = 1) (hR : a :: L ≠ [1] ∨ R ≠ []) :
    ((Option.bind · next505)^[fullSweepSteps (a :: L)] (some (.D (a :: L) R))).isNone ↔
      ∃ k, W (a :: L) = 2 ^ k := by
  change (it (fullSweepSteps (a :: L)) (some (.D (a :: L) R))).isNone ↔ _
  unfold fullSweepSteps
  dsimp only
  set ν := padicValNat 2 (W (a :: L))
  have hL : a :: L ≠ [] := by simp
  by_cases hpow : ∃ k, W (a :: L) = 2 ^ k
  · have htop0 : peelTop (a :: L) ν = 0 := (peelTop_eq_zero_iff_pow2 a L ha).mpr hpow
    rw [htop0, Nat.add_zero]
    exact oddSweep_halts_iff_powerOfTwo a L R ha hR
  · simp only [hpow, iff_false, Bool.not_eq_true]
    have hne0 : peelTop (a :: L) ν ≠ 0 :=
      mt (peelTop_eq_zero_iff_pow2 a L ha).mp hpow
    have hev : peelTop (a :: L) ν % 2 = 0 := (peelTop_padicValNat_even (a :: L) hL).1
    set m := peelTop (a :: L) ν / 2
    have hm_pos : 1 ≤ m := by omega
    have htop_eq : peelTop (a :: L) ν = 2 * m := by omega
    have hν_pos : 1 ≤ ν := padicValNat_pos_of_odd_top a L ha
    have hR0 : ∃ R_rest, oddSweepR (a :: L) R ν = 0 :: R_rest := by
      rcases ν with _ | d
      · omega
      · exact ⟨bumpHead^[peelTop (a :: L) d / 2] (oddSweepR (a :: L) R d), rfl⟩
    obtain ⟨R_rest, hR_rest⟩ := hR0
    have hsteps : oddSweepSteps (a :: L) ν + peelTop (a :: L) ν + 1 =
        oddSweepSteps (a :: L) ν + (2 * m + 1) := by omega
    rw [hsteps, it_add, oddSweep_at_depth (a :: L) R hL ν le_rfl, htop_eq, hR_rest,
      it_add (2 * m) 1]
    have hpairs : it (2 * m) (some (.D ((2 * m + 0) :: (a :: L).drop (ν + 1)) (0 :: R_rest))) =
        some (.D (0 :: bumpHead^[m] ((a :: L).drop (ν + 1))) (bumpHead^[m] (0 :: R_rest))) :=
      peelPairs_reaches m 0 ((a :: L).drop (ν + 1)) (0 :: R_rest)
    rw [Nat.add_zero] at hpairs
    rw [hpairs, bumpHead_iter_cons, Nat.zero_add]
    rcases m with _ | _ | m'
    · omega
    · rfl
    · rfl

/-- Clause 3c (halting from any positive singleton exposure `D [b] R` with `1 ≤ b` and `R ≠ []`,
for both even and odd `b`): the full `D`-sweep halts if and only if `b + 1` is a power of two. -/
theorem singleton_halts_iff_powerOfTwo (b : ℕ) (R : List ℕ) (hb : 1 ≤ b) (hR : R ≠ []) :
    ((Option.bind · next505)^[fullSweepSteps [b]] (some (.D [b] R))).isNone ↔
      ∃ k, b + 1 = 2 ^ k := by
  by_cases hodd : b % 2 = 1
  · have hW : W [b] = b + 1 := by simp [W]
    rw [← hW]
    exact fullSweep_halts_iff_powerOfTwo b [] R hodd (Or.inr hR)
  · have hnotpow : ¬ ∃ k, b + 1 = 2 ^ k := by
      rintro ⟨k, hk⟩
      rcases k with _ | k
      · omega
      · rw [pow_succ'] at hk
        omega
    change (it (fullSweepSteps [b]) (some (.D [b] R))).isNone ↔ _
    simp only [hnotpow, iff_false, Bool.not_eq_true]
    have hν0 : padicValNat 2 (W [b]) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      simp only [W]
      omega
    have htop : peelTop [b] 0 = b := by
      simp [peelTop, W]
    unfold fullSweepSteps
    dsimp only
    rw [hν0]
    change (it (0 + peelTop [b] 0 + 1) (some (.D [b] R))).isNone = false
    rw [Nat.zero_add, htop]
    set m := b / 2
    have hm_pos : 1 ≤ m := by omega
    have hb_eq : b = 2 * m := by omega
    cases R with
    | nil => contradiction
    | cons r₀ R' =>
      rw [hb_eq, it_add (2 * m) 1]
      have hpairs := peelPairs_reaches m 0 [] (r₀ :: R')
      rw [Nat.add_zero] at hpairs
      rw [hpairs, bumpHead_iter_cons]
      have hge1 : 1 ≤ r₀ + m := by omega
      rcases hrm : r₀ + m with _ | _ | d
      · omega
      · rfl
      · rfl

/-- `start505` satisfies the inductive orbit invariant `OrbitInv`. -/
theorem orbitInv_start505 : OrbitInv start505 := by
  decide

private theorem headI_bumpHead_iter_ge (k : ℕ) (hk : 1 ≤ k) (L : List ℕ) :
    k - 1 ≤ (bumpHead^[k] L).headI := by
  rcases k with _ | k'
  · omega
  · cases L with
    | nil =>
      rw [bumpHead_iter_nil_succ]
      simp
    | cons a L' =>
      rw [bumpHead_iter_cons]
      simp
      omega

/-- `OrbitInv` is preserved by every non-halting step of `next505`. -/
theorem orbitInv_step {s s' : State505} (h : OrbitInv s) (hstep : next505 s = some s') :
    OrbitInv s' := by
  cases s with
  | D L R =>
    obtain ⟨hLne, hRnil, hL0, hL2⟩ := h
    rcases L with _ | ⟨_ | _ | a, L'⟩
    · contradiction
    · rcases R with _ | ⟨_ | _ | d, R'⟩
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        have hhd := headI_bumpHead_iter_ge 3 (by omega) L'
        have hne := bumpHead_iter_succ_ne_nil 2 L'
        refine ⟨hne, fun _ => by omega, ?_, ?_⟩
        · intro h0; rw [h0] at hhd; simp at hhd
        · rintro ⟨_, h0⟩; omega
      · rcases R' with _ | ⟨e, R''⟩
        · simp only [next505, Option.some.injEq] at hstep
          subst hstep
          have hhd := headI_bumpHead_iter_ge 6 (by omega) L'
          have hne := bumpHead_iter_succ_ne_nil 5 L'
          refine ⟨hne, fun _ => by omega, ?_, ?_⟩
          · intro h0; rw [h0] at hhd; simp at hhd
          · rintro ⟨_, h0⟩; omega
        · simp [next505] at hstep
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        have hhd := headI_bumpHead_iter_ge 4 (by omega) L'
        have hne := bumpHead_iter_succ_ne_nil 3 L'
        have hRne := bumpHead_ne_nil R'
        refine ⟨hne, fun hR0 => absurd hR0 hRne, ?_, ?_⟩
        · intro h0; rw [h0] at hhd; simp at hhd
        · rintro ⟨_, h0⟩; omega
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        exact bumpHead_iter_succ_ne_nil 3 L'
    · simp only [next505, Option.some.injEq] at hstep
      subst hstep
      cases L' with
      | nil =>
        have hRne : R ≠ [] := by
          intro hR0
          have := hRnil hR0
          simp at this
        cases R with
        | nil => contradiction
        | cons e R' =>
          simp [OrbitInv, bumpHead]
      | cons b L'' =>
        simp [OrbitInv, bumpHead]
    · simp only [next505, Option.some.injEq] at hstep
      subst hstep
      exact bumpHead_ne_nil L'
  | FR a L R =>
    have hLne : L ≠ [] := h
    cases L with
    | nil => contradiction
    | cons b L' =>
      rcases R with _ | ⟨_ | d, R'⟩
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        simp [OrbitInv]
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        refine ⟨by simp, fun hR0 => absurd hR0 (bumpHead_ne_nil R'), by simp, ?_⟩
        rintro _ ⟨hlenR, hhdR⟩
        cases R' with
        | nil => simp [bumpHead] at hlenR
        | cons x xs => simp [bumpHead] at hhdR
      · simp only [next505, Option.some.injEq] at hstep
        subst hstep
        simp [OrbitInv]

private theorem orbitInv_iterate (t : ℕ) {s : State505}
    (ht : it t (some start505) = some s) : OrbitInv s := by
  induction t generalizing s with
  | zero =>
    simp only [it_zero, Option.some.injEq] at ht
    subst ht
    exact orbitInv_start505
  | succ t ih =>
    have hsplit : it (t + 1) (some start505) = it 1 (it t (some start505)) :=
      it_add t 1 (some start505)
    rw [hsplit] at ht
    rcases hprev : it t (some start505) with _ | sp
    · rw [hprev] at ht
      simp [it] at ht
    · rw [hprev] at ht
      simp only [it, Function.iterate_one, Option.bind_some] at ht
      exact orbitInv_step (ih hprev) ht

private theorem exists_halt_step_of_collatzHalts
    (h : CollatzHalts next505 start505) :
    ∃ t s, it t (some start505) = some s ∧ next505 s = none := by
  obtain ⟨n, hn⟩ := h
  change (it n (some start505)).isNone at hn
  induction n with
  | zero => simp [it] at hn
  | succ n ih =>
    by_cases hn' : (it n (some start505)).isNone
    · exact ih hn'
    · rcases hcur : it n (some start505) with _ | s
      · rw [hcur] at hn'; simp at hn'
      · refine ⟨n, s, hcur, ?_⟩
        have hnext : it (n + 1) (some start505) = next505 s := by
          rw [it_add n 1, hcur]
          rfl
        rw [hnext] at hn
        exact Option.isNone_iff_eq_none.mp hn

/-- Global halting reduction (`D`-states): the machine halts from the blank tape if and only if the
`next505`-orbit of `start505` ever reaches a `D L R` state whose weighted sum `W L` is a power of
two. -/
theorem isHalt_iff_D_powerOfTwo :
    IsHalt target ↔
      ∃ t L R,
        (Option.bind · next505)^[t] (some start505) = some (.D L R) ∧
        ∃ k, W L = 2 ^ k := by
  rw [isHalt_iff_next505]
  constructor
  · intro hhalt
    obtain ⟨t, s, ht, hnone⟩ := exists_halt_step_of_collatzHalts hhalt
    have hinv := orbitInv_iterate t ht
    cases s with
    | FR a L R =>
      rcases R with _ | ⟨_ | d, R'⟩ <;> simp [next505] at hnone
    | D L R =>
      obtain ⟨hLne, _, _, hL2⟩ := hinv
      rcases L with _ | ⟨_ | _ | a, L'⟩
      · contradiction
      · rcases R with _ | ⟨_ | _ | d, R'⟩
        · simp [next505] at hnone
        · rcases R' with _ | ⟨e, R''⟩
          · simp [next505] at hnone
          · cases L' with
            | nil =>
              exact ⟨t, [0], 0 :: e :: R'', ht, 0, rfl⟩
            | cons b L'' =>
              exfalso
              exact hL2 ⟨by simp, rfl⟩ ⟨by simp, rfl⟩
        · simp [next505] at hnone
        · simp [next505] at hnone
      · simp [next505] at hnone
      · simp [next505] at hnone
  · rintro ⟨t, L, R, ht, k, hk⟩
    change it t (some start505) = some (.D L R) at ht
    have hinv := orbitInv_iterate t ht
    obtain ⟨hLne, hRnil, hL0, _⟩ := hinv
    cases L with
    | nil => contradiction
    | cons a L' =>
      rcases k with _ | k
      · have ha0 : a = 0 ∧ L' = [] := by
          cases L' with
          | nil =>
            simp only [W, Nat.mul_zero, Nat.add_zero, pow_zero] at hk
            exact ⟨by omega, rfl⟩
          | cons b L'' =>
            simp only [W, pow_zero] at hk
            omega
        rw [ha0.1, ha0.2] at ht hL0
        obtain ⟨hlenR, hhdR⟩ := hL0 rfl
        rcases R with _ | ⟨r₀, _ | ⟨e, R''⟩⟩
        · simp at hlenR
        · simp at hlenR
        · simp only [List.headI_cons] at hhdR
          subst hhdR
          refine ⟨t + 1, ?_⟩
          change (it (t + 1) (some start505)).isNone
          rw [it_add t 1, ht]
          rfl
      · have ha_odd : a % 2 = 1 := by
          rw [pow_succ'] at hk
          simp only [W] at hk
          omega
        have hR : a :: L' ≠ [1] ∨ R ≠ [] := by
          by_cases hR0 : R = []
          · left
            have hge2 := hRnil hR0
            simp only [List.headI_cons] at hge2
            intro h1
            injection h1 with ha1 _
            omega
          · exact Or.inr hR0
        have hhalt :=
          (fullSweep_halts_iff_powerOfTwo a L' R ha_odd hR).mpr ⟨k + 1, hk⟩
        refine ⟨t + fullSweepSteps (a :: L'), ?_⟩
        change (it (t + fullSweepSteps (a :: L')) (some start505)).isNone
        rw [it_add, ht]
        exact hhalt

/-- Global halting reduction (odd-top `D`-sweep starts): the machine halts from the blank tape if
and only if the `next505`-orbit of `start505` ever reaches an odd-top `D (a :: L) R` state whose
weighted sum `W (a :: L)` is a power of two. -/
theorem isHalt_iff_oddTop_powerOfTwo :
    IsHalt target ↔
      ∃ t a L R,
        a % 2 = 1 ∧
        (Option.bind · next505)^[t] (some start505) = some (.D (a :: L) R) ∧
        ∃ k, W (a :: L) = 2 ^ k := by
  rw [isHalt_iff_D_powerOfTwo]
  constructor
  · rintro ⟨t, L, R, ht, k, hk⟩
    have hinv := orbitInv_iterate t ht
    obtain ⟨hLne, _, hL0, _⟩ := hinv
    cases L with
    | nil => contradiction
    | cons a L' =>
      by_cases ha_odd : a % 2 = 1
      · exact ⟨t, a, L', R, ha_odd, ht, k, hk⟩
      · have hk0 : k = 0 := by
          rcases k with _ | k'
          · rfl
          · rw [pow_succ'] at hk
            simp only [W] at hk
            omega
        subst hk0
        have ha0 : a = 0 ∧ L' = [] := by
          cases L' with
          | nil =>
            simp only [W, Nat.mul_zero, Nat.add_zero, pow_zero] at hk
            exact ⟨by omega, rfl⟩
          | cons b L'' =>
            simp only [W, pow_zero] at hk
            omega
        rw [ha0.1, ha0.2] at ht hL0
        obtain ⟨hlenR, hhdR⟩ := hL0 rfl
        rcases R with _ | ⟨r₀, _ | ⟨e, R''⟩⟩
        · simp at hlenR
        · simp at hlenR
        · simp only [List.headI_cons] at hhdR
          subst hhdR
          rcases t with _ | t'
          · simp [start505] at ht
          · have hsplit : it (t' + 1) (some start505) = it 1 (it t' (some start505)) :=
              it_add t' 1 (some start505)
            change it (t' + 1) (some start505) = _ at ht
            rw [hsplit] at ht
            rcases hprev : it t' (some start505) with _ | sp
            · rw [hprev] at ht; simp [it] at ht
            · rw [hprev] at ht
              simp only [it, Function.iterate_one, Option.bind_some] at ht
              have hinv_prev := orbitInv_iterate t' hprev
              cases sp with
              | FR a₀ L₀ R₀ =>
                have hL₀ : L₀ ≠ [] := hinv_prev
                cases L₀ with
                | nil => contradiction
                | cons b₀ L₀' =>
                  rcases R₀ with _ | ⟨_ | d₀, R₀'⟩ <;> simp [next505] at ht
              | D L₀ R₀ =>
                rcases L₀ with _ | ⟨_ | _ | a₀, L₀'⟩
                · simp [next505] at ht
                · rcases R₀ with _ | ⟨_ | _ | d₀, R₀'⟩
                  · simp [next505] at ht
                  · rcases R₀' with _ | ⟨e₀, R₀''⟩ <;> simp [next505] at ht
                  · have hhd4 := headI_bumpHead_iter_ge 4 (by omega) L₀'
                    simp only [next505, Option.some.injEq, State505.D.injEq] at ht
                    rw [ht.1] at hhd4
                    simp at hhd4
                  · simp [next505] at ht
                · simp only [next505, Option.some.injEq, State505.D.injEq] at ht
                  cases L₀' with
                  | nil =>
                    obtain ⟨_, hR_eq⟩ := ht
                    injection hR_eq with _ hR₀_eq
                    subst hR₀_eq
                    exact ⟨t', 1, [], e :: R'', rfl, hprev, 1, rfl⟩
                  | cons b₀ L₀'' =>
                    simp [bumpHead] at ht
                · simp [next505] at ht
  · rintro ⟨t, a, L, R, _, ht, k, hk⟩
    exact ⟨t, a :: L, R, ht, k, hk⟩

end AntihydraOrbit.Line505
