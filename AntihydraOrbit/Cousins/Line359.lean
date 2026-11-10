import Mathlib
import BusyBeaver.BB6.Accelerations.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

/-!
# The machine `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`: one stack, one sweep, one weighted sum

The DeepMind `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart`. This file restates that acceleration as
a single map `U` on one stack of natural numbers and gives its halting condition in closed form.

* After three steps every high-level state has the shape `D 0 0 L`, and one step is `L ↦ U L`.
* `U` is one sweep from the top of the stack: each entry plus the incoming carry is halved while
  it is even; at the first odd value the sweep stops and deposits on the next two entries. Below
  the last entry the stack behaves as if it held one more entry equal to `-1` (`bottom`).
* `paddedSum L = L[0] + 2 L[1] + 4 L[2] + ... + 2^n` (`n` the length) decides everything about one
  sweep: the sweep visits `padicValNat 2 (paddedSum L) + 1` levels, and the machine stops in this
  sweep if and only if `paddedSum L` is a power of two.

So the machine halts if and only if the orbit of `[2, 2, 0]` under `U` ever reaches a stack whose
padded sum is a power of two (`isHalt_iff_powerOfTwo`). Whether that happens is open: nothing here
decides it.
-/

namespace AntihydraOrbit.Line359

open BusyBeaver
open BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA
  (target HighLevelState highLevelNext highLevelStart)

/-! ### Definitions (the trusted base) -/

/-- What the sweep leaves on the stack below the level where it stops: `d` goes on the next entry
and `1` on the entry after it. A missing entry counts as `-1` followed by a fresh `0`. -/
def deposit (d : ℕ) : List ℕ → List ℕ
  | [] => [d - 1, 0]
  | [x] => [x + d, 0]
  | x :: y :: L => (x + d) :: (y + 1) :: L

/-- The sweep below the last entry, with incoming carry `c`: the stack continues with a virtual
entry `-1`. Carry `0` there is the halting transition. -/
def bottom : ℕ → Option (List ℕ)
  | 0 => none
  | c + 1 =>
    if c % 2 = 0 then (bottom (c / 2)).map (c / 2 :: ·)
    else some [(c - 1) / 2, (c + 1) / 2, 0]

/-- One sweep from the top of the stack with incoming carry `c`. -/
def sweep : ℕ → List ℕ → Option (List ℕ)
  | c, [] => bottom c
  | c, y :: L =>
    if (y + c) % 2 = 0 then (sweep ((y + c) / 2) L).map ((y + c) / 2 :: ·)
    else some ((y + c - 1) / 2 :: deposit ((y + c + 3) / 2) L)

/-- One step of the machine on the stack: a sweep with carry `0`. `none` means the machine halts. -/
def U (L : List ℕ) : Option (List ℕ) := sweep 0 L

/-- The padded weighted sum `L[0] + 2 L[1] + ... + 2^(n-1) L[n-1] + 2^n`. -/
def paddedSum : List ℕ → ℕ
  | [] => 1
  | y :: L => y + 2 * paddedSum L

/-- The number of levels the sweep below the last entry visits. -/
def bottomDepth : ℕ → ℕ
  | 0 => 1
  | c + 1 => if c % 2 = 0 then bottomDepth (c / 2) + 1 else 1

/-- The number of levels a sweep with incoming carry `c` visits. -/
def sweepDepth : ℕ → List ℕ → ℕ
  | c, [] => bottomDepth c
  | c, y :: L => if (y + c) % 2 = 0 then sweepDepth ((y + c) / 2) L + 1 else 1

/-! ### Sanity anchors: the first steps of the orbit -/

example : U [2, 2, 0] = some [1, 1, 3, 0] := by decide
example : U [1, 1, 3, 0] = some [0, 3, 4, 0] := by decide
example : U [0, 0, 9, 2] = some [0, 0, 4, 8, 0] := by decide
example : paddedSum [2, 2, 0] = 14 := by decide
example : sweepDepth 0 [2, 2, 0] = 2 := by decide

/-! ### A. The padded sum -/

/-- The padded sum is the base-2 value of the stack (entries are unrestricted "digits") plus
`2 ^ length`. -/
theorem paddedSum_eq_ofDigits (L : List ℕ) : paddedSum L = Nat.ofDigits 2 L + 2 ^ L.length := by
  induction L with
  | nil => simp [paddedSum]
  | cons y L ih =>
    simp only [paddedSum, ih, Nat.ofDigits_cons, List.length_cons, pow_succ]
    ring

theorem paddedSum_pos (L : List ℕ) : 0 < paddedSum L := by
  rw [paddedSum_eq_ofDigits]
  have : 0 < 2 ^ L.length := by positivity
  omega

/-- Leading zeros only double the padded sum. -/
theorem paddedSum_zero_cons (L : List ℕ) : paddedSum (0 :: L) = 2 * paddedSum L := by
  simp [paddedSum]

/-- Leading zeros pass through the sweep unchanged. -/
theorem U_zero_cons (L : List ℕ) : U (0 :: L) = (U L).map (0 :: ·) := by
  unfold U
  rw [sweep]
  simp

/-! ### B. Halting criterion and depth law for one sweep -/

private theorem exists_two_mul_eq_two_pow_iff (m : ℕ) (hm : 0 < m) :
    (∃ k, 2 * m = 2 ^ k) ↔ ∃ k, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · refine ⟨k, ?_⟩
      rw [pow_succ'] at hk
      omega
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, (pow_succ' 2 k).symm⟩

private theorem not_exists_eq_two_pow_of_odd {n : ℕ} (hodd : n % 2 = 1) (hge : 3 ≤ n) :
    ¬ ∃ k, n = 2 ^ k := by
  rintro ⟨k, rfl⟩
  rcases k with _ | k
  · omega
  · rw [pow_succ'] at hodd
    omega

theorem bottom_eq_none_iff (c : ℕ) : bottom c = none ↔ ∃ k, c + 1 = 2 ^ k := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    rcases c with _ | c
    · rw [bottom]
      simp only [true_iff]
      exact ⟨0, rfl⟩
    · rw [bottom]
      by_cases hev : c % 2 = 0
      · simp only [hev, ↓reduceIte, Option.map_eq_none_iff]
        rw [ih (c / 2) (by omega), show c + 1 + 1 = 2 * (c / 2 + 1) by omega,
          exists_two_mul_eq_two_pow_iff (c / 2 + 1) (by omega)]
      · simp only [hev, ↓reduceIte, reduceCtorEq, false_iff]
        exact not_exists_eq_two_pow_of_odd (by omega) (by omega)

theorem sweep_eq_none_iff (c : ℕ) (L : List ℕ) :
    sweep c L = none ↔ ∃ k, paddedSum L + c = 2 ^ k := by
  induction L generalizing c with
  | nil =>
    rw [sweep, paddedSum, add_comm 1 c]
    exact bottom_eq_none_iff c
  | cons y L ih =>
    rw [sweep, paddedSum]
    have hpos := paddedSum_pos L
    by_cases hev : (y + c) % 2 = 0
    · simp only [hev, ↓reduceIte, Option.map_eq_none_iff]
      rw [ih ((y + c) / 2),
        show y + 2 * paddedSum L + c = 2 * (paddedSum L + (y + c) / 2) by omega,
        exists_two_mul_eq_two_pow_iff (paddedSum L + (y + c) / 2) (by omega)]
    · simp only [hev, ↓reduceIte, reduceCtorEq, false_iff]
      exact not_exists_eq_two_pow_of_odd (by omega) (by omega)

/-- The machine stops in this sweep iff the padded sum is a power of two. -/
theorem U_eq_none_iff (L : List ℕ) : U L = none ↔ ∃ k, paddedSum L = 2 ^ k := by
  unfold U
  simpa using sweep_eq_none_iff 0 L

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem padicValNat_two_mul (m : ℕ) (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
  rw [padicValNat.mul (by omega) hm, padicValNat_self, add_comm]

private theorem bottomDepth_eq (c : ℕ) : bottomDepth c = padicValNat 2 (c + 1) + 1 := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    rcases c with _ | c
    · rw [bottomDepth]
      simp
    · rw [bottomDepth]
      by_cases hev : c % 2 = 0
      · simp only [hev, ↓reduceIte, ih (c / 2) (by omega)]
        rw [show c + 1 + 1 = 2 * (c / 2 + 1) by omega, padicValNat_two_mul (c / 2 + 1) (by omega)]
      · simp only [hev, ↓reduceIte]
        rw [padicValNat.eq_zero_of_not_dvd (by omega)]

theorem sweepDepth_eq (c : ℕ) (L : List ℕ) :
    sweepDepth c L = padicValNat 2 (paddedSum L + c) + 1 := by
  induction L generalizing c with
  | nil =>
    rw [sweepDepth, paddedSum, add_comm 1 c, bottomDepth_eq]
  | cons y L ih =>
    rw [sweepDepth, paddedSum]
    have hpos := paddedSum_pos L
    by_cases hev : (y + c) % 2 = 0
    · simp only [hev, ↓reduceIte, ih ((y + c) / 2)]
      rw [show y + 2 * paddedSum L + c = 2 * (paddedSum L + (y + c) / 2) by omega,
        padicValNat_two_mul (paddedSum L + (y + c) / 2) (by omega)]
    · simp only [hev, ↓reduceIte]
      rw [padicValNat.eq_zero_of_not_dvd (by omega)]

/-- The sweep visits `v₂(paddedSum L) + 1` levels. -/
theorem sweepDepth_zero_eq (L : List ℕ) :
    sweepDepth 0 L = padicValNat 2 (paddedSum L) + 1 := by
  simpa using sweepDepth_eq 0 L

private theorem length_deposit (d : ℕ) (L : List ℕ) : (deposit d L).length = max L.length 2 := by
  rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩ <;> simp [deposit]

private theorem length_of_bottom_eq_some (c : ℕ) :
    ∀ L', bottom c = some L' → L'.length = bottomDepth c + 2 := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    rcases c with _ | c
    · intro L' h
      rw [bottom] at h
      simp at h
    · intro L' h
      rw [bottom] at h
      rw [bottomDepth]
      by_cases hev : c % 2 = 0
      · simp only [hev, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
        obtain ⟨L₁, h₁, rfl⟩ := h
        have hlen := ih (c / 2) (by omega) L₁ h₁
        simp [hlen]
      · simp only [hev, ↓reduceIte, Option.some.injEq] at h ⊢
        subst h
        rfl

private theorem length_of_sweep_eq_some (c : ℕ) (L : List ℕ) :
    ∀ L', sweep c L = some L' → L'.length = max L.length (sweepDepth c L + 2) := by
  induction L generalizing c with
  | nil =>
    intro L' h
    rw [sweep] at h
    rw [sweepDepth]
    have hlen := length_of_bottom_eq_some c L' h
    simp [hlen]
  | cons y L ih =>
    intro L' h
    rw [sweep] at h
    rw [sweepDepth]
    by_cases hev : (y + c) % 2 = 0
    · simp only [hev, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
      obtain ⟨L₁, h₁, rfl⟩ := h
      have hlen := ih ((y + c) / 2) L₁ h₁
      simp only [List.length_cons, hlen]
      omega
    · simp only [hev, ↓reduceIte, Option.some.injEq] at h ⊢
      subst h
      simp only [List.length_cons, length_deposit]
      omega

/-- The stack grows exactly when the sweep reaches one of the last two entries or goes below. -/
theorem length_of_U_eq_some (L L' : List ℕ) (h : U L = some L') :
    L'.length = max L.length (sweepDepth 0 L + 2) :=
  length_of_sweep_eq_some 0 L L' h

/-! ### C. Bridge to the DeepMind acceleration -/

private def toList : HighLevelState → List ℕ
  | .D a b L => a :: b :: L

private theorem toList_injective : Function.Injective toList := by
  rintro ⟨a₁, b₁, L₁⟩ ⟨a₂, b₂, L₂⟩ h
  simp only [toList, List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

private theorem toList_sweepDHL (R : List ℕ) :
    ∀ (a b : ℕ) (L : List ℕ),
      toList (BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.sweepDHL a b L R) =
        R.reverse ++ a :: b :: L := by
  induction R with
  | nil => intro a b L; rfl
  | cons d R ih =>
    intro a b L
    unfold BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.sweepDHL at ih ⊢
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih d a (b :: L)

private theorem deposit_cons (d b : ℕ) (L : List ℕ) :
    deposit d (b :: L) = (b + d) :: Stack.bumpHead L := by
  rcases L with _ | ⟨y, L⟩ <;> rfl

private theorem bottom_succ_eq_sweep (c : ℕ) : bottom (c + 1) = sweep 0 [c] := by
  rw [bottom, sweep]
  simp only [Nat.add_zero]
  by_cases hev : c % 2 = 0
  · simp [hev, sweep]
  · have hdiv : (c + 3) / 2 - 1 = (c + 1) / 2 := by omega
    simp [hev, deposit, hdiv]

private theorem sweep_cons_eq_sweep_zero (c y : ℕ) (L : List ℕ) :
    sweep c (y :: L) = sweep 0 ((y + c) :: L) := by
  conv_lhs => rw [sweep]
  conv_rhs => rw [sweep]
  simp

private theorem map_toList_runE_nil (a : ℕ) :
    ∀ (r₀ : ℕ) (R' : List ℕ),
      (BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE a [] r₀ R').map toList =
        (sweep 0 [a]).map ((r₀ :: R').reverse ++ ·) := by
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro r₀ R'
    rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    simp only [↓reduceIte]
    rcases a with _ | _ | a₂
    · simp [← bottom_succ_eq_sweep, bottom]
    · simp [toList_sweepDHL, ← bottom_succ_eq_sweep, bottom]
    · simp only [Nat.add_eq_zero_iff, and_false, ↓reduceIte, Nat.reduceEqDiff]
      rw [show a₂ + 2 - 2 = a₂ by omega]
      by_cases hodd : a₂ % 2 = 1
      · have hnev : ¬ a₂ % 2 = 0 := by omega
        have h1 : (a₂ + 1) / 2 = a₂ / 2 + 1 := by omega
        have h2 : (a₂ + 2 + 0 + 3) / 2 - 1 = a₂ / 2 + 2 := by omega
        have hs : sweep 0 [a₂ + 2] = some [a₂ / 2 + 1, a₂ / 2 + 2, 0] := by
          rw [sweep]
          simp [hnev, deposit, h1, h2]
        simp [hodd, toList_sweepDHL, hs]
      · have hev : (a₂ + 2 + 0) % 2 = 0 := by omega
        have h1 : (a₂ + 2 + 0) / 2 = a₂ / 2 + 1 := by omega
        have hs : sweep 0 [a₂ + 2] = (sweep 0 [a₂ / 2]).map ((a₂ / 2 + 1) :: ·) := by
          rw [sweep]
          simp only [hev, ↓reduceIte, h1]
          rw [show sweep (a₂ / 2 + 1) [] = bottom (a₂ / 2 + 1) from rfl, bottom_succ_eq_sweep]
        simp only [hodd, ↓reduceIte]
        rw [iha (a₂ / 2) (by omega) (a₂ / 2 + 1) (r₀ :: R'), hs]
        simp [Option.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]

private theorem map_toList_runE (L : List ℕ) :
    ∀ (a r₀ : ℕ) (R' : List ℕ),
      (BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE a L r₀ R').map toList =
        (sweep 0 (a :: L)).map ((r₀ :: R').reverse ++ ·) := by
  induction L with
  | nil => exact map_toList_runE_nil
  | cons b L' ihL =>
    intro a r₀ R'
    rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
    rcases a with _ | _ | a₂
    · simp only [↓reduceIte, ihL b 0 (r₀ :: R')]
      conv_rhs => rw [sweep]
      simp [Option.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]
    · simp only [↓reduceIte, Nat.reduceEqDiff, Option.map_some, toList_sweepDHL]
      rw [sweep]
      simp [deposit_cons]
    · simp only [Nat.add_eq_zero_iff, and_false, ↓reduceIte, Nat.reduceEqDiff]
      rw [show a₂ + 2 - 2 = a₂ by omega]
      by_cases hodd : a₂ % 2 = 1
      · have hnev : ¬ a₂ % 2 = 0 := by omega
        have h1 : (a₂ + 1) / 2 = a₂ / 2 + 1 := by omega
        have h2 : b + (a₂ + 2 + 0 + 3) / 2 = b + 1 + a₂ / 2 + 2 := by omega
        have hs : sweep 0 ((a₂ + 2) :: b :: L') =
            some ((a₂ / 2 + 1) :: (b + 1 + a₂ / 2 + 2) :: Stack.bumpHead L') := by
          rw [sweep]
          simp [hnev, deposit_cons, h1, h2]
        simp [hodd, toList_sweepDHL, hs]
      · have hev : (a₂ + 2 + 0) % 2 = 0 := by omega
        have h1 : (a₂ + 2 + 0) / 2 = a₂ / 2 + 1 := by omega
        have h2 : b + (a₂ / 2 + 1) = b + 1 + a₂ / 2 := by omega
        have hs : sweep 0 ((a₂ + 2) :: b :: L') =
            (sweep 0 ((b + 1 + a₂ / 2) :: L')).map ((a₂ / 2 + 1) :: ·) := by
          rw [sweep]
          simp only [hev, ↓reduceIte, h1]
          rw [sweep_cons_eq_sweep_zero, h2]
        simp [hodd, ihL (b + 1 + a₂ / 2) (a₂ / 2 + 1) (r₀ :: R'), hs,
          Option.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]

/-- On states `D 0 0 L` one high-level step is one sweep. -/
theorem highLevelNext_D_zero_zero (L : List ℕ) :
    highLevelNext (.D 0 0 L) = (U L).map (HighLevelState.D 0 0) := by
  apply Option.map_injective toList_injective
  rw [highLevelNext]
  simp only [Nat.zero_mod, Nat.reduceEqDiff, ↓reduceIte, Nat.zero_div, Nat.add_zero]
  rcases L with _ | ⟨y, L'⟩
  · rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    simp [U, sweep, bottom]
  · rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
    rw [map_toList_runE L' y 0 [0]]
    simp [U, Option.map_map, Function.comp_def, toList]

/-- The third high-level state is `D 0 0 [2, 2, 0]`. -/
theorem highLevel_iterate_three :
    (Option.bind · highLevelNext)^[3] (some highLevelStart) = some (.D 0 0 [2, 2, 0]) := by
  have h1 : highLevelNext highLevelStart = some (.D 0 2 [0]) := rfl
  have h2 : highLevelNext (.D 0 2 [0]) = some (.D 0 1 [0, 1, 0]) := by
    rw [highLevelNext]
    simp only [Nat.zero_mod, Nat.reduceEqDiff, ↓reduceIte, Nat.zero_div, Nat.add_zero]
    rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons, Nat.reduceEqDiff,
      Nat.sub_self, Nat.zero_div, Nat.zero_mod, Nat.add_zero]
    rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    rfl
  have h3 : highLevelNext (.D 0 1 [0, 1, 0]) = some (.D 0 0 [2, 2, 0]) := by
    rw [highLevelNext]
    simp only [Nat.zero_mod, Nat.reduceEqDiff, ↓reduceIte, Nat.zero_div, Nat.add_zero]
    rw [BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.runE]
    rfl
  simp [Function.iterate_succ_apply, h1, h2, h3]

theorem is_valid_U_acceleration :
    IsValidAcceleration target [2, 2, 0]
      (fun L =>
        BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.highLevelEncode (.D 0 0 L))
      U :=
  BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.is_valid_highLevel_acceleration.of_collatz
    (embed := HighLevelState.D 0 0)
    ⟨3, highLevel_iterate_three⟩
    (fun L => CollatzStepsTo.of_eq (highLevelNext_D_zero_zero L))

theorem collatzHalts_highLevel_iff :
    CollatzHalts highLevelNext highLevelStart ↔ CollatzHalts U [2, 2, 0] := by
  have h1 :=
    BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.is_valid_highLevel_acceleration
  exact h1.collatzHalts_iff is_valid_U_acceleration

/-- The machine halts from the blank tape iff the sweep map halts from `[2, 2, 0]`. -/
theorem isHalt_iff_collatzHalts_U : IsHalt target ↔ CollatzHalts U [2, 2, 0] :=
  is_valid_U_acceleration.isHalt_iff

/-! ### D. The halting condition in closed form -/

theorem collatzHalts_U_iff (L₀ : List ℕ) :
    CollatzHalts U L₀ ↔
      ∃ t L, (Option.bind · U)^[t] (some L₀) = some L ∧ ∃ k, paddedSum L = 2 ^ k := by
  constructor
  · rintro ⟨n, hn⟩
    induction n with
    | zero => simp at hn
    | succ n ih =>
      rw [Function.iterate_succ_apply'] at hn
      rcases ht : (Option.bind · U)^[n] (some L₀) with _ | L
      · exact ih (by simp [ht])
      · rw [ht, Option.bind_some, Option.isNone_iff_eq_none] at hn
        exact ⟨n, L, ht, (U_eq_none_iff L).1 hn⟩
  · rintro ⟨t, L, ht, hk⟩
    refine ⟨t + 1, ?_⟩
    rw [Function.iterate_succ_apply', ht, Option.bind_some, Option.isNone_iff_eq_none]
    exact (U_eq_none_iff L).2 hk

/-- The machine halts from the blank tape iff the orbit of `[2, 2, 0]` under the sweep map reaches
a stack whose padded sum is a power of two. -/
theorem isHalt_iff_powerOfTwo :
    IsHalt target ↔
      ∃ t L, (Option.bind · U)^[t] (some [2, 2, 0]) = some L ∧ ∃ k, paddedSum L = 2 ^ k :=
  isHalt_iff_collatzHalts_U.trans (collatzHalts_U_iff [2, 2, 0])

end AntihydraOrbit.Line359
