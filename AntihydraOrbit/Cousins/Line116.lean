import Mathlib
import BusyBeaver.BB6.Accelerations.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

/-!
# The machine `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`: single-sum sweep and chain laws

The DeepMind `cryptids` library proves that this machine halts if and only if its high-level
acceleration `highLevelNext` halts from `highLevelStart`. This file formalizes the single-sum
sweep law, the 2-adic halving chain law, and the orbit phase
invariant linking them to `IsHalt target`:

* At any bottom reach `F 0 2 (ones k ++ u) 1 []` where every entry of `u` is odd, the unrolled
  carry sum `W u = 1 + ∑ 2^i u_i` governs the sweep in closed form: the sweep stops inside `u`
  when `v₂(W u) + 1 < |u|`, empties `u` with an even register when `v₂(W u) + 1 = |u|`, and
  empties `u` into a halving chain of value `(2 * paddedW u) / 2^|u|` when `|u| ≤ v₂(W u)`.
* A halving chain of even value `V ≥ 4` halts inside the chain if and only if `V` is a power of
  two, and otherwise exits at `.F q 0 [] 0 ...` where `q` is the odd part of `V`.
* From high-level step `27` onward, every reachable state satisfies the inductive phase invariant
  `OrbitInv`, so every reachable bottom reach `F 0 2 L 1 []` has all odd entries and either halts
  (when `paddedW L` is a power of two) or steps to a next all-odd bottom reach.

Consequently, the machine halts from the blank tape if and only if its high-level orbit ever
reaches a bottom reach `F 0 2 L 1 []` whose padded sum `W L + 2^|L|` is a power of two
(`isHalt_iff_bottomReach_powerOfTwo`). Whether that happens is open: nothing here decides it.
-/

namespace AntihydraOrbit.Line116

open BusyBeaver
open BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA
  (target HighLevelState highLevelNext highLevelStart)

/-! ### Definitions (the trusted base) -/

/-- Every entry of the stack is odd. -/
def AllOdd (u : List ℕ) : Prop := ∀ x ∈ u, x % 2 = 1

instance (u : List ℕ) : Decidable (AllOdd u) := by
  unfold AllOdd; infer_instance

/-- A run of `k` leading `1`s at the top of the stack. -/
def ones (k : ℕ) : List ℕ := List.replicate k 1

/-- Binary-weighted stack sum `∑_{i=0}^{m-1} 2^i u_i`. -/
def weightedSum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 * weightedSum xs

/-- Unpadded single-sum `W(u) = 1 + ∑_{i=0}^{m-1} 2^i u_i`. -/
def W (u : List ℕ) : ℕ := 1 + weightedSum u

/-- Padded single-sum `W̃(u) = W(u) + 2^|u| = 1 + ∑_{i=0}^{m-1} 2^i u_i + 2^|u|`. -/
def paddedW (u : List ℕ) : ℕ := W u + 2 ^ u.length

/-- Entries pushed onto `R` (top first) during `d` odd-register pops of `u`:
`[W(u.take (d - 1)) / 2^(d - 1), ..., W(u.take 0) / 2^0]`. -/
def sweepPushes (u : List ℕ) : ℕ → List ℕ
  | 0 => []
  | d + 1 => (W (u.take d) / 2 ^ d) :: sweepPushes u d

/-- Right stack `R` after sweeping `k` leading `1`s and `d` odd-register pops of `u`. -/
def sweepR (k : ℕ) (u : List ℕ) (d : ℕ) : List ℕ :=
  sweepPushes u d ++ ones k ++ [0]

/-- Number of `highLevelNext` steps from `F 0 2 (ones k ++ u) 1 []` to depth `d` in `u`. -/
def sweepSteps (u : List ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => sweepSteps u d + (W (u.take d) / 2 ^ d - 1)

/-- Entry outcome of a halving chain of even value `V ≥ 4` (`V = a_CR + 3`) with right stack `R`:
`none` at the single-gate halt `V = 4`, and `some (.F (V - 5) 0 [] 0 (0 :: 1 :: R))` for `V ≥ 6`. -/
def chainEntry (V : ℕ) (R : List ℕ) : Option HighLevelState :=
  if V ≤ 4 then none else some (.F (V - 5) 0 [] 0 (0 :: 1 :: R))

/-- Right stack `R` on exiting a non-halting chain of `2^ν * q` (`q ≥ 3` odd), pushing
`2^(ν - 1) * q - 1, ..., q - 1` onto `R` so `q - 1` sits at the top of `R`. -/
def chainR : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, R => R
  | t + 1, q, R => chainR t q ((2 ^ t * q - 1) :: R)

/-- Number of `highLevelNext` steps spent inside a halving chain of even value `V ≥ 4`. -/
def chainSteps (V : ℕ) : ℕ :=
  let ν := padicValNat 2 V
  let q := V / 2 ^ ν
  if q = 1 then V - 2 * ν else V - q - 2 * ν

/-- Right-stack tail shape `(odd entries) ++ [1, 0]` maintained between bottom reaches. -/
def EndsWithOdds10 (R : List ℕ) : Prop :=
  ∃ R_odds, R = R_odds ++ [1, 0] ∧ AllOdd R_odds

/-- Inductive phase invariant holding on every high-level state of the orbit from step `27` on. -/
def OrbitInv : HighLevelState → Prop
  | .F a b L r R =>
    (a = 0 ∧ b = 2 ∧ r = 1 ∧ R = [] ∧ AllOdd L) ∨
    (a = 0 ∧ b = 1 ∧ r = 0 ∧ R = [] ∧ AllOdd L) ∨
    (a = 1 ∧ b = 1 ∧ r = 0 ∧ R = [0] ∧ AllOdd L) ∨
    (a % 2 = 1 ∧ 2 ≤ b ∧ AllOdd L ∧ r = 0 ∧
      ∃ e R', (b + e) % 2 = 1 ∧ R = 0 :: e :: R' ∧ EndsWithOdds10 R') ∨
    (a % 2 = 1 ∧ L = [] ∧ r = 0 ∧
      ∃ R', R = 0 :: (b + 1) :: R' ∧ EndsWithOdds10 R') ∨
    (a % 2 = 1 ∧ b % 2 = 0 ∧ AllOdd L ∧ r = 0 ∧
      ∃ d R', 2 ≤ d ∧ d % 2 = 0 ∧ R = d :: R' ∧ EndsWithOdds10 R') ∨
    (a = 0 ∧ b % 2 = 1 ∧ AllOdd L ∧ r % 2 = 1 ∧ EndsWithOdds10 R) ∨
    (a = 0 ∧ b % 2 = 1 ∧ AllOdd L ∧ r = 1 ∧ R = [0])

/-! ### Concrete sanity anchors covering each sweep and chain case -/

-- Case 1 (the sweep stops inside the stack): k = 1, u = [3, 1, 3], W u = 18, v₂(W u) = 1 < 2
example : AllOdd [3, 1, 3] := by decide
example : W [3, 1, 3] = 18 ∧ sweepSteps [3, 1, 3] 2 = 2 := by decide
example :
    (Option.bind · highLevelNext)^[2] (some (.F 0 2 (ones 1 ++ [3, 1, 3]) 1 [])) =
      some (.F 5 4 [] 0 [2, 1, 1, 0]) := by decide

-- Case 2 (the sweep empties the stack with an even register): k = 1, u = [3, 3], W u = 10, v₂ = 1
example : AllOdd [3, 3] := by decide
example : W [3, 3] = 10 ∧ sweepSteps [3, 3] 2 = 2 := by decide
example :
    (Option.bind · highLevelNext)^[2] (some (.F 0 2 (ones 1 ++ [3, 3]) 1 [])) =
      some (.F 7 0 [] 0 [2, 1, 1, 0]) := by decide

-- Case 3a (single-gate halt V = 4): k = 0, u = [1], W u = 2, paddedW u = 4
example :
    (Option.bind · highLevelNext)^[1] (some (.F 0 2 (ones 0 ++ [1]) 1 [])) = none := by decide

-- Case 3b (multi-gate halting chain V = 8): k = 1, u = [5, 3], paddedW u = 16
example :
    (Option.bind · highLevelNext)^[3] (some (.F 0 2 (ones 1 ++ [5, 3]) 1 [])) =
      some (.F 3 0 [] 0 [0, 1, 3, 1, 1, 0]) := by decide
example :
    (Option.bind · highLevelNext)^[5] (some (.F 0 2 (ones 1 ++ [5, 3]) 1 [])) = none := by decide

-- Case 3c (non-halting chain V = 12 = 2^2 * 3): k = 0, u = [9, 5], paddedW u = 24
example :
    (Option.bind · highLevelNext)^[5] (some (.F 0 2 (ones 0 ++ [9, 5]) 1 [])) =
      some (.F 7 0 [] 0 [0, 1, 5, 1, 0]) := by decide
example :
    (Option.bind · highLevelNext)^[10] (some (.F 0 2 (ones 0 ++ [9, 5]) 1 [])) =
      some (.F 3 0 [] 0 [2, 5, 5, 1, 0]) := by decide

/-! ### A. Leading `1`s decoupling and single-sum sweep law (no orbit hypothesis) -/

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA (exitC)

theorem exitC_succ (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    exitC (a + 1) b L r R = some (.F a b L 0 (r :: R)) := by
  rcases L with _ | ⟨c, L'⟩ <;> rfl

theorem exitC_zero_nil (b r : ℕ) (R : List ℕ) :
    exitC 0 (b + 1) [] r R =
      if b % 2 = 0 then some (.F (b + 3) 0 [] r R)
      else if b = 1 then none
      else some (.F (2 * (b / 2) - 1) 0 [] 0 (0 :: (r + 1) :: R)) := rfl

theorem exitC_zero_cons (b c : ℕ) (L' : List ℕ) (r : ℕ) (R : List ℕ) :
    exitC 0 (b + 1) (c :: L') r R =
      if b % 2 = 0 then some (.F (b + 3) (c + 1) L' r R)
      else if b = 1 then exitC 0 (c + 1) L' 0 ((r + 1) :: R)
      else some (.F (2 * (b / 2) - 1) (c + 1) L' 0 (0 :: (r + 1) :: R)) := rfl

private def it (n : ℕ) (o : Option HighLevelState) : Option HighLevelState :=
  (Option.bind · highLevelNext)^[n] o

private theorem it_zero (o : Option HighLevelState) : it 0 o = o := rfl

private theorem it_succ_front (n : ℕ) (o : Option HighLevelState) :
    it (n + 1) o = it n (o.bind highLevelNext) :=
  Function.iterate_succ_apply _ n o

private theorem it_add (m n : ℕ) (o : Option HighLevelState) :
    it (m + n) o = it n (it m o) := by
  unfold it
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem it_none (n : ℕ) : it n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [it_succ_front]; exact ih

private theorem W_pos (u : List ℕ) : 0 < W u := by
  unfold W; omega

private theorem paddedW_pos (u : List ℕ) : 0 < paddedW u := by
  have := W_pos u
  have : 0 < 2 ^ u.length := by positivity
  unfold paddedW
  omega

private theorem weightedSum_append (xs ys : List ℕ) :
    weightedSum (xs ++ ys) = weightedSum xs + 2 ^ xs.length * weightedSum ys := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih =>
    simp only [List.cons_append, weightedSum, ih, List.length_cons, pow_succ]
    ring

private theorem W_append (xs ys : List ℕ) :
    W (xs ++ ys) = W xs + 2 ^ xs.length * weightedSum ys := by
  simp only [W, weightedSum_append]
  omega

private theorem W_one_cons (u : List ℕ) : W (1 :: u) = 2 * W u := by
  simp only [W, weightedSum]
  omega

/-- Prepending `k` leading `1`s multiplies the unpadded sum `W` by `2^k`. -/
theorem W_ones_append (k : ℕ) (u : List ℕ) : W (ones k ++ u) = 2 ^ k * W u := by
  induction k with
  | zero => simp [ones]
  | succ k ih =>
    simp only [ones, List.replicate_succ, List.cons_append, W_one_cons]
    rw [show List.replicate k 1 = ones k from rfl, ih, pow_succ']
    ring

/-- Prepending `k` leading `1`s multiplies the padded sum `paddedW` by `2^k`. -/
theorem paddedW_ones_append (k : ℕ) (u : List ℕ) :
    paddedW (ones k ++ u) = 2 ^ k * paddedW u := by
  unfold paddedW
  rw [W_ones_append, List.length_append, ones, List.length_replicate, pow_add]
  ring

private theorem list_take_succ_eq_append (u : List ℕ) (d : ℕ) (hd : d < u.length) :
    u.take (d + 1) = u.take d ++ [u[d]'hd] := by
  induction u generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    rcases d with _ | d
    · rfl
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hd
      change x :: xs.take (d + 1) = x :: (xs.take d ++ [xs[d]'hd])
      rw [ih d hd]

private theorem list_drop_eq_cons (u : List ℕ) (d : ℕ) (hd : d < u.length) :
    u.drop d = (u[d]'hd) :: u.drop (d + 1) := by
  induction u generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    rcases d with _ | d
    · rfl
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hd
      change xs.drop d = xs[d]'hd :: xs.drop (d + 1)
      exact ih d hd

private theorem two_pow_dvd_W_take (u : List ℕ) (j : ℕ) (hj : j ≤ padicValNat 2 (W u)) :
    2 ^ j ∣ W (u.take j) := by
  have hdvdW : 2 ^ j ∣ W u :=
    (padicValNat_dvd_iff_le (by have := W_pos u; omega)).mpr hj
  by_cases hlen : j ≤ u.length
  · have hsplit : W u = W (u.take j) + 2 ^ j * weightedSum (u.drop j) := by
      conv_lhs => rw [← List.take_append_drop j u, W_append]
      rw [List.length_take_of_le hlen]
    have hmul : 2 ^ j ∣ 2 ^ j * weightedSum (u.drop j) := dvd_mul_right _ _
    exact (Nat.dvd_add_iff_left hmul).mpr (hsplit ▸ hdvdW)
  · rw [List.take_of_length_le (by omega)]
    exact hdvdW

private theorem W_take_div_odd (u : List ℕ) (h : padicValNat 2 (W u) < u.length) :
    let ν := padicValNat 2 (W u)
    2 ^ ν ∣ W (u.take (ν + 1)) ∧ (W (u.take (ν + 1)) / 2 ^ ν) % 2 = 1 := by
  intro ν
  have hlen : ν + 1 ≤ u.length := by omega
  have hsplit : W u = W (u.take (ν + 1)) + 2 ^ (ν + 1) * weightedSum (u.drop (ν + 1)) := by
    conv_lhs => rw [← List.take_append_drop (ν + 1) u, W_append]
    rw [List.length_take_of_le hlen]
  have hdvdW : 2 ^ ν ∣ W u := pow_padicValNat_dvd
  have hndvdW : ¬ 2 ^ (ν + 1) ∣ W u :=
    pow_succ_padicValNat_not_dvd (by have := W_pos u; omega)
  have hmul_ν : 2 ^ ν ∣ 2 ^ (ν + 1) * weightedSum (u.drop (ν + 1)) := by
    rw [pow_succ]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hdvd_take : 2 ^ ν ∣ W (u.take (ν + 1)) :=
    (Nat.dvd_add_iff_left hmul_ν).mpr (hsplit ▸ hdvdW)
  refine ⟨hdvd_take, ?_⟩
  set q := W (u.take (ν + 1)) / 2 ^ ν
  have hq_eq : W (u.take (ν + 1)) = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd_take).symm
  by_contra hnotodd
  obtain ⟨r, hr⟩ : ∃ r, q = 2 * r := ⟨q / 2, by omega⟩
  have hdvd_take_succ : 2 ^ (ν + 1) ∣ W (u.take (ν + 1)) := by
    refine ⟨r, ?_⟩
    rw [hq_eq, hr, pow_succ]
    ring
  exact hndvdW (hsplit ▸ dvd_add hdvd_take_succ (dvd_mul_right _ _))

private theorem it_shift_loop (k b e : ℕ) (L R : List ℕ) :
    it (k + 1) (some (.F (2 * k + 1) b L 0 (0 :: e :: R))) =
      exitC 0 (b + k + 1) L 0 ((e + k + 1) :: R) := by
  induction k generalizing b e with
  | zero =>
    rw [it_succ_front, it_zero]
    simp [highLevelNext]
  | succ k ih =>
    have hstep :
        highLevelNext (.F (2 * (k + 1) + 1) b L 0 (0 :: e :: R)) =
          some (.F (2 * k + 1) (b + 1) L 0 (0 :: (e + 1) :: R)) := by
      have hodd : ¬ (2 * (k + 1) + 1) % 2 = 0 := by omega
      have hdiv : 2 * ((2 * (k + 1) + 1) / 2) = (2 * k + 1) + 1 := by omega
      rw [highLevelNext]
      simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero, hodd, hdiv]
      exact exitC_succ (2 * k + 1) (b + 1) L 0 ((e + 1) :: R)
    rw [it_succ_front, Option.bind_some, hstep, ih (b + 1) (e + 1)]
    congr 2 <;> omega

private theorem odd_pop_step (m c : ℕ) (L R : List ℕ) :
    it m (exitC 0 (2 * m + 2) (c :: L) 0 R) = exitC 0 (c + m + 1) L 0 ((m + 1) :: R) := by
  rcases m with _ | k
  · rfl
  · have hexit :
        exitC 0 (2 * (k + 1) + 2) (c :: L) 0 R =
          some (.F (2 * k + 1) (c + 1) L 0 (0 :: 1 :: R)) := by
      have h2 : ¬ (2 * k + 3) % 2 = 0 := by omega
      have h3 : 2 * k + 3 ≠ 1 := by omega
      have h4 : 2 * ((2 * k + 3) / 2) - 1 = 2 * k + 1 := by omega
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega, exitC_zero_cons]
      simp only [h2, h3, ↓reduceIte, h4, Nat.zero_add]
    rw [hexit, it_shift_loop]
    congr 2 <;> omega

private theorem exitC_ones_append (k : ℕ) (L R : List ℕ) :
    exitC 0 2 (ones k ++ L) 0 R = exitC 0 2 L 0 (ones k ++ R) := by
  induction k generalizing R with
  | zero => simp [ones]
  | succ k ih =>
    have hcons : (ones (k + 1) ++ L) = 1 :: (ones k ++ L) := by
      simp [ones, List.replicate_succ]
    have hstep : exitC 0 2 (1 :: (ones k ++ L)) 0 R = exitC 0 2 (ones k ++ L) 0 (1 :: R) := rfl
    have hr : ones k ++ 1 :: R = ones (k + 1) ++ R := by
      simp [ones, List.replicate_succ']
    rw [hcons, hstep, ih (1 :: R), hr]

private theorem sweep_unroll (k : ℕ) (u : List ℕ) (d : ℕ) (hd : d ≤ u.length)
    (hdvd : ∀ j < d, 2 ^ j ∣ W (u.take j)) :
    it (sweepSteps u d) (some (.F 0 2 (ones k ++ u) 1 [])) =
      exitC 0 ((2 * W (u.take d)) / 2 ^ d) (u.drop d) 0 (sweepR k u d) := by
  induction d with
  | zero =>
    rw [sweepSteps, it_succ_front, it_zero]
    have h0 : highLevelNext (.F 0 2 (ones k ++ u) 1 []) = exitC 0 2 (ones k ++ u) 0 [0] := rfl
    simp [h0, exitC_ones_append, W, weightedSum, sweepR, sweepPushes]
  | succ d ih =>
    have hd_lt : d < u.length := by omega
    have hih := ih (by omega) (fun j hj => hdvd j (by omega))
    obtain ⟨q, hq⟩ := hdvd d (by omega)
    have hq_pos : 0 < q := by
      have hpos := W_pos (u.take d)
      rcases q with _ | q'
      · simp [hq] at hpos
      · omega
    set m := q - 1
    have hq_m : q = m + 1 := by omega
    have hW_d : W (u.take d) = 2 ^ d * (m + 1) := by rw [hq, hq_m]
    have hpow_pos : 0 < 2 ^ d := by positivity
    have hdiv1 : W (u.take d) / 2 ^ d = m + 1 := by
      rw [hW_d, Nat.mul_div_cancel_left _ hpow_pos]
    have hdiv2 : (2 * W (u.take d)) / 2 ^ d = 2 * m + 2 := by
      rw [show 2 * W (u.take d) = 2 ^ d * (2 * m + 2) by rw [hW_d]; ring,
        Nat.mul_div_cancel_left _ hpow_pos]
    have hW_succ : (2 * W (u.take (d + 1))) / 2 ^ (d + 1) = (u[d]'hd_lt) + m + 1 := by
      have htake := list_take_succ_eq_append u d hd_lt
      have hlen : (u.take d).length = d := List.length_take_of_le (by omega)
      have hWs : W (u.take (d + 1)) = 2 ^ d * ((u[d]'hd_lt) + m + 1) := by
        rw [htake, W_append, hlen, hW_d]
        simp only [weightedSum]
        ring
      have hp2 : 0 < 2 ^ (d + 1) := by positivity
      rw [show 2 * W (u.take (d + 1)) = 2 ^ (d + 1) * ((u[d]'hd_lt) + m + 1) by
        rw [hWs, pow_succ]; ring, Nat.mul_div_cancel_left _ hp2]
    rw [sweepSteps, hdiv1, show m + 1 - 1 = m by omega, it_add, hih, hdiv2,
      list_drop_eq_cons u d hd_lt, odd_pop_step, hW_succ]
    simp [sweepR, sweepPushes, hdiv1]

/-- Sweep law, case 1 (`v₂(W u) + 1 < |u|`): the sweep stops inside `u` at index
`d = v₂(W u) + 1` with terminal even register `W(u.take d) / 2^(d - 1) - 1`. -/
theorem sweep_stops_inside (k : ℕ) (u : List ℕ) (hu : AllOdd u)
    (h : padicValNat 2 (W u) + 1 < u.length) :
    let d := padicValNat 2 (W u) + 1
    (Option.bind · highLevelNext)^[sweepSteps u d] (some (.F 0 2 (ones k ++ u) 1 [])) =
      some (.F (W (u.take d) / 2 ^ (d - 1) + 2) (u[d]'h + 1) (u.drop (d + 1)) 0
        (sweepR k u d)) := by
  let _ := hu
  intro d
  have hunroll := sweep_unroll k u d (by omega)
    (fun j hj => two_pow_dvd_W_take u j (by omega))
  obtain ⟨hdvd, hodd⟩ := W_take_div_odd u (by omega)
  set ν := padicValNat 2 (W u)
  have hd_eq : d = ν + 1 := rfl
  set q := W (u.take d) / 2 ^ ν
  have hW_eq : W (u.take d) = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hq_pos : 0 < q := by
    have hpos := W_pos (u.take d)
    rcases q with _ | q'
    · simp [hW_eq] at hpos
    · omega
  have hdiv : (2 * W (u.take d)) / 2 ^ d = q := by
    have hp : 0 < 2 ^ d := by positivity
    have hmul : 2 * W (u.take d) = 2 ^ d * q := by
      calc 2 * W (u.take d) = 2 * (2 ^ ν * q) := by rw [hW_eq]
        _ = 2 ^ (ν + 1) * q := by rw [pow_succ]; ring
        _ = 2 ^ d * q := rfl
    rw [hmul, Nat.mul_div_cancel_left _ hp]
  change it (sweepSteps u d) (some (.F 0 2 (ones k ++ u) 1 [])) = _
  rw [hunroll, hdiv, list_drop_eq_cons u d h, show q = (q - 1) + 1 by omega, exitC_zero_cons]
  have hev : (q - 1) % 2 = 0 := by omega
  simp only [hev, ↓reduceIte]
  congr 2
  rw [show d - 1 = ν by omega]
  change q - 1 + 3 = q + 2
  omega

/-- Sweep law, case 2 (`v₂(W u) + 1 = |u|`): the sweep empties the stack with even register
`W(u) / 2^(|u| - 1) - 1` and exits via `(C3)` without entering a gate chain. -/
theorem sweep_empties_even (k : ℕ) (u : List ℕ) (hu : AllOdd u)
    (h : padicValNat 2 (W u) + 1 = u.length) :
    (Option.bind · highLevelNext)^[sweepSteps u u.length]
        (some (.F 0 2 (ones k ++ u) 1 [])) =
      some (.F (W u / 2 ^ (u.length - 1) + 2) 0 [] 0 (sweepR k u u.length)) := by
  let _ := hu
  have hunroll := sweep_unroll k u u.length (le_refl _)
    (fun j hj => two_pow_dvd_W_take u j (by omega))
  obtain ⟨hdvd, hodd⟩ := W_take_div_odd u (by omega)
  set ν := padicValNat 2 (W u)
  have hlen_take : u.take (ν + 1) = u := by rw [h, List.take_length]
  rw [hlen_take] at hdvd hodd
  set q := W u / 2 ^ ν
  have hW_eq : W u = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hq_pos : 0 < q := by
    have hpos := W_pos u
    rcases q with _ | q'
    · simp [hW_eq] at hpos
    · omega
  have hdiv : (2 * W u) / 2 ^ u.length = q := by
    have hp : 0 < 2 ^ u.length := by positivity
    have hmul : 2 * W u = 2 ^ u.length * q := by
      calc 2 * W u = 2 * (2 ^ ν * q) := by rw [hW_eq]
        _ = 2 ^ (ν + 1) * q := by rw [pow_succ]; ring
        _ = 2 ^ u.length * q := by rw [h]
    rw [hmul, Nat.mul_div_cancel_left _ hp]
  change it (sweepSteps u u.length) (some (.F 0 2 (ones k ++ u) 1 [])) = _
  rw [hunroll, List.take_length, List.drop_length, hdiv, show q = (q - 1) + 1 by omega,
    exitC_zero_nil]
  have hev : (q - 1) % 2 = 0 := by omega
  simp only [hev, ↓reduceIte]
  congr 2
  rw [show u.length - 1 = ν by omega]
  change q - 1 + 3 = q + 2
  omega

theorem exitC_empty_even_eq_chainEntry (V : ℕ) (R : List ℕ) (hV : 4 ≤ V)
    (hev : V % 2 = 0) :
    exitC 0 (V - 2) [] 0 R = chainEntry V R := by
  by_cases h4 : V ≤ 4
  · have hV4 : V = 4 := by omega
    subst hV4
    rfl
  · have h2 : ¬ (V - 3) % 2 = 0 := by omega
    have h3 : V - 3 ≠ 1 := by omega
    have h5 : 2 * ((V - 3) / 2) - 1 = V - 5 := by omega
    unfold chainEntry
    rw [show V - 2 = (V - 3) + 1 by omega, exitC_zero_nil]
    simp only [h2, h3, h4, ↓reduceIte, h5, Nat.zero_add]

/-- Sweep law, case 3 (`|u| ≤ v₂(W u)`): the sweep empties the stack with an odd register and
enters a halving chain of even value `V = (2 * paddedW u) / 2^|u|` (`= paddedW u / 2^(|u| - 1)`
whenever `u ≠ []`). -/
theorem sweep_starts_chain (k : ℕ) (u : List ℕ) (hu : AllOdd u)
    (h : u.length ≤ padicValNat 2 (W u)) :
    (Option.bind · highLevelNext)^[sweepSteps u u.length]
        (some (.F 0 2 (ones k ++ u) 1 [])) =
      chainEntry ((2 * paddedW u) / 2 ^ u.length) (sweepR k u u.length) := by
  let _ := hu
  have hunroll := sweep_unroll k u u.length (le_refl _)
    (fun j hj => two_pow_dvd_W_take u j (by omega))
  have hdvd : 2 ^ u.length ∣ W u :=
    (padicValNat_dvd_iff_le (by have := W_pos u; omega)).mpr h
  obtain ⟨q, hq⟩ := hdvd
  have hq_pos : 0 < q := by
    have hpos := W_pos u
    rcases q with _ | q'
    · simp [hq] at hpos
    · omega
  have hp : 0 < 2 ^ u.length := by positivity
  have hdivW : (2 * W u) / 2 ^ u.length = 2 * q := by
    rw [show 2 * W u = 2 ^ u.length * (2 * q) by rw [hq]; ring,
      Nat.mul_div_cancel_left _ hp]
  have hdivP : (2 * paddedW u) / 2 ^ u.length = 2 * q + 2 := by
    rw [show 2 * paddedW u = 2 ^ u.length * (2 * q + 2) by unfold paddedW; rw [hq]; ring,
      Nat.mul_div_cancel_left _ hp]
  change it (sweepSteps u u.length) (some (.F 0 2 (ones k ++ u) 1 [])) = _
  rw [hunroll, List.take_length, List.drop_length, hdivW, hdivP,
    show 2 * q = (2 * q + 2) - 2 by omega]
  exact exitC_empty_even_eq_chainEntry (2 * q + 2) (sweepR k u u.length) (by omega) (by omega)

/-! ### B. 2-adic halving chain law -/

private theorem two_mul_lt_two_pow_add_three (t : ℕ) : 2 * (t + 3) < 2 ^ (t + 3) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [show t + 1 + 3 = (t + 3) + 1 by omega, pow_succ]
    omega

theorem two_mul_le_two_pow_succ (t : ℕ) : 2 * (t + 1) ≤ 2 ^ (t + 1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [show t + 1 + 1 = (t + 1) + 1 from rfl, pow_succ]
    omega

private theorem chain_halving_step (m : ℕ) (hm : 2 ≤ m) (R : List ℕ) :
    it (m - 1) (some (.F (2 * m - 3) 0 [] 0 (0 :: 1 :: R))) = exitC 0 (m - 1) [] 0 (m :: R) := by
  have h := it_shift_loop (m - 2) 0 1 [] R
  simpa [show m - 2 + 1 = m - 1 by omega, show 2 * (m - 2) + 1 = 2 * m - 3 by omega,
    show 1 + (m - 2) + 1 = m by omega] using h

private theorem chain_halt_pow2_aux (t : ℕ) :
    ∀ R : List ℕ,
      it (2 ^ (t + 3) - 2 * (t + 3)) (some (.F (2 ^ (t + 3) - 5) 0 [] 0 (0 :: 1 :: R))) = none := by
  induction t with
  | zero =>
    intro R
    have h := chain_halving_step 3 (by omega) R
    have hex : exitC 0 2 [] 0 (3 :: R) = none := rfl
    simpa [hex] using h
  | succ t ih =>
    intro R
    have ht_lt := two_mul_lt_two_pow_add_three t
    set P := 2 ^ (t + 3)
    have hpow7 : 2 * (t + 3) < P := ht_lt
    have hP_succ : 2 ^ (t + 4) = 2 * P := by
      change 2 ^ ((t + 3) + 1) = 2 * P
      rw [pow_succ]
      ring
    set m := P - 1
    have hm_def : m = P - 1 := rfl
    have hsplit : 2 ^ (t + 4) - 2 * (t + 4) = (m - 1) + (P - 2 * (t + 3)) := by
      rw [hP_succ]
      omega
    have ha : 2 ^ (t + 4) - 5 = 2 * m - 3 := by
      rw [hP_succ]
      omega
    rw [hsplit, it_add, ha, chain_halving_step m (by omega) R]
    have hP_ev : P % 2 = 0 := by
      change 2 ^ ((t + 2) + 1) % 2 = 0
      rw [pow_succ]
      omega
    have hexit : exitC 0 (m - 1) [] 0 (m :: R) =
        some (.F (P - 5) 0 [] 0 (0 :: 1 :: m :: R)) := by
      rw [show m - 1 = P - 2 by omega,
        exitC_empty_even_eq_chainEntry P (m :: R) (by omega) hP_ev]
      unfold chainEntry
      have hnot4 : ¬ P ≤ 4 := by omega
      simp only [hnot4, ↓reduceIte]
    rw [hexit]
    exact ih (m :: R)

/-- From the state starting a multi-gate chain of value `V ≥ 6`, if `V` is a power of two then
the chain halts in `V - 2 * v₂(V)` high-level steps. -/
theorem chain_halt_of_powerOfTwo (V : ℕ) (R : List ℕ) (hV : 6 ≤ V) (hp : ∃ p, V = 2 ^ p) :
    (Option.bind · highLevelNext)^[V - 2 * padicValNat 2 V]
      (some (.F (V - 5) 0 [] 0 (0 :: 1 :: R))) = none := by
  obtain ⟨p, rfl⟩ := hp
  have hp3 : 3 ≤ p := by
    by_contra hlt
    interval_cases p <;> norm_num at hV
  rw [padicValNat.prime_pow]
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  exact chain_halt_pow2_aux t R

private theorem chain_exit_aux (t : ℕ) (q : ℕ) (hq3 : 3 ≤ q) (hqodd : q % 2 = 1) :
    ∀ R : List ℕ,
      it (2 ^ (t + 1) * q - q - 2 * (t + 1))
          (some (.F (2 ^ (t + 1) * q - 5) 0 [] 0 (0 :: 1 :: R))) =
        some (.F q 0 [] 0 (chainR (t + 1) q R)) := by
  induction t with
  | zero =>
    intro R
    simp only [Nat.zero_add, pow_one, mul_one, chainR, pow_zero, one_mul]
    set m := q - 1
    have hstep := chain_halving_step m (by omega) R
    have h1 : 2 * q - q - 2 = m - 1 := by omega
    have h2 : 2 * q - 5 = 2 * m - 3 := by omega
    rw [h1, h2, hstep, show m - 1 = (q - 3) + 1 by omega, exitC_zero_nil]
    have hev : (q - 3) % 2 = 0 := by omega
    simp only [hev, ↓reduceIte, show q - 3 + 3 = q by omega]
  | succ t ih =>
    intro R
    have hpow_le := two_mul_le_two_pow_succ t
    set P := 2 ^ (t + 1)
    have hpow_le' : 2 * (t + 1) ≤ P := hpow_le
    have hP_ge2 : 2 ≤ P := by omega
    have hPq_ge : q + 2 * (t + 1) + 1 ≤ P * q := by nlinarith
    have hPq6 : 6 ≤ P * q := by nlinarith
    have hP_succ : 2 ^ (t + 2) * q = 2 * (P * q) := by
      change 2 ^ ((t + 1) + 1) * q = 2 * (P * q)
      rw [pow_succ]
      ring
    set m := P * q - 1
    have hm_def : m = P * q - 1 := rfl
    have hsplit : 2 ^ (t + 2) * q - q - 2 * (t + 2) =
        (m - 1) + (P * q - q - 2 * (t + 1)) := by
      rw [hP_succ]
      omega
    have ha : 2 ^ (t + 2) * q - 5 = 2 * m - 3 := by
      rw [hP_succ]
      omega
    rw [hsplit, it_add, ha, chain_halving_step m (by omega) R]
    have hPq_ev : (P * q) % 2 = 0 := by
      have : P * q = 2 * (2 ^ t * q) := by
        change 2 ^ (t + 1) * q = 2 * (2 ^ t * q)
        rw [pow_succ]
        ring
      rw [this]
      omega
    have hexit : exitC 0 (m - 1) [] 0 (m :: R) =
        some (.F (P * q - 5) 0 [] 0 (0 :: 1 :: m :: R)) := by
      rw [show m - 1 = P * q - 2 by omega,
        exitC_empty_even_eq_chainEntry (P * q) (m :: R) (by omega) hPq_ev]
      unfold chainEntry
      have hnot4 : ¬ P * q ≤ 4 := by omega
      simp only [hnot4, ↓reduceIte]
    rw [hexit, ih (m :: R)]
    rfl

theorem odd_part_properties (V : ℕ) (hV : 1 ≤ V) :
    let ν := padicValNat 2 V
    let q := V / 2 ^ ν
    V = 2 ^ ν * q ∧ 0 < q ∧ q % 2 = 1 ∧ (q = 1 ↔ ∃ p, V = 2 ^ p) := by
  intro ν q
  have hdvd : 2 ^ ν ∣ V := pow_padicValNat_dvd
  have hV_eq : V = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hq_pos : 0 < q := by
    rcases q with _ | q'
    · simp [hV_eq] at hV
    · omega
  have hndvd : ¬ 2 ^ (ν + 1) ∣ V := pow_succ_padicValNat_not_dvd (by omega)
  have hqodd : q % 2 = 1 := by
    by_contra hnot
    obtain ⟨r, hr⟩ : ∃ r, q = 2 * r := ⟨q / 2, by omega⟩
    apply hndvd
    refine ⟨r, ?_⟩
    rw [hV_eq, hr, pow_succ]
    ring
  refine ⟨hV_eq, hq_pos, hqodd, ?_⟩
  constructor
  · intro hq1
    exact ⟨ν, by rw [hV_eq, hq1, mul_one]⟩
  · rintro ⟨p, rfl⟩
    have hν : ν = p := padicValNat.prime_pow p
    have hp : 0 < 2 ^ p := by positivity
    change 2 ^ p / 2 ^ ν = 1
    rw [hν, Nat.div_self hp]

/-- From the state starting a chain of even value `V ≥ 6` that is not a power of two, the chain
exits in `V - q - 2 * v₂(V)` high-level steps at `.F q 0 [] 0 (chainR ν q R)`, where
`ν = v₂(V)` and `q = V / 2^ν` is the odd part of `V`. -/
theorem chain_exit_of_not_powerOfTwo (V : ℕ) (R : List ℕ) (hV : 6 ≤ V) (hev : V % 2 = 0)
    (hnp : ¬ ∃ p, V = 2 ^ p) :
    let ν := padicValNat 2 V
    let q := V / 2 ^ ν
    (Option.bind · highLevelNext)^[V - q - 2 * ν]
      (some (.F (V - 5) 0 [] 0 (0 :: 1 :: R))) = some (.F q 0 [] 0 (chainR ν q R)) := by
  intro ν q
  obtain ⟨hV_eq, hq_pos, hqodd, hq1_iff⟩ := odd_part_properties V (by omega)
  have hq_pos' : 0 < q := hq_pos
  have hqodd' : q % 2 = 1 := hqodd
  have hq_ne1 : q ≠ 1 := fun h1 => hnp (hq1_iff.mp h1)
  have hq3 : 3 ≤ q := by omega
  have h2dvd : 2 ^ 1 ∣ V := by simpa using Nat.dvd_of_mod_eq_zero hev
  have hν1 : 1 ≤ ν := (padicValNat_dvd_iff_le (by omega)).mp h2dvd
  obtain ⟨t, hν_eq⟩ : ∃ t, ν = t + 1 := ⟨ν - 1, by omega⟩
  change it (V - q - 2 * ν) (some (.F (V - 5) 0 [] 0 (0 :: 1 :: R))) =
    some (.F q 0 [] 0 (chainR ν q R))
  have h1 : V - q - 2 * ν = 2 ^ (t + 1) * q - q - 2 * (t + 1) := by rw [← hν_eq, ← hV_eq]
  have h2 : V - 5 = 2 ^ (t + 1) * q - 5 := by rw [← hν_eq, ← hV_eq]
  rw [h1, h2, hν_eq]
  exact chain_exit_aux t q hq3 hqodd R

/-- A chain of even value `V ≥ 4` halts inside the chain if and only if `V` is a power of two. -/
theorem chainEntry_halts_iff_powerOfTwo (V : ℕ) (R : List ℕ) (hV : 4 ≤ V) (hev : V % 2 = 0) :
    (Option.bind · highLevelNext)^[chainSteps V] (chainEntry V R) = none ↔ ∃ p, V = 2 ^ p := by
  by_cases h4 : V ≤ 4
  · have hV4 : V = 4 := by omega
    subst hV4
    simp only [chainEntry, le_refl, ↓reduceIte]
    change it (chainSteps 4) none = none ↔ ∃ p, 4 = 2 ^ p
    rw [it_none]
    exact ⟨fun _ => ⟨2, rfl⟩, fun _ => rfl⟩
  · have h6 : 6 ≤ V := by omega
    obtain ⟨_, _, _, hq1_iff⟩ := odd_part_properties V (by omega)
    unfold chainEntry
    simp only [h4, ↓reduceIte]
    by_cases hp : ∃ p, V = 2 ^ p
    · have hq1 : V / 2 ^ padicValNat 2 V = 1 := hq1_iff.mpr hp
      have hcs : chainSteps V = V - 2 * padicValNat 2 V := by simp [chainSteps, hq1]
      rw [hcs, chain_halt_of_powerOfTwo V R h6 hp]
      exact ⟨fun _ => hp, fun _ => rfl⟩
    · have hq_ne1 : V / 2 ^ padicValNat 2 V ≠ 1 := fun h1 => hp (hq1_iff.mp h1)
      have hcs : chainSteps V = V - V / 2 ^ padicValNat 2 V - 2 * padicValNat 2 V := by
        simp [chainSteps, hq_ne1]
      rw [hcs, chain_exit_of_not_powerOfTwo V R h6 hev hp]
      simp [hp]

/-- For any odd-entry stack `u`, `paddedW u = W u + 2^|u|` can be a power of two only in the
chain-starting regime `|u| ≤ v₂(W u)`. -/
theorem powerOfTwo_imp_chain (u : List ℕ) (hu : AllOdd u) (hp : ∃ p, paddedW u = 2 ^ p) :
    u.length ≤ padicValNat 2 (W u) := by
  let _ := hu
  obtain ⟨p, hp_eq⟩ := hp
  have hgt : 2 ^ u.length < 2 ^ p := by
    have := W_pos u
    unfold paddedW at hp_eq
    omega
  have hlt : u.length < p := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hgt
  have hdvd_p : 2 ^ u.length ∣ 2 ^ p := Nat.pow_dvd_pow 2 (by omega)
  have hdvd_W : 2 ^ u.length ∣ W u := by
    have hsum : W u + 2 ^ u.length = 2 ^ p := hp_eq
    exact (Nat.dvd_add_iff_left (dvd_refl _)).mpr (hsum ▸ hdvd_p)
  exact (padicValNat_dvd_iff_le (by have := W_pos u; omega)).mp hdvd_W

theorem exists_pow2_mul_iff (a m : ℕ) (hm : 0 < m) :
    (∃ p, 2 ^ a * m = 2 ^ p) ↔ ∃ p, m = 2 ^ p := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hm_eq, _, hqodd, hq1_iff⟩ := odd_part_properties m (by omega)
    set ν := padicValNat 2 m
    set q := m / 2 ^ ν
    have hmul : 2 ^ (a + ν) * q = 2 ^ p := by
      rw [pow_add, mul_assoc, ← hm_eq, hp]
    have hq_dvd : q ∣ 2 ^ p := ⟨2 ^ (a + ν), by rw [mul_comm, hmul]⟩
    have hq1 : q = 1 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hq_dvd with ⟨i, _, hqi⟩
      rcases i with _ | i
      · simpa using hqi
      · exfalso
        rw [hqi, pow_succ'] at hqodd
        omega
    exact hq1_iff.mp hq1
  · rintro ⟨p, rfl⟩
    exact ⟨a + p, (pow_add 2 a p).symm⟩

/-- Combining the sweep and chain laws: a chain-starting sweep from `F 0 2 (ones k ++ u) 1 []`
halts inside its chain if and only if `paddedW u = W u + 2^|u|` is a power of two. -/
theorem sweep_and_chain_halts_iff_powerOfTwo (k : ℕ) (u : List ℕ) (hu : AllOdd u)
    (h : u.length ≤ padicValNat 2 (W u)) :
    let V := (2 * paddedW u) / 2 ^ u.length
    (Option.bind · highLevelNext)^[sweepSteps u u.length + chainSteps V]
      (some (.F 0 2 (ones k ++ u) 1 [])) = none ↔ ∃ p, paddedW u = 2 ^ p := by
  intro V
  have hdvdW : 2 ^ u.length ∣ W u :=
    (padicValNat_dvd_iff_le (by have := W_pos u; omega)).mpr h
  obtain ⟨q, hq⟩ := hdvdW
  have hq_pos : 0 < q := by
    have hpos := W_pos u
    rcases q with _ | q'
    · simp [hq] at hpos
    · omega
  have hp : 0 < 2 ^ u.length := by positivity
  have h2P : 2 * paddedW u = 2 ^ u.length * (2 * q + 2) := by
    unfold paddedW
    rw [hq]
    ring
  have hV_eq : V = 2 * q + 2 := by
    change (2 * paddedW u) / 2 ^ u.length = 2 * q + 2
    rw [h2P, Nat.mul_div_cancel_left _ hp]
  have h2PV : 2 * paddedW u = 2 ^ u.length * V := by rw [h2P, hV_eq]
  change it (sweepSteps u u.length + chainSteps V) (some (.F 0 2 (ones k ++ u) 1 [])) = none ↔ _
  rw [it_add, show it (sweepSteps u u.length) (some (.F 0 2 (ones k ++ u) 1 [])) =
      chainEntry V (sweepR k u u.length) from sweep_starts_chain k u hu h]
  change (Option.bind · highLevelNext)^[chainSteps V] (chainEntry V (sweepR k u u.length)) =
    none ↔ _
  rw [chainEntry_halts_iff_powerOfTwo V (sweepR k u u.length) (by omega) (by omega)]
  have h1 : (∃ p, 2 * paddedW u = 2 ^ p) ↔ ∃ p, paddedW u = 2 ^ p := by
    simpa using exists_pow2_mul_iff 1 (paddedW u) (paddedW_pos u)
  have h2 : (∃ p, 2 ^ u.length * V = 2 ^ p) ↔ ∃ p, V = 2 ^ p :=
    exists_pow2_mul_iff u.length V (by omega)
  rw [← h2, ← h2PV]
  exact h1

/-! ### C. Orbit invariant and global halting characterization -/

/-- High-level step `27` from `highLevelStart` reaches the first bottom reach
`F 0 2 [5, 5, 1] 1 []`. -/
theorem orbit_step27 :
    (Option.bind · highLevelNext)^[27] (some highLevelStart) =
      some (.F 0 2 [5, 5, 1] 1 []) := by
  decide

/-- The first bottom reach `F 0 2 [5, 5, 1] 1 []` satisfies `OrbitInv`. -/
theorem orbitInv_step27 : OrbitInv (.F 0 2 [5, 5, 1] 1 []) := by
  exact Or.inl ⟨rfl, rfl, rfl, rfl, by decide⟩

theorem allOdd_nil : AllOdd [] := by simp [AllOdd]

theorem allOdd_cons {x : ℕ} {xs : List ℕ} :
    AllOdd (x :: xs) ↔ x % 2 = 1 ∧ AllOdd xs := by
  simp [AllOdd]

private theorem endsWithOdds10_one_zero : EndsWithOdds10 [1, 0] :=
  ⟨[], rfl, allOdd_nil⟩

private theorem endsWithOdds10_cons {x : ℕ} {R : List ℕ} (hx : x % 2 = 1)
    (hR : EndsWithOdds10 R) : EndsWithOdds10 (x :: R) := by
  obtain ⟨xs, rfl, hxs⟩ := hR
  exact ⟨x :: xs, rfl, allOdd_cons.mpr ⟨hx, hxs⟩⟩

private theorem orbitInv_of_exitC_two (L : List ℕ) :
    ∀ (R : List ℕ), AllOdd L → (R = [0] ∨ EndsWithOdds10 R) →
      ∀ s', exitC 0 2 L 0 R = some s' → OrbitInv s' := by
  induction L with
  | nil =>
    intro R _ _ s' hs
    rw [show (2 : ℕ) = 1 + 1 from rfl, exitC_zero_nil] at hs
    simp at hs
  | cons c L' ih =>
    intro R hL hR s' hs
    obtain ⟨hc, hL'⟩ := allOdd_cons.mp hL
    have hR1 : EndsWithOdds10 (1 :: R) := by
      rcases hR with rfl | hR'
      · exact endsWithOdds10_one_zero
      · exact endsWithOdds10_cons rfl hR'
    rw [show (2 : ℕ) = 1 + 1 from rfl, exitC_zero_cons] at hs
    simp only [Nat.one_mod, one_ne_zero, ↓reduceIte, Nat.zero_add] at hs
    by_cases hc1 : c = 1
    · subst hc1
      exact ih (1 :: R) hL' (Or.inr hR1) s' hs
    · have hc_nev : ¬ c % 2 = 0 := by omega
      have ha_odd : (2 * (c / 2) - 1) % 2 = 1 := by omega
      rcases L' with _ | ⟨c₂, L''⟩
      · rw [exitC_zero_nil] at hs
        simp only [hc_nev, hc1, ↓reduceIte, Nat.zero_add, Option.some.injEq] at hs
        subst hs
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨ha_odd, rfl, rfl, 1 :: R, rfl, hR1⟩
      · obtain ⟨hc₂, hL''⟩ := allOdd_cons.mp hL'
        rw [exitC_zero_cons] at hs
        simp only [hc_nev, hc1, ↓reduceIte, Nat.zero_add, Option.some.injEq] at hs
        subst hs
        refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ha_odd, by omega, hL'', rfl, ?_⟩
        exact ⟨1, 1 :: R, by omega, rfl, hR1⟩

private theorem orbitInv_of_exitC_ge2 (b : ℕ) (hb : 2 ≤ b) (L : List ℕ) (hL : AllOdd L)
    (d : ℕ) (hd : 1 ≤ d) (hpar : (b + d) % 2 = 0) (R' : List ℕ) (hR' : EndsWithOdds10 R')
    (s' : HighLevelState) (hs : exitC 0 (b + 1) L 0 (d :: R') = some s') : OrbitInv s' := by
  by_cases hbev : b % 2 = 0
  · have hdev : d % 2 = 0 := by omega
    have hd2 : 2 ≤ d := by omega
    have ha_odd : (b + 3) % 2 = 1 := by omega
    rcases L with _ | ⟨c, L'⟩
    · rw [exitC_zero_nil] at hs
      simp only [hbev, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨ha_odd, rfl, allOdd_nil, rfl, d, R', hd2, hdev, rfl, hR'⟩
    · obtain ⟨hc, hL'⟩ := allOdd_cons.mp hL
      rw [exitC_zero_cons] at hs
      simp only [hbev, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨ha_odd, by omega, hL', rfl, d, R', hd2, hdev, rfl, hR'⟩
  · have hb1 : b ≠ 1 := by omega
    have hdodd : d % 2 = 1 := by omega
    have hRd : EndsWithOdds10 (d :: R') := endsWithOdds10_cons hdodd hR'
    have ha_odd : (2 * (b / 2) - 1) % 2 = 1 := by omega
    rcases L with _ | ⟨c, L'⟩
    · rw [exitC_zero_nil] at hs
      simp only [hbev, hb1, ↓reduceIte, Nat.zero_add, Option.some.injEq] at hs
      subst hs
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨ha_odd, rfl, rfl, d :: R', rfl, hRd⟩
    · obtain ⟨hc, hL'⟩ := allOdd_cons.mp hL
      rw [exitC_zero_cons] at hs
      simp only [hbev, hb1, ↓reduceIte, Nat.zero_add, Option.some.injEq] at hs
      subst hs
      refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ha_odd, by omega, hL', rfl, ?_⟩
      exact ⟨1, d :: R', by omega, rfl, hRd⟩

/-- `OrbitInv` is preserved by every non-halting step of `highLevelNext`. -/
theorem orbitInv_preserved (s s' : HighLevelState) (hinv : OrbitInv s)
    (hstep : highLevelNext s = some s') : OrbitInv s' := by
  rcases s with ⟨a, b, L, r, R⟩
  rcases hinv with
    ⟨rfl, rfl, rfl, rfl, hL⟩ |
    ⟨rfl, rfl, rfl, rfl, hL⟩ |
    ⟨rfl, rfl, rfl, rfl, hL⟩ |
    ⟨ha, hb2, hL, rfl, e, R', hbe, rfl, hR'⟩ |
    ⟨ha, rfl, rfl, R', rfl, hR'⟩ |
    ⟨ha, hb, hL, rfl, d, R', hd2, hdev, rfl, hR'⟩ |
    ⟨rfl, hb, hL, hr, hR⟩ |
    ⟨rfl, hb, hL, rfl, rfl⟩
  · -- Clause 1: F 0 2 L 1 []
    have hx : highLevelNext (.F 0 2 L 1 []) = exitC 0 2 L 0 [0] := rfl
    rw [hx] at hstep
    exact orbitInv_of_exitC_two L [0] hL (Or.inl rfl) s' hstep
  · -- Clause 2: F 0 1 L 0 []
    have hx : highLevelNext (.F 0 1 L 0 []) = some (.F 1 1 L 0 [0]) := by
      rw [highLevelNext]
      simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      exact exitC_succ 1 1 L 0 []
    rw [hx, Option.some.injEq] at hstep
    subst hstep
    exact Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl, rfl, rfl, hL⟩
  · -- Clause 3: F 1 1 L 0 [0]
    have hx : highLevelNext (.F 1 1 L 0 [0]) = some (.F 0 2 L 1 []) := rfl
    rw [hx, Option.some.injEq] at hstep
    subst hstep
    exact Or.inl ⟨rfl, rfl, rfl, rfl, hL⟩
  · -- Clause 4: sweep shift loop
    have ha_nev : ¬ a % 2 = 0 := by omega
    rw [highLevelNext] at hstep
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero, ha_nev]
      at hstep
    by_cases ha1 : a = 1
    · subst ha1
      simp only [Nat.div_eq_of_lt (by norm_num : 1 < 2), Nat.mul_zero] at hstep
      exact orbitInv_of_exitC_ge2 b hb2 L hL (e + 1) (by omega) (by omega) R' hR' s' hstep
    · have hdiv : 2 * (a / 2) = (a - 2) + 1 := by omega
      rw [hdiv, exitC_succ, Option.some.injEq] at hstep
      subst hstep
      refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by omega, by omega, hL, rfl, ?_⟩
      exact ⟨e + 1, R', by omega, rfl, hR'⟩
  · -- Clause 5: chain shift loop
    have ha_nev : ¬ a % 2 = 0 := by omega
    rw [highLevelNext] at hstep
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero, ha_nev]
      at hstep
    by_cases ha1 : a = 1
    · subst ha1
      simp only [Nat.div_eq_of_lt (by norm_num : 1 < 2), Nat.mul_zero] at hstep
      by_cases hb1 : b = 1
      · subst hb1
        rw [exitC_zero_nil] at hstep
        simp at hstep
      · by_cases hb0 : b = 0
        · subst hb0
          rw [exitC_zero_nil] at hstep
          simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_add, Option.some.injEq] at hstep
          subst hstep
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨by decide, rfl, allOdd_nil, rfl, 2, R', by omega, by omega, rfl, hR'⟩
        · exact orbitInv_of_exitC_ge2 b (by omega) [] allOdd_nil (b + 2) (by omega)
            (by omega) R' hR' s' hstep
    · have hdiv : 2 * (a / 2) = (a - 2) + 1 := by omega
      rw [hdiv, exitC_succ, Option.some.injEq] at hstep
      subst hstep
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨by omega, rfl, rfl, R', rfl, hR'⟩
  · -- Clause 6: pre-drain (F5)
    have hd0 : d ≠ 0 := by omega
    rw [highLevelNext] at hstep
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero, hd0,
      Option.some.injEq] at hstep
    subst hstep
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨rfl, by omega, hL, ha, endsWithOdds10_cons (by omega) hR'⟩
  · -- Clause 7: drain (F7)
    have hr_nev : ¬ r % 2 = 0 := by omega
    have hr_div : 0 + 2 * (r / 2) + 1 = r := by omega
    obtain ⟨xs, rfl, hxs⟩ := hR
    rcases xs with _ | ⟨e, xs'⟩
    · rw [List.nil_append, highLevelNext] at hstep
      simp only [hr_nev, ↓reduceIte, hr_div, Option.some.injEq] at hstep
      subst hstep
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        ⟨rfl, hr, allOdd_cons.mpr ⟨hb, hL⟩, rfl, rfl⟩
    · obtain ⟨he, hxs'⟩ := allOdd_cons.mp hxs
      rw [List.cons_append, highLevelNext] at hstep
      simp only [hr_nev, ↓reduceIte, hr_div, Option.some.injEq] at hstep
      subst hstep
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨rfl, hr, allOdd_cons.mpr ⟨hb, hL⟩, he, ⟨xs', rfl, hxs'⟩⟩
  · -- Clause 8: final [0] drain step
    have hx : highLevelNext (.F 0 b L 1 [0]) = some (.F 0 1 (b :: L) 0 []) := rfl
    rw [hx, Option.some.injEq] at hstep
    subst hstep
    exact Or.inr <| Or.inl ⟨rfl, rfl, rfl, rfl, allOdd_cons.mpr ⟨hb, hL⟩⟩

private theorem orbitInv_iterate (n : ℕ) {s s' : HighLevelState} (hinv : OrbitInv s)
    (h : it n (some s) = some s') : OrbitInv s' := by
  induction n generalizing s with
  | zero =>
    simp only [it_zero, Option.some.injEq] at h
    subst h
    exact hinv
  | succ n ih =>
    rw [it_succ_front, Option.bind_some] at h
    rcases hnext : highLevelNext s with _ | s₁
    · rw [hnext, it_none] at h
      simp at h
    · rw [hnext] at h
      exact ih (orbitInv_preserved s s₁ hinv hnext) h

private def isBotState : HighLevelState → Bool
  | .F 0 2 _ 1 [] => true
  | _ => false

private def noBotBefore27 : Bool :=
  (List.range 27).all fun t =>
    match (Option.bind · highLevelNext)^[t] (some highLevelStart) with
    | some s => !isBotState s
    | none => true

private theorem noBotBefore27_eq_true : noBotBefore27 = true := by decide

/-- Every bottom reach `F 0 2 L 1 []` visited on the orbit from `highLevelStart` has all odd
stack entries. -/
theorem allOdd_of_bottomReach (t : ℕ) (L : List ℕ)
    (ht : (Option.bind · highLevelNext)^[t] (some highLevelStart) =
      some (.F 0 2 L 1 [])) :
    AllOdd L := by
  by_cases hlt : t < 27
  · exfalso
    have hall := List.all_eq_true.mp noBotBefore27_eq_true t (List.mem_range.mpr hlt)
    simp [ht, isBotState] at hall
  · have hsplit : t = 27 + (t - 27) := by omega
    change it t (some highLevelStart) = some (.F 0 2 L 1 []) at ht
    rw [hsplit, it_add, show it 27 (some highLevelStart) = some (.F 0 2 [5, 5, 1] 1 []) from
      orbit_step27] at ht
    have hinv := orbitInv_iterate (t - 27) orbitInv_step27 ht
    rcases hinv with
      ⟨_, _, _, _, hL⟩ |
      ⟨_, hb, _, _, _⟩ |
      ⟨_, hb, _, _, _⟩ |
      ⟨_, _, _, hr, _⟩ |
      ⟨_, _, hr, _⟩ |
      ⟨_, _, _, hr, _⟩ |
      ⟨_, _, _, _, ⟨xs, hR, _⟩⟩ |
      ⟨_, _, _, _, hR⟩
    · exact hL
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp at hR
    · simp at hR

private theorem sweepSteps_pos (u : List ℕ) (d : ℕ) : 0 < sweepSteps u d := by
  induction d with
  | zero => simp [sweepSteps]
  | succ d ih => unfold sweepSteps; omega

private theorem drain_odds_loop (xs : List ℕ) :
    ∀ (b r : ℕ) (L : List ℕ),
      AllOdd xs → b % 2 = 1 → r % 2 = 1 → AllOdd L →
        ∃ L', AllOdd L' ∧
          it (xs.length + 2) (some (.F 0 b L r (xs ++ [1, 0]))) = some (.F 0 1 L' 0 []) := by
  induction xs with
  | nil =>
    intro b r L _ hb hr hL
    refine ⟨r :: b :: L, allOdd_cons.mpr ⟨hr, allOdd_cons.mpr ⟨hb, hL⟩⟩, ?_⟩
    have hr_nev : ¬ r % 2 = 0 := by omega
    have hr_div : 2 * (r / 2) + 1 = r := by omega
    have h1 : highLevelNext (.F 0 b L r [1, 0]) = some (.F 0 r (b :: L) 1 [0]) := by
      rw [highLevelNext]
      simp [hr_nev, hr_div]
    have h2 : highLevelNext (.F 0 r (b :: L) 1 [0]) = some (.F 0 1 (r :: b :: L) 0 []) := rfl
    rw [List.length_nil, Nat.zero_add, List.nil_append, it_succ_front, Option.bind_some, h1,
      it_succ_front, Option.bind_some, h2, it_zero]
  | cons e xs' ih =>
    intro b r L hxs hb hr hL
    obtain ⟨he, hxs'⟩ := allOdd_cons.mp hxs
    have hr_nev : ¬ r % 2 = 0 := by omega
    have hr_div : 2 * (r / 2) + 1 = r := by omega
    have h1 : highLevelNext (.F 0 b L r (e :: (xs' ++ [1, 0]))) =
        some (.F 0 r (b :: L) e (xs' ++ [1, 0])) := by
      rw [highLevelNext]
      simp [hr_nev, hr_div]
    rw [List.length_cons, show xs'.length + 1 + 2 = (xs'.length + 2) + 1 by omega,
      List.cons_append, it_succ_front, Option.bind_some, h1]
    exact ih r e (b :: L) hxs' hr he (allOdd_cons.mpr ⟨hb, hL⟩)

private theorem drain_from_clause6 (a b : ℕ) (L₁ : List ℕ) (d : ℕ) (R' : List ℕ)
    (ha : a % 2 = 1) (hb : b % 2 = 0) (hL₁ : AllOdd L₁) (hd2 : 2 ≤ d) (hdev : d % 2 = 0)
    (hR' : EndsWithOdds10 R') :
    ∃ m L', 0 < m ∧ AllOdd L' ∧
      it m (some (.F a b L₁ 0 (d :: R'))) = some (.F 0 2 L' 1 []) := by
  obtain ⟨xs, rfl, hxs⟩ := hR'
  have hd0 : d ≠ 0 := by omega
  have hstep1 : highLevelNext (.F a b L₁ 0 (d :: (xs ++ [1, 0]))) =
      some (.F 0 (b + 1) L₁ a (((d - 1) :: xs) ++ [1, 0])) := by
    rw [highLevelNext]
    simp [hd0]
  obtain ⟨L', hL', hdrain⟩ := drain_odds_loop ((d - 1) :: xs) (b + 1) a L₁
    (allOdd_cons.mpr ⟨by omega, hxs⟩) (by omega) ha hL₁
  have hfin1 : highLevelNext (.F 0 1 L' 0 []) = some (.F 1 1 L' 0 [0]) := by
    rw [highLevelNext]
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
    exact exitC_succ 1 1 L' 0 []
  have hfin2 : highLevelNext (.F 1 1 L' 0 [0]) = some (.F 0 2 L' 1 []) := rfl
  have hs1 : it 1 (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) =
      some (.F 0 (b + 1) L₁ a (((d - 1) :: xs) ++ [1, 0])) := by
    rw [it_succ_front, Option.bind_some, hstep1, it_zero]
  have hs2 : it (1 + (((d - 1) :: xs).length + 2))
      (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) = some (.F 0 1 L' 0 []) := by
    rw [it_add, hs1, hdrain]
  have hs3 : it 2 (some (.F 0 1 L' 0 [])) = some (.F 0 2 L' 1 []) := by
    rw [it_succ_front, Option.bind_some, hfin1, it_succ_front, Option.bind_some, hfin2, it_zero]
  refine ⟨(1 + (((d - 1) :: xs).length + 2)) + 2, L', by omega, hL', ?_⟩
  rw [it_add, hs2, hs3]

private theorem finish_from_pre_drain (L : List ℕ) (hL : AllOdd L) (n₁ a b d : ℕ)
    (L₁ R' : List ℕ) (hn₁ : 0 < n₁) (ha2 : 2 ≤ a) (hd1 : 1 ≤ d)
    (hreach : it n₁ (some (.F 0 2 L 1 [])) = some (.F a b L₁ 0 (d :: R'))) :
    ∃ n L', 0 < n ∧ AllOdd L' ∧
      it n (some (.F 0 2 L 1 [])) = some (.F 0 2 L' 1 []) := by
  have hinv₀ : OrbitInv (.F 0 2 L 1 []) := Or.inl ⟨rfl, rfl, rfl, rfl, hL⟩
  have hinv₁ := orbitInv_iterate n₁ hinv₀ hreach
  rcases hinv₁ with
    ⟨_, _, hr, _⟩ |
    ⟨ha0, _⟩ |
    ⟨ha1, _⟩ |
    ⟨_, _, _, _, e, R'', _, hR, _⟩ |
    ⟨_, _, _, R'', hR, _⟩ |
    ⟨ha, hb, hL₁, _, d', R'', hd2, hdev, hR, hR'⟩ |
    ⟨ha0, _⟩ |
    ⟨ha0, _⟩
  · omega
  · omega
  · omega
  · simp only [List.cons.injEq] at hR; omega
  · simp only [List.cons.injEq] at hR; omega
  · simp only [List.cons.injEq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    obtain ⟨m, L', hm, hL', hdrain⟩ := drain_from_clause6 a b L₁ d R' ha hb hL₁ hd2 hdev hR'
    exact ⟨n₁ + m, L', by omega, hL', by rw [it_add, hreach, hdrain]⟩
  · omega
  · omega

private theorem sweepR_zero_cons (L : List ℕ) (d' : ℕ) (hdvd : 2 ^ d' ∣ W (L.take d')) :
    ∃ d₁ R', 1 ≤ d₁ ∧ sweepR 0 L (d' + 1) = d₁ :: R' := by
  obtain ⟨q, hq⟩ := hdvd
  have hq_pos : 0 < q := by
    have hpos := W_pos (L.take d')
    rcases q with _ | q'
    · simp [hq] at hpos
    · omega
  have hp : 0 < 2 ^ d' := by positivity
  have hdiv : W (L.take d') / 2 ^ d' = q := by rw [hq, Nat.mul_div_cancel_left _ hp]
  exact ⟨q, sweepPushes L d' ++ [0], hq_pos, by simp [sweepR, sweepPushes, ones, hdiv]⟩

private theorem chainR_head_ge_one (t q : ℕ) (hq3 : 3 ≤ q) :
    ∀ R : List ℕ, ∃ d₁ R', 1 ≤ d₁ ∧ chainR (t + 1) q R = d₁ :: R' := by
  induction t with
  | zero =>
    intro R
    exact ⟨q - 1, R, by omega, by simp [chainR]⟩
  | succ t ih =>
    intro R
    simpa [chainR] using ih ((2 ^ (t + 1) * q - 1) :: R)

/-- Every all-odd bottom reach `F 0 2 L 1 []` whose `paddedW L` is not a power of two steps in
one or more high-level steps to a next all-odd bottom reach `F 0 2 L' 1 []`. -/
theorem bottomReach_step_of_not_powerOfTwo (L : List ℕ) (hL : AllOdd L)
    (hnp : ¬ ∃ p, paddedW L = 2 ^ p) :
    ∃ n L', 0 < n ∧ AllOdd L' ∧
      (Option.bind · highLevelNext)^[n] (some (.F 0 2 L 1 [])) =
        some (.F 0 2 L' 1 []) := by
  have hne : L ≠ [] := by
    rintro rfl
    exact hnp ⟨1, rfl⟩
  have hlen_pos : 1 ≤ L.length := List.length_pos_iff.mpr hne
  set ν := padicValNat 2 (W L)
  by_cases hc1 : ν + 1 < L.length
  · have hs := sweep_stops_inside 0 L hL hc1
    simp only [ones, List.replicate_zero, List.nil_append] at hs
    obtain ⟨d₁, R', hd₁, hR⟩ := sweepR_zero_cons L ν (two_pow_dvd_W_take L ν (le_refl _))
    change it (sweepSteps L (ν + 1)) (some (.F 0 2 L 1 [])) =
      some (.F (W (L.take (ν + 1)) / 2 ^ ν + 2) (L[ν + 1]'hc1 + 1) (L.drop (ν + 2)) 0
        (sweepR 0 L (ν + 1))) at hs
    rw [hR] at hs
    exact finish_from_pre_drain L hL (sweepSteps L (ν + 1))
      (W (L.take (ν + 1)) / 2 ^ ν + 2) (L[ν + 1]'hc1 + 1) d₁ (L.drop (ν + 2)) R'
      (sweepSteps_pos L (ν + 1)) (Nat.le_add_left 2 _) hd₁ hs
  · by_cases hc2 : ν + 1 = L.length
    · have hs := sweep_empties_even 0 L hL hc2
      simp only [ones, List.replicate_zero, List.nil_append] at hs
      obtain ⟨d₁, R', hd₁, hR⟩ := sweepR_zero_cons L ν (two_pow_dvd_W_take L ν (le_refl _))
      change it (sweepSteps L L.length) (some (.F 0 2 L 1 [])) =
        some (.F (W L / 2 ^ (L.length - 1) + 2) 0 [] 0 (sweepR 0 L L.length)) at hs
      rw [← hc2, hR] at hs
      exact finish_from_pre_drain L hL (sweepSteps L (ν + 1))
        (W L / 2 ^ (ν + 1 - 1) + 2) 0 d₁ [] R'
        (sweepSteps_pos L (ν + 1)) (Nat.le_add_left 2 _) hd₁ hs
    · have hc3 : L.length ≤ ν := by omega
      set V := (2 * paddedW L) / 2 ^ L.length
      have hdvdW : 2 ^ L.length ∣ W L :=
        (padicValNat_dvd_iff_le (by have := W_pos L; omega)).mpr hc3
      obtain ⟨qW, hqW⟩ := hdvdW
      have hqW_pos : 0 < qW := by
        have hpos := W_pos L
        rcases qW with _ | q'
        · simp [hqW] at hpos
        · omega
      have hp : 0 < 2 ^ L.length := by positivity
      have hV_eq : V = 2 * qW + 2 := by
        change (2 * paddedW L) / 2 ^ L.length = 2 * qW + 2
        rw [show 2 * paddedW L = 2 ^ L.length * (2 * qW + 2) by unfold paddedW; rw [hqW]; ring,
          Nat.mul_div_cancel_left _ hp]
      have hV_not_pow2 : ¬ ∃ p, V = 2 ^ p := by
        intro hVp
        have hnone := (chainEntry_halts_iff_powerOfTwo V (sweepR 0 L L.length)
          (by omega) (by omega)).mpr hVp
        have hsc := sweep_starts_chain 0 L hL hc3
        have hcomb : (Option.bind · highLevelNext)^[sweepSteps L L.length + chainSteps V]
            (some (.F 0 2 (ones 0 ++ L) 1 [])) = none := by
          change it (sweepSteps L L.length + chainSteps V) (some (.F 0 2 (ones 0 ++ L) 1 [])) =
            none
          rw [it_add, show it (sweepSteps L L.length) (some (.F 0 2 (ones 0 ++ L) 1 [])) =
            chainEntry V (sweepR 0 L L.length) from hsc]
          exact hnone
        exact hnp ((sweep_and_chain_halts_iff_powerOfTwo 0 L hL hc3).mp hcomb)
      have hV6 : 6 ≤ V := by
        by_contra hlt6
        have hV4 : V = 4 := by omega
        exact hV_not_pow2 ⟨2, by omega⟩
      have hsc := sweep_starts_chain 0 L hL hc3
      simp only [ones, List.replicate_zero, List.nil_append] at hsc
      change it (sweepSteps L L.length) (some (.F 0 2 L 1 [])) =
        chainEntry V (sweepR 0 L L.length) at hsc
      have hce : chainEntry V (sweepR 0 L L.length) =
          some (.F (V - 5) 0 [] 0 (0 :: 1 :: sweepR 0 L L.length)) := by
        unfold chainEntry
        have hnot4 : ¬ V ≤ 4 := by omega
        simp only [hnot4, ↓reduceIte]
      rw [hce] at hsc
      set νV := padicValNat 2 V
      set qV := V / 2 ^ νV
      obtain ⟨_, hqV_pos, hqV_odd, hqV1_iff⟩ := odd_part_properties V (by omega)
      have hqV_pos' : 0 < qV := hqV_pos
      have hqV_odd' : qV % 2 = 1 := hqV_odd
      have hqV_ne1 : qV ≠ 1 := fun h1 => hV_not_pow2 (hqV1_iff.mp h1)
      have hqV3 : 3 ≤ qV := by omega
      have h2dvdV : 2 ^ 1 ∣ V := by simpa using Nat.dvd_of_mod_eq_zero (by omega : V % 2 = 0)
      have hνV1 : 1 ≤ νV := (padicValNat_dvd_iff_le (by omega)).mp h2dvdV
      obtain ⟨tV, htV⟩ : ∃ tV, νV = tV + 1 := ⟨νV - 1, by omega⟩
      obtain ⟨d₁, R', hd₁, hR⟩ := chainR_head_ge_one tV qV hqV3 (sweepR 0 L L.length)
      have hcex := chain_exit_of_not_powerOfTwo V (sweepR 0 L L.length) hV6 (by omega) hV_not_pow2
      change it (V - qV - 2 * νV) (some (.F (V - 5) 0 [] 0 (0 :: 1 :: sweepR 0 L L.length))) =
        some (.F qV 0 [] 0 (chainR νV qV (sweepR 0 L L.length))) at hcex
      have hR' : chainR νV qV (sweepR 0 L L.length) = d₁ :: R' := by rw [htV, hR]
      rw [hR'] at hcex
      have htot : it (sweepSteps L L.length + (V - qV - 2 * νV)) (some (.F 0 2 L 1 [])) =
          some (.F qV 0 [] 0 (d₁ :: R')) := by
        rw [it_add, hsc, hcex]
      exact finish_from_pre_drain L hL (sweepSteps L L.length + (V - qV - 2 * νV))
        qV 0 d₁ [] R' (by have := sweepSteps_pos L L.length; omega) (by omega) hd₁ htot

/-- Global criterion: the machine halts from the blank tape if and only if its high-level orbit
reaches a bottom reach `F 0 2 L 1 []` whose `W L + 2^|L|` (`paddedW L`) is a power of two. -/
theorem isHalt_iff_bottomReach_powerOfTwo :
    IsHalt target ↔
      ∃ t L, (Option.bind · highLevelNext)^[t] (some highLevelStart) =
          some (.F 0 2 L 1 []) ∧
        ∃ p, paddedW L = 2 ^ p := by
  rw [BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.isHalt_iff_highLevel_acceleration]
  constructor
  · rintro ⟨T, hT⟩
    rw [Option.isNone_iff_eq_none] at hT
    by_contra hno
    push Not at hno
    have hseq : ∀ j : ℕ, ∃ t L, 27 + j ≤ t ∧ AllOdd L ∧
        it t (some highLevelStart) = some (.F 0 2 L 1 []) := by
      intro j
      induction j with
      | zero =>
        exact ⟨27, [5, 5, 1], by omega, by decide, orbit_step27⟩
      | succ j ih =>
        obtain ⟨t, L, htj, hL, ht⟩ := ih
        have hnp : ¬ ∃ p, paddedW L = 2 ^ p := fun ⟨p, hp⟩ => hno t L ht p hp
        obtain ⟨n, L', hn, hL', hstep⟩ := bottomReach_step_of_not_powerOfTwo L hL hnp
        refine ⟨t + n, L', by omega, hL', ?_⟩
        rw [it_add, ht]
        exact hstep
    obtain ⟨t, L, htT, _, ht⟩ := hseq T
    have hsplit : t = T + (t - T) := by omega
    change it T (some highLevelStart) = none at hT
    rw [hsplit, it_add, hT, it_none] at ht
    simp at ht
  · rintro ⟨t, L, ht, hp⟩
    have hL : AllOdd L := allOdd_of_bottomReach t L ht
    have hc3 : L.length ≤ padicValNat 2 (W L) := powerOfTwo_imp_chain L hL hp
    have hhalt := (sweep_and_chain_halts_iff_powerOfTwo 0 L hL hc3).mpr hp
    simp only [ones, List.replicate_zero, List.nil_append] at hhalt
    set m := sweepSteps L L.length + chainSteps ((2 * paddedW L) / 2 ^ L.length)
    refine ⟨t + m, ?_⟩
    rw [Option.isNone_iff_eq_none]
    change it (t + m) (some highLevelStart) = none
    rw [it_add]
    change it m ((Option.bind · highLevelNext)^[t] (some highLevelStart)) = none
    rw [ht]
    exact hhalt

end AntihydraOrbit.Line116
