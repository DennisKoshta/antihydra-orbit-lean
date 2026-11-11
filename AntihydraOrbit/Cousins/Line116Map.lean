import Mathlib
import AntihydraOrbit.Cousins.Line116

/-!
# The machine `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`: one cycle as a map on the stack

`Line116.lean` proves that the machine halts if and only if some bottom reach `F 0 2 L 1 []` of
its high-level orbit has a padded sum that is a power of two. This file describes the whole cycle
from one bottom reach to the next by an explicit map `botStep` on the stack alone, with the exact
number `botSteps` of high-level steps the cycle takes.

One cycle, for a stack `L = [u_0, u_1, ...]` of odd entries (top first):

* carries: `p_0 = 1`, `B_(j+1) = u_j + p_j`; the sweep stops at the first odd `B_d`; while `B` is
  even, `p_(j+1) = B_(j+1) / 2`;
* stop inside the stack: `L' = [p_1, .., p_(d-2), p_(d-1) - 1, B_d + 2, u_d + 2] ++ rest`;
* stop at the last entry: `L' = [p_1, .., p_(d-2), p_(d-1) - 1, B_d + 2, 1]`;
* no stop (a halving chain of value `V = B + 2 = 2^ν * q`, `q` odd): halt when `q = 1`,
  otherwise `L' = [p_1, .., p_(m-1), 2^(ν-1) q - 1, .., 2 q - 1, q - 2, q, 1]`;
* high-level steps: `6 + (p_1 + .. + p_(d-1))`, plus `V - q - ν` in a chain.

Consequently the machine halts from the blank tape if and only if iterating `botStep` from
`[5, 5, 1]` ever returns `none` (`isHalt_iff_botStep`). Whether that happens is open: nothing here
decides it.
-/

namespace AntihydraOrbit.Line116

open BusyBeaver
open BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA
  (target HighLevelState highLevelNext highLevelStart)

/-! ### Definitions (the trusted base) -/

/-- `chainMid t q = [2^t q - 1, .., 2 q - 1]`. -/
def chainMid : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t + 1, q => (2 ^ (t + 1) * q - 1) :: chainMid t q

/-- Entries left at the bottom of the stack by a non-halting chain of value `2^ν * q`:
`[2^(ν-1) q - 1, .., 2 q - 1, q - 2, q, 1]`. -/
def chainTail (ν q : ℕ) : List ℕ := chainMid (ν - 1) q ++ [q - 2, q, 1]

/-- The entry below the stopping point gains `2`; below the last entry a new `1` appears. -/
def bumpBelow : List ℕ → List ℕ
  | [] => [1]
  | v :: rest => (v + 2) :: rest

/-- The carry sweep of one cycle, with incoming carry `p`. `first` is true while no entry has been
passed: the initial carry `1` is not written back. Returns the new stack, or `none` when the cycle
ends in a halt. -/
def botGo : Bool → ℕ → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | first, p, u :: rest =>
    if (u + p) % 2 = 1 then
      some ((if first then [] else [p - 1]) ++ (u + p + 2) :: bumpBelow rest)
    else
      match rest with
      | [] =>
        let V := u + p + 2
        let ν := padicValNat 2 V
        let q := V / 2 ^ ν
        if q = 1 then none else some ((if first then [] else [p]) ++ chainTail ν q)
      | _ :: _ =>
        (botGo false ((u + p) / 2) rest).map ((if first then [] else [p]) ++ ·)

/-- High-level steps of the sweep part of one cycle (the carries that are written back, plus the
chain when there is one). -/
def botGoSteps : Bool → ℕ → List ℕ → ℕ
  | _, _, [] => 0
  | first, p, u :: rest =>
    (if first then 0 else p) +
      (if (u + p) % 2 = 1 then 0
       else
        match rest with
        | [] =>
          let V := u + p + 2
          let ν := padicValNat 2 V
          V - V / 2 ^ ν - ν
        | _ :: _ => botGoSteps false ((u + p) / 2) rest)

/-- One cycle of the machine, from a bottom reach `F 0 2 L 1 []` to the next one, on the stack
alone. `none` means the machine halts in this cycle. -/
def botStep (L : List ℕ) : Option (List ℕ) := botGo true 1 L

/-- The number of high-level steps of the cycle that starts at the bottom reach with stack `L`. -/
def botSteps (L : List ℕ) : ℕ := 6 + botGoSteps true 1 L

/-! ### Sanity checks of the definitions (values computed independently) -/

example : botStep [5, 5, 1] = some [3, 3, 7, 1] ∧ botSteps [5, 5, 1] = 13 := by
  decide

example : botStep [3, 3, 7, 1] = some [1, 7, 9, 1] ∧ botSteps [3, 3, 7, 1] = 8 := by
  decide

example :
    botStep [1, 1, 9, 17, 1] = some [1, 1, 5, 11, 5, 7, 1] ∧ botSteps [1, 1, 9, 17, 1] = 30 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv14 : padicValNat 2 14 = 1 := by
    rw [show (14 : ℕ) = 2 ^ 1 * 7 from rfl, padicValNat.mul (by omega) (by omega),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by omega)]
  simp [botStep, botSteps, botGo, botGoSteps, chainTail, chainMid, hv14]

example : botStep [9, 5] = some [5, 5, 1, 3, 1] ∧ botSteps [9, 5] = 18 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv12 : padicValNat 2 12 = 2 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 from rfl, padicValNat.mul (by omega) (by omega),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by omega)]
  simp [botStep, botSteps, botGo, botGoSteps, chainTail, chainMid, hv12]

example : botStep [1, 5, 3] = none := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv8 : padicValNat 2 8 = 3 := by
    simpa using (padicValNat.prime_pow 3 : padicValNat 2 (2 ^ 3) = 3)
  simp [botStep, botGo, hv8]

example : botStep [13] = none := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv16 : padicValNat 2 16 = 4 := by
    simpa using (padicValNat.prime_pow 4 : padicValNat 2 (2 ^ 4) = 4)
  simp [botStep, botGo, hv16]

/-! ### Statements -/

open BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA (exitC)

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

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

private theorem allOdd_append {xs ys : List ℕ} :
    AllOdd (xs ++ ys) ↔ AllOdd xs ∧ AllOdd ys := by
  simp [AllOdd, or_imp, forall_and]

private theorem allOdd_reverse {xs : List ℕ} :
    AllOdd xs.reverse ↔ AllOdd xs := by
  simp [AllOdd]

private theorem it_shift_loop_lt (k b e : ℕ) (L R : List ℕ) :
    ∀ j ≤ k,
      it j (some (.F (2 * k + 1) b L 0 (0 :: e :: R))) =
        some (.F (2 * (k - j) + 1) (b + j) L 0 (0 :: (e + j) :: R)) := by
  induction k generalizing b e with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [it_zero]
  | succ k ih =>
    intro j hj
    rcases j with _ | j
    · simp [it_zero]
    · have hstep :
          highLevelNext (.F (2 * (k + 1) + 1) b L 0 (0 :: e :: R)) =
            some (.F (2 * k + 1) (b + 1) L 0 (0 :: (e + 1) :: R)) := by
        have hodd : ¬ (2 * (k + 1) + 1) % 2 = 0 := by omega
        have hdiv : 2 * ((2 * (k + 1) + 1) / 2) = (2 * k + 1) + 1 := by omega
        rw [highLevelNext]
        simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero, hodd, hdiv]
        exact exitC_succ (2 * k + 1) (b + 1) L 0 ((e + 1) :: R)
      rw [it_succ_front, Option.bind_some, hstep, ih (b + 1) (e + 1) j (by omega),
        show k + 1 - (j + 1) = k - j by omega, show b + 1 + j = b + (j + 1) by omega,
        show e + 1 + j = e + (j + 1) by omega]

private theorem it_shift_loop (k b e : ℕ) (L R : List ℕ) :
    it (k + 1) (some (.F (2 * k + 1) b L 0 (0 :: e :: R))) =
      exitC 0 (b + k + 1) L 0 ((e + k + 1) :: R) := by
  rw [it_add, it_shift_loop_lt k b e L R k (le_refl k), it_succ_front, it_zero]
  simp [highLevelNext, add_assoc]

private theorem odd_pop_step_and_no_bot (p : ℕ) (hp : 1 ≤ p) (u : ℕ) (rest R : List ℕ) :
    it (p - 1) (exitC 0 (2 * p) (u :: rest) 0 R) = exitC 0 (u + p) rest 0 (p :: R) ∧
      ∀ j < p - 1, ∀ M, it j (exitC 0 (2 * p) (u :: rest) 0 R) ≠ some (.F 0 2 M 1 []) := by
  rcases p with _ | p'
  · omega
  · rcases p' with _ | k
    · refine ⟨rfl, ?_⟩
      intro j hj
      omega
    · have hexit :
          exitC 0 (2 * (k + 1 + 1)) (u :: rest) 0 R =
            some (.F (2 * k + 1) (u + 1) rest 0 (0 :: 1 :: R)) := by
        have h2 : ¬ (2 * k + 3) % 2 = 0 := by omega
        have h3 : 2 * k + 3 ≠ 1 := by omega
        have h4 : 2 * ((2 * k + 3) / 2) - 1 = 2 * k + 1 := by omega
        rw [show 2 * (k + 1 + 1) = (2 * k + 3) + 1 by omega, exitC_zero_cons]
        simp only [h2, h3, ↓reduceIte, h4, Nat.zero_add]
      have hsub : k + 1 + 1 - 1 = k + 1 := by omega
      rw [hexit, hsub]
      refine ⟨?_, ?_⟩
      · rw [it_shift_loop, show u + 1 + k + 1 = u + (k + 1 + 1) by omega,
          show 1 + k + 1 = k + 1 + 1 by omega]
      · intro j hj M
        rw [it_shift_loop_lt k (u + 1) 1 rest R j (by omega)]
        simp

private theorem chain_halving_step (m : ℕ) (hm : 2 ≤ m) (R : List ℕ) :
    it (m - 1) (some (.F (2 * m - 3) 0 [] 0 (0 :: 1 :: R))) = exitC 0 (m - 1) [] 0 (m :: R) := by
  have h := it_shift_loop (m - 2) 0 1 [] R
  simpa [show m - 2 + 1 = m - 1 by omega, show 2 * (m - 2) + 1 = 2 * m - 3 by omega,
    show 1 + (m - 2) + 1 = m by omega] using h

private theorem chain_aux_no_bot (t q : ℕ) (hq3 : 3 ≤ q) (hqodd : q % 2 = 1) :
    ∀ (R : List ℕ) (k : ℕ), k < 2 ^ (t + 1) * q - q - 2 * (t + 1) →
      ∀ M, it k (some (.F (2 ^ (t + 1) * q - 5) 0 [] 0 (0 :: 1 :: R))) ≠
        some (.F 0 2 M 1 []) := by
  induction t with
  | zero =>
    intro R k hk M
    simp only [Nat.zero_add, pow_one, mul_one] at hk ⊢
    have ha : 2 * q - 5 = 2 * (q - 3) + 1 := by omega
    rw [ha, it_shift_loop_lt (q - 3) 0 1 [] R k (by omega)]
    simp
  | succ t ih =>
    intro R k hk M
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
    rw [hsplit] at hk
    by_cases hlt : k < m - 1
    · have ha : 2 ^ (t + 2) * q - 5 = 2 * (m - 2) + 1 := by
        rw [hP_succ]
        omega
      rw [ha, it_shift_loop_lt (m - 2) 0 1 [] R k (by omega)]
      simp
    · have hk_eq : k = (m - 1) + (k - (m - 1)) := by omega
      have ha : 2 ^ (t + 2) * q - 5 = 2 * m - 3 := by
        rw [hP_succ]
        omega
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
      rw [hk_eq, it_add, ha, chain_halving_step m (by omega) R, hexit]
      exact ih (m :: R) (k - (m - 1)) (by omega) M

private theorem drain_odds_exact (ys : List ℕ) :
    ∀ (b r : ℕ) (L₀ : List ℕ),
      AllOdd ys → b % 2 = 1 → r % 2 = 1 → AllOdd L₀ →
        it (ys.length + 2) (some (.F 0 b L₀ r (ys ++ [1, 0]))) =
            some (.F 0 1 (ys.reverse ++ r :: b :: L₀) 0 []) ∧
          AllOdd (ys.reverse ++ r :: b :: L₀) ∧
          ∀ k < ys.length + 2, ∀ M,
            it k (some (.F 0 b L₀ r (ys ++ [1, 0]))) ≠ some (.F 0 2 M 1 []) := by
  induction ys with
  | nil =>
    intro b r L₀ _ hb hr hL₀
    have hr_nev : ¬ r % 2 = 0 := by omega
    have hr_div : 2 * (r / 2) + 1 = r := by omega
    have h1 : highLevelNext (.F 0 b L₀ r [1, 0]) = some (.F 0 r (b :: L₀) 1 [0]) := by
      rw [highLevelNext]
      simp [hr_nev, hr_div]
    have h2 : highLevelNext (.F 0 r (b :: L₀) 1 [0]) = some (.F 0 1 (r :: b :: L₀) 0 []) := rfl
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, List.nil_append, List.reverse_nil]
      rw [it_succ_front, Option.bind_some, h1, it_succ_front, Option.bind_some, h2, it_zero]
    · simp only [List.reverse_nil, List.nil_append]
      exact allOdd_cons.mpr ⟨hr, allOdd_cons.mpr ⟨hb, hL₀⟩⟩
    · intro k hk M
      simp only [List.length_nil, Nat.zero_add, List.nil_append] at hk ⊢
      rcases k with _ | _ | k
      · simp [it_zero]
      · rw [it_succ_front, Option.bind_some, h1, it_zero]
        simp
      · omega
  | cons e ys' ih =>
    intro b r L₀ hys hb hr hL₀
    obtain ⟨he, hys'⟩ := allOdd_cons.mp hys
    have hr_nev : ¬ r % 2 = 0 := by omega
    have hr_div : 2 * (r / 2) + 1 = r := by omega
    have h1 : highLevelNext (.F 0 b L₀ r (e :: (ys' ++ [1, 0]))) =
        some (.F 0 r (b :: L₀) e (ys' ++ [1, 0])) := by
      rw [highLevelNext]
      simp [hr_nev, hr_div]
    obtain ⟨hreach, hodd, hnb⟩ := ih r e (b :: L₀) hys' hr he (allOdd_cons.mpr ⟨hb, hL₀⟩)
    have hlist : (e :: ys').reverse ++ r :: b :: L₀ = ys'.reverse ++ e :: r :: b :: L₀ := by
      simp
    refine ⟨?_, hlist ▸ hodd, ?_⟩
    · rw [List.length_cons, show ys'.length + 1 + 2 = (ys'.length + 2) + 1 by omega,
        List.cons_append, it_succ_front, Option.bind_some, h1, hlist]
      exact hreach
    · intro k hk M
      rcases k with _ | k'
      · simp [it_zero]
      · rw [List.cons_append, it_succ_front, Option.bind_some, h1]
        exact hnb k' (by simp at hk; omega) M

private theorem drain_from_clause6_exact (a b : ℕ) (L₁ : List ℕ) (d : ℕ) (xs : List ℕ)
    (ha : a % 2 = 1) (hb : b % 2 = 0) (hL₁ : AllOdd L₁) (hd2 : 2 ≤ d) (hdev : d % 2 = 0)
    (hxs : AllOdd xs) :
    let L' := xs.reverse ++ (d - 1) :: a :: (b + 1) :: L₁
    it (xs.length + 6) (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) =
        some (.F 0 2 L' 1 []) ∧
      AllOdd L' ∧
      ∀ k < xs.length + 6, ∀ M,
        it k (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) ≠ some (.F 0 2 M 1 []) := by
  intro L'
  have hd0 : d ≠ 0 := by omega
  have hstep1 : highLevelNext (.F a b L₁ 0 (d :: (xs ++ [1, 0]))) =
      some (.F 0 (b + 1) L₁ a (((d - 1) :: xs) ++ [1, 0])) := by
    rw [highLevelNext]
    simp [hd0]
  obtain ⟨hdrain, hodd_raw, hnb_drain⟩ := drain_odds_exact ((d - 1) :: xs) (b + 1) a L₁
    (allOdd_cons.mpr ⟨by omega, hxs⟩) (by omega) ha hL₁
  have hL'_eq : ((d - 1) :: xs).reverse ++ a :: (b + 1) :: L₁ = L' := by
    simp [L']
  rw [hL'_eq] at hdrain hodd_raw
  rw [List.length_cons, show xs.length + 1 + 2 = xs.length + 3 by omega] at hdrain
  have hfin1 : highLevelNext (.F 0 1 L' 0 []) = some (.F 1 1 L' 0 [0]) := by
    rw [highLevelNext]
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
    exact exitC_succ 1 1 L' 0 []
  have hfin2 : highLevelNext (.F 1 1 L' 0 [0]) = some (.F 0 2 L' 1 []) := rfl
  have hs1 : it 1 (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) =
      some (.F 0 (b + 1) L₁ a (((d - 1) :: xs) ++ [1, 0])) := by
    rw [it_succ_front, Option.bind_some, hstep1, it_zero]
  have hs2 : it (xs.length + 4) (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) =
      some (.F 0 1 L' 0 []) := by
    rw [show xs.length + 4 = 1 + (xs.length + 3) by omega, it_add, hs1, hdrain]
  have hs3 : it (xs.length + 5) (some (.F a b L₁ 0 (d :: (xs ++ [1, 0])))) =
      some (.F 1 1 L' 0 [0]) := by
    rw [show xs.length + 5 = (xs.length + 4) + 1 by omega, it_add, hs2, it_succ_front,
      Option.bind_some, hfin1, it_zero]
  refine ⟨?_, hodd_raw, ?_⟩
  · rw [show xs.length + 6 = (xs.length + 5) + 1 by omega, it_add, hs3, it_succ_front,
      Option.bind_some, hfin2, it_zero]
  · intro k hk M
    by_cases hk0 : k = 0
    · subst hk0; simp [it_zero]
    · by_cases hk3 : k ≤ xs.length + 3
      · rw [show k = 1 + (k - 1) by omega, it_add, hs1]
        exact hnb_drain (k - 1) (by simp; omega) M
      · by_cases hk4 : k = xs.length + 4
        · subst hk4; rw [hs2]; simp
        · have hk5 : k = xs.length + 5 := by omega
          subst hk5; rw [hs3]; simp

private theorem chainMid_length (t q : ℕ) : (chainMid t q).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [chainMid, ih]

private theorem allOdd_chainMid (t q : ℕ) (hq : 1 ≤ q) : AllOdd (chainMid t q) := by
  induction t with
  | zero => exact allOdd_nil
  | succ t ih =>
    have hpow : 1 ≤ 2 ^ t * q := Nat.mul_pos (by positivity) hq
    have hmul : 2 ^ (t + 1) * q = 2 * (2 ^ t * q) := by rw [pow_succ]; ring
    exact allOdd_cons.mpr ⟨by rw [hmul]; omega, ih⟩

private theorem chainR_eq_reverse_chainMid (t q : ℕ) :
    ∀ R₀ : List ℕ, chainR (t + 1) q R₀ = (q - 1) :: ((chainMid t q).reverse ++ R₀) := by
  induction t with
  | zero =>
    intro R₀
    simp [chainR, chainMid]
  | succ t ih =>
    intro R₀
    change chainR (t + 1) q ((2 ^ (t + 1) * q - 1) :: R₀) =
      (q - 1) :: (((2 ^ (t + 1) * q - 1) :: chainMid t q).reverse ++ R₀)
    rw [ih ((2 ^ (t + 1) * q - 1) :: R₀)]
    simp

private def sweepStack (first : Bool) (xs : List ℕ) : List ℕ :=
  if first then [0] else xs ++ [1, 0]

private def remSteps (first : Bool) (xs : List ℕ) (p : ℕ) (L : List ℕ) : ℕ :=
  (if first then 5 else 5 + xs.length) + botGoSteps first p L

private theorem botGo_spec (L : List ℕ) :
    ∀ (first : Bool) (p : ℕ) (xs L_out : List ℕ),
      1 ≤ p → AllOdd L → AllOdd xs → (first = true → p = 1 ∧ xs = []) →
      botGo first p L = some L_out →
        it (remSteps first xs p L) (exitC 0 (2 * p) L 0 (sweepStack first xs)) =
            some (.F 0 2 (xs.reverse ++ L_out) 1 []) ∧
          AllOdd L_out ∧
          ∀ t < remSteps first xs p L, ∀ M,
            it t (exitC 0 (2 * p) L 0 (sweepStack first xs)) ≠ some (.F 0 2 M 1 []) := by
  induction L with
  | nil =>
    intro _ _ _ _ _ _ _ _ hgo
    simp [botGo] at hgo
  | cons u rest ih =>
    intro first p xs L_out hp hL hxs hfirst hgo
    obtain ⟨hu, hrest⟩ := allOdd_cons.mp hL
    obtain ⟨hpop, hpop_nb⟩ := odd_pop_step_and_no_bot p hp u rest (sweepStack first xs)
    by_cases hodd : (u + p) % 2 = 1
    · have hfirst_false : first = false := by
        rcases first with _ | _
        · rfl
        · obtain ⟨rfl, _⟩ := hfirst rfl
          omega
      subst hfirst_false
      have hp_ev : p % 2 = 0 := by omega
      have hp2 : 2 ≤ p := by omega
      simp only [botGo, hodd, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at hgo
      subst hgo
      have hrem : remSteps false xs p (u :: rest) = (p - 1) + (xs.length + 6) := by
        unfold remSteps botGoSteps
        simp only [hodd, ↓reduceIte, Bool.false_eq_true]
        omega
      have hexit_form :
          ∃ b₁ L₁, b₁ % 2 = 0 ∧ AllOdd L₁ ∧ (b₁ + 1) :: L₁ = bumpBelow rest ∧
            exitC 0 (u + p) rest 0 (p :: (xs ++ [1, 0])) =
              some (.F (u + p + 2) b₁ L₁ 0 (p :: (xs ++ [1, 0]))) := by
        have hb_ev : (u + p - 1) % 2 = 0 := by omega
        rcases rest with _ | ⟨v, rest'⟩
        · refine ⟨0, [], rfl, allOdd_nil, rfl, ?_⟩
          rw [show u + p = (u + p - 1) + 1 by omega, exitC_zero_nil]
          simp only [hb_ev, ↓reduceIte, show u + p - 1 + 3 = u + p + 2 by omega]
        · obtain ⟨hv, hrest'⟩ := allOdd_cons.mp hrest
          refine ⟨v + 1, rest', by omega, hrest', rfl, ?_⟩
          rw [show u + p = (u + p - 1) + 1 by omega, exitC_zero_cons]
          simp only [hb_ev, ↓reduceIte, show u + p - 1 + 3 = u + p + 2 by omega]
      obtain ⟨b₁, L₁, hb₁_ev, hL₁_odd, hbump, hexit⟩ := hexit_form
      obtain ⟨hdrain, hodd_all, hdrain_nb⟩ := drain_from_clause6_exact
        (u + p + 2) b₁ L₁ p xs (by omega) hb₁_ev hL₁_odd hp2 hp_ev hxs
      have hL_eq : xs.reverse ++ (p - 1) :: (u + p + 2) :: (b₁ + 1) :: L₁ =
          xs.reverse ++ ([p - 1] ++ (u + p + 2) :: bumpBelow rest) := by
        simp [hbump]
      rw [hL_eq] at hdrain hodd_all
      refine ⟨?_, (allOdd_append.mp hodd_all).2, ?_⟩
      · rw [hrem, it_add, hpop]
        exact hexit ▸ hdrain
      · intro t ht M
        by_cases hlt : t < p - 1
        · exact hpop_nb t hlt M
        · rw [show t = (p - 1) + (t - (p - 1)) by omega, it_add, hpop,
            show sweepStack false xs = xs ++ [1, 0] from rfl, hexit]
          exact hdrain_nb (t - (p - 1)) (by omega) M
    · have hev : (u + p) % 2 = 0 := by omega
      set xs_next : List ℕ := if first then [] else p :: xs
      have hR_next : p :: sweepStack first xs = xs_next ++ [1, 0] := by
        rcases first with _ | _
        · rfl
        · obtain ⟨rfl, rfl⟩ := hfirst rfl
          rfl
      have hxs_next_odd : AllOdd xs_next := by
        rcases first with _ | _
        · exact allOdd_cons.mpr ⟨by omega, hxs⟩
        · exact allOdd_nil
      have hxs_next_rev : xs_next.reverse = xs.reverse ++ (if first then [] else [p]) := by
        rcases first with _ | _
        · simp [xs_next]
        · obtain ⟨rfl, rfl⟩ := hfirst rfl
          rfl
      have hxs_next_len :
          (if first then 5 else 5 + xs.length) + (if first then 0 else p) =
            (p - 1) + (5 + xs_next.length) := by
        rcases first with _ | _
        · simp [xs_next]
          omega
        · obtain ⟨rfl, rfl⟩ := hfirst rfl
          rfl
      rcases rest with _ | ⟨v, rest'⟩
      · rw [botGo] at hgo
        simp only [hodd, ↓reduceIte] at hgo
        set V := u + p + 2
        set ν := padicValNat 2 V
        set q := V / 2 ^ ν
        have hq_ne1 : q ≠ 1 := by
          intro hq1
          simp [hq1] at hgo
        simp only [hq_ne1, ↓reduceIte, Option.some.injEq] at hgo
        subst hgo
        obtain ⟨hV_eq, hq_pos, hq_odd, hq1_iff⟩ := odd_part_properties V (by omega)
        have hV_eq' : V = 2 ^ ν * q := hV_eq
        have hq_pos' : 0 < q := hq_pos
        have hq_odd' : q % 2 = 1 := hq_odd
        have hV_npow : ¬ ∃ k, V = 2 ^ k := fun hpow => hq_ne1 (hq1_iff.mpr hpow)
        have hq3 : 3 ≤ q := by omega
        have hV_ev : V % 2 = 0 := by omega
        have hV6 : 6 ≤ V := by
          by_contra hlt6
          have hV4 : V = 4 := by omega
          exact hV_npow ⟨2, by omega⟩
        have h2dvdV : 2 ^ 1 ∣ V := by simpa using Nat.dvd_of_mod_eq_zero hV_ev
        have hν1 : 1 ≤ ν := (padicValNat_dvd_iff_le (by omega)).mp h2dvdV
        set tν := ν - 1
        have hν_eq : ν = tν + 1 := by omega
        have h2ν_le : 2 * ν ≤ 2 ^ ν := by
          rw [hν_eq]
          exact two_mul_le_two_pow_succ tν
        have hP2 : 2 ≤ 2 ^ ν := by omega
        have hVq_lt : q + 2 * ν < V := by nlinarith
        set xs_drain := (chainMid tν q).reverse ++ xs_next
        have hxs_drain_odd : AllOdd xs_drain :=
          allOdd_append.mpr ⟨allOdd_reverse.mpr (allOdd_chainMid tν q hq_pos'), hxs_next_odd⟩
        have hxs_drain_len : xs_drain.length = tν + xs_next.length := by
          simp [xs_drain, chainMid_length]
        have hrem : remSteps first xs p [u] =
            (p - 1) + (V - q - 2 * ν) + (xs_drain.length + 6) := by
          unfold remSteps botGoSteps
          simp only [hodd, ↓reduceIte]
          change (if first then 5 else 5 + xs.length) + ((if first then 0 else p) + (V - q - ν)) =
            (p - 1) + (V - q - 2 * ν) + (xs_drain.length + 6)
          rw [← add_assoc, hxs_next_len, hxs_drain_len]
          omega
        have hexit_ce : exitC 0 (u + p) [] 0 (xs_next ++ [1, 0]) =
            some (.F (V - 5) 0 [] 0 (0 :: 1 :: (xs_next ++ [1, 0]))) := by
          rw [show u + p = V - 2 by omega,
            exitC_empty_even_eq_chainEntry V (xs_next ++ [1, 0]) (by omega) hV_ev]
          unfold chainEntry
          have hnot4 : ¬ V ≤ 4 := by omega
          simp only [hnot4, ↓reduceIte]
        have hcex := chain_exit_of_not_powerOfTwo V (xs_next ++ [1, 0]) hV6 hV_ev hV_npow
        change it (V - q - 2 * ν) (some (.F (V - 5) 0 [] 0 (0 :: 1 :: (xs_next ++ [1, 0])))) =
          some (.F q 0 [] 0 (chainR ν q (xs_next ++ [1, 0]))) at hcex
        have hcR : chainR ν q (xs_next ++ [1, 0]) = (q - 1) :: (xs_drain ++ [1, 0]) := by
          rw [hν_eq, chainR_eq_reverse_chainMid]
          simp [xs_drain, List.append_assoc]
        rw [hcR] at hcex
        obtain ⟨hdrain, hodd_all, hdrain_nb⟩ := drain_from_clause6_exact
          q 0 [] (q - 1) xs_drain hq_odd' rfl allOdd_nil (by omega) (by omega) hxs_drain_odd
        have hstack_eq :
            xs_drain.reverse ++ (q - 1 - 1) :: q :: (0 + 1) :: [] =
              xs.reverse ++ ((if first then [] else [p]) ++ chainTail ν q) := by
          rw [show q - 1 - 1 = q - 2 by omega, show 0 + 1 = 1 by omega]
          simp only [xs_drain, chainTail, tν, List.reverse_append, List.reverse_reverse,
            hxs_next_rev, List.append_assoc]
        rw [hstack_eq] at hdrain hodd_all
        refine ⟨?_, (allOdd_append.mp hodd_all).2, ?_⟩
        · rw [hrem, it_add, it_add (p - 1) (V - q - 2 * ν), hpop, hR_next, hexit_ce, hcex, hdrain]
        · intro t ht M
          rw [hrem] at ht
          by_cases hlt1 : t < p - 1
          · exact hpop_nb t hlt1 M
          · by_cases hlt2 : t < (p - 1) + (V - q - 2 * ν)
            · rw [show t = (p - 1) + (t - (p - 1)) by omega, it_add, hpop, hR_next, hexit_ce]
              have hcnb := chain_aux_no_bot tν q hq3 hq_odd' (xs_next ++ [1, 0]) (t - (p - 1))
              rw [← hν_eq, ← hV_eq'] at hcnb
              exact hcnb (by omega) M
            · rw [show t = ((p - 1) + (V - q - 2 * ν)) + (t - ((p - 1) + (V - q - 2 * ν)))
                  by omega,
                it_add, it_add, hpop, hR_next, hexit_ce, hcex]
              exact hdrain_nb _ (by omega) M
      · set p' := (u + p) / 2
        have hp' : 1 ≤ p' := by omega
        have hup : u + p = 2 * p' := by omega
        simp only [botGo, hodd, ↓reduceIte, Option.map_eq_some_iff] at hgo
        obtain ⟨L_rec, hgo_rec, rfl⟩ := hgo
        obtain ⟨hrec, hodd_rec, hnb_rec⟩ := ih false p' xs_next L_rec hp' hrest hxs_next_odd
          (by simp) hgo_rec
        have hrem : remSteps first xs p (u :: v :: rest') =
            (p - 1) + remSteps false xs_next p' (v :: rest') := by
          simp only [remSteps]
          rw [botGoSteps]
          simp only [hodd, Bool.false_eq_true, ↓reduceIte]
          rw [← add_assoc, hxs_next_len, add_assoc]
        have hstack_eq : xs_next.reverse ++ L_rec =
            xs.reverse ++ ((if first then [] else [p]) ++ L_rec) := by
          simp [hxs_next_rev, List.append_assoc]
        refine ⟨?_, ?_, ?_⟩
        · rw [hrem, it_add, hpop, hup, hR_next]
          change it (remSteps false xs_next p' (v :: rest'))
            (exitC 0 (2 * p') (v :: rest') 0 (sweepStack false xs_next)) = _
          rw [hrec, hstack_eq]
        · rcases first with _ | _
          · exact allOdd_cons.mpr ⟨by omega, hodd_rec⟩
          · simpa using hodd_rec
        · intro t ht M
          by_cases hlt : t < p - 1
          · exact hpop_nb t hlt M
          · rw [show t = (p - 1) + (t - (p - 1)) by omega, it_add, hpop, hup, hR_next]
            exact hnb_rec (t - (p - 1)) (by omega) M

/-- One cycle. From a bottom reach with an all-odd stack `L`, if `botStep L = some L'`, then
exactly `botSteps L` high-level steps later the machine is at the bottom reach with stack `L'`,
and `L'` is again all odd. -/
theorem botStep_reaches (L L' : List ℕ) (hL : AllOdd L) (h : botStep L = some L') :
    (Option.bind · highLevelNext)^[botSteps L] (some (.F 0 2 L 1 [])) =
        some (.F 0 2 L' 1 []) ∧
      AllOdd L' := by
  obtain ⟨hreach, hodd, _⟩ := botGo_spec L true 1 [] L' (le_refl 1) hL allOdd_nil
    (fun _ => ⟨rfl, rfl⟩) h
  refine ⟨?_, hodd⟩
  change it (botSteps L) (some (.F 0 2 L 1 [])) = some (.F 0 2 L' 1 [])
  have hsteps : botSteps L = 1 + remSteps true [] 1 L := by
    unfold botSteps remSteps
    simp
    omega
  have hs0 : it 1 (some (.F 0 2 L 1 [])) = exitC 0 (2 * 1) L 0 (sweepStack true []) := rfl
  rw [hsteps, it_add, hs0, hreach]
  rfl

private def paddedWp (p : ℕ) (L : List ℕ) : ℕ := p + weightedSum L + 2 ^ L.length

private theorem paddedWp_one (L : List ℕ) : paddedWp 1 L = paddedW L := by
  unfold paddedWp paddedW W
  ring

private theorem paddedWp_pos (p : ℕ) (L : List ℕ) : 0 < paddedWp p L := by
  have : 0 < 2 ^ L.length := by positivity
  unfold paddedWp
  omega

private theorem botGo_eq_none_iff (L : List ℕ) :
    ∀ (first : Bool) (p : ℕ), 1 ≤ p → L ≠ [] → AllOdd L →
      (botGo first p L = none ↔ ∃ k, paddedWp p L = 2 ^ k) := by
  induction L with
  | nil =>
    intro _ _ _ hne
    exact absurd rfl hne
  | cons u rest ih =>
    intro first p hp _ hL
    obtain ⟨hu, hrest⟩ := allOdd_cons.mp hL
    by_cases hodd : (u + p) % 2 = 1
    · simp only [botGo, hodd, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨k, hk⟩
      have hgt1 : 1 < paddedWp p (u :: rest) := by
        have : 0 < 2 ^ rest.length := by positivity
        simp only [paddedWp, weightedSum, List.length_cons, pow_succ]
        omega
      have hmod : paddedWp p (u :: rest) % 2 = 1 := by
        simp only [paddedWp, weightedSum, List.length_cons, pow_succ]
        omega
      rcases k with _ | k
      · omega
      · rw [pow_succ] at hk
        omega
    · rcases rest with _ | ⟨v, rest'⟩
      · have hV : paddedWp p [u] = u + p + 2 := by
          simp [paddedWp, weightedSum]
          omega
        obtain ⟨_, _, _, hq1_iff⟩ := odd_part_properties (u + p + 2) (by omega)
        rw [botGo]
        simp only [hodd, ↓reduceIte, hV]
        by_cases hq1 : (u + p + 2) / 2 ^ padicValNat 2 (u + p + 2) = 1
        · simp only [hq1, ↓reduceIte, true_iff]
          exact hq1_iff.mp hq1
        · simp only [hq1, ↓reduceIte, reduceCtorEq, false_iff]
          exact fun hpow => hq1 (hq1_iff.mpr hpow)
      · set p' := (u + p) / 2
        have hp' : 1 ≤ p' := by omega
        have hdouble : paddedWp p (u :: v :: rest') = 2 * paddedWp p' (v :: rest') := by
          simp only [paddedWp, weightedSum, List.length_cons, pow_succ]
          omega
        rw [botGo]
        simp only [hodd, ↓reduceIte, Option.map_eq_none_iff]
        rw [ih false p' hp' (List.cons_ne_nil _ _) hrest, hdouble]
        simpa using (exists_pow2_mul_iff 1 (paddedWp p' (v :: rest'))
          (paddedWp_pos p' (v :: rest'))).symm

/-- The cycle map halts exactly on the stacks whose padded sum is a power of two. -/
theorem botStep_eq_none_iff (L : List ℕ) (hL : AllOdd L) :
    botStep L = none ↔ ∃ p, paddedW L = 2 ^ p := by
  rcases L with _ | ⟨u, rest⟩
  · simp only [botStep, botGo, true_iff]
    exact ⟨1, by decide⟩
  · rw [botStep, botGo_eq_none_iff (u :: rest) true 1 (le_refl 1) (List.cons_ne_nil _ _) hL,
      paddedWp_one]

private theorem botStep_orbit_exists (n : ℕ) :
    ∀ L : List ℕ, (Option.bind · botStep)^[n] (some [5, 5, 1]) = some L →
      ∃ t, 27 + 6 * n ≤ t ∧
        (Option.bind · highLevelNext)^[t] (some highLevelStart) = some (.F 0 2 L 1 []) := by
  induction n with
  | zero =>
    intro L h
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    exact ⟨27, by omega, orbit_step27⟩
  | succ n ih =>
    intro L h
    rw [Function.iterate_succ_apply'] at h
    rcases hn : (Option.bind · botStep)^[n] (some [5, 5, 1]) with _ | L₀
    · simp [hn] at h
    · rw [hn, Option.bind_some] at h
      obtain ⟨t, ht, hreach⟩ := ih L₀ hn
      have hL₀ : AllOdd L₀ := allOdd_of_bottomReach t L₀ hreach
      have hstep := (botStep_reaches L₀ L hL₀ h).1
      refine ⟨t + botSteps L₀, by unfold botSteps; omega, ?_⟩
      change it (t + botSteps L₀) (some highLevelStart) = some (.F 0 2 L 1 [])
      rw [it_add]
      change it (botSteps L₀) ((Option.bind · highLevelNext)^[t] (some highLevelStart)) = _
      rw [hreach]
      exact hstep

/-- Global criterion on the stack alone: the machine halts from the blank tape if and only if
iterating `botStep` from the first bottom reach `[5, 5, 1]` ever returns `none`. -/
theorem isHalt_iff_botStep : IsHalt target ↔ CollatzHalts botStep [5, 5, 1] := by
  constructor
  · intro hhalt
    obtain ⟨T, hT⟩ :=
      BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.isHalt_iff_highLevel_acceleration.mp
        hhalt
    rw [Option.isNone_iff_eq_none] at hT
    by_contra hnh
    have hnot_none : ((Option.bind · botStep)^[T] (some [5, 5, 1])).isNone ≠ true :=
      fun h => hnh ⟨T, h⟩
    rcases hBT : (Option.bind · botStep)^[T] (some [5, 5, 1]) with _ | L
    · simp [hBT] at hnot_none
    · obtain ⟨t, ht, hreach⟩ := botStep_orbit_exists T L hBT
      have hsplit : t = T + (t - T) := by omega
      change it t (some highLevelStart) = some (.F 0 2 L 1 []) at hreach
      change it T (some highLevelStart) = none at hT
      rw [hsplit, it_add, hT, it_none] at hreach
      simp at hreach
  · rintro ⟨n, hn⟩
    have hex : ∃ k L, (Option.bind · botStep)^[k] (some [5, 5, 1]) = some L ∧
        botStep L = none := by
      induction n with
      | zero => simp at hn
      | succ n ih =>
        rw [Function.iterate_succ_apply'] at hn
        rcases hprev : (Option.bind · botStep)^[n] (some [5, 5, 1]) with _ | L
        · exact ih (by simp [hprev])
        · rw [hprev, Option.bind_some, Option.isNone_iff_eq_none] at hn
          exact ⟨n, L, hprev, hn⟩
    obtain ⟨k, L, hk, hnone⟩ := hex
    obtain ⟨t, _, hreach⟩ := botStep_orbit_exists k L hk
    have hL : AllOdd L := allOdd_of_bottomReach t L hreach
    exact isHalt_iff_bottomReach_powerOfTwo.mpr ⟨t, L, hreach, (botStep_eq_none_iff L hL).mp hnone⟩

/-- The high-level step at which the `n`-th cycle starts: `27`, then the sum of the cycle
lengths. -/
def botTime : ℕ → ℕ
  | 0 => 27
  | n + 1 => botTime n + (((Option.bind · botStep)^[n] (some [5, 5, 1])).elim 0 botSteps)

/-- The orbit of `botStep` is the sequence of bottom reaches of the machine, with exact times:
if the `n`-th iterate is `some L`, the high-level orbit is at `F 0 2 L 1 []` at step
`botTime n`. -/
theorem botStep_orbit (n : ℕ) (L : List ℕ)
    (h : (Option.bind · botStep)^[n] (some [5, 5, 1]) = some L) :
    (Option.bind · highLevelNext)^[botTime n] (some highLevelStart) = some (.F 0 2 L 1 []) := by
  induction n generalizing L with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    exact orbit_step27
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    rcases hn : (Option.bind · botStep)^[n] (some [5, 5, 1]) with _ | L₀
    · simp [hn] at h
    · rw [hn, Option.bind_some] at h
      have hreach := ih L₀ hn
      have hL₀ : AllOdd L₀ := allOdd_of_bottomReach (botTime n) L₀ hreach
      have hstep := (botStep_reaches L₀ L hL₀ h).1
      simp only [botTime, hn, Option.elim_some]
      change it (botTime n + botSteps L₀) (some highLevelStart) = some (.F 0 2 L 1 [])
      rw [it_add]
      change it (botSteps L₀) ((Option.bind · highLevelNext)^[botTime n] (some highLevelStart)) = _
      rw [hreach]
      exact hstep

/-- No bottom reach strictly inside a cycle: `botStep` is the first-return map. -/
theorem botStep_no_earlier (L L' M : List ℕ) (hL : AllOdd L) (h : botStep L = some L')
    (t : ℕ) (ht0 : 0 < t) (ht : t < botSteps L) :
    (Option.bind · highLevelNext)^[t] (some (.F 0 2 L 1 [])) ≠ some (.F 0 2 M 1 []) := by
  obtain ⟨_, _, hnb⟩ := botGo_spec L true 1 [] L' (le_refl 1) hL allOdd_nil
    (fun _ => ⟨rfl, rfl⟩) h
  have hsteps : botSteps L = 1 + remSteps true [] 1 L := by
    unfold botSteps remSteps
    simp
    omega
  have hs0 : it 1 (some (.F 0 2 L 1 [])) = exitC 0 (2 * 1) L 0 (sweepStack true []) := rfl
  change it t (some (.F 0 2 L 1 [])) ≠ some (.F 0 2 M 1 [])
  rw [show t = 1 + (t - 1) by omega, it_add, hs0]
  exact hnb (t - 1) (by omega) M

end AntihydraOrbit.Line116
