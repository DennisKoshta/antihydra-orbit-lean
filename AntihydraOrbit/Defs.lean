import Mathlib
import BusyBeaver.BB6.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA

/-!
# The Antihydra orbit: definitions

Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) halts if and only if the orbit of `8` under
`x ↦ ⌊3x/2⌋` has a prefix with more than twice as many odd terms as even terms.
This file fixes the definitions used to state that. They are the trusted base: keep them short
and do not change them without saying so.
-/

namespace AntihydraOrbit

/-- The Hydra map `H x = ⌊3x/2⌋`. -/
def H (x : ℕ) : ℕ := 3 * x / 2

/-- The Antihydra orbit: `X 0 = 8` and `X (n+1) = ⌊3 · X n / 2⌋`. -/
def X (n : ℕ) : ℕ := H^[n] 8

/-- The number of even terms among `X 0, …, X (n-1)`. -/
def evens (n : ℕ) : ℕ := ((Finset.range n).filter fun k => X k % 2 = 0).card

/-- The number of odd terms among `X 0, …, X (n-1)`. -/
def odds (n : ℕ) : ℕ := ((Finset.range n).filter fun k => X k % 2 = 1).card

/-- One step of the counter process on pairs `(x, b)`: an even `x` adds 2 to the counter `b`,
an odd `x` takes 1 away, and the process stops (`none`) at an odd `x` with `b = 0`. -/
def step : ℕ × ℕ → Option (ℕ × ℕ)
  | (x, b) =>
    if x % 2 = 0 then some (H x, b + 2)
    else if b = 0 then none
    else some (H x, b - 1)

/-- The counter process started at `(x, b)` has stopped within `n` steps. -/
def StopsWithin (n x b : ℕ) : Prop := ((Option.bind · step)^[n] (some (x, b))).isNone

/-- Mahler's map `z ↦ ⌈3z/2⌉`, the same orbit shifted by one (`X n = Z n + 1`). -/
def M (z : ℕ) : ℕ := (3 * z + 1) / 2

/-- The orbit of `7` under Mahler's map. -/
def Z (n : ℕ) : ℕ := M^[n] 7

/-- The walk read off a parity word (`true` = even term, `false` = odd term) from counter `b`:
does it ever meet an odd term with the counter at 0? -/
def wordStops : List Bool → ℕ → Bool
  | [], _ => false
  | true :: w, b => wordStops w (b + 2)
  | false :: _, 0 => true
  | false :: w, b + 1 => wordStops w b

end AntihydraOrbit
