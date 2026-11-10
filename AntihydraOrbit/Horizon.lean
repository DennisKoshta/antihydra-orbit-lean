import AntihydraOrbit.Defs
import AntihydraOrbit.Bridge

/-!
# A kernel-checked horizon (section C)

`adv d s` runs the counter process `2^d` steps from `s`, splitting the range in halves, so the
kernel's recursion depth is about `d` levels instead of `2^d`. `no_stop_pow d` is the Boolean
check; its soundness theorem turns it into a statement about `odds` and `evens`.
-/

namespace AntihydraOrbit.Aux

/-- Run `2^d` steps of the counter process from `s`, halving the range. -/
def adv : ℕ → ℕ × ℕ → Option (ℕ × ℕ)
  | 0, s => step s
  | d + 1, s => (adv d s).bind (adv d)

theorem adv_eq (d : ℕ) (s : ℕ × ℕ) : adv d s = (Option.bind · step)^[2 ^ d] (some s) := by
  induction d generalizing s with
  | zero => simp [adv]
  | succ d ih =>
    rw [pow_succ, mul_two, Function.iterate_add_apply, ← ih]
    simp only [adv]
    cases adv d s with
    | none => exact (Function.iterate_fixed rfl _).symm
    | some t => simp [ih]

/-- The Boolean check: the process from `(8,0)` has not stopped after `2^d` steps. -/
def noStop (d : ℕ) : Bool := (adv d (8, 0)).isSome

theorem noStop_sound (d : ℕ) (h : noStop d = true) : ∀ n ≤ 2 ^ d, odds n ≤ 2 * evens n := by
  intro n hn
  by_contra hb
  push Not at hb
  obtain ⟨m, hle, hodd, heq, hfirst⟩ := first_bad ⟨n, hb⟩
  have h1 : S (m + 1) = none := by
    rw [S_succ, S_eq m (fun j hj => by have := hle (j + 1) (by omega); exact this)]
    have hX : ¬ X m % 2 = 0 := by omega
    have hb0 : 2 * evens m - odds m = 0 := by omega
    simp [step, hX, hb0]
  have h2 : S (2 ^ d) = none := by
    have := S_none_persist h1 (2 ^ d - (m + 1))
    have e : m + 1 + (2 ^ d - (m + 1)) = 2 ^ d := by have := hfirst n hb; omega
    rwa [e] at this
  unfold noStop at h
  rw [adv_eq] at h
  have : S (2 ^ d) = (Option.bind · step)^[2 ^ d] (some (8, 0)) := rfl
  rw [← this, h2] at h
  simp at h

end AntihydraOrbit.Aux
