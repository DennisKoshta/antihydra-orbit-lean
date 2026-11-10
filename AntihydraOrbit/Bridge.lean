import AntihydraOrbit.Defs

/-!
# Helper lemmas for the bridge (section A of `Statements.lean`)

Orbit facts, the counter process along the orbit, and the macro steps of the DeepMind
acceleration `next` between two returns to `c = 1`.
-/

namespace AntihydraOrbit

open BusyBeaver
open BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA (State next start)

/-! ### The orbit -/

theorem X_zero : X 0 = 8 := rfl

theorem X_succ (n : ℕ) : X (n + 1) = H (X n) := by
  simp [X, Function.iterate_succ_apply']

theorem X_ge (n : ℕ) : 8 ≤ X n := by
  induction n with
  | zero => simp [X_zero]
  | succ n ih => rw [X_succ]; unfold H; omega

theorem evens_zero : evens 0 = 0 := by simp [evens]
theorem odds_zero : odds 0 = 0 := by simp [odds]

theorem evens_succ (n : ℕ) :
    evens (n + 1) = evens n + (if X n % 2 = 0 then 1 else 0) := by
  unfold evens
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : X n % 2 = 0
  · simp [h]
  · simp [h]

theorem odds_succ (n : ℕ) :
    odds (n + 1) = odds n + (if X n % 2 = 1 then 1 else 0) := by
  unfold odds
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : X n % 2 = 1
  · simp [h]
  · simp [h]

/-! ### The counter process along the orbit -/

/-- The `n`-th state of the counter process from `(8, 0)`. -/
def S (n : ℕ) : Option (ℕ × ℕ) := ((Option.bind · step)^[n] (some (8, 0)))

theorem S_zero : S 0 = some (8, 0) := rfl

theorem S_succ (n : ℕ) : S (n + 1) = (S n).bind step := by
  simp [S, Function.iterate_succ_apply']

theorem S_none_persist {n : ℕ} (h : S n = none) (m : ℕ) : S (n + m) = none := by
  induction m with
  | zero => simpa using h
  | succ m ih => rw [← Nat.add_assoc, S_succ, ih]; rfl

/-- Along the orbit the counter process is at `(X n, 2·evens n - odds n)` for as long as no
earlier prefix was odd-heavy. -/
theorem S_eq (n : ℕ) (h : ∀ j < n, odds (j + 1) ≤ 2 * evens (j + 1)) :
    S n = some (X n, 2 * evens n - odds n) := by
  induction n with
  | zero => simp [S_zero, X_zero, evens_zero, odds_zero]
  | succ n ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    have hn0 : odds n ≤ 2 * evens n := by
      rcases n with _ | n
      · simp [odds_zero]
      · exact h n (by omega)
    rw [S_succ, ih']
    rw [evens_succ, odds_succ] at hn ⊢
    simp only [Option.bind_some, step]
    by_cases he : X n % 2 = 0
    · simp [he, X_succ]
      omega
    · have ho : X n % 2 = 1 := by omega
      simp [ho] at hn ⊢
      have hb : 2 * evens n - odds n ≠ 0 := by omega
      simp [hb, X_succ]
      omega

/-! ### The macro steps of the acceleration `next` -/

/-- `m` steps of the acceleration. -/
def it (m : ℕ) (o : Option State) : Option State := (Option.bind · next)^[m] o

theorem it_zero (o : Option State) : it 0 o = o := rfl

theorem it_succ_front (m : ℕ) (o : Option State) : it (m + 1) o = it m (o.bind next) := by
  simp [it, Function.iterate_succ_apply]

theorem it_succ_back (m : ℕ) (o : Option State) : it (m + 1) o = (it m o).bind next := by
  simp [it, Function.iterate_succ_apply']

theorem it_add (m m' : ℕ) (o : Option State) : it (m' + m) o = it m' (it m o) :=
  Function.iterate_add_apply _ _ _ _

theorem it_none (m : ℕ) : it m none = none := by
  unfold it
  exact Function.iterate_fixed rfl m

theorem it_rule (k a j c : ℕ) :
    it k (some (.P a (2 * k + j + 1) c)) = some (.P a (j + 1) (c + 3 * k)) := by
  induction k generalizing c with
  | zero => simp [it_zero]
  | succ k ih =>
    have e : 2 * (k + 1) + j + 1 = (2 * k + j) + 3 := by ring
    rw [it_succ_front, e]
    have hn : (some (State.P a (2 * k + j + 3) c)).bind next
        = some (State.P a (2 * k + j + 1) (c + 3)) := by
      simp [next]
    rw [hn, ih]
    have e2 : c + 3 + 3 * k = c + 3 * (k + 1) := by ring
    rw [e2]

theorem macro_even (a x : ℕ) (hx : 6 ≤ x) (he : x % 2 = 0) :
    ∃ m ≥ 1, it m (some (.P a (x - 5) 1)) = some (.P (a + 2) (H x - 5) 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 6 := ⟨(x - 6) / 2, by omega⟩
  have h1 : 2 * k + 6 - 5 = 2 * k + 0 + 1 := by omega
  have h2 : H (2 * k + 6) - 5 = 1 + 3 * k + 3 := by unfold H; omega
  refine ⟨k + 1, by omega, ?_⟩
  rw [h1, h2, it_succ_back, it_rule k a 0 1]
  simp [next]

theorem macro_odd_pos (a x : ℕ) (hx : 7 ≤ x) (ho : x % 2 = 1) :
    ∃ m ≥ 1, it m (some (.P (a + 1) (x - 5) 1)) = some (.P a (H x - 5) 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 7 := ⟨(x - 7) / 2, by omega⟩
  have h1 : 2 * k + 7 - 5 = 2 * k + 1 + 1 := by omega
  have h2 : H (2 * k + 7) - 5 = 1 + 3 * k + 4 := by unfold H; omega
  refine ⟨k + 1, by omega, ?_⟩
  rw [h1, h2, it_succ_back, it_rule k (a + 1) 1 1]
  simp [next]

theorem macro_odd_zero (x : ℕ) (hx : 7 ≤ x) (ho : x % 2 = 1) :
    ∃ m, it m (some (.P 0 (x - 5) 1)) = none := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 7 := ⟨(x - 7) / 2, by omega⟩
  have h1 : 2 * k + 7 - 5 = 2 * k + 1 + 1 := by omega
  refine ⟨k + 1, ?_⟩
  rw [h1, it_succ_back, it_rule k 0 1 1]
  simp [next]

/-! ### The acceleration along the orbit -/

/-- Along the orbit, `next` passes through `P(2·evens n - odds n, X n - 5, 1)` (after at least `n`
steps), for as long as no earlier prefix was odd-heavy. -/
theorem reach (n : ℕ) (h : ∀ j < n, odds (j + 1) ≤ 2 * evens (j + 1)) :
    ∃ m ≥ n, it m (some start) = some (.P (2 * evens n - odds n) (X n - 5) 1) := by
  induction n with
  | zero => exact ⟨0, le_refl _, by simp [it_zero, start, X_zero, evens_zero, odds_zero]⟩
  | succ n ih =>
    obtain ⟨m, hm, e⟩ := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    have hn0 : odds n ≤ 2 * evens n := by
      rcases n with _ | n
      · simp [odds_zero]
      · exact h n (by omega)
    have hX := X_ge n
    rw [evens_succ, odds_succ] at hn ⊢
    by_cases he : X n % 2 = 0
    · obtain ⟨m', hm', e'⟩ := macro_even (2 * evens n - odds n) (X n) (by omega) he
      refine ⟨m' + m, by omega, ?_⟩
      rw [it_add, e, e', X_succ]
      simp [he]
      omega
    · have ho : X n % 2 = 1 := by omega
      simp [ho] at hn ⊢
      obtain ⟨a, ha⟩ : ∃ a, 2 * evens n - odds n = a + 1 := ⟨2 * evens n - odds n - 1, by omega⟩
      obtain ⟨m', hm', e'⟩ := macro_odd_pos a (X n) (by omega) ho
      refine ⟨m' + m, by omega, ?_⟩
      rw [it_add, e, ha, e', X_succ]
      simp
      omega

/-- The first odd-heavy prefix: all earlier ones are fine, and it comes right after an odd term
with the counter at 0. -/
theorem first_bad (hb : ∃ n, 2 * evens n < odds n) :
    ∃ m, (∀ j ≤ m, odds j ≤ 2 * evens j) ∧ X m % 2 = 1 ∧ odds m = 2 * evens m ∧
      ∀ n, 2 * evens n < odds n → m + 1 ≤ n := by
  classical
  let n0 := Nat.find hb
  have h0 : 2 * evens n0 < odds n0 := Nat.find_spec hb
  have hmin : ∀ j < n0, ¬ 2 * evens j < odds j := fun j hj => Nat.find_min hb hj
  have hpos : n0 ≠ 0 := by
    intro h; rw [h] at h0; simp [evens_zero, odds_zero] at h0
  obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
  have h1 := hmin m (by omega)
  rw [hm, evens_succ, odds_succ] at h0
  have hodd : X m % 2 = 1 := by
    by_contra hne
    have he : X m % 2 = 0 := by omega
    simp [he] at h0; omega
  have hodd2 : ¬ X m % 2 = 0 := by omega
  simp [hodd] at h0
  exact ⟨m, fun j hj => by have := hmin j (by omega); omega, hodd, by omega, fun n hn => by have := Nat.find_min' hb hn; have h' : Nat.find hb = m + 1 := hm; omega⟩

theorem never_none (h : ∀ n, odds n ≤ 2 * evens n) (m : ℕ) : it m (some start) ≠ none := by
  intro hm
  obtain ⟨m', hm', e⟩ := reach m (fun j _ => h (j + 1))
  obtain ⟨d, rfl⟩ : ∃ d, m' = d + m := ⟨m' - m, by omega⟩
  rw [it_add, hm, it_none] at e
  exact absurd e (by simp)

theorem halts_of_bad (hb : ∃ n, 2 * evens n < odds n) : ∃ m, it m (some start) = none := by
  obtain ⟨m, hle, hodd, heq, -⟩ := first_bad hb
  obtain ⟨m1, -, e⟩ := reach m (fun j hj => by
    have := hle (j + 1) (by omega); exact this)
  have ha : 2 * evens m - odds m = 0 := by omega
  rw [ha] at e
  obtain ⟨m2, e2⟩ := macro_odd_zero (X m) (by have := X_ge m; omega) hodd
  exact ⟨m2 + m1, by rw [it_add, e, e2]⟩

theorem step_halts_iff_bad : (∃ n, (S n).isNone) ↔ ∃ n, 2 * evens n < odds n := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra hb
    push Not at hb
    rw [S_eq n (fun j _ => hb (j + 1))] at hn
    simp at hn
  · intro hb
    obtain ⟨m, hle, hodd, heq, -⟩ := first_bad hb
    refine ⟨m + 1, ?_⟩
    rw [S_succ, S_eq m (fun j hj => by have := hle (j + 1) (by omega); exact this)]
    have hX : ¬ X m % 2 = 0 := by omega
    have hb0 : 2 * evens m - odds m = 0 := by omega
    simp [step, hX, hb0]

end AntihydraOrbit
