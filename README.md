# The Antihydra orbit in Lean 4

Antihydra is the 6-state Turing machine

```
1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA
```

Nobody knows whether it halts. It is one of the machines that stand between us and the value of
BB(6).

This package proves three things in Lean 4 with Mathlib.

1. The machine halts exactly when a simple integer sequence has a certain property. This is the
   known description of Antihydra, here checked all the way down to the machine.
2. Several facts about that sequence, among them two reasons why simple arguments cannot settle
   the question.
3. A count. If the same process is started at an arbitrary number instead of 8, at least 61.8% of
   the start values stop. This count was known on the bbchallenge Discord; the package proves it
   in Lean, for every starting value of the counter.

It does **not** prove that Antihydra never halts. The third result is about the family of all
start values and says nothing about the start value 8.

The package has a second part, about nine other open machines of BB(6). For each one it proves an
exact criterion: the machine halts if and only if its orbit reaches a state of an explicit form.
For five of them a number computed from a stack has to be a power of two. For the other four a
number has to lie in an explicit sparse sequence, such as `20 · 2^j - 2j - 16`. That says when
each machine halts, not whether it does. See "Nine related machines" below.

Every theorem is checked by the Lean kernel and depends only on the three standard axioms.

## The reduction

Let `H x = ⌊3x/2⌋` and `X n = H^[n] 8`, so the sequence is 8, 12, 18, 27, 40, 60, ...
Let `evens n` and `odds n` count the even and the odd terms among `X 0, ..., X (n-1)`.

```lean
theorem antihydra_isHalt_iff :
    IsHalt target ↔ ∃ n, 2 * evens n < odds n

theorem antihydra_isNotHalt_iff :
    IsNotHalt target ↔ ∀ n, odds n ≤ 2 * evens n
```

In words: Antihydra halts if and only if some prefix of the sequence has more than twice as many
odd terms as even terms.

Here `target` is the machine above. `IsHalt` means "halts when started on the blank tape", as
defined in the `BusyBeaver` library of
[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids).

The proof starts from that library's theorem

```lean
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start
```

where `next` is a six-rule map on triples `P(a, b, c)`. This package adds the passage from `next`
to the sequence `X`. The build re-checks the library's theorem as well.

## Facts about the sequence

All statements are in `AntihydraOrbit/Statements.lean`. The letters are the parts of that file.

| part | theorem | content |
|---|---|---|
| B | `H_iterate_add` | `H^[k] (x + 2^k t) = H^[k] x + 3^k t` |
| B | `parity_of_modEq`, `modEq_of_parity` | the first `k` parities of an orbit and its start value mod `2^k` determine each other |
| B | `H_iterate_two_pow_mul`, `H_iterate_two_pow_mul_add_one` | runs: `2^k m ↦ 3^k m` and `2^k m + 1 ↦ 3^k m + 1` in `k` steps |
| B | `X_eq_Z_add_one` | `X n = Z n + 1`, where `Z` is the orbit of 7 under `z ↦ ⌊(3z+1)/2⌋` (Mahler's form) |
| B | `X_bounds` | `7 · 3^n ≤ 2^n (X n − 1)` and `2^n X n ≤ 8 · 3^n` |
| B | `exists_even_within`, `exists_odd_within` | from `X n`, the next even term and the next odd term come within `log₂ (X n)` steps |
| C | `no_stop_upto_65536` | `odds n ≤ 2 * evens n` for all `n ≤ 65536`, computed inside the Lean kernel |
| D | `stopsWithin_iff_wordStops`, `card_stopping_residues` | among the `2^k` start values below `2^k`, the number that stop within `k` steps from counter `b` equals the number of parity words of length `k` on which a `+2/−1` walk from `b` goes below 0 |
| E | `lt_H`, `eq_of_parity_window`, `not_eventually_periodic` | the parity sequence of any start `x ≥ 2` is not eventually periodic |

Part C is a small horizon. Simulations by the community go far beyond it (past `2^38` steps). The
point of part C is only that this check runs inside the kernel, with no trusted program.

## Two barriers

The counter process behind the reduction works on pairs `(x, b)`. Parts D and E are about it.

- An even `x` gives `(H x, b + 2)`.
- An odd `x` with `b ≥ 1` gives `(H x, b − 1)`.
- An odd `x` with `b = 0` stops.

Antihydra is the start `(8, 0)`. The process can be started at any other pair.

```lean
theorem stopsWithin_two_pow_mul_add_one (b m : ℕ) :
    StopsWithin (b + 1) (2 ^ (b + 1) * m + 1) b

theorem exists_stopping_in_residue_class (M r b : ℕ) (hM : 0 < M) :
    ∃ x n, x % M = r % M ∧ StopsWithin n x b
```

The first says: for every counter value `b` and every `m`, the start value `2^(b+1) m + 1` stops
within `b + 1` steps.

Along Antihydra's orbit the counter is observed to be about `n/2` after `n` steps. That is less
than the bit length of `X n`, which is about `0.585 n`. So there are numbers with as many bits as
`X n` that stop from the same counter value. The size of the number and the value of the counter
alone cannot show that the orbit never stops.

The second says: every residue class modulo every `M > 0` contains a start value that stops, for
every counter value. So no congruence condition on the start value can show it either.

A proof has to use the arithmetic of this one orbit.

## How many start values stop

`AntihydraOrbit/Density.lean` counts the start values `x` for which the process stops.

Read the parities of an orbit as a word. An even term moves the counter up by 2, an odd term moves
it down by 1, and the walk stops when it would go below 0. Let `stopCount k b` be the number of
parity words of length `k` on which the walk from counter `b` stops. Let

```
q = (√5 − 1)/2 = 0.618...
```

```lean
theorem stopCount_le (k b : ℕ) : (stopCount k b : ℝ) ≤ q ^ (b + 1) * 2 ^ k

theorem stopCount_ge (k b : ℕ) :
    (q ^ (b + 1) - (4 / 5 : ℝ) ^ (b + 1) * (189 / 200 : ℝ) ^ k) * 2 ^ k ≤ (stopCount k b : ℝ)

theorem card_stopsWithin_range (k b m : ℕ) :
    ((Finset.range (2 ^ k * m)).filter fun x => StopsWithin k x b).card = m * stopCount k b

theorem lower_density_stopping (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (q ^ (b + 1) - ε) * (N : ℝ) ≤
        (((Finset.range N).filter fun x => CollatzHalts step (x, b)).card : ℝ)
```

In words:

- Among the start values below `2^k`, the fraction that stops within `k` steps lies between
  `q^(b+1) − (4/5)^(b+1) (189/200)^k` and `q^(b+1)`. It tends to `q^(b+1)`.
- Among the first `2^k · m` start values, exactly `m · stopCount k b` stop within `k` steps.
  The reason is in parts B and D: the first `k` parities and the residue mod `2^k` determine each
  other.
- So the start values that stop have lower density at least `q^(b+1)`. From counter 0 that is at
  least 61.8% of all start values.

The number `q^(b+1)` is the probability that a random walk with steps `+2` and `−1` ever goes
below 0 from `b`. That is the value the random-walk heuristic for this machine uses. The theorem
makes this part of the heuristic rigorous: for start values, not for the one orbit.

What it does not show:

- Nothing about the start value 8.
- Not that the density exists. A start value can stop after more than `log₂ x` steps, and there
  the count gives no control.

## Nine related machines

The folder `AntihydraOrbit/Cousins` is about nine other machines on the list of BB(6) holdouts.
Nobody knows whether they halt either.

| file | machine | name in `cryptids` |
|---|---|---|
| `Line359.lean` | `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` | Problem S2 (#391) |
| `Line116.lean`, `Line116Map.lean` | `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` | Problem S3 (#129) |
| `Line190.lean` | `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF` | Problem S4 (#209) |
| `Line439.lean` | `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD` | S4 sibling (#480) |
| `Line505.lean` | `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` | Problem S5 (#549) |
| `Line322.lean` | `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | Problem 2 (#352) |
| `Line487.lean` | `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` | Problem 2 (#530) |
| `Line167.lean` | `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` | Problem 2 (#183) |
| `Line594.lean` | `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | Cascade (#644) |

The numbers in the file names are the machines' line numbers in a list of 740 holdouts from
October 2026 that we worked from. The numbers after `#` are the library's own numbers for the
machines. The machine strings are what identifies the machines.

The machines are of two kinds:

- **Stack machines:** S2, S3, S4, the S4 sibling and S5. Each keeps one or two stacks of numbers
  on its tape and sweeps over them again and again. The `BusyBeaver` library proves for each of
  them that the machine halts if and only if a map on such stacks halts.
- **Counter machines:** the three machines of Problem 2, and Cascade. Each keeps two numbers on
  its tape. The library proves for each of them that the machine halts if and only if a map on
  pairs of numbers halts.

The files here build on those proofs, as the Antihydra part does.

For S2, S3 and S5 the result has the same form. At the start of a sweep, take the sum of the stack
entries weighted by powers of two. The machine halts in that sweep if and only if the sum is a
power of two. The number of times 2 divides the same sum says how deep the sweep goes.

For S4 and the S4 sibling the condition is on a single number. At certain points of the orbit one
of the two stacks is down to a single entry `x`. From such a point the machine halts before its
next sweep if and only if `x + 1` (for S4) or `x + 2` (for the sibling) is a power of two.

For the counter machines the condition is on a chain. While a certain one of the two numbers is
odd, the machine cannot halt. When that number becomes even, a chain follows in which the other
number about doubles at each step while this one shrinks. The chain ends in a halt exactly when the
even number at its start lies in an explicit sequence. These sequences grow like powers of two,
for example

```
20 · 2^j - 2j - 16  =  4, 22, 60, 138, 296, ...
```

### What the criteria show

- They show exactly when each machine halts. For a stack machine that is when its orbit reaches a
  stack whose sum (for S4 and the sibling, a single entry plus 1 or 2) is a power of two. For a
  counter machine it is when a chain starts at a value of its sequence.
- They do not show whether that ever happens. All nine machines remain open.
- A halt would be a finite event, and a run that finds one can be checked by anyone. To show that a
  machine never halts, one would have to prove that no such value occurs along its orbit.

### Problem S2 (`Line359.lean`)

After three steps, every state of the library's accelerated map has the form `D 0 0 L` with one
stack `L`. From there, one step is a map `U` on stacks. The file defines `U` as one sweep from the
top of the stack, and `U L = none` means that the machine halts in this sweep.

```lean
def paddedSum : List ℕ → ℕ
  | [] => 1
  | y :: L => y + 2 * paddedSum L

theorem U_eq_none_iff (L : List ℕ) : U L = none ↔ ∃ k, paddedSum L = 2 ^ k

theorem isHalt_iff_collatzHalts_U : IsHalt target ↔ CollatzHalts U [2, 2, 0]

theorem isHalt_iff_powerOfTwo :
    IsHalt target ↔
      ∃ t L, (Option.bind · U)^[t] (some [2, 2, 0]) = some L ∧ ∃ k, paddedSum L = 2 ^ k
```

For a stack with `n` entries the padded sum is

```
paddedSum L = L[0] + 2 L[1] + 4 L[2] + ... + 2^(n-1) L[n-1] + 2^n
```

In words: the machine halts if and only if the orbit of `[2, 2, 0]` under `U` reaches a stack
whose padded sum is a power of two.

The theorem `sweepDepth_zero_eq` adds the depth: the sweep visits
`padicValNat 2 (paddedSum L) + 1` levels of the stack.

### Problem S3 (`Line116.lean`)

This criterion is stated on the library's accelerated map `highLevelNext` itself. A bottom reach
is a state of the form `F 0 2 L 1 []`. It is the point where a sweep over the stack `L` starts.

```lean
def weightedSum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 * weightedSum xs

def W (u : List ℕ) : ℕ := 1 + weightedSum u

def paddedW (u : List ℕ) : ℕ := W u + 2 ^ u.length

theorem isHalt_iff_bottomReach_powerOfTwo :
    IsHalt target ↔
      ∃ t L, (Option.bind · highLevelNext)^[t] (some highLevelStart) =
          some (.F 0 2 L 1 []) ∧
        ∃ p, paddedW L = 2 ^ p
```

For a stack with `n` entries that is

```
paddedW L = 1 + L[0] + 2 L[1] + ... + 2^(n-1) L[n-1] + 2^n
```

In words: the machine halts if and only if it comes to a bottom reach whose stack has a padded
sum that is a power of two.

The file also proves what a sweep does in each case. Write the stack as some ones followed by a
rest `u` with odd entries, and `v` for the number of times 2 divides `W u`.

| theorem | case | what the sweep does |
|---|---|---|
| `sweep_stops_inside` | `v + 1` is less than the length of `u` | it stops inside the stack, after `v + 1` entries of `u` |
| `sweep_empties_even` | `v + 1` equals the length | it empties the stack and the machine goes on |
| `sweep_starts_chain` | `v` is at least the length | it empties the stack and starts a chain of halvings |
| `chainEntry_halts_iff_powerOfTwo` | a chain of even value `V ≥ 4` | the chain ends in a halt exactly when `V` is a power of two |

The theorem `allOdd_of_bottomReach` shows that every stack at a bottom reach of the orbit has only
odd entries. The sweep theorems assume that.

### Problem S3, one cycle at a time (`Line116Map.lean`)

`Line116.lean` describes each part of a sweep on its own. `Line116Map.lean` puts the parts together
into one map `botStep` on stacks. It takes the stack at one bottom reach to the stack at the next
bottom reach, or returns `none` when the machine halts in between.

```lean
def botStep (L : List ℕ) : Option (List ℕ) := botGo true 1 L

def botSteps (L : List ℕ) : ℕ := 6 + botGoSteps true 1 L

theorem botStep_reaches (L L' : List ℕ) (hL : AllOdd L) (h : botStep L = some L') :
    (Option.bind · highLevelNext)^[botSteps L] (some (.F 0 2 L 1 [])) =
        some (.F 0 2 L' 1 []) ∧
      AllOdd L'

theorem botStep_eq_none_iff (L : List ℕ) (hL : AllOdd L) :
    botStep L = none ↔ ∃ p, paddedW L = 2 ^ p

theorem isHalt_iff_botStep : IsHalt target ↔ CollatzHalts botStep [5, 5, 1]
```

One cycle passes a carry down the stack. Write the stack as `L = [u_0, u_1, ...]`, all entries
odd, and start with the carry `p_0 = 1`. At level `j` the cycle looks at

```
B_j = u_j + p_j
```

If `B_j` is even and there is another entry, the carry for the next level is `p_(j+1) = B_j / 2`.
The cycle ends at level `d`: the first level where `B_d` is odd, or the last level if all are
even. In the second case put `V = B_d + 2 = 2^ν q` with `q` odd. The new stack is:

| case | new stack |
|---|---|
| `B_0` is odd | `[B_0 + 2, u_1 + 2, u_2, ...]` |
| `B_d` is odd, `d ≥ 1` | `[p_1, ..., p_(d-1), p_d - 1, B_d + 2, u_(d+1) + 2, u_(d+2), ...]` |
| all even, `q ≥ 3` | `[p_1, ..., p_d, 2^(ν-1) q - 1, ..., 2 q - 1, q - 2, q, 1]` |
| all even, `q = 1` | none: the machine halts |

Two details of the table:

- If the odd `B_d` is at the last entry, a new entry `1` takes the place of `u_(d+1) + 2`.
- In the third row, the entries from `2^(ν-1) q - 1` down to `2 q - 1` are absent when `ν = 1`.

When the cycle does not halt, the number of steps of `highLevelNext` in it is

```
botSteps L = 6 + p_1 + ... + p_d                (first and second row)
botSteps L = 6 + p_1 + ... + p_d + V - q - ν    (third row)
```

For example, the first bottom reach has the stack `[5, 5, 1]`:

```
B_0 = 5 + 1 = 6   ->  p_1 = 3
B_1 = 5 + 3 = 8   ->  p_2 = 4
B_2 = 1 + 4 = 5   is odd, so d = 2
new stack [p_1, p_2 - 1, B_2 + 2, 1] = [3, 3, 7, 1], after 6 + 3 + 4 = 13 steps
```

Two more theorems tie the map to the machine's time:

- `botStep_orbit`: the `n`-th stack of the orbit of `[5, 5, 1]` is the bottom reach at step
  `botTime n` of `highLevelNext`. The first is at step 27, and each cycle adds its length.
- `botStep_no_earlier`: no other bottom reach comes inside a cycle.

### Problem S5 (`Line505.lean`)

For this machine the library proves that a reduction to a map on two stacks exists
(`HasStackReduction target`), and keeps the rules of that map private. `Line505.lean` writes the
rules out as an explicit map `next505` with 11 cases and proves that it is a valid acceleration of
the library's `target`. Then it proves the criterion.

```lean
def W : List ℕ → ℕ
  | [] => 0
  | a :: L => (a + 1) + 2 * W L

theorem isHalt_iff_next505 : IsHalt target ↔ CollatzHalts next505 start505

theorem isHalt_iff_D_powerOfTwo :
    IsHalt target ↔
      ∃ t L R,
        (Option.bind · next505)^[t] (some start505) = some (.D L R) ∧
        ∃ k, W L = 2 ^ k
```

A state `D L R` has a left stack `L` and a right stack `R`, and the sum is taken over the left
stack:

```
W L = (L[0] + 1) + 2 (L[1] + 1) + ... + 2^(n-1) (L[n-1] + 1)
```

In words: the machine halts if and only if the orbit of `next505` reaches a `D` state whose left
stack has a sum that is a power of two.

The theorem `oddPeelDepth_eq_padicValNat` gives the depth of a sweep as the number of times 2
divides `W L`. The theorem `isHalt_iff_oddTop_powerOfTwo` is the same criterion restricted to the
`D` states with an odd top entry, which is where a sweep starts.

`Line505Base.lean` is a copy of the library's file for this machine with the `private` keywords
removed, so that its rule lemmas can be used. The changes are listed at its top. The theorems above
are about the library's original `target`, not about the copy.

### S4 sibling (`Line439.lean`)

The library groups this machine with the machines of Problem S4. As for S5, it proves that a
reduction to a map on two stacks exists and keeps the rules private. `Line439.lean` writes them out
as a map `next439` with seven cases and proves that it is a valid acceleration of `target`.

A state is `D L R` or `AL L R`, with a left stack `L` and a right stack `R`:

```lean
def next439 : State439 → Option State439
  | .D [] R => some (.AL [] (bumpHead R))
  | .D (a :: L) R => some (.D L (a :: bumpHead R))
  | .AL L [] => some (.D L.tail [tailWeight L + 2])
  | .AL _ (0 :: _) => none
  | .AL L (1 :: R) => some (.D ((tailWeight L + 2) :: L.tail) R)
  | .AL L (2 :: R) => some (.AL (0 :: tailWeight L :: L.tail) (bumpHead R))
  | .AL L ((d + 3) :: R) => some (.AL ((tailWeight L + 1) :: L.tail) ((d + 1) :: bumpHead R))

theorem isHalt_iff_next439 : IsHalt target ↔ CollatzHalts next439 start439
```

Two helper functions appear in the rules:

- `bumpHead` adds 1 to the first entry of a stack, and turns `[]` into `[0]`.
- `tailWeight L` is the first entry of `L`, or 0 if `L` is empty.

The start is `start439 = D [3] [0]`, which the machine reaches from the blank tape after 23 steps.
In mode `D` the machine sweeps the left stack over to the right one.

Call a state `AL L [x]`, with a single entry on the right, an exposure of value `x`. The file proves
what follows an exposure, for every `L` and `x`:

| theorem | case | what follows |
|---|---|---|
| `exposure_even_step` | `x ≥ 2` even | after `x / 2` steps, an exposure of value `x / 2 - 1` |
| `exposure_odd_step` | `x` odd | after `(x + 1) / 2` steps, a `D` state |
| `exposure_halt_of_powerOfTwo` | `x + 2 = 2^k` | a halt after `2^k - k` steps, with no `D` state before it |
| `exposure_reaches_D_of_not_powerOfTwo` | `x + 2` is not a power of two | a `D` state after `exposureSteps x` steps |

Since `(x / 2 - 1) + 2 = (x + 2) / 2`, each even exposure halves `x + 2`. If `x + 2` is a power of
two, the halvings end at the value 0, and the machine halts. Otherwise they end at the odd part of
`x + 2` minus 2, an odd value, and the machine goes back to mode `D`. So:

```lean
theorem exposure_halts_before_D_iff (L : List ℕ) (x : ℕ) :
    (∃ T, (Option.bind · next439)^[T] (some (.AL L [x])) = none ∧
        ∀ t < T, ∀ L' R',
          (Option.bind · next439)^[t] (some (.AL L [x])) ≠ some (.D L' R')) ↔
      (x = 0 ∨ ∃ k, 2 ≤ k ∧ x + 2 = 2 ^ k)
```

On the orbit there is no other way to halt. In mode `D` the two stacks are never both empty
(`orbitInv_start439`, `orbitInv_step`). From this, `halt_after_exposure_two` shows that every halting
state of the orbit comes one step after an exposure of value 2. Together:

```lean
theorem isHalt_iff_exposure_powerOfTwo :
    IsHalt target ↔
      ∃ t L x, (Option.bind · next439)^[t] (some start439) = some (.AL L [x]) ∧
        ∃ k, 2 ≤ k ∧ x + 2 = 2 ^ k
```

In words: the machine halts if and only if its orbit reaches an exposure `AL L [x]` for which
`x + 2` is a power of two (at least 4).

`Line439Base.lean` is a copy of the library's file for this machine with the `private` keywords
removed, as for S5. The theorems are about the library's original `target`.

### Problem S4 (`Line190.lean`)

For this machine, too, the library proves that a reduction to a map on two stacks exists and
keeps the rules private. `Line190.lean` writes them out as a map `next190` with 17 cases and proves
that it is a valid acceleration of `target`:

```lean
theorem isHalt_iff_next190 : IsHalt target ↔ CollatzHalts next190 start190
```

A state is `C L R`, `D L R` or `D00 L R`, with a left stack `L` and a right stack `R`. The start is
`start190 = D [2] []`, which the machine reaches from the blank tape after 5 steps.

One case of the map, `C L (0 :: 0 :: R)`, runs an inner loop of the machine. The file contracts
that loop into a single step, `innerStep`.

Call a state `D00 [x] R`, with a single entry on the left, an exposure of value `x`. The file
proves what follows an exposure, for every `R` and `x`:

| theorem | case | what follows |
|---|---|---|
| `exposure_odd_step` | `x` odd | after `(x + 1) / 2` steps, the exposure `D00 [x / 2] (x / 2 :: R)` |
| `exposure_even_step` | `x ≥ 2` even | after `x / 2` steps, the state `C [x / 2 + 1, x / 2 - 1] R` |
| `exposure_halt_of_powerOfTwo` | `x + 1 = 2^k` | the machine has halted after `2^k` steps, with no `C` state before |
| `exposure_reaches_C_of_not_powerOfTwo` | `x + 1` is not a power of two | a `C` state after `exposureSteps x` steps |

For odd `x` we have `x / 2 + 1 = (x + 1) / 2`, so each odd exposure halves `x + 1`. If `x + 1` is a
power of two, the halvings end at the value 0, and the machine halts. Otherwise they end at the odd
part of `x + 1` minus 1, an even value, and the machine goes on to a `C` state. So:

```lean
theorem exposure_halts_before_C_iff (R : List ℕ) (x : ℕ) :
    (∃ T, (Option.bind · next190)^[T] (some (.D00 [x] R)) = none ∧
        ∀ t < T, ∀ L' R',
          (Option.bind · next190)^[t] (some (.D00 [x] R)) ≠ some (.C L' R')) ↔
      ∃ k, x + 1 = 2 ^ k
```

On the orbit there is no other way to halt. The invariant `ShieldInv` holds at the start and is
kept by every step (`shieldInv_start190`, `shieldInv_step`). It excludes every halting case of the
map except `D00 [0] R`, and it shows that the inner loop is never entered
(`shieldInv_excludes_hazards`).

From this, `halt_after_exposure_three` shows that every halting state of the orbit is
`D00 [0] (0 :: 1 :: R')`, three steps after the exposure `D00 [3] R'`. Together:

```lean
theorem isHalt_iff_exposure_powerOfTwo :
    IsHalt target ↔
      ∃ t R x, (Option.bind · next190)^[t] (some start190) = some (.D00 [x] R) ∧
        ∃ k, 2 ≤ k ∧ x + 1 = 2 ^ k
```

In words: the machine halts if and only if its orbit reaches an exposure `D00 [x] R` for which
`x + 1` is a power of two (at least 4). The law has the same form as for the S4 sibling, with
`x + 1` in place of `x + 2`.

`Line190Base.lean` is a copy of the library's file for this machine with the `private` keywords
removed, as for S5. The changes are listed at its top. The theorems are about the library's
original `target`.

### Problem 2 (`Line322.lean`, `Line487.lean`, `Line167.lean`)

For these three machines the library states the accelerated map itself, `highLevelNext`, and
proves

```lean
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart
```

The files work with that map directly. In each of them, `orbit t` is the state after `t` steps of
`highLevelNext` from `highLevelStart`.

The map of `Line322.lean` acts on states `D_p(a, w)`, with a bit `p` and two numbers `a` and `w`.
The start is `D_0(0, 3)`.

In Lean the bit is a Boolean, and `.D true a w` stands for `D_1(a, w)`.

Put `m = ⌊w/2⌋`. A state `D_1(a, w)` goes to `J_1(a, w)`. A state `D_0(a, w)` goes to the first
case of the table that applies, and `J_1(a, w)` is given by the same cases with other constants:

| case | `D_0(a, w)` goes to | `J_1(a, w)` is |
|---|---|---|
| `a ≥ m + 2` | `D_0(a - m - 2, 2w + 5)` | `D_0(a - m - 2, 2w + 7)` |
| `a = m + 1` | `D_1(1, 2w + 1)` | `D_1(1, 2w + 3)` |
| `a = m` | `D_1(1, 2w)` | `D_1(1, 2w + 2)` |
| `w = 2a + 2` | halt | halt |
| `w ≤ 2a + 5` | `D_0(2a + 2, 2w - 4a - 5)` | `D_0(2a + 3, 2w - 4a - 5)` |
| otherwise | `J_1(2a + 3, w - 2a - 6)` | `J_1(2a + 4, w - 2a - 6)` |

`J_1` is the library's `drainJ1`. It calls itself in its last case, so one step of
`highLevelNext` can run a whole chain.

The halting case needs `w = 2a + 2`, which is even. When `w` is odd, every case of the table gives
an odd `w` again, except the case `a = m`. The file proves:

- Every state on the orbit has `w` odd, or is `D_1(1, W)` with `W` even (`inv_orbit`).
- No state with `w` odd halts (`highLevelNext_ne_none_of_odd`).
- From `D_1(1, W)` the next step is the chain `J_1(1, W)`. For every `W`, it halts if and only if
  `W` is one of the numbers `SW j` below (`drainJ1_one_eq_none_iff`).

Along the chain from `(1, W)`, stage `i` has

```
a_i = 5 · 2^i - 4,    w_(i+1) = w_i - 2 a_i - 6,    w_0 = W
```

The chain halts at stage `j` when `w_j = 2 a_j + 2`, and that is the equation
`W + 2j + 16 = 20 · 2^j`:

```lean
def SW (j : ℕ) : ℕ := 20 * 2 ^ j - 2 * j - 16

theorem drainJ1_one_eq_none_iff (W : ℕ) : drainJ1 1 W = none ↔ ∃ j, W = SW j

theorem isHalt_iff_D_SW :
    IsHalt target ↔ ∃ t j, orbit t = some (.D true 1 (SW j))
```

The first values of `SW j` are 4, 22, 60, 138 and 296. In words: the machine halts if and only if
its orbit reaches a state `D_1(1, W)` with `W` one of these numbers. The first state of this form
on the orbit is `D_1(1, 24)`, after 8 steps.

`Line487.lean` has the same structure. The states are `D(a, w)`, the start is `D(0, 1)`, and the
chain is the library's `evalK2`. The states on the orbit with `w` even are states `D(0, W)`, and
the halting values are

```
SW k = 12 · 2^k - 2k - 10  =  2, 12, 34, 80, 174, ...
```

```lean
theorem highLevelNext_D_zero_eq_none_iff (W : ℕ) :
    highLevelNext (.D 0 W) = none ↔ ∃ k, W = SW k

theorem isHalt_iff_D_SW :
    IsHalt target ↔ ∃ t k, orbit t = some (.D 0 (SW k))
```

`Line167.lean` is about states `P_1(a, c)`, from the start `P_1(2, 1)`. Here a chain takes several
steps of `highLevelNext`, so the file follows the orbit from waypoint to waypoint.

A *waypoint* (`Wp`) is a state with `c` odd, or an *entry*: a state `P_1(2, c)` with `c` even.

- With `c` odd the step never halts (`m_no_halt`), and `c` stays odd unless it is 1 (`m_step`).
- From `P_1(a, 1)` two steps lead to `P_1(2, a + 3)`, an entry if `a` is odd
  (`entry_two_steps`).
- From an entry `P_1(2, c_0)` a chain of states `P_1(a_i, c_i)` follows, two steps each, with
  `a_i + 12 = 14 · 2^i` and `c_(i+1) = c_i - a_i - 10`.

The chain ends in a halt if and only if `c_0` is one of

```
SW k = 14 · 2^k - 2k - 10  =  4, 16, 42, 96, 206, ...
```

Otherwise it reaches the next waypoint (`excursion_halts`, `excursion_ends`). The start is a
waypoint (`Wp_start`), and every waypoint is a halting entry or leads to the next waypoint
(`next_waypoint`). So:

```lean
theorem isHalt_iff_P_SW : IsHalt target ↔ ∃ t k, orbit t = some (.P_1 2 (SW k))
```

### Cascade (`Line594.lean`)

The library states the accelerated map for this machine too, on states `E(b, d)`, and proves
`isHalt_iff_highLevel_acceleration` for it. The start is `E(0, 1)`.

Put `m = ⌊d/2⌋` and `c = d + 1`. A state `E(b, d)` goes to the first case of the table that
applies:

| case | `E(b, d)` goes to |
|---|---|
| `b = m + 1` | `E(0, 2c + 3)` |
| `b = m + 2` | `E(2, 2c + 1)` |
| `b ≥ m + 3` | `E(b - m - 3, 2c + 5)` |
| `c - 2b ≤ 2` | `E(0, 2c + 2)` |
| `c - 2b = 3` | halt |
| `c - 2b ≤ 6` | `E(2b + 2, 2(c - 2b) - 7)` |
| otherwise | `E(2b + 4, c - 2b - 7)` |

The parity of `d` plays the part of the parity of `w` above. The halting case is `d = 2b + 2`.

- With `d` odd the step never halts, and the new `d` is odd again, with one exception: the
  coincidence `d = 2b + 1`, where `E(b, 2b + 1)` goes to `E(0, 4b + 6)` (`odd_step`).
- From `E(0, 4b + 6)` a chain of states `E(b_i, d_i)` follows while `d` is even, with
  `b_i + 4 = 4 · 2^i` and `d_(i+1) = d_i - 2 b_i - 6`.
- The chain ends at an odd `d`, or in a halt when `d_i = 2 b_i + 2`, or in a restart when
  `d_i = 2 b_i`. A restart goes to `E(0, 4 b_i + 4)`, and the chain from there neither halts nor
  restarts again (`restart_not_hal`).

For every `b`, the chain from the coincidence halts if and only if

```
b = SW j = 4^j - j - 4   with j ≥ 2   (10, 57, 248, 1015, ...)
```

and otherwise it ends at an odd `d` (`excursion_halts`, `excursion_ends`). So:

```lean
theorem isHalt_iff_E_SW :
    IsHalt target ↔ ∃ t j, 2 ≤ j ∧ orbit t = some (.E (SW j) (2 * SW j + 1))
```

In words: the machine halts if and only if its orbit reaches a coincidence `E(b, 2b + 1)` with `b`
one of these numbers. The proof follows the orbit from one state with `d` odd to the next
(`next_waypoint`), as in `Line167.lean`.

For example, `b = SW 2 = 10` gives the coincidence `E(10, 21)`. Its chain is `E(0, 46)`,
`E(4, 40)`, `E(12, 26)`, and then the machine halts, since `26 = 2 · 12 + 2`.

The orbit from the start does reach coincidences. One is `E(114, 229)`, after 220 steps, but 114 is
not in the sequence.

## Earlier work

None of the mathematics in the reduction is new. What this package adds is noted at the end.

- **The machine and its rules.** mxdys found the machine in June 2024 and Racheline worked out its
  rules. Shawn Ligocki's
  [BB(6) is Hard (Antihydra)](https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html) states the
  halting question in the form used here: is the number of odd terms ever more than twice the
  number of even terms?
- **Coq.** The `busycoq` project proves the machine's rules in Coq (`verify/AntiHydra.v`).
- **Lean, machine to rules.** The `BusyBeaver` library of `google-deepmind/cryptids` proves
  `isHalt_iff_acceleration`. This package starts from it.
- **Lean, an earlier formalization.**
  [rwst/Antihydra-Basics](https://github.com/rwst/Antihydra-Basics) (March 2026) has its own
  model of the machine. It contains a halting equivalence (`antihydra_halts_iff`) and the
  non-periodicity of the parity sequence. Part A and the non-periodicity theorem overlap with it.
- **Parities and residues, aperiodicity.** Racheline and apgoucher gave these arguments on the
  bbchallenge Discord on 10 August 2024. A. Dubickas, "On integer sequences generated by linear
  maps", proves a stronger form of the aperiodicity.
- **The heuristic.** The value `(1/φ)^(b+1)`, with `φ` the golden ratio, is in Ligocki's
  [BB(2, 5) is Hard (Hydra)](https://www.sligocki.com/2024/05/10/bb-2-5-is-hard.html). Note that
  `q = 1/φ`. The counting method is the one Terras used for the 3x+1 map.
- **The count.** Both counts below were posted on the bbchallenge Discord.
  - On 20 April 2024, k00 counted the start values that stop after exactly `3k + 1` steps (OEIS
    A001764). This was for another Collatz-like map whose counter takes the same steps `+2` and
    `−1`. k00 estimated that about 61.8% of the start values stop.
  - On 31 May 2025, Sixshaman gave the count for Antihydra from counter 0, with an argument. The
    stopping parity words are counted as ternary trees, and each stopping start value repeats
    with period `2^n`. Summing the densities gives `φ − 1 = 0.618...`.

Earlier work on the related machines:

- **The reductions.** The maps and the proofs that the machines follow them are in the
  `BusyBeaver` library: in `BusyBeaver/BB6/Accelerations` for the stack machines, and in
  `BusyBeaver/BB6` for the counter machines.
- **The hardness table.** The same library names the trigger of the halt for each machine. For
  S2, S4, S5 and the S4 sibling that is a power-of-two condition at the bottom of the stack. The
  table also gives near misses from simulations.
- **Problem S4 and its sibling.** For the machines of Problem S4 the hardness notes describe the
  exposures seen in simulations as halvings down to an odd part, for example `1292 → 646 → 323`.
- **Problem S3.** nerdyjoe described the machine as a rewriting system on a string of integers on
  the bbchallenge Discord on 3 December 2025 and conjectured that it does not halt.
- **Problem S5, the wiki.** The machine's
  [wiki page](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF)
  gives macro rules, an era structure, and a list of invariants that failed. It also notes two facts
  about halting:
  - with no run left of the cursor, the cursor values `3, 7, 15, 31, …` lead to a halt;
  - in general, halting depends on the whole configuration and not on any single field.
- **Problem S5, Lean.** The page links Lean proofs of its macro rules in
  [rwst/bbchallenge](https://github.com/rwst/bbchallenge/tree/main/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF).
- **Problem 2 and Cascade, the hardness table.** For Problem 2 the table gives the trigger as an
  equality "with leaky parity shield". For Cascade it gives a "second-order coincidence", and the
  notes say that a halt requires both `c = 2b - 4` and `c_odd = 2^(k+3) - 2k - 5`, in the
  variables of those notes.
- **The counter machines in Coq.** The `busycoq` project certifies a three-counter macro map for
  each of the four counter machines, in
  [`verify/CubicCap.v`](https://github.com/ccz181078/busycoq/blob/BB6/verify/CubicCap.v) (lemmas
  `WF32`, `WF33`, `WF35`, `WF36`). The machine strings there are mirror images of ours, with the
  states renamed.
- **The translation.** The doc comments of `Line322.lean`, `Line487.lean` and `Line167.lean` give
  the halting values in the variables of that macro map. This translation is not part of the
  proofs. We checked it by computation, over the first million steps of each orbit.

What this package adds:

- The reduction is stated on the `BusyBeaver` library's own definitions of machine and halting, as
  a count over the plain orbit of 8.
- The two barriers.
- The count and the density bound as Lean theorems, for every starting counter `b`, with an
  explicit error term. For counter 0 the value and a counting argument were known (see "The
  count" above).
- For S2, S3 and S5: one condition on the whole stack, a weighted sum being a power of two, that is
  equivalent to halting, with the proof down to the machine. We have not found these sums stated
  before.
- For S3, the whole cycle as one map on stacks, with the exact number of steps.
- For Problem S4 and the S4 sibling: the library's notes name the trigger; the package proves that
  it is the only way these machines can halt, and that each exposure halts exactly when `x + 1`
  (for S4) or `x + 2` (for the sibling) is a power of two.
- For Problem 2 and Cascade: the package proves that these machines can halt only at the end of a
  chain, and that a chain halts exactly when its starting value lies in an explicit sequence. We
  have not found these sequences stated with a proof before.

## How to check it

```
lake exe cache get
lake build
```

The first command fetches the dependencies and downloads the prebuilt Mathlib. Afterwards the
project directory holds about 8 GB, most of it Mathlib.

The second command builds the fifteen library files that are needed (fourteen of `BusyBeaver` and
`Cryptids/Machines.lean`) and the files of this package. From a fresh clone it took about seven
minutes on our machine, with two threads.

The top level has two symbolic links, `artifacts` and `baselines`. They point into the fetched
copy of the library. One of its files, `Cryptids/Machines.lean`, reads machine tables by paths
relative to the directory in which the build runs, and the links make these paths resolve. On a
system without symbolic links, copy the two directories from `.lake/packages/Cryptids/` instead.

The build prints one line per theorem, for example

```
'AntihydraOrbit.antihydra_isHalt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Lean 4.35.0-rc4 and Mathlib at the matching tag: the versions pinned by `google-deepmind/cryptids`
  at commit `1f9ffee`, on which this package depends.
- No `sorry`, no `native_decide`.
- Every theorem depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`,
  or on fewer.
- `no_stop_upto_65536` is checked by `decide +kernel`: the kernel itself runs the 65536 steps. That
  takes about 20 seconds. The same check for `2^17` steps did not finish in ten minutes, and we did
  not look into why.

## What you have to trust

- The Lean kernel and Mathlib.
- The definitions of a Turing machine, `IsHalt` and `IsNotHalt` in the `BusyBeaver` library
  (`BusyBeaver/Defs.lean` in `google-deepmind/cryptids`), and its reading of the machine string.
- The definitions in `AntihydraOrbit/Defs.lean` (52 lines): `H`, `X`, `evens`, `odds`, the counter
  process `step`, `StopsWithin`, `M`, `Z`, `wordStops`. For the count, also `stopCount` and `q` at
  the top of `AntihydraOrbit/Density.lean`.

- For the related machines: the definitions at the top of each file, under the heading
  "Definitions (the trusted base)". The criteria for S3, Problem 2 and Cascade are stated with the
  library's own `highLevelNext` and `highLevelStart`.

The definitions and the statements were written before the proofs. The definitions were compared
with a direct computation of the orbit, and the statements about the related machines with direct
computations on their rules.

## Files

| file | content |
|---|---|
| `AntihydraOrbit/Defs.lean` | the definitions |
| `AntihydraOrbit/Statements.lean` | every theorem of parts A to E, with its proof |
| `AntihydraOrbit/Bridge.lean` | from the accelerated map `next` to the counter process and to `evens`/`odds` |
| `AntihydraOrbit/Lemmas.lean` | lemmas for parts B, D and E |
| `AntihydraOrbit/Horizon.lean` | the checker for part C and its soundness proof |
| `AntihydraOrbit/Density.lean` | the count of stopping parity words, its limit, and the lower density of stopping start values |
| `AntihydraOrbit/Audit.lean` | `#print axioms` for the 22 theorems of `Statements.lean` |
| `AntihydraOrbit/DensityAudit.lean` | `#print axioms` for the 11 theorems of `Density.lean` |
| `AntihydraOrbit/Cousins/Line359.lean` | Problem S2: the map `U`, the padded sum, the halting criterion |
| `AntihydraOrbit/Cousins/Line116.lean` | Problem S3: the sweep and chain laws, the halting criterion |
| `AntihydraOrbit/Cousins/Line116Map.lean` | Problem S3: one cycle as the map `botStep` on stacks, with exact times |
| `AntihydraOrbit/Cousins/Line505Base.lean` | Problem S5: the library's file for the machine, with its rule lemmas made public |
| `AntihydraOrbit/Cousins/Line505.lean` | Problem S5: the explicit map `next505`, the sum law, the halting criterion |
| `AntihydraOrbit/Cousins/Line439Base.lean` | S4 sibling: the library's file for the machine, with its rule lemmas made public |
| `AntihydraOrbit/Cousins/Line439.lean` | S4 sibling: the explicit map `next439`, the exposure law, the halting criterion |
| `AntihydraOrbit/Cousins/Line190Base.lean` | Problem S4: the library's file for the machine, with its rule lemmas made public |
| `AntihydraOrbit/Cousins/Line190.lean` | Problem S4: the explicit map `next190`, the exposure law, the shield invariant, the halting criterion |
| `AntihydraOrbit/Cousins/Line322.lean` | Problem 2 (#352): the parity invariant, the halting values `SW j`, the halting criterion |
| `AntihydraOrbit/Cousins/Line487.lean` | Problem 2 (#530): the same for this machine |
| `AntihydraOrbit/Cousins/Line167.lean` | Problem 2 (#183): waypoints, the chain law, the halting criterion |
| `AntihydraOrbit/Cousins/Line594.lean` | Cascade (#644): the odd phase, the chain law with restarts, the halting criterion |
| `AntihydraOrbit/Cousins/Line359Audit.lean`, `Line116Audit.lean`, `Line116MapAudit.lean`, `Line505Audit.lean`, `Line439Audit.lean`, `Line190Audit.lean`, `Line322Audit.lean`, `Line487Audit.lean`, `Line167Audit.lean`, `Line594Audit.lean` | `#print axioms` for the 17, 16, 5, 20, 11, 12, 15, 14, 17 and 12 theorems of the ten files |

## License

Apache-2.0, the license of the library this package builds on.

## AI assistance

AI assistance: the statements, the proofs and the checks were produced with the help of Claude
(Anthropic); the proofs in `Density.lean` and in the files for S2, S3, S4, S5 and the S4 sibling
were written with the help of Gemini (Google).

The proofs were written by the models and checked by the Lean kernel. They have not been read line
by line by a person. What needs a human eye is short: the definitions and the statements.
