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
   the start values stop.

It does **not** prove that Antihydra never halts. The third result is about the family of all
start values and says nothing about the start value 8.

The package has a second part, about three other open machines of BB(6). For each one it proves an
exact criterion: the machine halts if and only if a certain weighted sum becomes a power of two.
That says when each machine halts, not whether it does. See "Three related machines" below.

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

## Three related machines

The folder `AntihydraOrbit/Cousins` is about three other machines on the list of BB(6) holdouts.
Nobody knows whether they halt either.

| file | machine | name in `cryptids` |
|---|---|---|
| `Line359.lean` | `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` | Problem S2 |
| `Line116.lean` | `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` | Problem S3 |
| `Line505.lean` | `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` | Problem S5 |

The numbers in the file names are the machines' line numbers in a list of 740 holdouts from
October 2026 that we worked from. The machine strings are what identifies the machines.

Each machine keeps a stack of numbers on its tape and sweeps over it again and again. The
`BusyBeaver` library proves for each of them that the machine halts if and only if a map on such
stacks halts. The files here build on those proofs, as the Antihydra part does.

The result has the same form for all three. At the start of a sweep, take the sum of the stack
entries weighted by powers of two. The machine halts in that sweep if and only if the sum is a
power of two. The number of times 2 divides the same sum says how deep the sweep goes.

### What the criteria show

- They show exactly when each machine halts: when its orbit reaches a stack whose sum is a power
  of two.
- They do not show whether that ever happens. All three machines remain open.
- A halt would be a finite event, and a run that finds one can be checked by anyone. To show that a
  machine never halts, one would have to prove that no sum along its orbit is a power of two.

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

Earlier work on the three related machines:

- **The reductions.** The stack maps and the proofs that the machines follow them are in the
  `BusyBeaver` library (`BusyBeaver/BB6/Accelerations`). Its hardness table names the trigger of
  the halt for each machine. For S2 and S5 that is a power-of-two condition at the bottom of the
  stack. The table also gives near misses from simulations.
- **Problem S3.** nerdyjoe described the machine as a rewriting system on a string of integers on
  the bbchallenge Discord on 3 December 2025 and conjectured that it does not halt.
- **Problem S5, the wiki.** The machine's
  [wiki page](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF)
  gives macro rules, an era structure, and a list of invariants that failed. It notes that halting
  depends on the whole configuration and not on any single field.
- **Problem S5, Lean.** The page links Lean proofs of its macro rules in
  [rwst/bbchallenge](https://github.com/rwst/bbchallenge/tree/main/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF).

What this package adds:

- The reduction is stated on the `BusyBeaver` library's own definitions of machine and halting, as
  a count over the plain orbit of 8.
- The two barriers.
- The exact count of stopping start values and the density bound. We have not found these stated
  with a proof for this family. Pointers are welcome.
- For the three related machines: one condition on the whole stack, a weighted sum being a power
  of two, that is equivalent to halting, with the proof down to the machine. We have not found
  these sums stated before. Pointers are welcome here too.

## How to check it

```
lake exe cache get
lake build
```

The first command fetches the dependencies and downloads the prebuilt Mathlib. Afterwards the
project directory holds about 8 GB, most of it Mathlib.

The second command builds the nine library files that are needed (eight of `BusyBeaver` and
`Cryptids/Machines.lean`) and the files of this package. From a fresh clone it took a little over
four minutes on our machine, with two threads.

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

- For the three related machines: the definitions at the top of each file, under the heading
  "Definitions (the trusted base)". The criterion for Problem S3 is stated with the library's own
  `highLevelNext` and `highLevelStart`.

The definitions and the statements were written before the proofs. The definitions were compared
with a direct computation of the orbit, and the statements about the three related machines with
direct computations on their rules.

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
| `AntihydraOrbit/Cousins/Line505Base.lean` | Problem S5: the library's file for the machine, with its rule lemmas made public |
| `AntihydraOrbit/Cousins/Line505.lean` | Problem S5: the explicit map `next505`, the sum law, the halting criterion |
| `AntihydraOrbit/Cousins/Line359Audit.lean`, `Line116Audit.lean`, `Line505Audit.lean` | `#print axioms` for the 17, 16 and 20 theorems of the three files |

## License

Apache-2.0, the license of the library this package builds on.

## AI assistance

AI assistance: the statements, the proofs and the checks were produced with the help of Claude
(Anthropic); the proofs in `Density.lean` and the files in `AntihydraOrbit/Cousins` were written
with the help of Gemini (Google).

The proofs were written by the models and checked by the Lean kernel. They have not been read line
by line by a person. What needs a human eye is short: the definitions and the statements.
