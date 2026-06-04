# dijkstra-challenge

Dijkstra's verification challenge to Backus, from a [1979
letter](https://github.com/jiahao/backus-dijkstra-letters-1979)
(see [this page](#the-letter)).

This repository encodes two variants; one is based on a refinement
of a dependent inductive type magic trick I learned from the Lean
[reference](https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/)
("_Example: Inaccessible Patterns_") which allows for _literally_ pattern
matching a natural number on `2 * n` and `2 * n + 1`, following the
notation in the letter to the letter.

```lean
inductive Parity : Nat -> Type where
  | even (n : Nat) : Parity (2 * n)
  | odd  (n : Nat) : Parity (2 * n + 1)

def parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | 1 => .odd  0
  | n + 2 => match parity n with
    | .even h => .even (h + 1)
    | .odd  h => .odd  (h + 1)
termination_by structural n

def f : Nat -> Nat
| 0 => 0
| 1 => 1
| m@(_ + 2) => match m, parity m with
  | .(2 * n),     .even n => f n
  | .(2 * n + 1), .odd  n => f n + f (n + 1)
```

However, this encoding breaks tactics like `grind`, `fun_induction`,
`fun_cases`, `cases`, `split`, `rw`, etc. because attempting to
substitute an equality `n = m` into the term `parity n : Parity
n` simultaneously rewrites both the term and its type. It is also
difficult to use `match` without providing an explicit motive.

The other encoding is a straightforward recursive
definition of `even` and is more amenable to automation.

```lean
def is_even : Nat -> Bool
  | 0 => true
  | 1 => false
  | n + 2 => is_even n
termination_by structural n => n

def g (n : Nat) (a : Nat := 1) (b : Nat := 0) :=
  match n with
  | 0 => b
  | n@(_ + 1) => match is_even n with
    | true  => g ((n - 0) / 2) (a + b) b
    | false => g ((n - 1) / 2) a (b + a)
```

## Checking

The proofs are checked with
[comparator](https://github.com/leanprover/comparator)
and the entire toolchain is precisely managed with Nix.

Enter the right directory and run

```shell
nix run
```

to check the proof (which uses `landrun` and `systemd-run`
for runtime isolation). Alternatively, check the proofs with
`nix build {even,parity,mixed}`. Building in the Nix sandbox
provides more reproducibility guarantees but is not designed
for security, so the two checks are complementary.

## The letter

![letter to Backus](https://misc.cgdct.moe/repos/1978-05-29-dijkstra-p4.jpg)
