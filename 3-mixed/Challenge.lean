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

def is_even : Nat -> Bool
  | 0 => true
  | 1 => false
  | n + 2 => is_even n
termination_by structural n => n

def f : Nat -> Nat
| 0 => 0
| 1 => 1
| m@(_ + 2) => match m, parity m with
  | .(2 * n),     .even n => f n
  | .(2 * n + 1), .odd  n => f n + f (n + 1)

def g (n : Nat) (a : Nat := 1) (b : Nat := 0) :=
  match n with
  | 0 => b
  | n@(_ + 1) => match is_even n with
    | true  => g ((n - 0) / 2) (a + b) b
    | false => g ((n - 1) / 2) a (b + a)

theorem f_eq_g (n : Nat) : f n = g n := by
  sorry
