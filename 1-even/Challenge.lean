def is_even : Nat -> Bool
  | 0 => true
  | 1 => false
  | n + 2 => is_even n
termination_by structural n => n

def f : Nat -> Nat
| 0 => 0
| 1 => 1
| m@(_ + 2) => match is_even m with
  | true  => let n := (m - 0) / 2; f n
  | false => let n := (m - 1) / 2; f n + f (n + 1)

def g (n : Nat) (a : Nat := 1) (b : Nat := 0) :=
  match n with
  | 0 => b
  | n@(_ + 1) => match is_even n with
    | true  => g ((n - 0) / 2) (a + b) b
    | false => g ((n - 1) / 2) a (b + a)

theorem f_eq_g (n : Nat) : f n = g n := by
  sorry
