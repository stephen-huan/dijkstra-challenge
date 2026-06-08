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

def transport (n : Nat) : Prop :=
  match n with
  | 0 => True
  | Nat.succ _ => False

theorem n_lt_2n {n a : Nat} (h : 2 * n = a + 1) : n < 2 * n := match n with
  -- Nat.succ_ne_zero depends on propext
  | 0 => False.elim $ Eq.subst (motive := transport) h trivial
  | 1 => by decide
  | _ + 2 => Nat.le.step $ Nat.succ_lt_succ $ n_lt_2n rfl

theorem n_lt_2np1 {n : Nat} : n < 2 * n + 1 := match n with
  | 0 => by decide
  | _ + 1 => Nat.le.step $ Nat.succ_lt_succ $ n_lt_2np1

def f : Nat -> Nat
| 0 => 0
| 1 => 1
| m@(_ + 2) => match m, parity m with
  | .(2 * n),     .even n => f n
  | .(2 * n + 1), .odd  n => f n + f (n + 1)
-- https://github.com/leanprover/lean4/pull/7965
termination_by n => (n, 0)
decreasing_by
  all_goals rename_i a _ p
  . apply Prod.Lex.left
    change n < a + 2
    rw [<- p]
    exact n_lt_2n p
  . apply Prod.Lex.left
    change n < a + 2
    rw [<- p]
    exact n_lt_2np1
  . apply Prod.Lex.left
    change n + 1 < a + 2
    rw [<- p]
    exact Nat.succ_lt_succ $ n_lt_2n $ congrArg Nat.pred p

def g (n : Nat) (a : Nat := 1) (b : Nat := 0) (fuel : Nat := n) :=
  match n, fuel with
  | _, 0
  | 0, _ => b
  | n@(_ + 1), fuel + 1 => match n, parity n with
    | .(2 * h),     .even h => g h (a + b) b fuel
    | .(2 * h + 1), .odd  h => g h a (b + a) fuel
termination_by structural fuel

theorem f_eq_g (n : Nat) : f n = g n := by
  sorry
