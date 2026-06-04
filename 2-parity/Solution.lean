set_option maxHeartbeats 4096

inductive Parity : Nat -> Type where
  | even (n : Nat) : Parity (2 * n)
  | odd (n : Nat) : Parity (2 * n + 1)

def parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | 1 => .odd  0
  | n + 2 => match parity n with
    | .even h => .even (h + 1)
    | .odd  h => .odd  (h + 1)
termination_by structural n

@[simp low]
def f : Nat -> Nat
| 0 => 0
| 1 => 1
| m@(_ + 2) => match m, parity m with
  | .(2 * n),     .even n => f n
  | .(2 * n + 1), .odd  n => f n + f (n + 1)

@[simp]
def g (n : Nat) (a : Nat := 1) (b : Nat := 0) :=
  match n with
  | 0 => b
  | n@(_ + 1) => match n, parity n with
    | .(2 * h),     .even h => g h (a + b) b
    | .(2 * h + 1), .odd  h => g h a (b + a)

theorem par_equal {n : Nat} {a b : Parity n} : a = b := by grind only [Parity]

@[simp]
theorem par1 {n : Nat} : parity (2 * n + 1) = Parity.odd n := par_equal

@[simp]
theorem par2 {n : Nat} : parity (2 * n + 2) = Parity.even (n + 1) := par_equal

@[simp]
theorem par3 {n : Nat} : parity (2 * n + 3) = Parity.odd (n + 1) := par_equal

theorem g_ab (n a b c d : Nat) : g n a b + g n c d = g n (a + c) (b + d) :=
  match n with
  | 0 => by unfold g; rfl
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) a b + g (n + 1) c d = g (n + 1) (a + c) (b + d)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [(by ac_rfl : (b + a) + (d + c) = (b + d) + (a + c))]
        using g_ab h a (b + a) c (d + c)
    | .(2 * h + 1), .odd h, _ => by
      simpa [(by ac_rfl : (a + b) + (c + d) = (a + c) + (b + d))]
        using g_ab (h + 1) (a + b) b (c + d) d

theorem g_nb (n b : Nat) : g n 1 b + g (n + 1) = g n 1 (b + 1) :=
  match n with
  | 0 => by simp [(par_equal : parity 1 = Parity.odd 0)]
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) 1 b + g (n + 2) = g (n + 1) 1 (b + 1)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by simpa using g_nb h (b + 1)
    | .(2 * h + 1), .odd h, _ => by simpa using g_ab (h + 1) (1 + b) b 1 1

theorem f_eq_g (n : Nat) : f n = g n :=
  match n with
  | 0 => by unfold f g; rfl
  | 1 => by unfold f g g; rfl
  | n@(m + 2) => match (
    motive := (n : Nat) -> Parity n -> n = m -> f (n + 2) = g (n + 2)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by simpa using f_eq_g (h + 1)
    | .(2 * h + 1), .odd h, _ => by
      simpa [f_eq_g (h + 1), f_eq_g (h + 2)] using g_nb (h + 1) 0
