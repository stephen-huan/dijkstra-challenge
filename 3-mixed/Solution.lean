set_option maxHeartbeats 4096

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
  | n@(_ + 1) => match is_even n with
    | true  => g ((n - 0) / 2) (a + b) b
    | false => g ((n - 1) / 2) a (b + a)

theorem parity_equal {n : Nat} (a b : Parity n) : a = b := by
  grind only [Parity]

theorem even_true {n : Nat} (h : ∃ k, n = 2 * k) : is_even n = true := by
  fun_induction is_even n with
  | case1 => decide
  | case2 => omega
  | case3 n ih => match h with
    | ⟨k, _⟩ => exact ih ⟨k - 1, by omega⟩

theorem odd_false {n : Nat} (h : ∃ k, n = 2 * k + 1) : is_even n = false := by
  fun_induction is_even n with
  | case1 => omega
  | case2 => decide
  | case3 n ih => match h with
    | ⟨k, _⟩ => exact ih ⟨k - 1, by omega⟩

@[simp]
theorem n2 {n : Nat} : is_even (2 * n + 2) = true := even_true ⟨n + 1, rfl⟩

@[simp]
theorem n3 {n : Nat} : is_even (2 * n + 3) = false := odd_false ⟨n + 1, rfl⟩

@[simp]
theorem div2 (n : Nat) : (2 * n + 2) / 2 = n + 1 := by omega

theorem g_ab (n a b c d : Nat) : g n a b + g n c d = g n (a + c) (b + d) :=
  match n with
  | 0 => by unfold g; rfl
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) a b + g (n + 1) c d = g (n + 1) (a + c) (b + d)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [
        odd_false ⟨h, rfl⟩, (by ac_rfl : (b + a) + (d + c) = (b + d) + (a + c))
      ] using g_ab h a (b + a) c (d + c)
    | .(2 * h + 1), .odd h, _ => by
      simpa [(by ac_rfl : (a + b) + (c + d) = (a + c) + (b + d))]
        using g_ab (h + 1) (a + b) b (c + d) d

theorem g_nb (n b : Nat) : g n 1 b + g (n + 1) = g n 1 (b + 1) :=
  match n with
  | 0 => by unfold g g; rfl
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) 1 b + g (n + 2) = g (n + 1) 1 (b + 1)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [odd_false ⟨h, rfl⟩] using g_nb h (b + 1)
    | .(2 * h + 1), .odd h, _ => by simpa using g_ab (h + 1) (1 + b) b 1 1

theorem f_eq_g (n : Nat) : f n = g n :=
  match n with
  | 0 => by unfold f g; rfl
  | 1 => by unfold f g g; rfl
  | n@(m + 2) => match (
    motive := (n : Nat) -> Parity n -> n = m -> f (n + 2) = g (n + 2)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [(parity_equal (parity (2 * h + 2)) (Parity.even (h + 1)))]
        using f_eq_g (h + 1)
    | .(2 * h + 1), .odd h, _ => by
      simpa [
        parity_equal (parity (2 * h + 3)) (Parity.odd (h + 1)),
        f_eq_g (h + 1),
        f_eq_g (h + 2),
      ] using g_nb (h + 1) 0
