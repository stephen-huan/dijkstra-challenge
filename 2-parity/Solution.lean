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

theorem n_le_2n {n : Nat}: n ≤ 2 * n := calc n
  _ ≤ n + n := Nat.le_add_right n n
  _ = 0 + n + n := by rw [Nat.add_comm 0 n]; rfl
  _ = n * 2 := rfl
  _ = 2 * n := Nat.mul_comm n 2

@[simp low]
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

-- adapted from Init.Data.Nat.Basic
-- probably not the most efficient for the terminal goals

theorem add_sub_self_left (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero => exact Nat.zero_add b
  | succ a ih => rw [Nat.succ_add, Nat.succ_sub_succ]; apply ih

theorem add_sub_self_right (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]; apply add_sub_self_left

theorem add_sub_add_right (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change n + k + 1 - (m + k + 1) = n - m
    rw [Nat.succ_sub_succ_eq_sub]
    exact ih

theorem add_sub_cancel (n m : Nat) : n + m - m = n :=
  suffices n + m - (0 + m) = n by rw [Nat.zero_add] at this; assumption
  by rw [add_sub_add_right, Nat.sub_zero]

theorem pred_mul (n m : Nat) : Nat.pred n * m = n * m - m := by
  cases n with
  | zero   => change 0 * m = 0 * m - m; rw [Nat.zero_mul, Nat.zero_sub]
  | succ n => rw [Nat.pred_succ, Nat.succ_mul, add_sub_cancel]

theorem sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

theorem mul_sub_right_distrib (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => rw [Nat.zero_mul]; rfl
  | succ m ih => rw [Nat.sub_succ, pred_mul, ih, Nat.add_one_mul, sub_sub]

theorem mul_sub_left_distrib (n m k : Nat) : n * (m - k) = n * m - n * k := by
  rw [Nat.mul_comm, mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

theorem one_lt_2n (n : Nat) (h : 0 < n) : 1 < 2 * n := match n with
  | 0 => False.elim $ Nat.lt_irrefl 0 h
  | m + 1 => Nat.lt_add_of_pos_left $ Nat.add_one_pos (2 * m)

theorem add_left_cancel {n m k : Nat} : n + m = n + k → m = k := by
  induction n with
  | zero => intro h; (repeat rw [Nat.add_comm 0 _] at h); exact h
  | succ n ih =>
    intro h
    conv at h =>
      congr; all_goals rw [Nat.add_assoc, Nat.add_comm 1 _, <- Nat.add_assoc]
    exact ih (congrArg Nat.pred h)

theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match Nat.le.dest h with
  | ⟨d, hd⟩ =>
    apply @Nat.le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply add_left_cancel hd

theorem le_of_add_le_add_right {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  rw [Nat.add_comm _ b, Nat.add_comm _ b]
  apply le_of_add_le_add_left

-- user theorems

theorem one_ne_2n (n : Nat) : 1 ≠ 2 * n := match n with
  | 0 => by decide
  | m + 1 => Nat.ne_of_lt $ one_lt_2n (m + 1) (Nat.add_one_pos m)

theorem one_not_even (n m : Nat) : 2 * n + 1 ≠ 2 * m := by
  intro this
  rw [Nat.add_comm] at this
  have := congrArg (fun x => x - 2 * n) this
  change 1 + 2 * n - 2 * n = 2 * m - 2 * n at this
  rw [add_sub_self_right 1 (2 * n)] at this
  suffices 1 = 2 * (m - n) from absurd this $ one_ne_2n (m - n)
  rw [mul_sub_left_distrib]
  exact this

theorem par_equal {n : Nat} {a b : Parity n} : a = b :=
  eq_of_heq $ match (
    motive := (x y : Nat) -> n = x -> n = y -> (a : Parity x) -> (b : Parity y)
      -> a ≍ b
  ) n, n, rfl, rfl, a, b with
  | .(2 * k), .(2 * h), _, _, .even k, .even h => by
    rename n = 2 * k => p
    rename n = 2 * h => q
    suffices k = h from this ▸ (HEq.refl $ Parity.even k)
    suffices 2 * k = 2 * h from Nat.eq_of_mul_eq_mul_left (by decide) this
    rw [<- p, <- q]
  | .(2 * k + 1), .(2 * h), _, _, .odd k, .even h => by
    rename n = 2 * k + 1 => p
    rename n = 2 * h => q
    suffices 2 * k + 1 = 2 * h from absurd this (one_not_even k h)
    rw [p] at q
    exact q
  | .(2 * k), .(2 * h + 1), _, _, .even k, .odd h => by
    rename n = 2 * k => p
    rename n = 2 * h + 1 => q
    suffices 2 * h + 1 = 2 * k from absurd this (one_not_even h k)
    rw [q] at p
    exact p
  | .(2 * k + 1), .(2 * h + 1), _, _, .odd k, .odd h => by
    rename n = 2 * k + 1 => p
    rename n = 2 * h + 1 => q
    suffices k = h from this ▸ (HEq.refl $ Parity.odd k)
    suffices 2 * k + 1 = 2 * h + 1 from Nat.eq_of_mul_eq_mul_left
      (by decide) (congrArg Nat.pred this)
    rw [<- p, <- q]

@[simp]
theorem par1 {n : Nat} : parity (2 * n + 1) = Parity.odd n := par_equal

@[simp]
theorem par2 {n : Nat} : parity (2 * n + 2) = Parity.even (n + 1) := par_equal

@[simp]
theorem par3 {n : Nat} : parity (2 * n + 3) = Parity.odd (n + 1) := par_equal

theorem g_fuel (n a b fuel : Nat) (h : n ≤ fuel) : g n a b fuel = g n a b :=
  match n, fuel with
  | n, 0 => by rw [Nat.le_antisymm h (Nat.zero_le ..)]
  | 0, fuel => by cases fuel <;> rfl
  | n@(m + 1), fuel + 1 => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) a b (fuel + 1) = g (n + 1) a b
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [g, g_fuel h a (b + a) (2 * h) n_le_2n]
        using g_fuel h a (b + a) fuel (calc h
          _ ≤ 2 * h := n_le_2n
          _ = m := by assumption
          m ≤ fuel := le_of_add_le_add_right (by assumption)
        )
    | .(2 * h + 1), .odd h, _ => by
      unfold g
      simpa [
        g_fuel (h + 1) (a + b) b (2 * h + 1) (Nat.add_le_add_right n_le_2n 1)
      ] using g_fuel (h + 1) (a + b) b fuel (calc h + 1
        _ ≤ 2 * h + 1 := Nat.add_le_add_right n_le_2n 1
        _ = m := by assumption
        m ≤ fuel := le_of_add_le_add_right (by assumption)
      )
termination_by n
decreasing_by
  iterate 2
    change h < m + 1
    rename 2 * h = m => p
    rw [<- p]
    exact n_lt_2np1
  iterate 2
    change h + 1 < m + 1
    rename 2 * h + 1 = m => p
    rw [<- p]
    exact Nat.succ_lt_succ $ n_lt_2np1

@[simp]
theorem fuel_2n {n a b : Nat} : g n a b = g n a b (2 * n) :=
  Eq.symm $ g_fuel n a b (2 * n) n_le_2n

@[simp]
theorem fuel_2np1 {n a b : Nat} : g (n + 1) a b (2 * n + 1) = g (n + 1) a b :=
  g_fuel (n + 1) a b (2 * n + 1) (Nat.add_le_add_right n_le_2n 1)

theorem swap {a b c d : Nat} : (a + b) + (c + d) = (a + c) + (b + d) := by rw [
  Nat.add_assoc,
  <- Nat.add_assoc b c d,
  Nat.add_comm b c,
  Nat.add_assoc c b d,
  Nat.add_assoc,
]

theorem g_ab (n a b c d : Nat) : g n a b + g n c d = g n (a + c) (b + d) :=
  match n with
  | 0 => by unfold g; rfl
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) a b + g (n + 1) c d = g (n + 1) (a + c) (b + d)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by
      simpa [g, (swap : (b + a) + (d + c) = (b + d) + (a + c))]
        using g_ab h a (b + a) c (d + c)
    | .(2 * h + 1), .odd h, _ => by
      unfold g; simpa [(swap : (a + b) + (c + d) = (a + c) + (b + d))]
        using g_ab (h + 1) (a + b) b (c + d) d
termination_by n
decreasing_by
  . change h < m + 1
    rename 2 * h = m => p
    rw [<- p]
    exact n_lt_2np1
  . change h + 1 < m + 1
    rename 2 * h + 1 = m => p
    rw [<- p]
    exact Nat.succ_lt_succ $ n_lt_2np1

theorem g_nb (n b : Nat) : g n 1 b + g (n + 1) = g n 1 (b + 1) :=
  match n with
  | 0 => rfl
  | n@(m + 1) => match (
    motive := (n : Nat) -> Parity n -> n = m
      -> g (n + 1) 1 b + g (n + 2) = g (n + 1) 1 (b + 1)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by unfold g; simpa using g_nb h (b + 1)
    | .(2 * h + 1), .odd h, _ => by
      unfold g
      simpa using g_ab (h + 1) (1 + b) b 1 1
termination_by n
decreasing_by
  . change h < m + 1
    rename 2 * h = m => p
    rw [<- p]
    exact n_lt_2np1

theorem f_eq_g (n : Nat) : f n = g n :=
  match n with
  | 0 => by unfold f; rfl
  | 1 => by unfold f; rfl
  | n@(m + 2) => match (
    motive := (n : Nat) -> Parity n -> n = m -> f (n + 2) = g (n + 2)
  ) m, parity m, rfl with
    | .(2 * h), .even h, _ => by unfold g; simpa using f_eq_g (h + 1)
    | .(2 * h + 1), .odd h, _ => by
      unfold g
      simpa [f_eq_g (h + 1), f_eq_g (h + 2)] using g_nb (h + 1) 0
termination_by n
decreasing_by
  . change h + 1 < m + 2
    rename 2 * h = m => p
    rw [<- p]
    exact Nat.succ_lt_succ $ n_lt_2np1
  . change h + 1 < m + 2
    rename 2 * h + 1 = m => p
    rw [<- p]
    exact Nat.le.step $ Nat.succ_lt_succ $ n_lt_2np1
  . change h + 2 < m + 2
    rename 2 * h + 1 = m => p
    rw [<- p]
    exact Nat.succ_lt_succ $ Nat.succ_lt_succ $ n_lt_2np1

#print axioms f_eq_g
