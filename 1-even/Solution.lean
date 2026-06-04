set_option maxHeartbeats 4096

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

theorem even_or_odd (n : Nat) : is_even n = true ∨ is_even n = false := by
  cases is_even n <;> decide

theorem even_odd {n : Nat} : is_even n = true -> is_even (n + 1) = false := by
  fun_induction is_even <;> grind only [is_even]

theorem odd_even {n : Nat} : is_even n = false -> is_even (n + 1) = true := by
  fun_induction is_even <;> grind only [is_even]

theorem g_ab (n a b c d : Nat) : g n a b + g n c d = g n (a + c) (b + d) := by
  unfold g
  cases n with
  | zero => rfl
  | succ n =>
    dsimp only
    cases is_even (n + 1) with
    | true => simpa [(by ac_rfl : (a + b) + (c + d) = (a + c) + (b + d))]
        using g_ab ((n + 1) / 2) (a + b) b (c + d) d
    | false => simpa [(by ac_rfl : (b + a) + (d + c) = (b + d) + (a + c))]
        using g_ab ((n + 0) / 2) a (b + a) c (d + c)

theorem g_nb (n b : Nat) : g n 1 b + g (n + 1) = g n 1 (b + 1) := by
  unfold g
  cases n with
  | zero => unfold g; rfl
  | succ n =>
    dsimp only
    cases even_or_odd (n + 1) with
    | inl h => rw [h, even_odd h]; exact g_ab ((n + 1) / 2) (1 + b) b 1 1
    | inr h => simpa [h, (odd_even h), (by omega : (n + 2) / 2 = n / 2 + 1)]
      using g_nb (n / 2) (b + 1)

theorem f_eq_g (n : Nat) : f n = g n := by
  fun_induction f with
  | case1 => unfold g; rfl
  | case2 => unfold g g; rfl
  | case3 _ h _ ih => unfold g; rw [h, ih]
  | case4 _ h m ih1 ih2 => unfold g; rw [h, ih1, ih2]; exact g_nb m 0
