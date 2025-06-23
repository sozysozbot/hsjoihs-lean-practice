import Mathlib.Algebra.Ring.Defs

inductive TropicalNat where
  | fromNat : Nat → TropicalNat
  | infinity

-- multiplication in tropical arithmetic is addition in normal arithmetic
def TropicalNat.mul (a b : TropicalNat) : TropicalNat :=
  match b with
  | .infinity => TropicalNat.infinity
  | .fromNat n => match a with
    | .infinity => TropicalNat.infinity
    | .fromNat m => TropicalNat.fromNat (m + n)

-- addition in tropical arithmetic is minimum in normal arithmetic
def TropicalNat.add (a b : TropicalNat) : TropicalNat :=
  match a, b with
  | .infinity, b => b
  | a, .infinity => a
  | .fromNat m, .fromNat n => TropicalNat.fromNat (min m n)

instance : Add TropicalNat where
  add a b := TropicalNat.add a b

instance : Mul TropicalNat where
  mul a b := TropicalNat.mul a b

instance : Zero TropicalNat where
  zero := TropicalNat.infinity

instance : One TropicalNat where
  one := TropicalNat.fromNat 0

infix:70 " ⊕τ " => TropicalNat.add
infix:90 " ⊗τ " => TropicalNat.mul

@[simp] theorem TropicalNat.add_zero (a : TropicalNat) : a ⊕τ TropicalNat.infinity = a := by
  match a with
  | .infinity => rfl
  | .fromNat n => rfl

@[simp] theorem TropicalNat.zero_add (a : TropicalNat) : TropicalNat.infinity ⊕τ a = a := by
  match a with
  | .infinity => rfl
  | .fromNat n => rfl

@[simp] theorem TropicalNat.mul_zero (a : TropicalNat) : a ⊗τ TropicalNat.infinity = TropicalNat.infinity := by
  match a with
  | .infinity => rfl
  | .fromNat n => rfl

@[simp] theorem TropicalNat.zero_mul (a : TropicalNat) : TropicalNat.infinity ⊗τ a = TropicalNat.infinity := by
  match a with
  | .infinity => rfl
  | .fromNat n => rfl

theorem TropicalNat.add_assoc (m n k : TropicalNat) : (m ⊕τ n) ⊕τ k = m ⊕τ (n ⊕τ k) := by
  match m with
  | .infinity => simp only [TropicalNat.zero_add, TropicalNat.zero_add]
  | .fromNat m' =>
    match n with
    | .infinity =>
      simp only [add_zero, zero_add]
    | .fromNat n' =>
      match k with
      | .infinity =>
        simp only [add_zero, zero_add]
      | .fromNat k' =>
        simp only [TropicalNat.add, Nat.min_assoc]

theorem TropicalNat.add_comm (m n : TropicalNat) : m ⊕τ n = n ⊕τ m := by
  match m, n with
  | .infinity, _ => simp only [TropicalNat.zero_add, TropicalNat.add_zero]
  | _, .infinity => simp only [TropicalNat.add_zero, TropicalNat.zero_add]
  | .fromNat m', .fromNat n' => rw [TropicalNat.add, TropicalNat.add, Nat.min_comm]

instance : Std.Associative (α := TropicalNat) (· ⊕τ ·) where
  assoc := TropicalNat.add_assoc

instance : Std.Commutative (α := TropicalNat) (· ⊕τ ·) where
  comm := TropicalNat.add_comm

theorem TropicalNat.mul_comm (m n : TropicalNat) : m ⊗τ n = n ⊗τ m := by
  match m, n with
  | .infinity, _ => simp only [TropicalNat.zero_mul, TropicalNat.mul_zero]
  | _, .infinity => simp only [TropicalNat.mul_zero, TropicalNat.zero_mul]
  | .fromNat m', .fromNat n' =>
    rw [TropicalNat.mul, TropicalNat.mul, Nat.add_comm]

instance : Std.Commutative (α := TropicalNat) (· ⊗τ ·) where
  comm := TropicalNat.mul_comm

theorem TropicalNat.mul_assoc (m n k : TropicalNat) : (m ⊗τ n) ⊗τ k = m ⊗τ (n ⊗τ k) := by
  match m with
  | .infinity => simp only [TropicalNat.zero_mul, TropicalNat.mul_zero]
  | .fromNat m' =>
    match n with
    | .infinity =>
      simp only [TropicalNat.mul_zero, TropicalNat.zero_mul]
    | .fromNat n' =>
      match k with
      | .infinity =>
        simp only [TropicalNat.mul_zero, TropicalNat.zero_mul]
      | .fromNat k' =>
        simp only [TropicalNat.mul, Nat.add_assoc]

instance : Std.Associative (α := TropicalNat) (· ⊗τ ·) where
  assoc := TropicalNat.mul_assoc

theorem distrib_succ (n k : Nat): min n k + 1 = min (n + 1) (k + 1) := by
  repeat rw [Nat.min_def]
  by_cases h : n ≤ k
  case pos =>
    simp [h]
  case neg =>
    simp [h]

theorem TropicalNat.left_distrib (m n k : TropicalNat) :
  m ⊗τ (n ⊕τ k) = m ⊗τ n ⊕τ m ⊗τ k := by
  match m with
  | .infinity =>
    simp only [TropicalNat.zero_mul, TropicalNat.mul_zero, TropicalNat.add_zero]
  | .fromNat m' =>
    match n with
    | .infinity =>
      simp only [TropicalNat.zero_add, TropicalNat.add_zero, TropicalNat.mul_zero]
    | .fromNat n' =>
      match k with
      | .infinity =>
        simp only [TropicalNat.zero_add, TropicalNat.add_zero, TropicalNat.mul_zero]
      | .fromNat k' =>
        simp only [TropicalNat.mul, TropicalNat.add, Nat.add_assoc, Nat.add_comm]
        have h : m' + min n' k' = min (m' + n') (m' + k') := by
          induction m' with
          | zero => simp
          | succ l h =>
            rw [show l + 1 + min n' k' = l + min n' k' + 1 from by ac_rfl]
            rw [show l + 1 + n' = l + n' + 1 from by ac_rfl]
            rw [show l + 1 + k' = l + k' + 1 from by ac_rfl]
            rw [← distrib_succ]
            rw [h]
        rw [h]

theorem TropicalNat.right_distrib (m n k : TropicalNat) :
  (m ⊕τ n) ⊗τ k = m ⊗τ k ⊕τ n ⊗τ k := by
  rw [TropicalNat.add_comm m n]
  rw [TropicalNat.add_comm (m ⊗τ k) (n ⊗τ k)]
  rw [TropicalNat.mul_comm n k]
  rw [TropicalNat.mul_comm m k]
  rw [TropicalNat.mul_comm (n ⊕τ m) k]
  exact TropicalNat.left_distrib k n m

theorem TropicalNat.one_mul (n : TropicalNat) : TropicalNat.fromNat 0 ⊗τ n = n := by
  match n with
  | .infinity => rfl
  | .fromNat n' => rw [TropicalNat.mul, Nat.zero_add]

theorem TropicalNat.mul_one (n : TropicalNat) : n ⊗τ TropicalNat.fromNat 0 = n := by
  match n with
  | .infinity => rfl
  | .fromNat n' => rw [TropicalNat.mul, Nat.add_zero]

def TropicalNat.nsmul := fun n a =>
    match n with
    | 0 => TropicalNat.infinity
    | Nat.succ _ => a -- minimum of n copies of a is just a

theorem TropicalNat.nsmul_zero (a : TropicalNat) : TropicalNat.nsmul 0 a = TropicalNat.infinity := by
  rfl

theorem TropicalNat.nsmul_n_zero (n : Nat) : TropicalNat.nsmul n TropicalNat.infinity = TropicalNat.infinity := by
  cases n with
  | zero => rfl
  | succ n' => rw [TropicalNat.nsmul]

@[simp] theorem TropicalNat.add_self (a : TropicalNat) : a ⊕τ a = a := by
  match a with
  | .infinity => rfl
  | .fromNat n =>
    rw [TropicalNat.add, Nat.min_self]


instance : Semiring TropicalNat where
  add := (· ⊕τ ·)
  mul := (· ⊗τ ·)

  zero := TropicalNat.infinity
  one  := TropicalNat.fromNat 0

  add_comm    := TropicalNat.add_comm
  add_assoc   := TropicalNat.add_assoc
  zero_add    := TropicalNat.zero_add
  add_zero    := TropicalNat.add_zero

  mul_assoc   := TropicalNat.mul_assoc
  one_mul     := TropicalNat.one_mul
  mul_one     := TropicalNat.mul_one
  zero_mul    := TropicalNat.zero_mul
  mul_zero    := TropicalNat.mul_zero

  left_distrib  := TropicalNat.left_distrib
  right_distrib := TropicalNat.right_distrib

  nsmul := TropicalNat.nsmul
  nsmul_zero := TropicalNat.nsmul_zero
  nsmul_succ := by
    intro n a
    match a with
    | .infinity =>
      repeat rw [TropicalNat.nsmul_n_zero]
      rfl
    | .fromNat m =>
      simp only [TropicalNat.nsmul]
      cases n with
      | zero => rfl
      | succ n' =>
        simp only [TropicalNat.nsmul]
        rw [show TropicalNat.fromNat m + TropicalNat.fromNat m = TropicalNat.fromNat m ⊕τ TropicalNat.fromNat m by rfl]
        rw [TropicalNat.add_self]
