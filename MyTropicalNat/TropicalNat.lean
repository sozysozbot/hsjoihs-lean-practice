import Mathlib.Algebra.Ring.Defs

inductive TropicalNat where
  | fromNat : Nat → TropicalNat
  | infinity

namespace TropicalNat

-- multiplication in tropical arithmetic is addition in normal arithmetic
def mul (a b : TropicalNat) : TropicalNat :=
  match a, b with
  | .infinity, _
  | _, .infinity => infinity
  | .fromNat a, .fromNat b => fromNat (a + b)

-- addition in tropical arithmetic is minimum in normal arithmetic
def add (a b : TropicalNat) : TropicalNat :=
  match a, b with
  | .infinity, b => b
  | a, .infinity => a
  | .fromNat m, .fromNat n => fromNat (min m n)

instance : Add TropicalNat where
  add a b := add a b

instance : Mul TropicalNat where
  mul a b := mul a b

instance : Zero TropicalNat where
  zero := infinity

instance : One TropicalNat where
  one := fromNat 0

infix:70 " ⊕τ " => add
infix:90 " ⊗τ " => mul

@[simp] theorem add_zero (a : TropicalNat) : a ⊕τ infinity = a := by rcases a <;> rfl;

@[simp] theorem zero_add (a : TropicalNat) : infinity ⊕τ a = a := by rcases a <;> rfl;

@[simp] theorem mul_zero (a : TropicalNat) : a ⊗τ infinity = infinity := by rcases a <;> rfl;

@[simp] theorem zero_mul (a : TropicalNat) : infinity ⊗τ a = infinity := by rcases a <;> rfl;

theorem add_assoc (m n k : TropicalNat) : (m ⊕τ n) ⊕τ k = m ⊕τ (n ⊕τ k) := by
  match m, n, k with
  | .infinity, _, _
  | _, .infinity, _
  | _, _, .infinity =>
    simp [zero_mul, add_zero]
  | .fromNat m, .fromNat n, .fromNat k =>
    simp only [add, Nat.min_assoc]

theorem add_comm (m n : TropicalNat) : m ⊕τ n = n ⊕τ m := by
  match m, n with
  | .infinity, _
  | _, .infinity => simp [zero_add, add_zero]
  | .fromNat m', .fromNat n' => simp [add, Nat.min_comm]

instance : Std.Associative (· ⊕τ ·) where
  assoc := add_assoc

instance : Std.Commutative (· ⊕τ ·) where
  comm := add_comm

theorem mul_comm (m n : TropicalNat) : m ⊗τ n = n ⊗τ m := by
  match m, n with
  | .infinity, _
  | _, .infinity => simp [zero_mul, mul_zero]
  | .fromNat m', .fromNat n' => simp only [mul, Nat.add_comm]

instance : Std.Commutative (α := TropicalNat) (· ⊗τ ·) where
  comm := mul_comm

theorem mul_assoc (m n k : TropicalNat) : (m ⊗τ n) ⊗τ k = m ⊗τ (n ⊗τ k) := by
  match m, n, k with
  | .infinity, _, _
  | _, .infinity, _
  | _, _, .infinity =>
    simp [zero_mul, add_zero]
  | .fromNat m, .fromNat n, .fromNat k =>
    simp only [mul, Nat.add_assoc]

instance : Std.Associative (· ⊗τ ·) where
  assoc := mul_assoc

theorem distrib_succ (n k : Nat): min n k + 1 = min (n + 1) (k + 1) := by
  simp only [Nat.min_def, Nat.add_le_add_iff_right]
  by_cases h : n ≤ k <;> simp [h]

theorem left_distrib (m n k : TropicalNat) : m ⊗τ (n ⊕τ k) = m ⊗τ n ⊕τ m ⊗τ k := by
  match m, n, k with
  | .infinity, _, _
  | _, .infinity, _
  | _, _, .infinity =>
    simp [zero_mul, add_zero]
  | .fromNat m, .fromNat n, .fromNat k =>
    simp [mul, add, Nat.add_min_add_left];

theorem right_distrib (m n k : TropicalNat) : (m ⊕τ n) ⊗τ k = m ⊗τ k ⊕τ n ⊗τ k := calc
  (m ⊕τ n) ⊗τ k = (n ⊕τ m) ⊗τ k    := by simp [add_comm]
  _             = k ⊗τ (n ⊕τ m)    := by simp [mul_comm]
  _             = k ⊗τ n ⊕τ k ⊗τ m := by apply left_distrib
  _             = n ⊗τ k ⊕τ m ⊗τ k := by simp [mul_comm]
  _             = m ⊗τ k ⊕τ n ⊗τ k := by simp [add_comm]

theorem one_mul (n : TropicalNat) : fromNat 0 ⊗τ n = n := by
  match n with
  | .infinity => rfl
  | .fromNat n' => rw [mul, Nat.zero_add]

theorem mul_one (n : TropicalNat) : n ⊗τ fromNat 0 = n := by
  match n with
  | .infinity => rfl
  | .fromNat n' => rw [mul, Nat.add_zero]

def nsmul := fun n a =>
  match n with
  | 0     => infinity
  | _ + 1 => a -- minimum of n copies of a is just a

theorem nsmul_zero (a : TropicalNat) : nsmul 0 a = infinity := rfl

theorem nsmul_n_zero (n : Nat) : nsmul n infinity = infinity := by
  match n with
  | 0 => rfl
  | n + 1 => rw [nsmul]

@[simp] theorem add_self (a : TropicalNat) : a ⊕τ a = a := by
  match a with
  | .infinity => rfl
  | .fromNat n => rw [add, Nat.min_self]


instance : Semiring TropicalNat where
  add := (· ⊕τ ·)
  mul := (· ⊗τ ·)

  zero := infinity
  one  := fromNat 0

  add_comm    := add_comm
  add_assoc   := add_assoc
  zero_add    := zero_add
  add_zero    := add_zero

  mul_assoc   := mul_assoc
  one_mul     := one_mul
  mul_one     := mul_one
  zero_mul    := zero_mul
  mul_zero    := mul_zero

  left_distrib  := left_distrib
  right_distrib := right_distrib

  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := by
    intro n a;
    match n, a with
    | _, .infinity=> simp only [nsmul_n_zero]; rfl
    | 0, .fromNat m => dsimp [nsmul]; rfl;
    | n + 1, .fromNat m =>
      dsimp [nsmul];
      rw [show fromNat m + fromNat m = fromNat m ⊕τ fromNat m by rfl]
      simp [add_self]

end TropicalNat
