inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr

notation "ℕ" => MyNat

-- for automatically modifing the default natural numbers to our implementation
def nat_to_mynat (n: Nat): MyNat :=
  match n with
  | Nat.zero => MyNat.zero
  | Nat.succ (n') => MyNat.succ (nat_to_mynat (n'))

instance : OfNat MyNat n where
  ofNat := nat_to_mynat (n)

-- for converting in the other direction
def mynat_to_nat (n: MyNat): Nat :=
  match n with
  | MyNat.zero => Nat.zero
  | MyNat.succ (n') => Nat.succ (mynat_to_nat (n'))
  

open MyNat

def add(m: MyNat) (n: MyNat) : MyNat :=
  match n with
  | zero => m
  | succ (n') => succ (add (m) (n'))

instance : Add MyNat where
  add:= add

example : add (5) (6) = 11 := rfl
example : add (0) (1) = 1 := rfl
example : (0: MyNat) + (1: MyNat) = 1 := rfl
example : (1: MyNat) + (1: MyNat) = 2 :=  rfl


def mul (m n : MyNat) : MyNat :=
  match n with
  | zero => zero
  -- 4 * 3 => 4 + 4 * 2 => 4 + 4 + 4 * 1 => 4 + 4 + 4 => 12
  | succ n' => add m (mul m n')

instance: Mul MyNat where
  mul:= mul

example : mul (3) (4) = 12 := rfl
example : mul 4 0 = 0 := rfl
example : mul 0 4 = 0 := rfl
example : (5: MyNat) * (6: MyNat) = 30 := rfl

def pow(m n: MyNat) : MyNat :=
  match n with
  | zero => 1
  | succ n' => mul m (pow m n')

instance: Pow MyNat MyNat where
  pow:= pow

example : pow (1) (0) = 1 := rfl
example : 2 ^ (3: MyNat) = 8 := rfl
example : pow (3) (2) = 9 := rfl
example : zero ^ (2) = 0 := rfl
example : zero ^ (0) = 1 := rfl