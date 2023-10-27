import Mathlib.Algebra.Ring.Basic

namespace MyRing

variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_neg_cancel_right c a, add_comm c a, ← h, add_comm a b, add_neg_cancel_right]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    . rw [← add_mul, zero_add, zero_add]
  exact add_right_cancel h

#check MyRing.add_zero
#check add_zero

#print add_left_cancel

end MyRing

macro Γ:term "|-" e:term ":" τ:term : term => `(Typing $Γ $e $τ )

syntax (priority := high) "↑" term : term

macro_rules
  | `(↑ $x) => `(⟨$x, by simp⟩)

def getOrElse (m : Option String) (e : String) : String := match m with
  | some x => x
  | none => e

def isInt (s : String) :=
  let alp := List.contains "0123456789".data
  let rec f := (match · with
    | [] => false
    | [c] => alp c
    | c :: cs => alp c ∧ f cs)
  f s.data

structure Date where
  month : { n : Nat // 1 <= n ∧ n <= 12 }
  day : { n : Nat // 1 <= n ∧ n <= 31 }
  year : { n : Nat // 1900 ≤ n ∧ n ≤ 2100 }

syntax (priority := high) "@[[" term "," term "," term "]]!" : term

macro_rules
  | `(@[[ $m, $d, $y ]]!) => `({ month := ↑ $m, day := ↑ $d, year := ↑ $y : Date })

example : Date := @[[ 11, 19, 2010 ]]!

def IntString := { s : String // isInt s }

def goodString : IntString := ↑"128379812398172391236871263988"
def badString  : IntString := ↑"1029381092830192830291309120873a"

theorem x : False = ¬True := by simp

#print x

example (x : Nat) (hx : x ∈ (∅ : Set Nat)) : p := absurd hx id

syntax "`0s" term: term

-- def from_seximal (n : Nat) := match n with
-- | 0 => 0
-- | n => 6 * from_seximal ((n - n % 10) / 10) + n % 10

-- #eval from_seximal 100

-- macro_rules
--   | `(`0s$x) => `(from_seximal $x)

-- #eval `0s123