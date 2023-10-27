import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic

-- def sum [Add α] [Zero α] (list: List α) : α :=
--   match list with
--     | List.nil => 0
--     | List.cons x xs => x + sum xs

-- def range (a b : ℤ) (hleq : a ≤ b) : List ℤ :=
--   if h : a == b then []
--   else
--     have h₁ : a ≠ b := by simp at h; assumption
--     have h₂ : a < b := Int.lt_iff_le_and_ne.mpr (And.intro hleq h₁)
--     have h₃ : a + 1 ≤ b := by linarith
--     a :: range (a + 1) b h₃

-- termination_by range a b _ => b - a

-- def range (a b : ℤ) (hleq : a ≤ b) : List ℤ :=
--   if h : a == b then []
--   else
--     have h₁ : a ≠ b := by simp at h; assumption
--     have h₂ : a < b := Int.lt_iff_le_and_ne.mpr (And.intro hleq h₁)
--     have h₃ : a + 1 ≤ b := by linarith
--     a :: range (a + 1) b h₃

-- termination_by range a b _ => b - a

example := Int.range 1 10

def sum_from (a b : ℤ) (f : ℤ → ℤ) := List.sum $ (Int.range a b).map f

theorem sum_same : sum_from a a f = 0 := by simp [sum_from, Int.range]
theorem sum_diff : sum_from a (Nat.succ b) f = sum_from a b f + f b := sorry

declare_syntax_cat psuedo_program
declare_syntax_cat psuedo_block

syntax "PROGRAM" psuedo_block "END PROGRAM" : psuedo_program
syntax "FOR" term "IN" term "DO" psuedo_block "END FOR" : psuedo_block
syntax "IF" term "DO" psuedo_block "END IF" : psuedo_block
syntax ">" term : psuedo_block

syntax "!!<" psuedo_program ">!!" : term
syntax "!!< b_parse" psuedo_block ">!!" : term

macro_rules
  | `(!!< PROGRAM $block END PROGRAM >!!) => `(!!< b_parse $block >!!)
  | `(!!< b_parse FOR $t IN $l DO $block END FOR >!!) => `(List.map (fun $t => !!< b_parse $block >!!) $l)
  | `(!!< b_parse > $term >!!) => `($term)

def my_program := !!<
  PROGRAM
    FOR x IN (Int.range 1 10) DO
      FOR y IN (Int.range 1 10) DO
        > x * y * (List.prod !!< PROGRAM FOR _ IN (Int.range 1 5) DO > x END FOR END PROGRAM >!!)
      END FOR
    END FOR
  END PROGRAM
>!!

#eval my_program