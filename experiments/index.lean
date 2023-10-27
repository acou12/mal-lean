import Mathlib.Data.Set.Basic
import Mathlib.Tactic

def O (g : ℤ → ℤ) : Set (ℤ → ℤ) :=
  fun f => ∃ N k, ∀ n ≥ N, f n ≤ k * g n

def Ω (g : ℤ → ℤ) : Set (ℤ → ℤ) :=
  fun f => ∃ N k, ∀ n ≥ N, f n ≥ k * g n

def Θ (g : ℤ → ℤ) : Set (ℤ → ℤ) := O g ∩ Ω g  

theorem ge_coeff (a n : ℤ) (ha : a ≥ 1) (hn : n ≥ 1) : a * n ≥ n := by
  have := Int.mul_le_mul ha (Int.le_refl n) (Int.le_of_lt hn) (Int.le_of_lt ha)
  simp at this
  exact this

theorem quadratic_o_n2 (a b c : ℤ) (positive : a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1)
  : (fun n => a * n ^ 2 + b * n + c) ∈ O (fun n => n ^ 2) :=
  
  let f := fun n => a * n ^ 2 + b * n + c
  let g := fun n => n ^ 2

  show ∃ N k, ∀ n ≥ N, f n ≤ k * g n from
    ⟨1, (a + b + c),
        fun n => fun hgen => calc f n
          _ = a * n^2 + b * n + c := rfl
          _ ≤ a * n^2 + b * n + c * n^2 := by linarith [ge_coeff (n^2) c (sorry) (positive.right.right)]
          _ ≤ a * n^2 + b * n^2 + c * n^2 := by sorry
          _ = (a + b + c) * n^2 := by ring
          _ = (a + b + c) * g n := by rfl
    ⟩

theorem x
  (a n : ℤ) (k l : ℕ) 
  (hkl : k ≤ l)
  (ha : a ≥ 0)
  (hn : n ≥ 0)
  : a * n^k ≤ a * n^l := sorry

namespace Test

noncomputable def dist (x y : ℝ) := abs (x - y)

def is_interior_point_of (x : ℝ) (E : Set ℝ) := ∀ r > 0, ∀ y, dist x y < r → y ∈ E

def open_set (E : Set ℝ) := ∀ x ∈ E, is_interior_point_of x E 

def is_limit_point_of (x : ℝ) (E : Set ℝ) := ∀ r > 0, ∃ y ∈ E, dist x y < r 

def limit_points (E : Set ℝ) : Set ℝ := fun x => x ∈ E ∧ is_limit_point_of x E

def closed_set (E : Set ℝ) := limit_points E ⊆ E

def bounded (E : Set ℝ) : Prop := ∃ x r, r > 0 ∧ ∀ y ∈ E, dist x y < r

open Classical

theorem R_not_bounded : ¬ bounded (Real.real) := by
  intro hb
  match hb with
  | ⟨x, r, hr, hydist⟩ =>
    . let y := x + 10 * r
      have : ¬ (dist x y < r) := by
        simp
        rw [dist]
        ring_nf
        simp only [abs]
        ring_nf
        admit
      have hd := hydist y
      







def reals : Set ℝ := fun _ => true

def nonempty_bounded_clopen_real_nonexistence : ¬ ∃ E, open_set E ∧ closed_set E ∧ Nonempty E ∧ bounded E := by
  intro existsE
  match existsE with
  | ⟨E, openE, closedE, nonemptyE, boundedE⟩ =>
    . match nonemptyE with
      | ⟨x, hx⟩ =>
        . admit
          
          
      



end Test