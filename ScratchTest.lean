import Mathlib.Tactic

namespace ScratchTest
open scoped Classical

variable {α : Type} [DecidableEq α]

def Cx (C : α → Option Bool) (v : α) (b : Bool) : α → Option Bool :=
  fun x => if x = v then some b else C x

-- TEST 1: ext + if_pos rw path
example (A : Finset α) (C : α → Option Bool) (v : α) (b : Bool) :
    A.filter (fun x => Cx C v b x = none) = (A.filter fun x => C x = none).erase v := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase, Cx]
  by_cases hxv : x = v
  · rw [if_pos hxv]
    simp [hxv]
  · rw [if_neg hxv]
    simp [hxv]

-- TEST 2: sum over Bool
example (f : Bool → ℝ) : (∑ x : Bool, f x) = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_insert (by simp), Finset.sum_singleton]

-- TEST 3: push_neg name survival
example (h : ¬ ∃ x : α, x = v ∧ x = v) : True := by
  push_neg at h
  have h2 := h
  trivial

-- TEST 4: split_ifs variant for same filter goal
example (A : Finset α) (C : α → Option Bool) (v : α) (b : Bool) :
    A.filter (fun x => Cx C v b x = none) = (A.filter fun x => C x = none).erase v := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase, Cx]
  split_ifs with hxv <;> simp [hxv]

end ScratchTest
