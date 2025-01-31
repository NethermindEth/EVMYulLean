import Batteries.Data.Array.Lemmas

import Mathlib.Tactic.Linarith

namespace Array

section Array

variable {α : Type}

def splitAt (n : Nat) (l : Array α) : Array α × Array α :=
  (l.extract 0 n, l.extract n l.size)

section splitAt

variable {l : Array α} {n : Nat}

@[simp]
theorem splitAt_size_lt_lt : (l.splitAt n).2.size = l.size - n := by simp [splitAt]

end splitAt

-- def take (n : Nat) (l : Array α) : Array α := l.extract 0 n

section take

variable {l : Array α} {n : Nat}

theorem size_take_of_le (h : n ≤ l.size) : (l.take n).size = n := by simp only [size_take, inf_eq_left]; linarith

@[simp]
theorem splitAt_1_eq_take : (l.splitAt n).1 = l.take n := by sorry


end take

def drop (n : Nat) (l : Array α) : Array α := l.extract n l.size

section drop

variable {l : Array α} {n : Nat} {i : Nat}

@[simp]
theorem size_drop : (l.drop i).size = l.size - i := by simp [drop]

@[simp]
theorem splitAt_2_eq_drop : (l.splitAt n).2 = l.drop n := by simp [drop, splitAt]

end drop

end Array

end Array
