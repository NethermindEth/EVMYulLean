namespace EvmYul

abbrev Stack (α : Type) := List α

namespace Stack

variable {α : Type}

def new : Stack α := []

def isEmpty (s : Stack α) := List.isEmpty s

def size (s : Stack α) : Nat := List.length s
def push (s : Stack α) (v : α) : Stack α := v :: s

def pop : Stack α → Option (Stack α × α)
  | hd :: tl => .some (tl, hd)
  | []       => .none

def pop2 : Stack α → Option (Stack α × α × α)
  | hd :: hd₁ :: tl => .some (tl, hd, hd₁)
  | _               => .none

def pop3 : Stack α → Option (Stack α × α × α × α)
  | hd :: hd₁ :: hd₂ :: tl => .some (tl, hd, hd₁, hd₂)
  | _                      => .none

def pop4 : Stack α → Option (Stack α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: tl => .some (tl, hd, hd₁, hd₂, hd₃)
  | _                             => .none

def pop5 : Stack α → Option (Stack α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄)
  | _                             => .none

def pop6 : Stack α → Option (Stack α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅)
  | _                             => .none

def pop7 : Stack α → Option (Stack α × α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: hd₆ :: tl =>
    .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆)
  | _                             => .none

section StackLemmas

variable {x : α} {s : Stack α}

@[simp]
theorem isEmpty_push_false : (s.push x).isEmpty = false := rfl

@[simp]
theorem isEmpty_nil : Stack.isEmpty (α := α) [] := rfl

@[simp]
theorem isEmpty_cons_false : Stack.isEmpty (α := α) (x :: s) = false := rfl

@[simp]
theorem size_nil : Stack.size (α := α) [] = 0 := rfl

@[simp]
theorem size_new : Stack.new.size (α := α) = 0 := rfl

@[simp]
theorem size_cons : Stack.size (α := α) (x :: s) = Stack.size s + 1 := rfl

theorem size_zero_iff_isEmpty_eq_true : s.size = 0 ↔ s.isEmpty = true := by
  cases s <;> simp

@[simp]
theorem size_push : (s.push x).size = s.size + 1 := rfl

@[simp]
theorem pop_push : (s.push x).pop = some (s, x) := rfl

end StackLemmas

instance {α} : Inhabited (Stack α) := ⟨Stack.new⟩
instance {α} [DecidableEq α] : DecidableEq (Stack α) := inferInstanceAs (DecidableEq (List α))
instance {α} : EmptyCollection (Stack α) := ⟨Stack.new⟩

end Stack

instance {α : Type} [ToString α] : ToString (Stack α) := inferInstanceAs (ToString (List α))

end EvmYul
