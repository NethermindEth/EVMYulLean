import EvmYul.Yul.Ast

namespace EvmYul

namespace Yul

namespace SizeLemmas

section

open EvmYul Ast Expr Stmt FunctionDefinition

variable {expr arg : Expr}
         {stmt : Stmt}
         {exprs args args' : List Expr}
         {stmts : List Stmt}
         {f : FunctionDefinition}
         {prim : PrimOp}
         {α : Type}
         {xs ys : List α}

-- ============================================================================
--  SIZEOF LEMMAS
-- ============================================================================

@[simp]
lemma Zero.zero_le {n : ℕ} : Zero.zero ≤ n := by ring_nf; exact Nat.zero_le _

@[simp]
lemma List.zero_lt_sizeOf : 0 < sizeOf xs
:= by
  rcases xs <;> simp

@[simp]
lemma List.reverseAux_size : sizeOf (List.reverseAux args args') = sizeOf args + sizeOf args' - 1 := by
  induction args generalizing args' with
    | nil => simp
    | cons z zs ih =>
      aesop (config := {warnOnNonterminal := false}); omega

@[simp]
lemma List.reverse_size : sizeOf (args.reverse) = sizeOf args := by
  unfold List.reverse
  rw [List.reverseAux_size]
  simp

/--
  Expressions have positive size.
-/ 
@[simp]
lemma Expr.zero_lt_sizeOf : 0 < sizeOf expr := by
  rcases expr <;> simp

@[simp]
lemma Stmt.sizeOf_stmt_ne_0 : sizeOf stmt ≠ 0 := by cases stmt <;> aesop

/--
  Statements have positive size.
-/
@[simp]
lemma Stmt.zero_lt_sizeOf : 0 < sizeOf stmt := by
  have : sizeOf stmt ≠ 0 := by simp
  omega

/--
  Lists of expressions have positive size.
-/
@[simp]
lemma Expr.zero_lt_sizeOf_List : 0 < sizeOf exprs := by
  have : sizeOf exprs ≠ 0 := by cases exprs <;> aesop
  omega

@[simp]
lemma Expr.sizeOf_head_lt_sizeOf_List : sizeOf expr < sizeOf (expr :: exprs) := by
  simp +arith

@[simp]
lemma Expr.sizeOf_tail_lt_sizeOf_List : sizeOf exprs < sizeOf (expr :: exprs) := by
  simp

/--
  Lists of statements have positive size.
-/
@[simp]
lemma Stmt.zero_lt_sizeOf_List : 0 < sizeOf stmts := by cases stmts <;> aesop

/--
  Function definitions have positive size.
-/
@[simp]
lemma FunctionDefinition.zero_lt_sizeOf : 0 < sizeOf f := by cases f; aesop


@[simp]
lemma Expr.sizeOf_args_lt_sizeOf_PrimCall : sizeOf args < sizeOf (PrimCall prim args) := by
  simp

/--
  The size of the body of a function is less than the size of the function itself.
-/
@[simp]
lemma FunctionDefinition.sizeOf_body_lt_sizeOf : sizeOf (body f) < sizeOf f := by unfold body; aesop

lemma FunctionDefinition.sizeOf_body_succ_lt_sizeOf : sizeOf (FunctionDefinition.body f) + 1 < sizeOf f := by
  cases f
  unfold body
  simp +arith
  exact le_add_right List.zero_lt_sizeOf

/--
  The size of the head of a list of statements is less than the size of a block containing the whole list.
-/
@[simp]
lemma Stmt.sizeOf_head_lt_sizeOf : sizeOf stmt < sizeOf (Block (stmt :: stmts)) := by
  simp only [Block.sizeOf_spec, List.cons.sizeOf_spec]
  linarith

/--
  The size of the head of a list of statements is less than the size of a block containing the whole list.
-/
@[simp]
lemma Stmt.sizeOf_head_lt_sizeOf_tail : sizeOf (Block stmts) < sizeOf (Block (stmt :: stmts)) := by simp

end

end SizeLemmas

end Yul

end EvmYul
