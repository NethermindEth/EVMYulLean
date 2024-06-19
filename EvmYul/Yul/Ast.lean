/- Yul specification:
https://docs.soliditylang.org/en/v0.8.9/yul.html
-/

import EvmYul.UInt256
import EvmYul.Operations
import EvmYul.Wheels

namespace EvmYul

namespace Yul

namespace Ast

open EvmYul UInt256

abbrev Literal := UInt256
-- def Identifier := String

instance : ToString Identifier := inferInstanceAs (ToString String)

instance : Inhabited Identifier := ⟨""⟩
instance : DecidableEq Identifier := String.decEq

abbrev PrimOp := Operation .Yul

def stringOfPrimOp : PrimOp → String := toString ∘ repr

instance : ToString PrimOp := ⟨stringOfPrimOp⟩

-- https://docs.soliditylang.org/en/latest/yul.html#informal-description-of-yul

mutual
  inductive FunctionDefinition where
    | Def : List Identifier → List Identifier → List Stmt → FunctionDefinition

  inductive Expr where
    | PrimCall : PrimOp → List Expr → Expr
    | Call : FunctionDefinition → List Expr → Expr
    | Var : Identifier → Expr
    | Lit : Literal → Expr

  -- | The loop constructor 'Stmt.For' has no initialiser because of
  -- https://docs.soliditylang.org/en/latest/internals/optimizer.html#forloopinitrewriter
  inductive Stmt where
    | Block : List Stmt → Stmt
    | Let : List Identifier → Stmt
    | LetEq : Identifier → Expr → Stmt
    | LetCall : List Identifier → FunctionDefinition → List Expr → Stmt
    | LetPrimCall : List Identifier → PrimOp → List Expr → Stmt
    | Assign : Identifier → Expr → Stmt
    | AssignCall : List Identifier → FunctionDefinition → List Expr → Stmt
    | AssignPrimCall : List Identifier → PrimOp → List Expr → Stmt
    | ExprStmtCall : FunctionDefinition → List Expr -> Stmt
    | ExprStmtPrimCall : PrimOp → List Expr -> Stmt
    | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
    | For : Expr → List Stmt → List Stmt → Stmt
    | If : Expr → List Stmt → Stmt
    | Continue : Stmt
    | Break : Stmt
    | Leave : Stmt
end

namespace FunctionDefinition

def params : FunctionDefinition → List Identifier
  | Def params _ _ => params

def rets : FunctionDefinition → List Identifier
  | Def _ rets _ => rets

def body : FunctionDefinition → List Stmt
  | Def _ _ body => body

end FunctionDefinition

end Ast

end Yul

end EvmYul
