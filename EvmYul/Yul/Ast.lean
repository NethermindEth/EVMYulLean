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

abbrev YulFunctionName := String

mutual
  inductive FunctionDefinition where
    | Def : List Identifier → List Identifier → List Stmt → FunctionDefinition
  deriving BEq, Inhabited

  inductive Expr where
    | Call : (PrimOp ⊕ YulFunctionName) → List Expr → Expr
    | Var : Identifier → Expr
    | Lit : Literal → Expr

  -- | The loop constructor 'Stmt.For' has no initialiser because of
  -- https://docs.soliditylang.org/en/latest/internals/optimizer.html#forloopinitrewriter
  inductive Stmt where
    | Block : List Stmt → Stmt
    | Let : List Identifier → Option Expr → Stmt
    | Assign : List Identifier → Expr → Stmt
    | ExprStmtCall : Expr → Stmt
    | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
    | For : Expr → List Stmt → List Stmt → Stmt
    | If : Expr → List Stmt → Stmt
    | Continue : Stmt
    | Break : Stmt
    | Leave : Stmt
    deriving BEq, Inhabited, Repr
end

structure YulContract where
  dispatcher : Yul.Ast.Stmt
  functions : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition)
  deriving Inhabited

instance : Repr YulContract where
  reprPrec _ _ := "YulContract" -- TODO: implement an actual `reprPrec` for YulContract

instance : BEq YulContract where
  beq a b := 
    a.dispatcher == b.dispatcher
    && (a.functions.keys == b.functions.keys &&
        a.functions.all (λ k _ => a.functions.lookup k == b.functions.lookup k))

abbrev contractCode (τ : OperationType) :=
  match τ with
    | OperationType.EVM => ByteArray
    | OperationType.Yul => YulContract

instance {τ} : BEq (contractCode τ) where
  beq a b := match τ with
              | .EVM => a == b
              | .Yul => a == b

instance {τ} : Inhabited (contractCode τ) where
  default := match τ with
                | .EVM => default
                | .Yul => default
              
instance {τ} : Repr (contractCode τ) where
  reprPrec a _ := match τ with
                     | .EVM => reprPrec a 0
                     | .Yul => reprPrec a 0


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
