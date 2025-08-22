import EvmYul.Yul.Ast
import Lean.Parser
import EvmYul.Operations

namespace EvmYul

namespace Yul

namespace Notation

open Ast Lean Parser Elab Term

def yulKeywords := ["let", "if", "default", "switch", "case"]

def idFirstChar : Array Char := Id.run <| do
  let mut arr := #[]
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('a'.toNat + i))
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('A'.toNat + i))
  arr := (arr.push '_').push '$'
  return arr

def idSubsequentChar : Array Char := Id.run <| do
  let mut arr := idFirstChar
  for i in [0:10] do
    arr := arr.push (Char.ofNat ('0'.toNat + i))
  return arr.push '.'

def idFn : ParserFn := fun c s => Id.run do
  let input := c.input
  let start := s.pos
  if h : input.atEnd start then
    s.mkEOIError
  else
    let fst := input.get' start h
    if not (idFirstChar.contains fst) then
      return s.mkError "yul identifier"
    let s := takeWhileFn idSubsequentChar.contains c (s.next input start)
    let stop := s.pos
    let name := .str .anonymous (input.extract start stop)
    if yulKeywords.contains name.lastComponentAsString then
      return s.mkError "yul identifier"
    mkIdResult start none name c s

def idNoAntiquot : Parser := { fn := idFn }

section
open PrettyPrinter Parenthesizer Syntax.MonadTraverser Formatter

@[combinator_formatter idNoAntiquot]
def idNoAntiquot.formatter : Formatter := do
  Formatter.checkKind identKind
  let Syntax.ident info _ idn _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  Formatter.pushToken info idn.toString true
  goLeft

@[combinator_parenthesizer idNoAntiquot]
def idNoAntiquot.parenthesizer := Parenthesizer.visitToken
end

@[run_parser_attribute_hooks]
def ident : Parser := withAntiquot (mkAntiquot "ident" identKind) idNoAntiquot

declare_syntax_cat expr
declare_syntax_cat stmt

syntax identifier_list := ident,*
syntax typed_identifier_list := ident,*
syntax function_call := ident "(" expr,* ")"
syntax block := "{" stmt* "}"
syntax if' := "if" expr block
syntax function_definition :=
  "function" ident "(" typed_identifier_list ")"
    ("->" typed_identifier_list)?
    block
syntax params_list := "[" typed_identifier_list "]"
syntax variable_declaration := "let" ident (":=" expr)?
-- syntax let_str_literal := "let" ident ":=" str -- TODO(fix)
syntax variable_declarations := "let" typed_identifier_list (":=" expr)?
syntax for_loop := "for" block expr block block
syntax assignment := identifier_list ":=" expr

syntax stmtlist := stmt*

syntax block : stmt
syntax if' : stmt
syntax function_definition : stmt
syntax variable_declarations : stmt
syntax assignment : stmt
syntax expr : stmt
-- syntax let_str_literal : stmt -- TODO(fix)
syntax for_loop : stmt
syntax "break" : stmt
syntax "continue" : stmt
syntax "leave" : stmt

syntax ident : expr
syntax numLit : expr
syntax function_call: expr

syntax default := "default" "{" stmt* "}"
syntax case := "case" expr "{" stmt* "}"
syntax switch := "switch" expr case+ (default)?
syntax switch_default := "switch" expr default

syntax switch : stmt
syntax switch_default : stmt

scoped syntax:max "<<" expr ">>" : term
scoped syntax:max "<f" function_definition ">" : term
scoped syntax:max "<s" stmt ">" : term
scoped syntax:max "<ss" stmt ">" : term
scoped syntax:max "<params" params_list ">" : term

partial def translatePrimOp (primOp : PrimOp) : TermElabM Term := do
  let (family, instr) ← familyAndInstr primOp
  PrettyPrinter.delab (
    ←Lean.Meta.mkAppM
      family.toName
      #[←Lean.Meta.mkAppOptM instr.toName #[mkConst YulTag]]
  )
  where
    familyAndInstr (primOp : PrimOp) : TermElabM (String × String) := do
      let family :: instr :: [] := toString primOp |>.splitOn | throwError s!"{primOp} shape not <family> <instruction>"
      pure (family, instr.drop 1 |>.dropRight 1)
    YulTag : Name := "EvmYul.OperationType.Yul".toName

partial def translateIdent (idn : TSyntax `ident) : TSyntax `term :=
  Syntax.mkStrLit idn.getId.lastComponentAsString

def parseFunction : String → PrimOp ⊕ Identifier
  | "add" => .inl .ADD
  | "sub" => .inl .SUB
  | "mul" => .inl .MUL
  | "div" => .inl .DIV
  | "sdiv" => .inl .SDIV
  | "mod" => .inl .MOD
  | "smod" => .inl .SMOD
  | "addmod" => .inl .ADDMOD
  | "mulmod" => .inl .MULMOD
  | "exp" => .inl .EXP
  | "signextend" => .inl .SIGNEXTEND
  | "lt" => .inl .LT
  | "gt" => .inl .GT
  | "slt" => .inl .SLT
  | "sgt" => .inl .SGT
  | "eq" => .inl .EQ
  | "iszero" => .inl .ISZERO
  | "and" => .inl .AND
  | "or" => .inl .OR
  | "xor" => .inl .XOR
  | "not" => .inl .NOT
  | "byte" => .inl .BYTE
  | "shl" => .inl .SHL
  | "shr" => .inl .SHR
  | "sar" => .inl .SAR
  | "keccak256" => .inl .KECCAK256
  | "address" => .inl .ADDRESS
  | "balance" => .inl .BALANCE
  | "origin" => .inl .ORIGIN
  | "caller" => .inl .CALLER
  | "callvalue" => .inl .CALLVALUE
  | "calldataload" => .inl .CALLDATALOAD
  | "calldatacopy" => .inl .CALLDATACOPY
  | "calldatasize" => .inl .CALLDATASIZE
  | "codesize" => .inl .CODESIZE
  | "codecopy" => .inl .CODECOPY
  | "gasprice" => .inl .GASPRICE
  | "extcodesize" => .inl .EXTCODESIZE
  | "extcodecopy" => .inl .EXTCODECOPY
  | "extcodehash" => .inl .EXTCODEHASH
  | "returndatasize" => .inl .RETURNDATASIZE
  | "returndatacopy" => .inl .RETURNDATACOPY
  | "blockhash" => .inl .BLOCKHASH
  | "coinbase" => .inl .COINBASE
  | "timestamp" => .inl .TIMESTAMP
  | "gaslimit" => .inl .GASLIMIT
  | "chainid" => .inl .CHAINID
  | "selfbalance" => .inl .SELFBALANCE
  | "mload" => .inl .MLOAD
  | "mstore" => .inl .MSTORE
  | "sload" => .inl .SLOAD
  | "sstore" => .inl .SSTORE
  | "msize" => .inl .MSIZE
  | "gas" => .inl .GAS
  | "pop" => .inl .POP
  | "revert" => .inl .REVERT
  | "return" => .inl .RETURN
  | "call" => .inl .CALL
  | "staticcall" => .inl .STATICCALL
  | "delegatecall" => .inl .DELEGATECALL
  -- | "loadimmutable" => .inl  .LOADI
  -- | "log0" => .inl .LOG0
  | "log1" => .inl .LOG1
  | "log2" => .inl .LOG2
  | "log3" => .inl .LOG3
  | "log4" => .inl .LOG4
  | "number" => .inl .NUMBER
  | userF => .inr userF

partial def translateExpr (expr : TSyntax `expr) : TermElabM Term :=
  match expr with
    | `(expr| $idn:ident) => `(Expr.Var $(translateIdent idn))
    | `(expr| $num:num) => `(Expr.Lit (.ofNat $num))
    | `(expr| $name:ident($args:expr,*)) => do
      let args' ← (args : TSyntaxArray `expr).mapM translateExpr
      let f' := parseFunction (TSyntax.getId name).lastComponentAsString
      match f' with
        | .inl primOp =>
          let primOp ← translatePrimOp primOp
          `(Expr.PrimCall $primOp [$args',*])
        | .inr _ =>
          `(Expr.Call $name [$args',*])
    | _ => throwError "unknown expr"

partial def translateExpr' (expr : TSyntax `expr) : TermElabM Term :=
  match expr with
  | `(expr| $num:num) => `(.ofNat $num)
  | exp => translateExpr exp

partial def translateParamsList
  (params : TSyntax `EvmYul.Yul.Notation.params_list)
: TermElabM Term :=
  match params with
  | `(params_list| [ $args:ident,* ]) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    `([$args',*])
  | _ => throwError (toString params.raw)

mutual
partial def translateFdef
  (fdef : TSyntax `EvmYul.Yul.Notation.function_definition)
: TermElabM Term :=
  match fdef with
  | `(function_definition| function $_:ident($args:ident,*) {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(EvmYul.Yul.Ast.FunctionDefinition.Def [$args',*] [] [$body',*])
  | `(function_definition| function $_:ident($args:ident,*) -> $rets,* {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let rets' := (rets : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(EvmYul.Yul.Ast.FunctionDefinition.Def [$args',*] [$rets',*] [$body',*])
  | _ => throwError (toString fdef.raw)

partial def translateStmt (stmt : TSyntax `stmt) : TermElabM Term :=
  match stmt with

  -- Block
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `(Stmt.Block ([$stmts',*]))

  -- If
  | `(stmt| if $cond:expr {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let body' ← body.mapM translateStmt
    `(Stmt.If $cond' [$body',*])

  -- Function Definition
  | `(stmt| $fdef:function_definition) => do
    let fdef' ← translateFdef fdef
    `(Stmt.FunctionDefinition $fdef')

  -- Switch
  | `(stmt| switch $expr:expr $[case $lits { $cs:stmt* }]* $[default { $dflts:stmt* }]?) => do
    let expr ← translateExpr expr
    let lits ← lits.mapM translateExpr'
    let cases ← cs.mapM (λ cc ↦ cc.mapM translateStmt)
    let f (litCase : TSyntax `term × Array Term) : TermElabM Term := do
      let (lit, cs) := litCase; `(($lit, [$cs,*]))
    let switchCases ← lits.zip cases |>.mapM f
    let dflt ← match dflts with
                 | .none => `([.Break])
                 | .some dflts => `([$(←dflts.mapM translateStmt),*])
    `(Stmt.Switch $expr [$switchCases,*] $dflt)

  -- Switch
  | `(stmt| switch $expr:expr default {$dflts:stmt*}) => do
    let expr ← translateExpr expr
    let dflt ← dflts.mapM translateStmt
    `(Stmt.Switch $expr [] ([$dflt,*]))

  -- LetCall
  | `(stmt| let $ids:ident,* := $f:ident ( $es:expr,* )) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let f' := parseFunction (TSyntax.getId f).lastComponentAsString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp ← translatePrimOp primOp
        `(Stmt.LetPrimCall [$ids',*] $primOp [$es',*])
      | .inr _ =>
        `(Stmt.LetCall [$ids',*] $f [$es',*])

  -- LetEq
  | `(stmt| let $idn:ident := $init:expr) => do
    let idn' := translateIdent idn
    let expr' ← translateExpr init
    `(Stmt.LetEq $idn' $expr')

  -- TODO(fix)
  -- | `(stmt| let $idn:ident := $s:str) => do
  --   let idn' := translateIdent idn
  --   `(Stmt.LetEq $idn' _)

  -- Let
  | `(stmt| let $ids:ident,*) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    `(Stmt.Let [$ids',*])

  -- AssignCall
  | `(stmt| $ids:ident,* := $f:ident ( $es:expr,* )) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let f' := parseFunction (TSyntax.getId f).lastComponentAsString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp ← translatePrimOp primOp
        `(Stmt.AssignPrimCall [$ids',*] $primOp [$es',*])
      | .inr _ =>
        `(Stmt.AssignCall [$ids',*] $f [$es',*])

  -- Assign
  | `(stmt| $idn:ident := $init:expr) => do
    let idn' := translateIdent idn
    let expr' ← translateExpr init
    `(Stmt.Assign $idn' $expr')

  -- ExprStmt
  | `(stmt| $f:ident ( $es:expr,* )) => do
    let f' := parseFunction (TSyntax.getId f).lastComponentAsString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp ← translatePrimOp primOp
        `(Stmt.ExprStmtPrimCall $primOp [$es',*])
      | .inr _ =>
        `(Stmt.ExprStmtCall $f [$es',*])

  -- For
  | `(stmt| for {} $cond:expr {$post:stmt*} {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let post' ← post.mapM translateStmt
    let body' ← body.mapM translateStmt
    `(Stmt.For $cond' [$post',*] [$body',*])

  -- Break
  | `(stmt| break) => `(Stmt.Break)

  -- Continue
  | `(stmt| continue) => `(Stmt.Continue)

  -- Leave
  | `(stmt| leave) => `(Stmt.Leave)

  -- Anything else
  | _ => throwError (toString stmt.raw)
end

partial def translateStmtList (stmt : TSyntax `stmt) : TermElabM Term :=
  match stmt with
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `([$stmts',*])
  | _ => throwError (toString stmt.raw)

private def elabWith {β : SyntaxNodeKinds}
  (x : Syntax) (translator : TSyntax β → TermElabM Term) : TermElabM Lean.Expr := do
  elabTerm (←translator (TSyntax.mk (ks := β) x)) .none

elab "<<" e:expr ">>"               : term => elabWith e translateExpr
elab "<f" f:function_definition ">" : term => elabWith f translateFdef
elab "<s" s:stmt ">"                : term => elabWith s translateStmt
elab "<ss" ss:stmt ">"              : term => elabWith ss translateStmtList
elab "<params" p:params_list ">"    : term => elabWith p translateParamsList

def f : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>

example : <params [a,b,c] > = ["a", "b", "c"] := rfl
example : << bar >> = Expr.Var "bar" := rfl
example : << 42 >> = Expr.Lit ⟨42⟩ := rfl
example : <s break > = Stmt.Break := rfl
-- example : <s let a, b := f(42) > = Stmt.LetCall ["a", "b"] f [Expr.Lit ⟨42⟩] := rfl -- TODO: resolve
example : <s let a > = Stmt.Let ["a"] := rfl
example : <s let a := 5 > = Stmt.LetEq "a" (.Lit ⟨5⟩) := rfl
-- example : <s a, b := f(42) > = Stmt.AssignCall ["a", "b"] f [Expr.Lit ⟨42⟩] := rfl -- TODO: resolve
example : <s a := 42 > = Stmt.Assign "a" (.Lit ⟨42⟩) := rfl

example : <s c := add(a, b) > = Stmt.AssignPrimCall ["c"] (Operation.StopArith Operation.SAOp.ADD) [Expr.Var "a", Expr.Var "b"] := rfl
example : <s let c := sub(a, b) > = Stmt.LetPrimCall ["c"] (Operation.StopArith Operation.SAOp.SUB) [Expr.Var "a", Expr.Var "b"] := rfl
example : <s let a := 5 > = Stmt.LetEq "a" (.Lit ⟨5⟩) := rfl
example : <s {} >
  = Stmt.Block [] := rfl
example : <s
{
  break
  let a := 5
  break
}
> = Stmt.Block [<s break>, <s let a := 5>, <s break>] := rfl
example : <s
  if a {
    let b := 5
    break
  }
> = Stmt.If <<a>> [<s let b := 5>, <s break >] := rfl

example : <ss {
  let a
  let b
  let c
} > = [<s let a>, <s let b>, <s let c>] := rfl

example : <s for {} 0 {} {} > = Stmt.For (.Lit ⟨0⟩) [] [] := by rfl

example : <<
  add(1, 1)
  >> = Expr.PrimCall (Operation.StopArith Operation.SAOp.ADD) [Expr.Lit ⟨1⟩, Expr.Lit ⟨1⟩] := rfl

example : <s
  for {} lt(i, exponent) { i := add(i, 1) }
  {
    result := mul(result, base)
  }
> = Stmt.For <<lt(i, exponent)>> [<s i := add(i, 1)>]
      [<s result := mul(result, base)>] := rfl

def sort2 : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>

def no_rets : FunctionDefinition := <f
  function no_rets(a, b) {
  }
>

example : <s
  switch a
  case 42 { continue }
  default { break }
> = Stmt.Switch (Expr.Var "a") [(⟨42⟩, [.Continue])] [.Break] := rfl

example : <s let a, b, c > = Stmt.Let ["a", "b", "c"] := rfl
example : <s revert(0, 0) > = Stmt.ExprStmtPrimCall (.System (.REVERT)) [(Expr.Lit ⟨0⟩), (Expr.Lit ⟨0⟩)] := rfl
example : <s if 1 { leave } > = Stmt.If (.Lit ⟨1⟩) [Stmt.Leave] := rfl
example : <s {
    if 1 { leave }
    leave
  }
> = Stmt.Block [Stmt.If (.Lit ⟨1⟩) [.Leave], .Leave] := rfl

end Notation

end Yul

end EvmYul
