/-
Syntax definitions for `ModArith`, providing a custom `[mod_arith q, hq | ...]` with syntax sugar
analogous to FHE's `[poly| ...]`.

Authors: Jaeho Choi<zerozerozero0216@gmail.com>
-/
import LeanMLIR.MLIRSyntax.EDSL
import SSA.Projects.ModArith.Basic

open MLIR AST Ctxt ZMod Lean Meta Elab Qq Ty Op

variable {γ₁ γ₂ γ₃}
  [ValueMap ℕ γ₁] [DecidableEq γ₁] [Repr γ₁] [Inhabited γ₁]
  [ValueMap ℤ γ₂] [DecidableEq γ₂] [Repr γ₂] [Inhabited γ₂]
  [ValueMap CoprimeNats γ₃] [DecidableEq γ₃] [Repr γ₃]

section MkFuns

syntax "!mod_arith.int<" term:max ">" : mlir_type
syntax "!mod_arith.int<" "%" term:max ">" : mlir_type
syntax "!rns.rns<" term:max ">" : mlir_type
syntax "!rns.rns<" "%" term:max ">" : mlir_type
syntax "tensor<" term:max &"x" mlir_type ">" : mlir_type
syntax "tensor<" "%" term:max &"x" mlir_type ">" : mlir_type

open Parser.Term in
def mkQuotedName (name : Ident) : Term :=
  let stx := Syntax.mkNameLit ("`" ++ name.getId.toString)
  ⟨Syntax.node1 .none ``quotedName stx⟩

open Macro in
partial def stxToTerm (stx : TSyntax `mlir_type) : MacroM Term := do
  match stx with
  | `(mlir_type| !mod_arith.int< $q >) => `(Ty.mod_arith.int (.val $q))
  | `(mlir_type| !mod_arith.int< %$q >) => `(Ty.mod_arith.int (.var $q))
  | `(mlir_type| !rns.rns< $qs >) => `(Ty.rns.rns (.val ⟨$qs, by decide⟩))
  | `(mlir_type| !rns.rns< %$qs >) => `(Ty.rns.rns (.var $qs))
  | `(mlir_type| tensor< $n x $t >) => `(Ty.tensor $n $(← stxToTerm t))
  | `(mlir_type| tensor< %$n x $t >) => `(Ty.tensor (.var $n) $(← stxToTerm t))
  | t =>
    let t' ← expandMacros (← `([mlir_type| $t]))
    match t' with
    | `(MLIRType.int $_ $_) => `(Ty.int)
    | `(MLIRType.index) => `(Ty.index)
    | _ => Macro.throwUnsupported

open Term in
@[term_elab MLIR.EDSL.«term[mlir_type|_]»]
def expandType : TermElab := fun stx ty? => do
  let fn := fun
    | `([mlir_type| $t]) => do
      `(MLIR.AST.MLIRType.expr quoted($(← liftMacroM <| stxToTerm t)))
    | e => return e
  adaptExpander fn stx ty?

def getValueMap (t : Q(Type)) :
    MetaM (Σ γ : Q(Type), Q(ValueMap $t $γ) × Q(DecidableEq $γ)) := do
  let γ : Q(Type) ← mkFreshExprMVar none
  let _inst : Q(ValueMap $t $γ) ← synthInstance q(ValueMap $t $γ)
  let _inst₂ : Q(DecidableEq $γ) ← synthInstance q(DecidableEq $γ)
  return ⟨← instantiateMVars γ, _inst, _inst₂⟩

def mkTy (_ : Expr) (ty : MLIRType 0) (_ : Expr) : TermElabM Expr := do
  let ⟨_, _, _⟩ ← getValueMap q(ℕ)
  let ⟨_, _, _⟩ ← getValueMap q(ℤ)
  let ⟨_, _, _⟩ ← getValueMap q(CoprimeNats)
  show TermElabM Q(ExceptM ModArith ModArith.Ty) from
  match ty with
  | .int _ _ => return q(.ok .int)
  | .index => return q(.ok .index)
  | .expr (e : Q(ModArith.Ty)) => return q(.ok $e)
  | _ => throwError "Unsupported type"

instance : LeanExprMLIRTransformTy ModArith 0 where
  mkTy := mkTy

/--
A helper to construct a constant integer expression (in Lean’s sense of “plain Int”).
-/
def cstInt {Γ : Ctxt _} (z : ℤ%) : Expr ModArith Γ .pure [int] :=
  Expr.mk
    (op      := arith.constant z)
    (ty_eq   := rfl)
    (eff_le  := by constructor)
    (args    := .nil)
    (regArgs := .nil)

def cstIndex {Γ : Ctxt _} (z : ℕ%) : Expr ModArith Γ .pure [index] :=
  Expr.mk
    (op      := index.constant z)
    (ty_eq   := rfl)
    (eff_le  := by constructor)
    (args    := .nil)
    (regArgs := .nil)

macro "build_modarith_op" name:ident op:term:max : command => `(command |
  def $name {Γ : Ctxt Ty} (q : ℕ%) (x y : Var Γ (mod_arith.int q)) :
      Expr ModArith Γ .pure [mod_arith.int q] :=
    Expr.mk
      (op      := $op q)
      (ty_eq   := rfl)
      (eff_le  := by constructor)
      (args    := [x, y]ₕ)
      (regArgs := []ₕ))

macro "build_arith_op" name:ident op:term:max : command => `(command |
  def $name {Γ : Ctxt Ty} (x y : Var Γ int) :
      Expr ModArith Γ .pure [int] :=
    Expr.mk
      (op      := $op)
      (ty_eq   := rfl)
      (eff_le  := by constructor)
      (args    := [x, y]ₕ)
      (regArgs := []ₕ))

build_modarith_op mod_add mod_arith.add
build_modarith_op mod_sub mod_arith.sub
build_modarith_op mod_mul mod_arith.mul
build_arith_op add arith.add
build_arith_op sub arith.sub
build_arith_op mul arith.mul
build_arith_op remui arith.remui

def getValueInfoBinaryOp (Γ : Ctxt ModArith.Ty) (opStx : Op 0) :
    ReaderM ModArith <|
      ModArith.Ty × (s : ModArith.Ty) × (t : ModArith.Ty) ×
      Γ.Var s × Γ.Var t := do
  let [xStx, yStx] := opStx.args
    | throw <| .generic s!"{opStx.name} expects exactly 2 args, got {opStx.args.length}"
  let [resStx] := opStx.res
    | throw <| .generic s!"{opStx.name} returns exactly 1 args, got {opStx.args.length}"
  let ⟨tyX, x⟩ ← TypedSSAVal.mkVal Γ xStx
  let ⟨tyY, y⟩ ← TypedSSAVal.mkVal Γ yStx
  let tyRes : ModArith.Ty ← TypedSSAVal.mkTy resStx
  return ⟨tyRes, tyX, tyY, x, y⟩

def getValueInfoUnaryOp (Γ : Ctxt ModArith.Ty) (opStx : Op 0) :
    ReaderM ModArith <|
      ModArith.Ty × (t : ModArith.Ty) × Γ.Var t := do
  let [xStx] := opStx.args
    | throw <| .generic s!"{opStx.name} expects exactly 1 args, got {opStx.args.length}"
  let [resStx] := opStx.res
    | throw <| .generic s!"{opStx.name} returns exactly 1 args, got {opStx.args.length}"
  let ⟨tyX, x⟩ ← TypedSSAVal.mkVal Γ xStx
  let tyRes : ModArith.Ty ← TypedSSAVal.mkTy resStx
  return ⟨tyRes, tyX, x⟩

def mkModArith (Γ : Ctxt ModArith.Ty) (opStx : Op 0)
    (mk : ∀ {Γ : Ctxt Ty} (q : ℕ%) (_ _ : Var Γ (mod_arith.int q)),
      Expr ModArith Γ .pure [mod_arith.int q]) :
    ReaderM ModArith (Σ eff ty, Expr ModArith Γ eff ty):= do
  let ⟨_, mod_arith.int q, mod_arith.int q', x, y⟩ ← getValueInfoBinaryOp Γ opStx
    | throw <| .generic s!"expected both operands to be of type '!mod_arith.int'"
  let .isTrue (.refl _) := decEq q q'
    | throw <| .generic s!"expected both modulus to be the same"
  return ⟨.pure, [mod_arith.int q], mk q x y⟩

def mkArith (Γ : Ctxt ModArith.Ty) (opStx : Op 0)
    (mk : ∀ {Γ : Ctxt Ty} (_ _ : Var Γ int), Expr ModArith Γ .pure [int]) :
    ReaderM ModArith (Σ eff ty, Expr ModArith Γ eff ty):= do
  let ⟨_, int, int, x, y⟩ ← getValueInfoBinaryOp Γ opStx
    | throw <| .generic s!"expected both operands to be of type 'int'"
  return ⟨.pure, [int], mk x y⟩

/--
Given a single MLIR operation, produce a Lean expression in the `ModArith` dialect.

We match on `opStx.name` to see if it is `"mod_arith.add"`, `"mod_arith.sub"`,
`"arith.const"`, etc. Then we decode the arguments, attribute `value`,
and produce the corresponding expression builder (add, sub, cstInt, etc.).
-/
def mkExpr (Γ : Ctxt ModArith.Ty) (opStx : Op 0) :
    ReaderM ModArith (Σ eff ty, Expr ModArith Γ eff ty) := do
  match opStx.name with
  | "arith.constant" =>
    match opStx.res with
    | [(_, MLIRType.int .Signless _)] =>
      match opStx.attrs.find "value" with
      | .some (.int x _) => return ⟨.pure, [int], cstInt (.val x)⟩
      | .some (.expr e) => return ⟨.pure, [int], cstInt (.var (evalLeanExprMLIRExpr γ₂ e))⟩
      | ret => throw <| .generic <|
        s!"arith.constant expects integer typed attribute 'value', got {repr opStx.attrs}"
    | other => throw <| .generic s!"arith.constant: unsupported result type {repr other}"
  | "arith.add" => mkArith Γ opStx add
  | "arith.sub" => mkArith Γ opStx sub
  | "arith.mul" => mkArith Γ opStx mul
  | "arith.remui" => mkArith Γ opStx remui
  | "index.constant" =>
    match opStx.res with
    | [(_, MLIRType.int .Signless _)] =>
      match opStx.attrs.find "value" with
      | .some (.int x _) => return ⟨.pure, [index], cstIndex (.val x.toNat)⟩
      | .some (.expr e) => return ⟨.pure, [index], cstIndex (.var (evalLeanExprMLIRExpr γ₁ e))⟩
      | ret => throw <| .generic <|
        s!"index.constant expects natural number typed attribute 'value', got {repr opStx.attrs}"
    | other => throw <| .generic s!"index.constant: unsupported result type {repr other}"
  | "mod_arith.add" => mkModArith Γ opStx mod_add
  | "mod_arith.sub" => mkModArith Γ opStx mod_sub
  | "mod_arith.mul" => mkModArith Γ opStx mod_mul
  | "mod_arith.encapsulate" =>
    let ⟨mod_arith.int q, int, x⟩ ← getValueInfoUnaryOp Γ opStx
      | throw <| .generic <|
        s!"expected the operand to be of type `int` and the result to be of type `mod_arith.int _`"
    return ⟨.pure, [mod_arith.int q], Expr.mk
      (op      := mod_arith.encapsulate q)
      (ty_eq   := rfl)
      (eff_le  := by constructor)
      (args    := [x]ₕ)
      (regArgs := []ₕ)⟩
  | "mod_arith.mod_switch" =>
    match ← getValueInfoUnaryOp Γ opStx with
    | ⟨rns.rns qs, mod_arith.int q, x⟩ =>
      return ⟨.pure, [rns.rns qs], Expr.mk
        (op      := mod_arith.mod_switch.decompose qs q)
        (ty_eq   := rfl)
        (eff_le  := by constructor)
        (args    := [x]ₕ)
        (regArgs := []ₕ)⟩
    | ⟨mod_arith.int q, rns.rns qs, x⟩ =>
      return ⟨.pure, [mod_arith.int q], Expr.mk
        (op      := mod_arith.mod_switch.interpolate q qs)
        (ty_eq   := rfl)
        (eff_le  := by constructor)
        (args    := [x]ₕ)
        (regArgs := []ₕ)⟩
    | _ => throw <| .generic <|
        s!"expected exactly one of the operand and the result to be of type `rns.rns _` and " ++
        s!"the another be of type `mod_arith.int _`"
  | "tensor.extract" =>
    let ⟨t, .tensor n t', .index, x, y⟩ ← getValueInfoBinaryOp Γ opStx
      | throw <| .generic <| s!"Invalid `tensor.extract` operation"
    let .isTrue (.refl _) := decEq t t'
      | throw <| .generic s!"The return type and the type of tensor elements must be same"
    return ⟨.pure, [t], Expr.mk
      (op      := tensor.extract t n)
      (ty_eq   := rfl)
      (eff_le  := by constructor)
      (args    := [x, y]ₕ)
      (regArgs := []ₕ)⟩
  | other => throw <| .unsupportedOp <|
    s!"[mod_arith] mkExpr: operation name {other} not recognized"

/--
Given a return statement, produce a `Com (ModArith q)` that returns the given value.
We check that the op is named "return" and has exactly one argument.
-/
def mkReturn (Γ : Ctxt ModArith.Ty) (opStx : Op 0) :
    ReaderM ModArith (Σ eff ty, Com ModArith Γ eff ty) :=
  if opStx.name == "return" then
    match opStx.args with
    | [argStx] => do
      let ⟨tyArg, x⟩ ← TypedSSAVal.mkVal Γ argStx
      return ⟨.pure, [tyArg], Com.ret x⟩
    | _ =>
      throw <| .generic s!"[mod_arith] return expects exactly 1 argument"
  else
      throw <| .generic s!"[mod_arith] mkReturn called on non-return op {opStx.name}"

instance : TransformExpr ModArith 0 where
  mkExpr := mkExpr

instance : TransformReturn ModArith 0 where
  mkReturn := mkReturn

end MkFuns

elab "[mod_arith " " | " reg:mlir_region "]" : term => do
  let ⟨γ₁, _, _⟩ ← getValueMap q(ℕ)
  let ⟨γ₂, _, _⟩ ← getValueMap q(ℤ)
  let ⟨γ₃, _, _⟩ ← getValueMap q(CoprimeNats)
  let _inst : Q(Repr $γ₁) ← synthInstance q(Repr $γ₁)
  let _inst : Q(Inhabited $γ₁) ← synthInstance q(Inhabited $γ₁)
  let _inst : Q(Repr $γ₂) ← synthInstance q(Repr $γ₂)
  let _inst : Q(Inhabited $γ₂) ← synthInstance q(Inhabited $γ₂)
  let _inst : Q(Repr $γ₃) ← synthInstance q(Repr $γ₃)
  SSA.elabIntoCom reg q(ModArith)

elab "%[mod_arith " " | " reg:mlir_region "]" : term => do
  let ⟨γ₁, _, _⟩ ← getValueMap q(ℕ)
  let ⟨γ₂, _, _⟩ ← getValueMap q(ℤ)
  let ⟨γ₃, _, _⟩ ← getValueMap q(CoprimeNats)
  let _inst : Q(Repr $γ₁) ← synthInstance q(Repr $γ₁)
  let _inst : Q(Inhabited $γ₁) ← synthInstance q(Inhabited $γ₁)
  let _inst : Q(Repr $γ₂) ← synthInstance q(Repr $γ₂)
  let _inst : Q(Inhabited $γ₂) ← synthInstance q(Inhabited $γ₂)
  let _inst : Q(Repr $γ₃) ← synthInstance q(Repr $γ₃)
  SSA.elabIntoComExtended reg q(ModArith)
