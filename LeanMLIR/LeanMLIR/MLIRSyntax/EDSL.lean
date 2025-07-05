/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax.GenericParser
import LeanMLIR.MLIRSyntax.Transform
import LeanMLIR.Framework.Trace

/-!
# MLIR Dialect Domain Specific Language
This file sets up generic glue meta-code to tie together the generic MLIR parser with the
`Transform` mechanism, to obtain an easy way to specify a DSL that elaborates into `Com`/`Expr`
instances for a specific dialect.
-/

namespace SSA

open Qq Lean Meta Elab Term
open MLIR.AST

unsafe def processLeanExprMLIROpaque
    (numArgs : Nat) (opaqueName newName appFnName : Name) (appArgs : Array Expr)
    (newArgs : Unit → Array Expr) : TermElabM (Option Expr) := do
  if appFnName == opaqueName && appArgs.size >= numArgs then
    let moreArgs := appArgs[numArgs...*]
    let e ← mkAppM newName (newArgs ())
    let e ← whnf e
    if e.hasFVar || e.hasMVar then
      throwError m!"{e} has free variable or meta variable"
    let newExpr ← evalExpr (TermElabM Expr) q(TermElabM Expr) e
    return some (← whnf (mkAppN (← newExpr) moreArgs))
  else
    return none

unsafe def whnfTransformImpl (old : Expr) : TermElabM Expr := do
  let e ← whnf old
  let e ← (match e with
    | .app .. => do
      let mut args := e.getAppArgs
      let c@(.const fname _) := e.getAppFn | return e
      if let some info ← getMatcherInfo? fname then
        let prefixSz := info.numParams + 1
        for i in List.range' prefixSz info.numDiscrs do
          if i >= args.size then break
          let oldArg := args[i]!
          let newArg ← whnfTransformImpl oldArg
          args := args.modify i fun _ => newArg
        return mkAppN c args
      else return e
    | _ => return e)
  let new ← Meta.transform e fun
    | e@(.app ..) => do
      let mut args := e.getAppArgs
      let .const fname _ := e.getAppFn | return .continue
      if let some e' ← processLeanExprMLIROpaque 4
        ``defaultMkTy ``LeanExprMLIRTransformTy.mkTy fname args
        fun _ => #[args[1]!, toExpr args[1]!, args[3]!, toExpr args[3]!] then
        return .visit e'
      if let some e' ← processLeanExprMLIROpaque 5
        ``defaultMkExpr ``LeanExprMLIRTransformExpr.mkExpr fname args
        fun _ => #[toExpr args[1]!, args[3]!, toExpr args[3]!, args[4]!, toExpr args[4]!] then
        return .visit e'
      if let some e' ← processLeanExprMLIROpaque 5
        ``defaultMkReturn ``LeanExprMLIRTransformReturn.mkReturn fname args
        fun _ => #[toExpr args[1]!, args[3]!, toExpr args[3]!, args[4]!, toExpr args[4]!] then
        return .visit e'
      if fname == ``evalLeanExprMLIRExpr && args.size >= 3 then
        let expr ← whnf args[2]!
        if expr.hasFVar || expr.hasMVar then
          throwError m!"{expr} has free variable or meta variable"
        let newExpr ← evalExpr Lean.Expr q(Lean.Expr) expr
        return .done newExpr
      else return .continue
    | _ => return .continue
  if new != old then whnfTransformImpl new
  else return old

@[implemented_by whnfTransformImpl]
opaque whnfTransform : Expr → TermElabM Expr

/-- `ctxtNf` reduces an expression of type `Ctxt _` to something in between whnf and normal form.
`ctxtNf` recursively calls `whnf` on the tail of the list, so that the result is of the form
  `a₀ :: a₁ :: ... :: aₙ :: [] `
where each element `aᵢ` is not further reduced -/
partial def ctxtNf (as : Expr) : TermElabM Expr := do
  let as ← whnfTransform as
  match_expr as with
    | Ctxt.cons _ a as =>
        let a ← whnfTransform a
        let as ← ctxtNf as
        mkAppM ``Ctxt.cons #[a, as]
    | List.cons _ a as =>
        let a ← whnfTransform a
        let as ← ctxtNf as
        mkAppM ``Ctxt.cons #[a, as]
    | _ => return as

partial def listNf (as : Expr) : TermElabM Expr := do
  let as ← whnfTransform as
  match_expr as with
    | List.cons _ a as =>
        let a ← whnfTransform a
        let as ← listNf as
        mkAppM ``List.cons #[a, as]
    | _ => return as

partial def vectorNf (xs : Expr) : TermElabM Expr := do
  let xs ← whnfTransform xs
  match_expr xs with
    | HVector.cons α f as a x xs =>
        let as ← listNf as
        let a ← whnfTransform a
        let x ← whnfTransform x
        let xs ← vectorNf xs
        return mkAppN (.const ``HVector.cons [0, 0]) #[α, f, as, a, x, xs]
    | _ => return xs

def exprNf (expr : Expr) : TermElabM Expr := do
  let expr ← whnfTransform expr
  match_expr expr with
    | Expr.mk d opSig eff Γ ty op ty_eq eff_le args regArgs =>
        let eff ← whnfTransform eff
        let Γ ← ctxtNf Γ
        let ty ← whnfTransform ty
        let op ← whnfTransform op
        let args ← vectorNf args
        let regArgs ← whnfTransform regArgs
        return mkAppN (.const ``Expr.mk []) #[d, opSig, eff, Γ, ty, op, ty_eq, eff_le, args, regArgs]
    | _ => throwError "Expected `Expr.mk _ _ _ _ _`, found:\n\t{expr}"

/-- `comNf` reduces an expression of type `Com` to something in between whnf and normal form.
`comNf` recursively calls `whnf` on the expression and body of a `Com.var`, resulting in
  `Com.var (Expr.mk ...) <| Com.var (Expr.mk ...) <| Com.var (Expr.mk ...) <| ... <| Com.rete _`
where the arguments to `Expr.mk` are not reduced -/
partial def comNf (com : Expr) : TermElabM Expr := do
  let com ← whnfTransform com
  match_expr com with
    | Com.var d opSig Γ eff α β e body =>
        let Γ ← ctxtNf Γ
        let eff ← whnfTransform eff
        let α ← whnfTransform α
        let β ← whnfTransform β
        let e ← exprNf e
        let body ← comNf body
        return mkAppN (.const ``Com.var []) #[d, opSig, Γ, eff, α, β, e, body]
    | Com.rets _d _inst _Γ _eff _t _ => return com
    | _ => throwError "Expected `Com.var _ _` or `Com.ret _`, found:\n\t{com}"

/--
`elabIntoCom` is a building block for defining a dialect-specific DSL based on the geneeric MLIR
syntax parser.

For example, if `FooOp` is the type of operations of a "Foo" dialect, we can build a term elaborator
for this dialect as follows:
```
elab "[foo_com| " reg:mlir_region "]" : term => SSA.elabIntoCom reg q(FooOp)
--     ^^^^^^^                                                        ^^^^^
```
-/
unsafe def elabIntoComImpl (region : TSyntax `mlir_region) (d : Q(Dialect)) {φ : Q(Nat)}
    (_dialectSignature : Q(DialectSignature $d)   := by exact q(by infer_instance))
    (_transformTy      : Q(TransformTy $d $φ)     := by exact q(by infer_instance))
    (_transformExpr    : Q(TransformExpr $d $φ)   := by exact q(by infer_instance))
    (_transformReturn  : Q(TransformReturn $d $φ) := by exact q(by infer_instance)) :
    TermElabM Expr := do
  let com : Q(ExceptM $d (Σ Γ' eff ty, Com $d Γ' eff ty)) ←
    withTraceNode `LeanMLIR.Elab (return m!"{exceptEmoji ·} building `Com` expression") <| do
    let ast_stx ← `([mlir_region| $region])
    let ast ← elabTermEnsuringTypeQ ast_stx q(Region $φ)
    return q(MLIR.AST.mkCom $ast)
  withTraceNode `LeanMLIR.Elab (return m!"{exceptEmoji ·} synthesizingMVars") <|
    synthesizeSyntheticMVarsNoPostponing

  withTraceNode `LeanMLIR.Elab (return m!"{exceptEmoji ·} unwrapping `Com` expression") <| do
    /- Now we repeatedly call `whnf` and then match on the resulting expression, to extract an
      expression of type `Com ..` -/
    let com : Q(ExceptM $d (Σ Γ' eff ty, Com $d Γ' eff ty)) ← whnfTransform com
    match_expr com with
    | Except.ok _ _ expr =>
      let (expr : Q(Σ Γ eff ty, Com $d Γ eff ty)) ← whnfTransform expr
      match expr.app4? ``Sigma.mk with
      | .some (_αexpr, _βexpr, (_Γ : Q(Ctxt ($d).Ty)), expr) =>
        let (expr : Q(Σ eff ty, Com $d $_Γ eff ty)) ← whnfTransform expr
        match expr.app4? ``Sigma.mk with
        | .some (_αexpr, _βexpr, (_eff : Q(EffectKind)), expr) =>
          match expr.app4? ``Sigma.mk with
          | .some (_αexpr, _βexpr, (_ty : Q(List ($d).Ty)), (com : Q(Com $d $_Γ $_eff $_ty))) =>
              /- Finally, use `comNf` to ensure the resulting expression is of the form
                  `Com.var (Expr.mk ...) <| Com.var (Expr.mk ...) ... <| Com.rete _`,
                where the arguments to `Expr.mk` are not reduced -/
              withTraceNode `LeanMLIR.Elab (return m!"{exceptEmoji ·} reducing `Com` expression") <|
                comNf com
          | .none => throwError "Expected (Sigma.mk _ _), found {expr}"
        | .none => throwError "Expected (Sigma.mk _ _), found {expr}"
      | .none => throwError "Expected (Sigma.mk _ _), found {expr}"
    | Except.error _ _ expr =>
      if !expr.hasFVar && !expr.hasMVar then
        let errorValue ← evalExpr TransformError q(TransformError) expr
        throwError "Error: {repr errorValue}"
      else
        throwError "Error: {expr}"
    | _ =>
      throwError "Expected `Except.ok`, found {com}"

def elabIntoCom (region : TSyntax `mlir_region) (d : Q(Dialect)) {φ : Q(Nat)}
    (_dialectSignature : Q(DialectSignature $d)   := by exact q(by infer_instance))
    (_transformTy      : Q(TransformTy $d $φ)     := by exact q(by infer_instance))
    (_transformExpr    : Q(TransformExpr $d $φ)   := by exact q(by infer_instance))
    (_transformReturn  : Q(TransformReturn $d $φ) := by exact q(by infer_instance)) :
    TermElabM Expr :=
  unsafe (@elabIntoComImpl region d φ _dialectSignature _transformTy _transformExpr _transformReturn)

syntax "quoted" "(" term ("," term)? ")" : term
syntax "syntax" "(" term ")" : term
syntax "mlir_attr_quoted" "(" term ("," term)? ")" : mlir_attr_val
syntax "mlir_syntax_quoted" "(" term ("," term)? ")" : mlir_attr_val

elab_rules : term
  | `(quoted($stx)) => do
    let mvar ← mkFreshExprMVar none
    return toExpr <| ← instantiateMVars <| ← elabTermAndSynthesize stx <| some mvar
  | `(quoted($stx, $expected)) => do
    let mvar ← mkFreshExprMVar none
    let expectedType ← elabTermAndSynthesize expected (some mvar)
    return toExpr <| ← instantiateMVars <| ← elabTermAndSynthesize stx <| some expectedType
  | `(syntax($stx)) => return toExpr stx.raw

macro_rules
  | `([mlir_attr_val| mlir_attr_quoted($stx)]) =>
    `(MLIR.AST.AttrValue.expr quoted($stx))
  | `([mlir_attr_val| mlir_attr_quoted($stx, $expected)]) =>
    `(MLIR.AST.AttrValue.expr quoted($stx, $expected))
  | `([mlir_attr_val| mlir_syntax_quoted($stx)]) =>
    `(MLIR.AST.AttrValue.syntax syntax($stx))

variable (d : Dialect) [DialectSignature d] [DecidableEq d.Ty] [ToString d.Ty]
  {φ} [TransformTy d φ] [TransformExpr d φ] [TransformReturn d φ]

syntax mlir_op_operand " = " "[" term "]" mlir_op_operand,* " : "
  "(" mlir_type,* ")" "->" mlir_type : mlir_op

macro_rules
  | `(mlir_op| $v:mlir_op_operand = [ $com ] $ops,* : ($opsArgs,*) -> $t) => do
    `(mlir_op| $v:mlir_op_operand = "_generator" ($ops,*)
      {com = mlir_attr_quoted($com)} : ($opsArgs,*) -> ($t))

instance : TransformTy (extendedDialect d) φ where
  mkTy := TransformTy.mkTy (d := d)

noncomputable def mkExprOriginalAux (Γ : Ctxt d.Ty) (opStx : Op φ) :
    ReaderM (extendedDialect d) (Σ eff ty, Expr (extendedDialect d) Γ eff ty) := do
  let ⟨_, _, e⟩ ← TransformExpr.mkExpr Γ opStx
  return ⟨_, _, e.toExtended⟩

noncomputable def mkReturnOriginalAux (Γ : Ctxt d.Ty) (opStx : Op φ) :
    ReaderM (extendedDialect d) (Σ eff ty, Com (extendedDialect d) Γ eff ty) := do
  let ⟨_, _, e⟩ ← TransformReturn.mkReturn Γ opStx
  return ⟨_, _, e.toExtended⟩

open DialectSignature in
def mkExprGeneratorAux
    {Δ eff ty} (Γ : Ctxt d.Ty) (com : Com d Δ eff ty) (opStx : Op φ) :
    ReaderM (extendedDialect d) (Σ eff ty, Expr (extendedDialect d) Γ eff ty) := do
  let args := (← opStx.args.mapM (TypedSSAVal.mkVal Γ ·)).reverse
  let argTypes := args.map (·.1)
  if eq : Δ.toList = argTypes then
    have eq₁ : Δ.toList.length = args.length := by
      simp [eq, argTypes]
    have eq₂ : ∀ i, args[Fin.cast eq₁ i].fst = Δ.toList[i] := by
      simp [eq, argTypes]
    let argsVec := HVector.ofFn _ _ fun i => args[i.cast eq₁].2.cast (eq₂ i)
    pure ⟨eff, ty, .mk (.generator com) rfl (le_refl _) argsVec .nil⟩
  else
    throw <| .generic s!"Incompatiable arguments types for Com generator: {Δ.toList} and {argTypes}"

def getOriginalDialect (extended : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar none
  let mvar' ← mkFreshExprMVar none
  let template := mkAppN (.const ``extendedDialect []) #[mvar, mvar']
  unless ← isDefEq template extended do
    throwError m!"Not an extended dialect: {extended}"
  instantiateMVars mvar

instance [TransformExpr d φ] : LeanExprMLIRTransformExpr (extendedDialect d) φ where
  mkExpr dialectExpr _ ΓExpr
  | ⟨name, _, _, _, atts⟩, opExpr => do
    let dialectExpr ← getOriginalDialect dialectExpr
    if name != "_generator" then
      mkAppM ``mkExprOriginalAux #[dialectExpr, ΓExpr, opExpr]
    else
      let some (.expr comExpr) := atts.getAttr "com" | throwError "`com` attribute not found"
      mkAppM ``mkExprGeneratorAux #[dialectExpr, ΓExpr, comExpr, opExpr]

instance [TransformReturn d φ] : LeanExprMLIRTransformReturn (extendedDialect d) φ where
  mkReturn dialectExpr _ ΓExpr _ opExpr := do
    let dialectExpr ← getOriginalDialect dialectExpr
    mkAppM ``mkReturnOriginalAux #[dialectExpr, ΓExpr, opExpr]

def elabIntoComExtended (region : TSyntax `mlir_region) (d : Q(Dialect)) {φ : Q(Nat)}
    (_dialectSignature : Q(DialectSignature $d)         := by exact q(by infer_instance))
    (_transformTy      : Q(TransformTy $d $φ)           := by exact q(by infer_instance))
    (_transformExpr    : Q(TransformExpr $d $φ)         := by exact q(by infer_instance))
    (_transformReturn  : Q(TransformReturn $d $φ)       := by exact q(by infer_instance))
    (_inhabited        : Q(Inhabited (Dialect.Ty $d))   := by exact q(by infer_instance))
    (_decidableEq      : Q(DecidableEq (Dialect.Ty $d)) := by exact q(by infer_instance))
    (_toString         : Q(ToString (Dialect.Ty $d))    := by exact q(by infer_instance)) :
    TermElabM Expr := do
  let e ← elabIntoCom region q(extendedDialect $d)
  mkAppM ``Com.expand #[e]

end SSA
