/-
This file contains the definition of the MLIR `ModArith` dialect as
implemented in HEIR, see:
  https://heir.dev/docs/dialects/modarith/

It is structurally similar to `FullyHomomorphicEncryption.Basic.lean` but focuses on arithmetic
directly in ℤ/qℤ (ZMod q), rather than polynomials over ℤ/qℤ.

Authors: Jaeho Choi<zerozerozero0216@gmail.com>
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Pairwise.List
import Mathlib.Data.Nat.ChineseRemainder
import LeanMLIR.Framework

open ZMod
open Lean hiding NameMap
open scoped Function

class ValueMap (α : Type) (γ : outParam Type) where
  map : γ → α

def TheIndex (α : Type) {γ : Type} [ValueMap α γ] := γ

-- replace name to `TrackedValue`, or `PseudoNumber`, `QuasiNumber`?
inductive Value (α : Type) {γ : Type} [ValueMap α γ]
  | val (x : α)
  | var (index : γ)
deriving DecidableEq, Repr

namespace Value

variable {α β γ} [M : ValueMap α γ] [ValueMap β γ] [Repr γ] [Repr α] [DecidableEq γ] [Inhabited α]

instance : Repr (Value α) where
  reprPrec
  | .val v, n => reprPrec v n
  | .var index, n => "%" ++ reprPrec index n

protected def get : Value α → α
  | .val v => v
  | .var index => M.map index

protected def map (f : α → β) : Value α → Value β
  | .val v => .val (f v)
  | .var index => .var index

postfix:50 "%" => Value
postfix:max "&" => Value.get

end Value

/-!
  # ModArith Dialect

  The `ModArith` dialect is a simpler variant that models integer arithmetic
  **modulo `q`**, i.e., arithmetic in the ring `ZMod q`.

  We assume `q > 1` as a fact. We denote our base ring as: `R = ZMod q`.

  The dialect's type system includes (for example) `integer`, and
  a specialized type `modLike` for elements in `ZMod q`.

  Operations: Add, Sub, Mul, and constants for this ring, and integers.
-/

section CommRing

/--
By analogy to `R q n` from the `Poly` dialect, we simply define
`R q := ZMod q`. The ring structure on `ZMod q` is already known
to mathlib.
-/
abbrev R := ZMod

end CommRing

/-!
## Dialect type definitions

Here, we define a small type system for the `ModArith` dialect:
  1. `integer` – for full-range integers in Lean (ℤ).
  2. `modLike` – for our ring `ZMod q`.

You can freely add more types or rename them according to your needs.
-/

def CoprimeNats := {qs : List ℕ // qs.Pairwise Nat.Coprime}
deriving instance DecidableEq, Repr for CoprimeNats

instance : Inhabited CoprimeNats where
  default := ⟨[], by simp⟩

variable {γ₁ γ₂ γ₃}
  [ValueMap ℕ γ₁] [DecidableEq γ₁] [Repr γ₁]
  [ValueMap ℤ γ₂] [DecidableEq γ₂] [Repr γ₂]
  [ValueMap CoprimeNats γ₃] [DecidableEq γ₃] [Repr γ₃]

set_option linter.dupNamespace false in
inductive Ty where
  | int
  | index
  | mod_arith.int (q : ℕ%)
  | rns.rns (qs : CoprimeNats%)
  | tensor (n : ℕ%) (type : Ty)
deriving DecidableEq, Inhabited, Repr
open Ty

/--
We provide a `ToString` instance: this is a human-readable name for each type.
-/
instance : ToString Ty where
  toString := toString
where
  toString := fun
  | int => "int"
  | index => "index"
  | mod_arith.int (q : ℕ%) => s!"!mod_arith.int<{repr q}>"
  | rns.rns qs => s!"!rns.rns<{repr qs}>"
  | tensor n type => s!"!tensor<{repr n}x{toString type}>"

/-!
## Dialect operation definitions

Here are some sample operations. Adjust as appropriate for the
`modarith` dialect: e.g. you might have add/sub/mul, an operation for
returning constants mod q, an integer constant, etc.
-/
inductive Op where
  | arith.constant (c : ℤ%)
  | arith.add
  | arith.sub
  | arith.mul
  | arith.remui
  | tensor.from_elements (ty : Ty) (n : ℕ%)
  | tensor.extract (ty : Ty) (n : ℕ%)
  | index.constant (c : ℕ%)
  | mod_arith.add (q : ℕ%)
  | mod_arith.sub (q : ℕ%)
  | mod_arith.mul (q : ℕ%)
  | mod_arith.encapsulate (q : ℕ%)
  | mod_arith.extract (q : ℕ%)
  | mod_arith.mod_switch.decompose (qs : CoprimeNats%) (q : ℕ%)
  | mod_arith.mod_switch.interpolate (q : ℕ%) (qs : CoprimeNats%)
deriving Repr, Inhabited
open Op

/-!
## The `ModArith` dialect

We bundle up our `Op` and `Ty` into a dialect called `ModArith q`.
-/
abbrev ModArith : Dialect where
  Op := Op
  Ty := Ty

/--
We provide a `TyDenote` instance: this is how we translate each
dialect type into an actual Lean type.
-/
instance : TyDenote Ty where
  toType := toType
where
  toType := fun
  | int => ℤ
  | index => ℕ
  | mod_arith.int q => R q&  -- i.e. `ZMod q`
  | rns.rns qs => Π i : Fin qs&.1.length, R qs&.1[i]  -- i.e. `RNS qs`
  | tensor n type => Fin n& → toType type

instance (α : Ty) : Inhabited ⟦α⟧ where
  default := default₀ α
where
  default₀ (α : Ty) : ⟦α⟧ := match α with
  | int => by whnf; exact default
  | index => by whnf; exact default
  | mod_arith.int q => by simpa only [toType, instTyDenoteTy.toType] using default
  | rns.rns _ => by simpa only [toType, instTyDenoteTy.toType] using default
  | tensor n ty => by
    haveI : Inhabited ⟦ty⟧ := ⟨default₀ ty⟩
    change Fin n& → ⟦ty⟧
    exact default

/--
For each operation, we specify its input `sig` (a list of
types) and its `outTy` (the output type).
-/
@[simp, reducible]
def Op.sig : Op → List Ty
  | arith.constant _ => []
  | arith.add => [int, int]
  | arith.sub => [int, int]
  | arith.mul => [int, int]
  | arith.remui => [int, int]
  | tensor.from_elements ty n => List.replicate n& ty
  | tensor.extract ty n => [tensor n ty, index]
  | index.constant _ => []
  | mod_arith.add q => [mod_arith.int q, mod_arith.int q]
  | mod_arith.sub q => [mod_arith.int q, mod_arith.int q]
  | mod_arith.mul q => [mod_arith.int q, mod_arith.int q]
  | mod_arith.encapsulate _ => [int]
  | mod_arith.extract q => [mod_arith.int q]
  | mod_arith.mod_switch.decompose _ q => [mod_arith.int q]
  | mod_arith.mod_switch.interpolate _ qs => [rns.rns qs]

@[simp, reducible]
def Op.outTy : Op → List Ty
  | arith.constant _ => [int]
  | arith.add => [int]
  | arith.sub => [int]
  | arith.mul => [int]
  | arith.remui => [int]
  | tensor.from_elements ty n => [tensor n ty]
  | tensor.extract ty _ => [ty]
  | index.constant _ => [index]
  | mod_arith.add q => [mod_arith.int q]
  | mod_arith.sub q => [mod_arith.int q]
  | mod_arith.mul q => [mod_arith.int q]
  | mod_arith.encapsulate q => [mod_arith.int q]
  | mod_arith.extract _ => [int]
  | mod_arith.mod_switch.decompose qs _ => [rns.rns qs]
  | mod_arith.mod_switch.interpolate q _ => [mod_arith.int q]

/-- Put them together into a `Signature`. -/
@[simp, reducible]
def Op.signature : Op → Signature Ty
  | o => { sig := o.sig, returnTypes := o.outTy, regSig := [] }

instance : DialectSignature ModArith := ⟨Op.signature⟩

def HVector.toSeq {α} {f : α → Type u} {l}
    (v : HVector f l) (β : Type u) (hf : ∀ x ∈ l, f x = β) :
    Fin l.length → β :=
  fun i => _root_.cast (hf l[i] (by simp)) (v.get i)

def CoprimeNats.coprime_get (qs : CoprimeNats) :
    Pairwise (Function.onFun Nat.Coprime qs.1.get) := by
  rintro i j ne
  simp only [Function.onFun, List.get_eq_getElem]
  wlog lt : i < j generalizing i j
  · rw [Nat.coprime_comm]
    exact this ne.symm (by omega)
  · have := List.pairwise_iff_getElem.mp qs.2
    exact this i.1 j.1 i.2 j.2 lt

def CRTInterpolate (q : ℕ) (qs : CoprimeNats) (x : Π i : Fin qs.1.length, R qs.1[i]) : R q :=
  let n := qs.1.length
  Nat.chineseRemainderOfList (fun i => (x i).val) qs.1.get (List.finRange n) <| by
    apply List.Nodup.pairwise_of_set_pairwise (List.nodup_finRange _)
    simpa using Pairwise.set_pairwise qs.coprime_get _

/-!
## Dialect semantics

Finally, we provide the Lean semantics for each operation in the dialect:
i.e., how to interpret `add`, `sub`, `mul`, etc. as Lean functions.
-/
noncomputable instance : DialectDenote ModArith where
denote
  | arith.constant c, arg, _ => [(c& : ℤ)]ₕ
  | arith.add, arg, _ =>
    let ((x : ℤ), (y : ℤ)) := arg.toPair; [x + y]ₕ
  | arith.sub, arg, _ =>
    let ((x : ℤ), (y : ℤ)) := arg.toPair; [x - y]ₕ
  | arith.mul, arg, _ =>
    let ((x : ℤ), (y : ℤ)) := arg.toPair; [x * y]ₕ
  | arith.remui, arg, _ =>
    let ((x : ℤ), (y : ℤ)) := arg.toPair; [x % y]ₕ
  | tensor.from_elements ty n, arg, _ =>
    [cast (by erw [List.length_replicate]; rfl) <|
      arg.toSeq ⟦ty⟧ fun x => by
        simp [DialectSignature.sig, DialectSignature.signature]
        intros
        congr]ₕ
  | tensor.extract ty n, arg, _ =>
    let ((x : Fin n& → ⟦ty⟧), (i : ℕ)) := arg.toPair
    [if lt : i < n& then x ⟨i, lt⟩ else default]ₕ
  | index.constant c, arg, _ => [(c& : ℕ)]ₕ
  | mod_arith.add q, arg, _ =>
    let ((x : R q&), (y : R q&)) := arg.toPair; [x + y]ₕ
  | mod_arith.sub q, arg, _ =>
    let ((x : R q&), (y : R q&)) := arg.toPair; [x - y]ₕ
  | mod_arith.mul q, arg, _ =>
    let ((x : R q&), (y : R q&)) := arg.toPair; [x * y]ₕ
  | mod_arith.encapsulate q, arg, _ =>
    let x : ℤ := arg.toSingle; [(x : ZMod q&)]ₕ
  | mod_arith.extract q, arg, _ =>
    let x : ZMod q& := arg.toSingle; [(x.cast : ℤ)]ₕ
  | mod_arith.mod_switch.decompose qs q, arg, _ =>
    let x : ZMod q& := arg.toSingle
    [fun _ => x.cast]ₕ
  | mod_arith.mod_switch.interpolate q qs, arg, _ =>
    let n := qs&.1.length
    let x : Π i : Fin n, R qs&.1[i] := arg.toSingle
    [CRTInterpolate q& qs& x]ₕ
