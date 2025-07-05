/-
This file contains the definition of the MLIR `ModArith` dialect as
implemented in HEIR, see:
  https://heir.dev/docs/dialects/modarith/

It is structurally similar to `FullyHomomorphicEncryption.Basic.lean` but focuses on arithmetic
directly in ℤ/qℤ (ZMod q), rather than polynomials over ℤ/qℤ.

Authors: Jaeho Choi<zerozerozero0216@gmail.com>
-/
import Mathlib.Data.ZMod.Basic
import SSA.Core.Framework

open ZMod

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
/- We assume `q > 1`. -/
variable (q : ℕ) [Fact (q > 1)]

/--
By analogy to `R q n` from the `Poly` dialect, we simply define
`R q := ZMod q`. The ring structure on `ZMod q` is already known
to mathlib.
-/
abbrev R := ZMod q

end CommRing

/-!
## Dialect type definitions

Here, we define a small type system for the `ModArith` dialect:
  1. `integer` – for full-range integers in Lean (ℤ).
  2. `modLike` – for our ring `ZMod q`.

You can freely add more types or rename them according to your needs.
-/
inductive Ty where
| integer
| modLike (q : ℕ)
| RNS (qs : List ℕ)
| tensor (type : Ty) (n : ℕ)

deriving DecidableEq, Repr, Inhabited

/--
We provide a `ToString` instance: this is a human-readable name for each type.
-/
instance : ToString Ty where
  toString := toString
where
  toString := fun
  | .integer => "int"
  | .modLike (q : ℕ) => s!"!mod_arith.int{q}"
  | .RNS (qs : List ℕ) => s!"!rns.rns{qs}"
  | .tensor type n => s!"!tensor{toString type} {n}"

/--
We provide a `TyDenote` instance: this is how we translate each
dialect type into an actual Lean type.
-/
instance : TyDenote Ty where
  toType := toType
where
  toType := fun
  | .integer => Int
  | .modLike q => R q  -- i.e. `ZMod q`
  | .RNS qs => Π i : Fin qs.length, R qs[i]  -- i.e. `RNS qs`
  | .tensor type n => Fin n → toType type

/-!
## Dialect operation definitions

Here are some sample operations. Adjust as appropriate for the
`modarith` dialect: e.g. you might have add/sub/mul, an operation for
returning constants mod q, an integer constant, etc.
-/
inductive Op where
| arith.constant (ty : Ty) (c : ⟦ty⟧) : Op  -- produce a constant
| arith.add : Op              -- (modLike, modLike) → modLike
| arith.mul : Op              -- (modLike, modLike) → modLike
| arith.remui : Op            -- (modLike, modLike) → modLike
| mod_arith.encapsulate : Op  -- (modLike, modLike) → modLike
| mod_arith.extract : Op      -- (modLike, modLike) → modLike
| mod_arith.mod_switch : Op   -- (modLike, modLike) → modLike
| tensor.from_elements (ty : Ty) (n : ℕ) : Op
| mod_arith.add : Op          -- (modLike, modLike) → modLike
| mod_arith.sub : Op          -- (modLike, modLike) → modLike
| mod_arith.mul : Op          -- (modLike, modLike) → modLike

/--
For each operation, we specify its input `sig` (a list of
types) and its `outTy` (the output type).
-/
@[simp, reducible]
def Op.sig : Op → List Ty
| .modSwitch      => [Ty.modLike q, Ty.RNS [q]]
| .add            => [Ty.modLike q, Ty.modLike q]
| .add            => [Ty.modLike q, Ty.modLike q]
| .add            => [Ty.modLike q, Ty.modLike q]
| .add            => [Ty.modLike q, Ty.modLike q]
| .sub            => [Ty.modLike q, Ty.modLike q]
| .mul            => [Ty.modLike q, Ty.modLike q]
| .arith.mul      => [Ty.modLike q, Ty.modLike q]
| .const _ _      => []

@[simp, reducible]
def Op.outTy : Op → Ty
| .add         => Ty.modLike
| .sub         => Ty.modLike
| .mul         => Ty.modLike
| .const ty _   => ty

/-- Put them together into a `Signature`. -/
@[simp, reducible]
def Op.signature : Op q → Signature (Ty q)
| o => { sig := o.sig, outTy := o.outTy, regSig := [] }

/-!
## The `ModArith` dialect

We bundle up our `Op` and `Ty` into a dialect called `ModArith q`.
-/
abbrev ModArith (q : ℕ) [Fact (q > 1)] : Dialect where
Op := Op q
Ty := Ty q

instance (q : ℕ) [Fact (q > 1)] : DialectSignature (ModArith q) := ⟨Op.signature⟩

/-!
## Dialect semantics

Finally, we provide the Lean semantics for each operation in the dialect:
i.e., how to interpret `add`, `sub`, `mul`, etc. as Lean functions.
-/
noncomputable instance (q : ℕ) [Fact (q > 1)] : DialectDenote (ModArith q) where
denote
  | .add, arg, _ =>
      -- Add mod q
      (fun args : R q × R q => args.1 + args.2) arg.toPair
  | .sub, arg, _ =>
      -- Sub mod q
      (fun args : R q × R q => args.1 - args.2) arg.toPair
  | .mul, arg, _ =>
      -- Mul mod q
      (fun args : R q × R q => args.1 * args.2) arg.toPair
  | .const _ c, _, _ =>
      -- A constant
      c
