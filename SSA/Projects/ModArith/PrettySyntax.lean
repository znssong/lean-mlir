/-
This file defines a "pretty syntax" for the `ModArith` dialect, analogous to
`FullyHomomorphicEncryption/PrettySyntax.lean`.

It provides macros to parse lines of the form:
  %v = mod_arith.constant 12 : !Zp
  %w = mod_arith.add %x, %y : !Zp
etc., into the uniform EDSL used by the MLIR translation in Lean.

Authors: Jaeho Choi <zerozerozero0216@gmail.com>
-/
import LeanMLIR.MLIRSyntax.PrettyEDSL
import SSA.Projects.ModArith.Syntax

namespace MLIR.EDSL.Pretty
open Lean

/--
We declare `mod_arith.constant`, `mod_arith.add`, `mod_arith.sub`, etc.
as uniform ops. This means we can write lines like:

  %x = mod_arith.add %a, %b : (!Zp, !Zp) -> !Zp

and the `PrettyEDSL` machinery will parse them automatically.
-/
syntax "mod_arith.add" : MLIR.Pretty.uniform_op
syntax "mod_arith.sub" : MLIR.Pretty.uniform_op
syntax "mod_arith.mul" : MLIR.Pretty.uniform_op
syntax "arith.add" : MLIR.Pretty.uniform_op
syntax "arith.sub" : MLIR.Pretty.uniform_op
syntax "arith.mul" : MLIR.Pretty.uniform_op
syntax "arith.remui" : MLIR.Pretty.uniform_op
syntax "return" : MLIR.Pretty.uniform_op

/--
We handle two forms:

  1) `%v = arith.constant 42 : !int`
     which gets parsed as an integer attribute with value 42

  2) `%v = arith.constant -10 : !int`
     for negative numbers

For each, we produce a uniform op in the underlying IR:

  `%v = "arith.constant" () {value = 42} : () -> (!Zp)`
-/

syntax mlir_op_operand " = " "arith.constant" neg_num " : " mlir_type : mlir_op
syntax mlir_op_operand " = " "arith.constant" "%" term:max " : " mlir_type : mlir_op
syntax mlir_op_operand " = " "index.constant" num " : " mlir_type : mlir_op
syntax mlir_op_operand " = " "index.constant" "%" term:max " : " mlir_type : mlir_op
syntax mlir_op_operand " = " "mod_arith.encapsulate" mlir_op_operand " : " mlir_type " -> " mlir_type : mlir_op
syntax mlir_op_operand " = " "mod_arith.mod_switch" mlir_op_operand " : " mlir_type &" to " mlir_type : mlir_op
syntax mlir_op_operand " = " "tensor.extract" mlir_op_operand "[" mlir_op_operand "]" " : " mlir_type " -> " mlir_type : mlir_op

macro_rules
  | `(mlir_op| $v:mlir_op_operand = arith.constant $x:neg_num : $t) =>
    `(mlir_op| $v:mlir_op_operand = "arith.constant" () {value = $x:neg_num} : () -> ($t))
  | `(mlir_op| $v:mlir_op_operand = arith.constant %$x:term : $t) =>
    `(mlir_op| $v:mlir_op_operand = "arith.constant" () {value = mlir_attr_quoted($x, TheIndex ℤ)} : () -> ($t))
  | `(mlir_op| $v:mlir_op_operand = index.constant $x:num : $t) =>
    `(mlir_op| $v:mlir_op_operand = "index.constant" () {value = $x:num} : () -> ($t))
  | `(mlir_op| $v:mlir_op_operand = index.constant %$x:term : $t) =>
    `(mlir_op| $v:mlir_op_operand = "index.constant" () {value = mlir_attr_quoted($x, TheIndex ℕ)} : () -> ($t))
  | `(mlir_op| $v:mlir_op_operand = mod_arith.encapsulate $x : $s -> $t) =>
    `(mlir_op| $v:mlir_op_operand = "mod_arith.encapsulate" ($x) : ($s) -> ($t))
  | `(mlir_op| $v:mlir_op_operand = mod_arith.mod_switch $x : $s to $t) =>
    `(mlir_op| $v:mlir_op_operand = "mod_arith.mod_switch" ($x) : ($s) -> ($t))
  | `(mlir_op| $v:mlir_op_operand = tensor.extract $x[$i] : $s -> $t) =>
    `(mlir_op| $v:mlir_op_operand = "tensor.extract" ($x, $i) : ($s, index) -> ($t))

section Test

local instance : ValueMap ℕ Name := { map := fun _ => default }
local instance : ValueMap ℤ Name := { map := fun _ => default }
local instance : ValueMap CoprimeNats Name := { map := fun _ => default }

private def test := [mod_arith | {
  ^bb0(%a : i64, %b : !mod_arith.int<%`n>) :
    %c = arith.constant 3 : i64
    %d = arith.mul %a, %c : i64
    return %d : i64
}]

/--
A small test snippet. If you do:

  #check test_one_lhs

It shows how Lean parses:

  %e1 = mod_arith.constant 12 : !R
  %e2 = mod_arith.constant -5 : !R
  %add = mod_arith.add %e1, %e2 : !R
  return %add : !R
-/
private def test_lhs := %[mod_arith | {
  ^bb0(%a : !mod_arith.int<%`n>, %b : !rns.rns<[3, 5]>):
    %e1 = arith.constant 12 : i64
    %e2 = [test] %e1, %a : (i64, !mod_arith.int<%`n>) -> i64
    %e3 = arith.mul %e1, %e2 : i64
    return %e3 : i64
}]

/--
info: '_private.SSA.Projects.ModArith.PrettySyntax.0.MLIR.EDSL.Pretty.test_lhs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms test_lhs

end Test

end Pretty

end EDSL

end MLIR
