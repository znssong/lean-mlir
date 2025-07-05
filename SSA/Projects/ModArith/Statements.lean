/-
This file contains some basic lemmas for the `ModArith` dialect in HEIR,
analogous to the `Statements.lean` file from the `Poly` dialect.

Authors: Jaeho Choi<zerozerozero0216@gmail.com>
-/
import SSA.Projects.ModArith.Basic
import Batteries.Data.List.Lemmas
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing

open scoped Function

lemma ZMod.prodEquivPi_apply {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) (x : ZMod (∏ i, a i)) (i : ι) :
    ZMod.prodEquivPi a coprime x i = x.cast := ZMod.intCast_cast _
