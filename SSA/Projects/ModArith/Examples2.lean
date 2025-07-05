import LeanMLIR.MLIRSyntax.PrettyEDSL
import LeanMLIR.Tactic
import SSA.Projects.ModArith.Basic
import SSA.Projects.ModArith.Statements
import SSA.Projects.ModArith.Syntax
import SSA.Projects.ModArith.PrettySyntax
import Mathlib.Data.ZMod.Coprime

class Parameters where
  qs : List ℕ
  coprime : qs.Pairwise Nat.Coprime
  not_contain_zero : 0 ∉ qs

open Lean Parameters Value Ctxt Ty Translation TypeTranslation

variable [inst : Parameters]

def n := qs.length
def q := qs.prod
def c (i : Fin n) : ℤ := q / qs[i] * ((q / qs[i] : ZMod qs[i])⁻¹).cast
def qs' : CoprimeNats := ⟨qs, coprime⟩

inductive VarIndex
  | Q | N | Qs | C (i : Fin n) | I (i : Fin n)
deriving DecidableEq, Repr, Inhabited
open VarIndex

instance : ValueMap ℕ VarIndex where
  map
  | Q => q
  | N => n
  | I i => i
  | _ => default

instance : ValueMap ℤ VarIndex where
  map
  | Q => q
  | C i => c i
  | _ => default

instance : ValueMap CoprimeNats VarIndex where
  map
  | Qs => qs'
  | _ => default

lemma q_ne_zero : q ≠ 0 := by
  simpa only [q, ne_eq, List.prod_eq_zero_iff] using not_contain_zero

instance : NeZero q := ⟨q_ne_zero⟩

def lhsInitContext : Ctxt ModArith.Ty := [rns.rns (var Qs)]
def lhsFinalContext : List ModArith.Ty := [(mod_arith.int (var Q) : Ty)]

def lhsInterpolate := [mod_arith | {
  ^bb0(%arg : !rns.rns<%Qs>):
    %result = mod_arith.mod_switch %arg : !rns.rns<%Qs> to !mod_arith.int<%Q>
    return %result : !mod_arith.int<%Q>
}]

def rhsInitContext : Ctxt ModArith.Ty := [tensor (var N) int]
def rhsFinalContext : List ModArith.Ty := [int]

def rhsLoop (i : Fin (n + 1)) : Com ModArith rhsInitContext .pure rhsFinalContext := by
  induction i using Fin.induction with
  | zero => exact [mod_arith | {
    ^bb0(%arg : tensor<%N x i64>):
      %result = arith.constant 0 : i64
      return %result : i64
    }]
  | succ i rhsLoop => exact %[mod_arith | {
    ^bb0(%arg : tensor<%N x i64>):
      %old_sum = [rhsLoop] %arg : (tensor<%N x i64>) -> i64
      %coeff = arith.constant %(C i) : i64
      %index = index.constant %(I i) : i64
      %value = tensor.extract %arg[%index] : tensor<%N x i64> -> i64
      %mul = arith.mul %value, %coeff : i64
      %result = arith.add %old_sum, %mul : i64
      return %result : i64
    }]

def rhsInterpolate := %[mod_arith | {
  ^bb0(%arg : tensor<%N x i64>):
    %mod = arith.constant %Q : i64
    %sum = [rhsLoop (Fin.last n)] %arg : (tensor<%N x i64>) -> i64
    %result = arith.remui %sum, %mod : i64
    return %result : i64
}]

instance : TypeTranslation ModArith ModArith where
  translateType
  | rns.rns (var Qs) => .tensor (var N) int
  | mod_arith.int (var Q) => int
  | _ => default

instance : Translation ModArith ModArith where
  translate
  | rns.rns (var Qs) => fun x i => ((x i).cast : ℤ)
  | mod_arith.int (var Q) => fun x => (x.cast : ℤ)
  | _ => default

def lhsType := Π i : Fin n, ZMod qs[i]
def lhsValue (arg : lhsType) : ℤ := (CRTInterpolate q ⟨qs, coprime⟩ arg).cast

def rhsType := Fin n → ℤ
def rhsTypeList := [tensor (var N) int]
def rhsCtxt : Ctxt ModArith.Ty := rhsTypeList
def rhsLoopValue (arg : rhsType) (i : Fin (n + 1)) : ℤ :=
  ∑ j : Fin n with j.castSucc < i, arg j * c j
def rhsValue (arg : rhsType) : ℤ := rhsLoopValue arg (Fin.last n) % q

lemma rhsValue_eq (arg : rhsType) : rhsValue arg = (∑ j : Fin n, arg j * c j) % q := by
  simp [rhsValue, rhsLoopValue]

def loweringRNS (arg : lhsType) : rhsType :=
  translate (rns.rns (var Qs)) (d := ModArith) (d' := ModArith) arg

lemma loweringRNS_apply (arg : lhsType) (i : Fin n) : loweringRNS arg i = (arg i).cast := rfl

def rhsLoopValuation (arg : Fin n → ℤ) : rhsCtxt.Valuation
  | t, ⟨i, hi⟩ => by
    convert ([arg]ₕ : HVector toType rhsTypeList).get ⟨i, ?_⟩; swap
    · rw [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff] at hi
      exact hi.1
    · rw [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff] at hi
      simp [rhsCtxt, rhsTypeList] at hi
      simpa using hi.2.symm

lemma rhsLoopDenote (arg : Fin n → ℤ) (i : Fin (n + 1)) :
    (rhsLoop i).denote (rhsLoopValuation arg) = [rhsLoopValue arg i]ₕ := by
  induction i using Fin.induction with
  | zero =>
    simp only [rhsLoop, Fin.induction_zero]
    simp_peephole
    simp [rhsLoopValue]
    rfl
  | succ i ih =>
    simp only [rhsLoop, Fin.induction_succ]
    rw [← rhsLoop]
    simp_peephole
    simp only [show ((var (I i))& : ℕ) < (var N)& from i.2, ↓reduceDIte]
    erw [ih]
    unfold rhsLoopValuation
    simp_peephole
    simp only [Eq.mpr, Value.get, ValueMap.map, Fin.mk_val]
    simp only [rhsLoopValue, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_succ_iff]
    convert Finset.sum_Iio_add_eq_sum_Iic i (f := fun j => arg j * c j)
    · ext j; simp
    · ext j; simp

lemma q_div_eq (i : Fin n) : q / qs[i] = ∏ j ∈ {i}ᶜ, qs[j] := by
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.pos_of_ne_zero fun h => not_contain_zero (List.mem_of_getElem h)
  · rw [show {i}ᶜ = Finset.univ.erase i by ext; simp, Finset.prod_erase_mul _ _ (by simp)]
    simp [q, ← Fin.prod_univ_getElem]
    rfl

lemma c_cast (i j : Fin n) : (c i : ZMod qs[j]) = if i = j then 1 else 0 := by
  simp only [c]
  split_ifs with eq
  · subst eq
    push_cast
    norm_cast
    apply ZMod.mul_inv_of_unit
    rw [ZMod.isUnit_iff_coprime, q_div_eq, Nat.coprime_prod_left_iff]
    simpa [← ne_eq] using fun j ne => qs'.coprime_get ne
  · push_cast
    suffices ((q / qs[i] : ℤ) : ZMod qs[j]) = 0 by rw [this]; simp
    norm_cast
    rw [ZMod.natCast_eq_zero_iff, q_div_eq]
    apply Finset.dvd_prod_of_mem
    simpa [eq_comm] using eq

lemma value_eq : lhsValue = rhsValue ∘ loweringRNS := by
  ext x
  simp only [Function.comp]
  have q_ne_zero := q_ne_zero
  rw [← Int.emod_eq_of_lt (a := lhsValue _) (b := q),
      ← Int.emod_eq_of_lt (a := rhsValue _) (b := q),
      ← ZMod.intCast_eq_intCast_iff']
  · rw [show q = ∏ i : Fin qs.length, qs[i] by simp [q]]
    apply_fun ZMod.prodEquivPi qs.get qs'.coprime_get
    ext i
    have qs_dvd_q : qs[i] ∣ q := by
      simpa [q, ← Fin.prod_univ_getElem] using Finset.dvd_prod_of_mem _ (by simp)
    rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply,
        ZMod.cast_intCast (by simpa using qs_dvd_q), ZMod.cast_intCast (by simpa using qs_dvd_q)]
    simp only [lhsValue, CRTInterpolate, rhsValue_eq, loweringRNS_apply]
    rw [ZMod.intCast_cast, ZMod.cast_natCast qs_dvd_q]
    calc
      _ = ((x i).val : ZMod qs[i]) := by
        rw [ZMod.eq_iff_modEq_nat]
        exact (Nat.chineseRemainderOfList _ _ _ _).2 i (by simp)
      _ = x i := by
        haveI : NeZero qs[i] := ⟨fun h => not_contain_zero (List.mem_of_getElem h)⟩
        simp
      _ = ∑ i, (x i).cast * c i := by simp [c_cast]
      _ = _ := by
        rw [ZMod.intCast_eq_intCast_iff', Int.emod_emod_of_dvd]
        norm_cast
  · simpa only [rhsValue] using Int.emod_nonneg _ (by omega)
  · simpa only [rhsValue] using Int.emod_lt_of_pos _ (by omega)
  · simpa only [lhsValue, ← ZMod.natCast_val] using Int.natCast_nonneg _
  · simpa [lhsValue, CRTInterpolate, ← ZMod.natCast_val] using Int.emod_lt_of_pos _ (by omega)

theorem lowering_denote_eq (Γv : Valuation lhsInitContext) :
    HVector.map' (translateType (d := ModArith)) (translate (d' := ModArith))
    (lhsInterpolate.denote Γv) = rhsInterpolate.denote (Γv.translate ModArith) := by
  revert Γv
  simp only [lhsInitContext, lhsInterpolate, rhsInterpolate]
  simp_peephole
  intro arg
  change lhsType at arg
  conv_lhs => change ([lhsValue arg]ₕ : HVector toType [int])
  erw [rhsLoopDenote]
  conv_rhs => enter [1]; change rhsValue (loweringRNS arg)
  simp [value_eq]

def loweringCorrect : TranslateRewrite ModArith ModArith lhsInitContext lhsFinalContext where
  lhs := lhsInterpolate
  rhs := rhsInterpolate
  correct := lowering_denote_eq

/--
info: 'loweringCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms loweringCorrect
