import LeanMLIR.Framework.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order

open Ctxt EffectKind

def Ctxt.Hom.fromHVector {Ty} {Γ Δ : Ctxt Ty} (vec : HVector Γ.Var Δ.toList) : Δ.Hom Γ := by
  intro t v
  obtain ⟨i, hi⟩ := v
  rw [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff] at hi
  rw [← hi.2]
  exact vec.getN i hi.1

lemma Var.apply_appendCases {Ty t} [TyDenote Ty] {Γ Δ Ε : Ctxt Ty}
    {Γv : Valuation Ε} {left : Hom Γ Ε} {right : Hom Δ Ε} {v : (Γ ++ Δ).Var t} :
    Γv (v.appendCases (fun t => left t) (fun t => right t)) =
    v.appendCases (fun t => Γv (left t)) (fun t => Γv (right t)) := by
  cases' v using Var.appendCases <;> simp

lemma List.sizeOf_eq {α : Type u} [SizeOf α] (l : List α) :
    sizeOf l = l.length + 1 + ∑ i : Fin l.length, sizeOf l[i] := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.cons.sizeOf_spec, ih, List.length_cons]
    suffices sizeOf x + ∑ i : Fin l.length, sizeOf l[i] =
        ∑ i : Fin (l.length + 1), sizeOf (x :: l)[i] by omega
    simp [Fin.sum_univ_succ]

namespace HVector

variable {α : Type v} {A B : α → Type u} {l : List α} (v : HVector A l)

section SizeOf

variable [SizeOf α] [∀ a : α, SizeOf (A a)]

lemma sizeOf_eq :
    sizeOf v = l.length + 1 +
    ∑ i : Fin l.length, ((i.val + 1) * (sizeOf l[i] + 1) + sizeOf (v.get i)) := by
  induction v with
  | nil => simp
  | @cons l a x v ih =>
    simp [ih, Fin.sum_univ_succ, List.sizeOf_eq, Fin.succ, HVector.get,
      Finset.sum_add_distrib, mul_add, add_mul]
    omega

lemma sizeOf_get_lt (i : Fin l.length) : sizeOf (v.get i) < sizeOf v := calc
  _ ≤ ∑ i : Fin l.length, sizeOf (v.get i) :=
    CanonicallyOrderedAddCommMonoid.single_le_sum
      (f := fun i => sizeOf (v.get i)) (by simp)
  _ < _ := by
    simp [sizeOf_eq, Finset.sum_add_distrib, mul_add, add_mul]
    omega

end SizeOf

@[simp] lemma ofFn_get : (ofFn A l v.get) = v := by
  induction l with
  | nil => cases v; rfl
  | cons a l ih =>
    rcases v with _ | ⟨x, v⟩
    conv_rhs => rw [← ih v]
    simp [ofFn]

@[simp] lemma get_denote
    {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d] [Monad d.m]
    {l : List (Ctxt d.Ty × List d.Ty)} (T : HVector (fun t => Com d t.1 .impure t.2) l)
    (i : Fin l.length) : T.denote.get i = (T.get i).denote := by
  induction T with
  | nil => exact i.elim0
  | @cons l a x xs ih =>
    haveI : NeZero (a :: l).length := by constructor; simp
    by_cases hi : i = 0
    · cases hi; rfl
    · cases' i with j' hj
      obtain ⟨j, ⟨_⟩⟩ := Nat.exists_eq_add_one_of_ne_zero (n := j') (by simp at hi; omega)
      simpa [get] using ih ⟨j, by simpa using hj⟩

end HVector

variable (d) [DialectSignature d] [TyDenote d.Ty] [DialectDenote d] [Monad d.m] [LawfulMonad d.m]

inductive ExtendedOp
  | original (op : d.Op)
  | generator {Γ eff t} (com : Com d Γ eff t)

def extendedDialect : Dialect where
  Op := ExtendedOp d
  Ty := d.Ty
  m := d.m

variable {d}

instance : DialectSignature (extendedDialect d) where
signature
  | .original op => signature (d := d) op
  | @ExtendedOp.generator _ _ Γ eff t _ => {
    sig := Γ.toList
    regSig := []
    returnTypes := t
    effectKind := eff
  }

instance : TyDenote (extendedDialect d).Ty := (inferInstance : TyDenote d.Ty)

instance : DialectDenote (extendedDialect d) where
denote
  | .original op => DialectDenote.denote op
  | .generator com => fun args _ => by
    refine com.denote fun | t, ⟨i, hi⟩ => ?_
    rw [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff] at hi
    rw [← hi.2]
    exact args.getN i hi.1

instance : Monad ((extendedDialect d).m) := (inferInstance : Monad d.m)
instance : LawfulMonad ((extendedDialect d).m) := (inferInstance : LawfulMonad d.m)

def Lets.combine {Γ eff s t} :
    Lets d Γ eff s → Com d s eff t → Com d Γ eff t
  | nil, c => c
  | var body e, c => body.combine (.var e c)

lemma Lets.denote_combine {Γ eff s t} (l : Lets d Γ eff s) (body : Com d s eff t) :
    (l.combine body).denote =
    fun Γv => l.denote Γv >>= fun Γ'v => body.denote Γ'v := by
  induction l with
  | nil => simp [combine]
  | var e body ih => simp [combine, ih]

def Com.combine {Γ eff s t}
    (c : Com d Γ eff s) (body : Com d (s ++ Γ) eff t) : Com d Γ eff t :=
  c.toLets.combine <| body.changeVars <| fun _ => Var.appendCases
    (fun v => Hom.fromHVector c.returnVars v)
    (fun v => c.outContextHom v)

lemma Com.denoteLets_outContextHom'
    {Γ eff t} (c : Com d Γ eff t) (Γv : Valuation Γ)
    {α} {motive : Valuation c.outContext → Valuation Γ → eff.toMonad d.m α} :
    (c.denoteLets Γv >>= fun Γv' => motive Γv' (Γv'.comap c.outContextHom)) =
    (c.denoteLets Γv >>= fun Γv' => motive Γv' Γv) := by
  induction c using Com.rec' with
  | rets _ => simp
  | var e body ih =>
    simp (config := {unfoldPartialApp := true}) [Hom.comp]
    conv_lhs =>
      enter [2, Γv']
      conv =>
        enter [2, Γv'', 2]
        change fun _ v => Γv''.comap body.outContextHom v.appendInr
      rw [ih Γv' (motive := fun Γv Γv' => motive Γv fun _ v => Γv' v.appendInr)]
    simp [Expr.denote_unfold]

lemma Com.denoteLets_returnVars' {Γ eff t} (c : Com d Γ eff t) (V : Valuation Γ) :
    c.returnVars.map <$> c.denoteLets V = c.denote V := by
  induction c using Com.rec' with
  | rets vs => simp
  | var _ _ ih => simp [denoteLets, ih, denote]

lemma Com.denote_combine {Γ eff s t} (c : Com d Γ eff s) (body : Com d (s ++ Γ) eff t) :
    (c.combine body).denote =
    fun Γv => c.denote Γv >>= fun xs => body.denote (xs ++ Γv) := by
  simp only [combine, Lets.denote_combine, denote_changeVars, ← denoteLets_eq]
  ext Γv
  conv_rhs => enter [1]; simp only [← denoteLets_returnVars']
  simp (config := {unfoldPartialApp := true}) only [
    Valuation.instAppendHVector, Ctxt.instHAppendValuationHAppend,
    bind_map_left, Valuation.comap, Var.apply_appendCases
  ]
  conv_lhs => enter [2, Γv', 2, u, v, 2, w]; change Γv'.comap c.outContextHom w
  rw [Com.denoteLets_outContextHom' (motive :=
    fun Γv' Γv'' => body.denote
      fun s v => Var.appendCases
        (fun t => Γv' (Hom.fromHVector c.returnVars t)) (@Γv'' s) v)]
  congr! 7 with - - Γv' t - v v
  simp only [Valuation.ofHVector_apply, HVector.getElem_map]
  rfl

omit [LawfulMonad d.m] in
lemma Expr.denote_changeEffect_same {Γ eff t} (expr : Expr d Γ eff t) :
    (expr.changeEffect (show eff ≤ eff by rfl)).denote = expr.denote := by
  cases expr; rfl

lemma Com.denote_changeEffect_same {Γ eff t} (com : Com d Γ eff t) :
    (com.changeEffect (show eff ≤ eff by rfl)).denote = com.denote := by
  induction com with
  | rets vs => rfl
  | var e body ih => simp [changeEffect, Expr.denote_changeEffect_same, ← ih]

lemma Com.denote_changeEffect {Γ eff₁ eff₂ t} (h : eff₁ ≤ eff₂) (com : Com d Γ eff₁ t) :
    (com.changeEffect h).denote = fun Γv => liftEffect h (com.denote Γv) :=
  match eff₁, eff₂, h with
    | .pure, .pure, _ | .impure, .impure, _ => by rw [Com.denote_changeEffect_same]; rfl
    | .pure, .impure, _ => Com.denote_castPureToEff

def Com.expand {Γ eff t} (c : Com (extendedDialect d) Γ eff t) : Com d Γ eff t :=
  match c with
  | rets vs => rets vs
  | var (.mk (.original op) ty_eq eff_le args regArgs) body =>
    var (.mk op ty_eq eff_le args
      (HVector.ofFn _ _ fun i => Com.expand (regArgs.get i))) body.expand
  | var (.mk (.generator com) ty_eq eff_le args regArgs) body => by
    rw [ty_eq] at body
    exact ((com.changeEffect eff_le).changeVars (.fromHVector args)).combine body.expand
termination_by sizeOf c
decreasing_by
  · suffices sizeOf (regArgs.get i) < sizeOf regArgs by simp; omega
    apply HVector.sizeOf_get_lt
  · dsimp; omega
  · generalize_proofs h
    have : sizeOf (h.mp body) = sizeOf body := by congr 2 <;> simp [ty_eq]
    rw [this]
    dsimp; omega

@[simp] lemma Com.denote_expand {Γ eff t} (c : Com (extendedDialect d) Γ eff t) :
    c.expand.denote = c.denote :=
  match c with
  | rets vs => by simp only [expand]; rfl
  | c@hc:(var (.mk (.original op) ty_eq eff_le args regArgs) body) => by
    cases ty_eq
    simp only [expand, denote_var, Expr.denote]
    congr! 2 with v
    · congr 3
      ext1 i
      conv_rhs => rw [HVector.get_denote regArgs]
      simpa using denote_expand (regArgs.get i)
    · rw [denote_expand body]
  | c@hc:(var (.mk (.generator com) ty_eq eff_le args regArgs) body) => by
    cases ty_eq
    simp only [expand, denote_combine, denote_changeVars, denote_changeEffect,
      denote_var, ← denote_expand body, Expr.denote, bind_pure_comp, bind_map_left]
    congr! 3 with Γv
    congr 1
    change (_ : ∀ _, _) = _
    ext t ⟨i, hi⟩
    simp [Hom.fromHVector, HVector.get_map, eq_cast_iff_heq]
    congr 1
    · simp only [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff] at hi
      simpa [DialectSignature.sig, signature] using hi.2.symm
    · simp
termination_by sizeOf c
decreasing_by
  · suffices sizeOf (regArgs.get i) < sizeOf regArgs by simp [namedPattern]; omega
    apply HVector.sizeOf_get_lt
  · rename_i hc' _ _ _ _ _
    simp [namedPattern, ← hc', hc]
  · rename_i hc' _ _ _ _
    simp [namedPattern, ← hc', hc]

private def toExtendedAux {Γ eff t} (n : ℕ) :
    ((e : Expr d Γ eff t) → sizeOf e < n → Expr (extendedDialect d) Γ eff t) ×
    ((c : Com d Γ eff t) → sizeOf c < n → Com (extendedDialect d) Γ eff t) :=
  match n with
  | 0 => by constructor <;> omega
  | n + 1 => (
    fun
    | .mk op ty_eq eff_le args regArgs, he =>
      .mk (.original op) ty_eq eff_le args <|
      HVector.ofFn _ _ fun i => (toExtendedAux n).2 (regArgs.get i) <| by
        suffices sizeOf (regArgs.get i) < sizeOf regArgs by simp at he ⊢; omega
        apply HVector.sizeOf_get_lt,
    fun
    | .rets vs, hc => .rets vs
    | .var expr body, hc => .var
      ((toExtendedAux n).1 expr (by simp at hc ⊢; omega))
      ((toExtendedAux n).2 body (by simp at hc ⊢; omega))
  )

noncomputable def Expr.toExtended {Γ eff t} (e : Expr d Γ eff t) : Expr (extendedDialect d) Γ eff t :=
  (toExtendedAux (sizeOf e + 1)).1 e (by simp)

noncomputable def Com.toExtended {Γ eff t} (c : Com d Γ eff t) : Com (extendedDialect d) Γ eff t :=
  (toExtendedAux (sizeOf c + 1)).2 c (by simp)
