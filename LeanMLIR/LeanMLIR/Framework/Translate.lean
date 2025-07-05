import LeanMLIR.Framework.Basic

variable (d d') [DialectSignature d] [DialectSignature d']
    [TyDenote d.Ty] [TyDenote d'.Ty] [DialectDenote d] [DialectDenote d']
    [Monad d.m] [Monad d'.m] [LawfulMonad d.m] [LawfulMonad d'.m]

class TypeTranslation (d d' : Dialect) : Type 1 where
  translateType : d.Ty → d'.Ty
open TypeTranslation (translateType)

class Translation (d d' : Dialect) [TyDenote d.Ty] [TyDenote d'.Ty]
    [TypeTranslation d d'] : Type 1 where
  translate : ∀ t : d.Ty, ⟦t⟧ → ⟦(translateType t : d'.Ty)⟧
open Translation (translate)

variable {d} [TypeTranslation d d'] [Translation d d']

def Ctxt.translate (Γ : Ctxt d.Ty) : Ctxt d'.Ty := Γ.map translateType

def Ctxt.Var.translate {t} {Γ : Ctxt d.Ty} : Γ.Var t → (Γ.translate d').Var (translateType t)
  | ⟨i, hi⟩ => ⟨i, by
    simp [Ctxt.translate, Ctxt.map, List.getElem?_map, ← getElem?_eq_toList_getElem?, hi]
  ⟩

def Ctxt.Valuation.translate {Γ : Ctxt d.Ty} (Γv : Valuation Γ) : Valuation (Γ.translate d') := by
  intro t ⟨i, hi⟩
  simp [Ctxt.translate, Ctxt.map, List.getElem?_map] at hi
  have : i < Γ.toList.length := by
    rcases hi with ⟨t', h, ⟨_⟩⟩
    rw [List.getElem?_eq_some_iff] at h
    exact h.1
  have : t = translateType Γ[i] := by
    rcases hi with ⟨t', h, ⟨_⟩⟩
    rw [List.getElem?_eq_some_iff] at h
    rcases h with ⟨_, ⟨_⟩⟩
    rfl
  cases this
  refine Translation.translate _ (Γv (t := Γ[i]) ⟨i, ?_⟩)
  rw [getElem?_eq_toList_getElem?, List.getElem?_eq_some_iff]
  exact ⟨this, rfl⟩

variable (d) in
structure TranslateRewrite (Γ : Ctxt d.Ty) (ts : List d.Ty) where
  lhs : Com d Γ .pure ts
  rhs : Com d' (Γ.map translateType) .pure (ts.map translateType)
  correct : ∀ Γv, HVector.map' translateType translate (lhs.denote Γv) =
    rhs.denote (Γv.translate d')
