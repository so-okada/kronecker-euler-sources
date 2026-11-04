import KroneckerAbelianCharacterReindex

/- Original module: KroneckerFiniteCharacterSubgroup -/
section
/-! The actual direct-sum character lattice is a subgroup of the product
characters. Its equivalence with finitely supported integer functions is
explicit; membership is exactly finite nonzero coordinate support. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteCharacterSubgroup
open KroneckerAbelianCover KroneckerAbelianCharacterReindex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A B : Type}

def finiteCharacters (A : Type) : AddSubgroup (Character A) where
  carrier := {χ | ∃ d : A →₀ ℤ, (d : A → ℤ) = χ}
  zero_mem' := ⟨0,rfl⟩
  add_mem' := by
    rintro a b ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨f+g,rfl⟩
  neg_mem' := by
    rintro a ⟨f,rfl⟩
    exact ⟨-f,rfl⟩

def characterEquiv (A : Type) : (A →₀ ℤ) ≃+ finiteCharacters A where
  toFun d := ⟨d,⟨d,rfl⟩⟩
  invFun χ := Classical.choose χ.property
  left_inv d := by
    apply Finsupp.ext
    intro a
    exact congrFun (Classical.choose_spec (show ∃ e : A →₀ ℤ, (e : A → ℤ) = d from ⟨d,rfl⟩)) a
  right_inv χ := Subtype.ext (Classical.choose_spec χ.property)
  map_add' _ _ := rfl



theorem reindex_mem (e : A ≃ B) {χ : Character A} (h : χ ∈ finiteCharacters A) :
    reindex e χ ∈ finiteCharacters B := by
  obtain ⟨d,rfl⟩ := h
  refine ⟨d.mapDomain e,?_⟩
  funext b
  rw [Finsupp.mapDomain_equiv_apply]
  rfl


end KroneckerFiniteCharacterSubgroup
end
end

/- Original module: KroneckerDirectSumAbelianCover -/
section
/-! The abelian cover built from the direct sum of the arrow-indexed integer
lattice, for arbitrary arrow types. Its inclusion in the product model is
injective and preserves both endpoints of each actual arrow. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumAbelianCover
open KroneckerAbelianCover KroneckerFiniteCharacterSubgroup
attribute [local instance] Classical.decEq Classical.propDecidable

def directCover (Q : TypedQuiver) : TypedQuiver where
  V := Q.V × (Q.A →₀ ℤ)
  A := Q.A × (Q.A →₀ ℤ)
  source a := (Q.source a.1,a.2)
  target a := (Q.target a.1,a.2 + Finsupp.single a.1 1)

def vertexInclusion (Q : TypedQuiver) (v : (directCover Q).V) : Q.abelian.V := (v.1,v.2)
def arrowInclusion (Q : TypedQuiver) (a : (directCover Q).A) : Q.abelian.A := (a.1,a.2)


theorem arrowInclusion_injective (Q : TypedQuiver) : Function.Injective (arrowInclusion Q) := by
  rintro ⟨v,χ⟩ ⟨w,ψ⟩ h
  apply Prod.ext
  · exact congrArg (fun x : Q.abelian.A => x.1) h
  · apply Finsupp.ext
    exact congrFun (congrArg (fun x : Q.abelian.A => x.2) h)

theorem inclusion_source (Q : TypedQuiver) (a : (directCover Q).A) :
    Q.abelian.source (arrowInclusion Q a) = vertexInclusion Q ((directCover Q).source a) := rfl

theorem inclusion_target (Q : TypedQuiver) (a : (directCover Q).A) :
    Q.abelian.target (arrowInclusion Q a) = vertexInclusion Q ((directCover Q).target a) := by
  apply Prod.ext
  · rfl
  · funext b
    change a.2 b + unit a.1 b = ((a.2 + Finsupp.single a.1 1) : Q.A →₀ ℤ) b
    simp only [Finsupp.add_apply,Finsupp.single_apply,unit,Pi.single_apply,eq_comm]

theorem vertex_range (Q : TypedQuiver) (v : Q.abelian.V) :
    v ∈ Set.range (vertexInclusion Q) ↔ v.2 ∈ finiteCharacters Q.A := by
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w.2,rfl⟩
  · rintro ⟨χ,hχ⟩
    exact ⟨(v.1,χ),Prod.ext rfl hχ⟩

end KroneckerDirectSumAbelianCover
end
end
