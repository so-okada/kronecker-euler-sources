import KroneckerDirectSumIteratedEmbedding

/-! The direct-sum inclusion has full outgoing and incoming arrow lifting at
every point of its image. This is stronger than being a quiver embedding and
is what makes its image a union of entire connected components. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumEmbeddingLocalLifts
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerDirectSumAbelianCover
open KroneckerDirectSumCoverEmbeddingLift KroneckerDirectSumIteratedEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def LocallySurjective (f : QuiverMap P Q) : Prop :=
  (∀ (x : P.V) (a : Q.A), Q.source a = f.vertex x →
    ∃ b : P.A, P.source b = x ∧ f.arrow b = a) ∧
  (∀ (x : P.V) (a : Q.A), Q.target a = f.vertex x →
    ∃ b : P.A, P.target b = x ∧ f.arrow b = a)

theorem liftMap_locallySurjective (f : QuiverMap P Q) (hf : LocallySurjective f) :
    LocallySurjective (liftMap f) := by
  constructor
  · intro x a h
    obtain ⟨b,hs,hb⟩ := hf.1 x.1 a.1 (congrArg (fun z : Q.abelian.V => z.1) h)
    refine ⟨(b,x.2),Prod.ext hs rfl,?_⟩
    apply Prod.ext
    · exact hb
    · exact (congrArg (fun z : Q.abelian.V => z.2) h).symm
  · intro x a h
    obtain ⟨b,ht,hb⟩ := hf.2 x.1 a.1 (congrArg (fun z : Q.abelian.V => z.1) h)
    refine ⟨(b,x.2-Finsupp.single b 1),?_,?_⟩
    · apply Prod.ext
      · exact ht
      · exact sub_add_cancel _ _
    · apply Prod.ext
      · exact hb
      · have hc : pushCharacter f (x.2-Finsupp.single b 1) + unit a.1 = pushCharacter f x.2 := by
          rw [← hb,← pushCharacter_single,← pushCharacter_add,sub_add_cancel]
        exact add_right_cancel (hc.trans (congrArg (fun z : Q.abelian.V => z.2) h).symm)

theorem embedding_locallySurjective (Q : TypedQuiver) (n : ℕ) :
    LocallySurjective (embedding Q n) := by
  induction n with
  | zero => exact ⟨fun x a h => ⟨a,h,rfl⟩,fun x a h => ⟨a,h,rfl⟩⟩
  | succ n ih => exact liftMap_locallySurjective _ ih

end KroneckerDirectSumEmbeddingLocalLifts
