import KroneckerFiniteBranchClasses
import KroneckerBranchWeights

set_option autoImplicit false
namespace KroneckerBranchClassWeights
open KroneckerFiniteBranchObjects KroneckerBranchClassRelations KroneckerBranchWeights
open KroneckerFiniteBranchClasses KroneckerGradedProfileWeights
open scoped BigOperators

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}
variable {R : Type*} [CommSemiring R]

noncomputable def sourceClassWeight (x : R) (y : Fin 3 → R) : SourceClass I J d → R :=
  Quotient.lift (fun S => sourceWeight S.1.1 x y) (by
    rintro S T ⟨e,_⟩
    exact source_weight_iso e x y)

noncomputable def sinkClassWeight (x : R) (y : Fin 3 → R) : SinkClass I J d → R :=
  Quotient.lift (fun S => sinkWeight S.1.1 S.1.2 d x y) (by
    rintro S T ⟨e,he⟩
    have h := sink_weight_iso e S.1.2 d x y
    simpa only [he] using h)

theorem source_class_weight_at_one (q : SourceClass I J d) :
    sourceClassWeight (1 : R) (fun _ => 1) q=1 := by
  induction q using Quotient.inductionOn with | _ S =>
    simp [sourceClassWeight,sourceWeight,gradedWeight]

theorem sink_class_weight_at_one (q : SinkClass I J d) :
    sinkClassWeight (1 : R) (fun _ => 1) q=1 := by
  induction q using Quotient.inductionOn with | _ S =>
    simp [sinkClassWeight,sinkWeight,gradedWeight]

theorem source_class_weight_sum_at_one :
    (∑ q : SourceClass I J d,sourceClassWeight (1 : R) (fun _ => 1) q)=
      (Fintype.card (SourceClass I J d) : R) := by simp [source_class_weight_at_one]

theorem sink_class_weight_sum_at_one :
    (∑ q : SinkClass I J d,sinkClassWeight (1 : R) (fun _ => 1) q)=
      (Fintype.card (SinkClass I J d) : R) := by simp [sink_class_weight_at_one]

end KroneckerBranchClassWeights
