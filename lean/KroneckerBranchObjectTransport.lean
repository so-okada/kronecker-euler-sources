import KroneckerFiniteBranchClasses

set_option autoImplicit false
namespace KroneckerBranchObjectTransport
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerColoredTableTransport
open KroneckerBranchIsomorphismInvariance

variable {I J I' J' : Type} {d : Fin 3}

noncomputable def transportSourceObject (S : SourceObject I J d) (s : I ≃ I') (t : J ≃ J') :
    SourceObject I' J' d :=
  ⟨(transportTable S.1.1 s t,s S.1.2),(source_branch_iso_iff (transportIso S.1.1 s t) S.1.2 d).mpr S.2⟩

noncomputable def transportSinkObject (S : SinkObject I J d) (s : I ≃ I') (t : J ≃ J') :
    SinkObject I' J' d :=
  ⟨(transportTable S.1.1 s t,t S.1.2),(sink_branch_iso_iff (transportIso S.1.1 s t) S.1.2 d).mpr S.2⟩

theorem source_transport_inverse (S : SourceObject I J d) (s : I ≃ I') (t : J ≃ J') :
    transportSourceObject (transportSourceObject S s t) s.symm t.symm=S := by
  apply Subtype.ext
  apply Prod.ext
  · exact transport_table_roundtrip S.1.1 s t
  · exact s.symm_apply_apply S.1.2

theorem sink_transport_inverse (S : SinkObject I J d) (s : I ≃ I') (t : J ≃ J') :
    transportSinkObject (transportSinkObject S s t) s.symm t.symm=S := by
  apply Subtype.ext
  apply Prod.ext
  · exact transport_table_roundtrip S.1.1 s t
  · exact t.symm_apply_apply S.1.2

noncomputable def sourceObjectEquiv (s : I ≃ I') (t : J ≃ J') :
    SourceObject I J d ≃ SourceObject I' J' d where
  toFun S := transportSourceObject S s t
  invFun S := transportSourceObject S s.symm t.symm
  left_inv S := source_transport_inverse S s t
  right_inv S := source_transport_inverse S s.symm t.symm

noncomputable def sinkObjectEquiv (s : I ≃ I') (t : J ≃ J') :
    SinkObject I J d ≃ SinkObject I' J' d where
  toFun S := transportSinkObject S s t
  invFun S := transportSinkObject S s.symm t.symm
  left_inv S := sink_transport_inverse S s t
  right_inv S := sink_transport_inverse S s.symm t.symm

end KroneckerBranchObjectTransport
