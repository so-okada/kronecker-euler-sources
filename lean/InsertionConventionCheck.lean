import KroneckerGeometricRunEdits
import KroneckerPaperPathGradings

set_option autoImplicit false

namespace KroneckerPaperPaths

abbrev CRot := rotateRuns

/-- Exchange at the edge position given by the prefix length. -/
def Exc (U : TNEPath) (k : ℕ) (A B : TNEPath) : TNEPath :=
  ofSteps (U.steps.take k ++ B.steps ++ A.steps ++
    U.steps.drop (k + A.steps.length + B.steps.length)) U.origin

theorem Exc_formula (U A B : TNEPath) (pre suffix : List Bool)
    (h : U.steps = pre ++ A.steps ++ B.steps ++ suffix) :
    Exc U pre.length A B =
      translate (ofSteps (pre ++ B.steps ++ A.steps ++ suffix) 0) U.origin := by
  rw [ofSteps_translate, zero_add]
  simp [Exc, h, List.append_assoc, Nat.add_assoc,
    List.drop_length_add_append]

theorem Exc_origin (U A B : TNEPath) (pre suffix : List Bool)
    (h : U.steps = pre ++ A.steps ++ B.steps ++ suffix) (hA : A.steps ≠ []) :
    (Exc U pre.length A B).origin = U.origin := by
  rw [Exc_formula U A B pre suffix h, ofSteps_translate, zero_add]
  apply ofSteps_origin_of_ne_nil
  simp [List.append_eq_nil_iff, hA]

/-- The exchange formula with the manuscript's prefix length argument. -/
theorem Exc_length (U L A B : TNEPath) (suffix : List Bool)
    (h : U.steps = L.steps ++ A.steps ++ B.steps ++ suffix) :
    Exc U L.steps.length A B =
      translate (ofSteps (L.steps ++ B.steps ++ A.steps ++ suffix) 0) U.origin := by
  exact Exc_formula U A B L.steps suffix h

/-- An empty prefix has length zero. -/
theorem Exc_empty_prefix (U A B : TNEPath) (suffix : List Bool)
    (h : U.steps = A.steps ++ B.steps ++ suffix) :
    Exc U 0 A B =
      translate (ofSteps (B.steps ++ A.steps ++ suffix) 0) U.origin := by
  simpa using Exc_formula U A B [] suffix (by simpa using h)


theorem path_from_steps (P : TNEPath) :
    translate (ofSteps P.steps 0) P.origin = P := by
  rw [ofSteps_translate, zero_add, ofSteps_self]

theorem insert_zero_concat (U V : TNEPath) : insert U 0 V = concat V U := by
  apply TNEPath.ext
  · simp [insert_steps, concat_steps]
  · by_cases hU : U.steps = [] <;> by_cases hV : V.steps = [] <;>
      simp [insert, concat, ofSteps, hU, hV]

theorem insert_zero_origin (U V : TNEPath) (hV : V.steps ≠ []) :
    (insert U 0 V).origin = V.origin := by
  rw [insert_zero_concat, concat_origin V U hV]

theorem insert_positive_origin (U V : TNEPath) (i : ℕ)
    (hU : U.steps ≠ []) (hi : 0 < i) : (insert U i V).origin = U.origin := by
  have hs := insert_nonempty U V i hU
  rw [insert_steps] at hs
  change (ofSteps _ _).origin = _
  rw [ofSteps_origin_of_ne_nil _ _ hs]
  simp [hU, Nat.ne_of_gt hi]

theorem insert_empty_path (V : TNEPath) : insert empty 0 V = V := insert_empty V

/-- Recentring the direct insertion gives the origin-preserving convention. -/
theorem insert_recenter (U V : TNEPath) (i : ℕ) :
    translate (insert U i V) (U.origin - (insert U i V).origin) =
      ofSteps (U.steps.take i ++ V.steps ++ U.steps.drop i) U.origin := by
  rw [translate_to_origin]
  rfl

theorem insertion_count_recenter (m d : ℕ) (U V : TNEPath) (i : ℕ) :
    KroneckerPaperPathGradings.connectedCount m (insert U i V) d =
      KroneckerPaperPathGradings.connectedCount m
        (ofSteps (U.steps.take i ++ V.steps ++ U.steps.drop i) U.origin) d := by
  rw [← insert_recenter U V i]
  exact KroneckerPaperPathGradings.connectedCount_translate _ _ _ _

end KroneckerPaperPaths

#print axioms KroneckerPaperPaths.insert_paper_formula
#print axioms KroneckerPaperPaths.path_from_steps
#print axioms KroneckerPaperPaths.insert_zero_concat
#print axioms KroneckerPaperPaths.insert_zero_origin
#print axioms KroneckerPaperPaths.insert_positive_origin
#print axioms KroneckerPaperPaths.insert_empty_path
#print axioms KroneckerPaperPaths.insert_recenter
#print axioms KroneckerPaperPaths.insertion_count_recenter
#print axioms KroneckerPaperPaths.rotateRuns_cut
#print axioms KroneckerPaperPaths.exchangeRuns_adjacent

#print axioms KroneckerPaperPaths.Exc_formula
#print axioms KroneckerPaperPaths.Exc_origin
#print axioms KroneckerPaperPaths.Exc_length
#print axioms KroneckerPaperPaths.Exc_empty_prefix
