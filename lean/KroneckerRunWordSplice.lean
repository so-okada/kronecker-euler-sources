import KroneckerFullComposition

/-! A complete-run insertion at a run boundary has exactly the expected run word. -/
set_option autoImplicit false
namespace KroneckerRunWordSplice
open KroneckerStack KroneckerWordCounts KroneckerListSplice KroneckerCompleteRunPalette

theorem splice_boundary {α : Type*} (pre post block : List α) :
    splice pre.length block (pre++post)=pre++block++post := by
  simp [splice]

theorem complete_runWord (pre post : List ℕ) (r : ℕ) :
    completePath r (runWord pre).length (runWord (pre++post))=runWord (pre++r::post) := by
  simpa only [completePath,runWord,List.flatMap_append,List.flatMap_cons,List.append_assoc] using
    splice_boundary (runWord pre) (runWord post) (runShape r)

end KroneckerRunWordSplice
