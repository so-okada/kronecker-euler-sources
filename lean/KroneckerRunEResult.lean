import KroneckerManuscriptRunEditList

/-! Definition 4.1(3): RunEResult(Ω,U) is the final path of the run-edit list.
Lean infers U from Ω. The indexed constructors record each operation's source
and target, so the result is the target index, not an arbitrary supplied path. -/
set_option autoImplicit false
namespace KroneckerPaperPaths

def RunEResult {U V : TNEPath} {n : ℕ} (_Ω : RunEditList U V n) : TNEPath := V

@[simp] theorem RunEResult_nil {U : TNEPath} (hU : IsRun U) :
    RunEResult (RunEditList.nil hU) = U := rfl

@[simp] theorem RunEResult_snoc {U V W : TNEPath} {n : ℕ}
    (Ω : RunEditList U V n) (ω : RunEdit V W) :
    RunEResult (RunEditList.snoc Ω ω) = W := rfl

@[simp] theorem RunEResult_append {U V W : TNEPath} {n k : ℕ}
    (Ω : RunEditList U V n) (Λ : RunEditList V W k) :
    RunEResult (Ω.append Λ) = RunEResult Λ := rfl

#print axioms RunEResult
#print axioms RunEResult_nil
#print axioms RunEResult_snoc
#print axioms RunEResult_append
end KroneckerPaperPaths
