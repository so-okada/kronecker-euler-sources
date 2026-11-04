import KroneckerDirectSumCoverEmbeddingLift
import KroneckerDirectSumIteratedGirth

/-! Every iterated direct-sum cover embeds in the corresponding product model.
The recursion respects the actual preceding-stage arrow injection; it does not
confuse the infinitely many old arrow coordinates with original arrow colors. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumIteratedEmbedding
open KroneckerAbelianCover
open KroneckerTypedQuiverMaps KroneckerDirectSumCoverEmbeddingLift
open KroneckerDirectSumIteratedGirth
attribute [local instance] Classical.decEq Classical.propDecidable

def embedding (Q : TypedQuiver) : (n : ℕ) → QuiverMap (iterate Q n) (Q.iterate n)
  | 0 => QuiverMap.identity Q
  | n+1 => liftMap (embedding Q n)

theorem embedding_injective (Q : TypedQuiver) (n : ℕ) :
    Function.Injective (embedding Q n).vertex ∧ Function.Injective (embedding Q n).arrow := by
  induction n with
  | zero => exact ⟨Function.injective_id,Function.injective_id⟩
  | succ n ih => exact ⟨lift_vertex_injective _ ih.1 ih.2,lift_arrow_injective _ ih.2⟩

def baseVertex (Q : TypedQuiver) : (n : ℕ) → (iterate Q n).V → Q.V
  | 0,v => v
  | n+1,v => baseVertex Q n v.1

def baseArrow (Q : TypedQuiver) : (n : ℕ) → (iterate Q n).A → Q.A
  | 0,a => a
  | n+1,a => baseArrow Q n a.1

theorem embedding_base_vertex (Q : TypedQuiver) (n : ℕ) (v : (iterate Q n).V) :
    TypedQuiver.baseVertex Q n ((embedding Q n).vertex v) = baseVertex Q n v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih v.1

theorem embedding_base_arrow (Q : TypedQuiver) (n : ℕ) (a : (iterate Q n).A) :
    TypedQuiver.baseArrow Q n ((embedding Q n).arrow a) = baseArrow Q n a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1

end KroneckerDirectSumIteratedEmbedding
