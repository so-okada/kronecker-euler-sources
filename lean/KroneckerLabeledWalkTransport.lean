import KroneckerIteratedFiniteSupportForest

set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A W B : Type} {s t : A → V} {s' t' : B → W}

def castEndpoints {u v u' v' : V} (hu : u = u') (hv : v = v')
    (p : LabeledWalk s t u v) : LabeledWalk s t u' v' := hu ▸ hv ▸ p

@[simp] theorem labels_castEndpoints {u v u' v' : V} (hu : u = u') (hv : v = v')
    (p : LabeledWalk s t u v) : labels (castEndpoints hu hv p) = labels p := by
  subst u'; subst v'; rfl

/-- Actual functorial transport of typed walks along a quiver map. -/
noncomputable def transport (f : V → W) (a : A → B)
    (hs : ∀e, s' (a e) = f (s e)) (ht : ∀e, t' (a e) = f (t e))
    {u v : V} (p : LabeledWalk s t u v) : LabeledWalk s' t' (f u) (f v) := by
  induction p with
  | nil w => exact .nil (f w)
  | @forward e w p ih =>
    exact castEndpoints (hs e) rfl (.forward (a e) (castEndpoints (ht e).symm rfl ih))
  | @backward e w p ih =>
    exact castEndpoints (ht e) rfl (.backward (a e) (castEndpoints (hs e).symm rfl ih))

theorem transport_labels (f : V → W) (a : A → B)
    (hs : ∀e, s' (a e) = f (s e)) (ht : ∀e, t' (a e) = f (t e))
    {u v : V} (p : LabeledWalk s t u v) :
    labels (transport f a hs ht p) = (labels p).map (fun x => (a x.1,x.2)) := by
  induction p with
  | nil => rfl
  | forward e p ih => simpa [transport,labels] using congrArg (List.cons (a e,true)) ih
  | backward e p ih => simpa [transport,labels] using congrArg (List.cons (a e,false)) ih

theorem transport_reduced_iff (f : V → W) (a : A → B) (ha : Function.Injective a)
    (hs : ∀e, s' (a e) = f (s e)) (ht : ∀e, t' (a e) = f (t e))
    {u v : V} (p : LabeledWalk s t u v) :
    Reduced (transport f a hs ht p) ↔ Reduced p := by
  simp only [Reduced,transport_labels,List.isChain_map]
  have hrel : (fun x y : A × Bool => a x.1 ≠ a y.1 ∨ x.2 = y.2) =
      (fun x y => x.1 ≠ y.1 ∨ x.2 = y.2) := by
    funext x y
    apply propext
    exact or_congr (not_congr ha.eq_iff) Iff.rfl
  rw [hrel]

end LabeledWalk
end KroneckerAbelianCover
