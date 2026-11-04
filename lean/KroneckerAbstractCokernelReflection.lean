import KroneckerReflectionKernelDescent

section

/-! Outgoing coordinate maps commute with representation morphisms. Their
ranges are preserved by the diagonal sink map, enabling the inverse cokernel functor. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractOutgoingNaturality
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def outgoing (R : Rep m V W) : V →ₗ[ℂ] (Fin m → W) := LinearMap.pi R

theorem naturality {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) (x : V) :
    diagonal f.sink (outgoing R x)=outgoing S (f.source x) := by
  funext i
  exact f.commutes i x

theorem range_preserved {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S)
    {x : Fin m → W} (hx : x∈LinearMap.range (outgoing R)) :
    diagonal f.sink x∈LinearMap.range (outgoing S) := by
  obtain ⟨y,rfl⟩ := hx
  exact ⟨f.source y,(naturality f y).symm⟩
end KroneckerAbstractOutgoingNaturality
end
end

section

/-! Inverse source reflection on actual representations and morphisms:
quotient the outgoing coordinate space by the outgoing image. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractCokernelReflection
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

abbrev Cokernel (R : Rep m V W) := (Fin m → W) ⧸ LinearMap.range (outgoing R)

def quotient (R : Rep m V W) : (Fin m → W) →ₗ[ℂ] Cokernel R := (LinearMap.range (outgoing R)).mkQ

def reflection (R : Rep m V W) : Rep m W (Cokernel R) :=
  fun i => (quotient R).comp (LinearMap.single ℂ (fun _ : Fin m => W) i)

def cokernelMap {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) : Cokernel R →ₗ[ℂ] Cokernel S :=
  (LinearMap.range (outgoing R)).mapQ (LinearMap.range (outgoing S)) (diagonal f.sink)
    (fun _ hx => range_preserved f hx)

theorem cokernelMap_mk {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) (x : Fin m → W) :
    cokernelMap f (quotient R x)=quotient S (diagonal f.sink x) := rfl

def map {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) : Hom (reflection R) (reflection S) where
  source := f.sink
  sink := cokernelMap f
  commutes i x := by
    change cokernelMap f (quotient R (Pi.single i x))=quotient S (Pi.single i (f.sink x))
    rw [cokernelMap_mk,KroneckerReflectionKernelDescent.diagonal_single]
end KroneckerAbstractCokernelReflection
end
end

