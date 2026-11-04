import KroneckerCanonicalPublishedEuler
import KroneckerEulerFramePositivity

/-! A named, unconstructed source-application obligation for actual Euler.
The existing Literature fields are source results, but their identification
with these actual moduli remains C01; this file does not assume a frame identity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerActualFrameApplication
open KroneckerPublishedModuli KroneckerCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerEulerObservables
open KroneckerWordCounts KroneckerFrameBadDensity

def Application (G : Geometry) :=
  ∀ p : Parameters, Literature p (euler (family G) p.m p.a p.b)

theorem finite_coloring_identity (G : Geometry) (A : Application G) (p : Parameters) :
    (Nat.card {g : KroneckerColoring.Coloring p.m (frameLength p) //
      KroneckerStack.Connected p.m (KroneckerColoring.word (frameShape p) g) 0} : ℤ) =
      (p.m : ℤ)*euler (family G) p.m p.a p.b :=
  finite_frame_identity p _ (A p)

theorem literal_identity (G : Geometry) (A : Application G) (p : Parameters) :
    (runCount p.m (frameWord p.a p.b p.d₁) 0 : ℤ) =
      (p.m : ℤ)*euler (family G) p.m p.a p.b :=
  KroneckerConditionalEulerLower.literal_frame_identity p _ (A p)

theorem euler_nonnegative (G : Geometry) (A : Application G) (p : Parameters) :
    0 ≤ euler (family G) p.m p.a p.b := by
  have h := literal_identity G A p
  have hm : (0 : ℤ) < p.m := by exact_mod_cast (show 0 < p.m by have := p.hm; omega)
  have hn : (0 : ℤ) ≤ runCount p.m (frameWord p.a p.b p.d₁) 0 := by exact_mod_cast Nat.zero_le _
  nlinarith

theorem euler_toNat (G : Geometry) (A : Application G) (p : Parameters) :
    ((euler (family G) p.m p.a p.b).toNat : ℤ) = euler (family G) p.m p.a p.b :=
  Int.toNat_of_nonneg (euler_nonnegative G A p)

def point (G : Geometry) (A : Application G) (p : Parameters) : EulerPoint p.m where
  P := p
  E := (euler (family G) p.m p.a p.b).toNat
  hmP := rfl
  source := by rw [euler_toNat G A p]; exact A p

theorem point_height (G : Geometry) (A : Application G) (p : Parameters) :
    KroneckerEulerObservables.height (point G A p) = p.a := rfl

theorem point_slope (G : Geometry) (A : Application G) (p : Parameters) :
    KroneckerEulerObservables.slope (point G A p) = (p.b : ℝ)/p.a := rfl

theorem point_value (G : Geometry) (A : Application G) (p : Parameters) :
    KroneckerEulerObservables.value (point G A p) =
      Real.log (euler (family G) p.m p.a p.b : ℝ)/(p.a : ℝ) := by
  have h : ((euler (family G) p.m p.a p.b).toNat : ℝ) =
      (euler (family G) p.m p.a p.b : ℝ) := by exact_mod_cast euler_toNat G A p
  exact congrArg (fun z : ℝ => Real.log z/(p.a : ℝ)) h

theorem natural_identity (G : Geometry) (A : Application G) (p : Parameters) :
    runCount p.m (frameWord p.a p.b p.d₁) 0 = p.m*(euler (family G) p.m p.a p.b).toNat :=
  KroneckerEulerObservables.point_dictionary p.m (point G A p)

theorem euler_positive_of_legal (G : Geometry) (A : Application G) (p : Parameters)
    (hl : ∀ r ∈ frameWord p.a p.b p.d₁, 1 ≤ r ∧ r ≤ p.m-1) :
    0 < euler (family G) p.m p.a p.b := by
  have h := KroneckerEulerFramePositivity.euler_positive_of_alphabet p.m p.hm (point G A p) hl
  have hz := euler_toNat G A p
  change 0 < (euler (family G) p.m p.a p.b).toNat at h
  omega

end KroneckerActualFrameApplication
