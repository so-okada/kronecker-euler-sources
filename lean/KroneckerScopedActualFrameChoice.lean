import KroneckerActualFrameApplication
import KroneckerScopedActualFrameApplication

/- Original module: KroneckerActualFrameChoice -/
section
/-! Construct the finite-frame parameters from actual primitive dimensions.
No source-bearing restriction is added to the actual moduli domain. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerActualFrameChoice
open KroneckerPublishedModuli KroneckerCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerActualFrameApplication

structure Input (m : ℕ) where
  a : ℕ
  b : ℕ
  height : 2 ≤ a
  increasing : a < b
  primitive : a.Coprime b

def parameters (m : ℕ) (hm : 3 ≤ m) (x : Input m) : Parameters :=
  Classical.choose (parameters_exist m x.a x.b hm x.height x.increasing x.primitive)

theorem parameters_spec (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    (parameters m hm x).m = m ∧ (parameters m hm x).a = x.a ∧
    (parameters m hm x).b = x.b := by
  have h := Classical.choose_spec (parameters_exist m x.a x.b hm x.height x.increasing x.primitive)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

def toEuler (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.EulerPoint m where
  P := parameters m hm x
  E := (euler (family G) m x.a x.b).toNat
  hmP := (parameters_spec m hm x).1
  source := by
    have h := (point G A (parameters m hm x)).source
    change Literature (parameters m hm x)
      ((euler (family G) (parameters m hm x).m (parameters m hm x).a
        (parameters m hm x).b).toNat : ℤ) at h
    simpa only [(parameters_spec m hm x).1, (parameters_spec m hm x).2.1,
      (parameters_spec m hm x).2.2] using h

theorem toEuler_height (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.height (toEuler G A m hm x) = x.a := (parameters_spec m hm x).2.1

theorem toEuler_slope (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.slope (toEuler G A m hm x) = (x.b : ℝ)/x.a := by
  dsimp [KroneckerEulerObservables.slope, toEuler]
  rw [(parameters_spec m hm x).2.1, (parameters_spec m hm x).2.2]

theorem input_euler_nonnegative (G : Geometry) (A : Application G)
    (m : ℕ) (hm : 3 ≤ m) (x : Input m) : 0 ≤ euler (family G) m x.a x.b := by
  have h := euler_nonnegative G A (parameters m hm x)
  simpa only [(parameters_spec m hm x).1, (parameters_spec m hm x).2.1,
    (parameters_spec m hm x).2.2] using h

theorem toEuler_value (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.value (toEuler G A m hm x) =
      Real.log (euler (family G) m x.a x.b : ℝ)/(x.a : ℝ) := by
  have h : ((euler (family G) m x.a x.b).toNat : ℝ) = (euler (family G) m x.a x.b : ℝ) :=
    by exact_mod_cast Int.toNat_of_nonneg (input_euler_nonnegative G A m hm x)
  dsimp [KroneckerEulerObservables.value, toEuler]
  rw [h, (parameters_spec m hm x).2.1]

end KroneckerActualFrameChoice
end
end

/- Original module: KroneckerScopedActualFrameChoice -/
section
/-! Construct the finite-frame parameters from actual primitive dimensions.
No source-bearing restriction is added to the actual moduli domain. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualFrameChoice
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerScopedActualFrameApplication

export KroneckerActualFrameChoice (Input parameters parameters_spec)

def toEuler (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.EulerPoint m where
  P := parameters m hm x
  E := (euler (family G) m x.a x.b).toNat
  hmP := (parameters_spec m hm x).1
  source := by
    have h := (point G A (parameters m hm x)).source
    change Literature (parameters m hm x)
      ((euler (family G) (parameters m hm x).m (parameters m hm x).a
        (parameters m hm x).b).toNat : ℤ) at h
    simpa only [(parameters_spec m hm x).1, (parameters_spec m hm x).2.1,
      (parameters_spec m hm x).2.2] using h

theorem toEuler_height (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.height (toEuler G A m hm x) = x.a := (parameters_spec m hm x).2.1

theorem toEuler_slope (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.slope (toEuler G A m hm x) = (x.b : ℝ)/x.a := by
  dsimp [KroneckerEulerObservables.slope, toEuler]
  rw [(parameters_spec m hm x).2.1, (parameters_spec m hm x).2.2]

theorem input_euler_nonnegative (G : Geometry) (A : Application G)
    (m : ℕ) (hm : 3 ≤ m) (x : Input m) : 0 ≤ euler (family G) m x.a x.b := by
  have h := euler_nonnegative G A (parameters m hm x)
  simpa only [(parameters_spec m hm x).1, (parameters_spec m hm x).2.1,
    (parameters_spec m hm x).2.2] using h

theorem toEuler_value (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    KroneckerEulerObservables.value (toEuler G A m hm x) =
      Real.log (euler (family G) m x.a x.b : ℝ)/(x.a : ℝ) := by
  have h : ((euler (family G) m x.a x.b).toNat : ℝ) = (euler (family G) m x.a x.b : ℝ) :=
    by exact_mod_cast Int.toNat_of_nonneg (input_euler_nonnegative G A m hm x)
  dsimp [KroneckerEulerObservables.value, toEuler]
  rw [h, (parameters_spec m hm x).2.1]

end KroneckerScopedActualFrameChoice
end
end
