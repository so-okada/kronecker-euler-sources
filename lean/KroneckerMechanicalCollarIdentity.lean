import KroneckerMechanicalWordSums

set_option autoImplicit false
namespace KroneckerMechanicalCollarIdentity
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem mechanical_collar_identity (s u : ℝ) (P T : ℕ) :
    mechanicalWord s u 0 (P+1+T+1+P) =
      mechanicalWord s u 0 P ++ (natRun s u P :: mechanicalWord s u (P+1) T ++
        [natRun s u (P+1+T)]) ++ mechanicalWord s u (P+1+T+1) P := by
  rw [mechanicalWord_append s u 0 (P+1+T+1) P,
    mechanicalWord_append s u 0 (P+1+T) 1,
    mechanicalWord_append s u 0 (P+1) T,
    mechanicalWord_append s u 0 P 1]
  simp only [Nat.zero_add,mechanicalWord_one,List.append_assoc,List.singleton_append]

end KroneckerMechanicalCollarIdentity
