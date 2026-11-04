import KroneckerMechanicalWordSums

set_option autoImplicit false
namespace KroneckerMechanicalPrefixSublist
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem mechanical_prefix_sublist (s u : ℝ) (i n k : ℕ) (h : n ≤ k) :
    (mechanicalWord s u i n).Sublist (mechanicalWord s u i k) := by
  have hk : k = n + (k-n) := by omega
  rw [hk, mechanicalWord_append]
  exact List.sublist_append_left _ _

end KroneckerMechanicalPrefixSublist
