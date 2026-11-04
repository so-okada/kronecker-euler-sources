import KroneckerRecoveryCode

/-! Joint reconstruction of original horizontal and vertical palettes. -/
set_option autoImplicit false
namespace KroneckerInputRecovery
open KroneckerColoring KroneckerDecrementSlack KroneckerRecoveryCode
open KroneckerHorizontalRecovery KroneckerSparsePaletteRecovery

abbrev Input (m n q : ℕ) := Coloring m n × Coloring m q

noncomputable def encodeInput {m n q D : ℕ} (d : Decrements n D)
    (deleted : Finset (Fin q)) (hd : deleted.card ≤ D) (g : Input m n q) :
    RecoveryCode m n D :=
  ⟨d,recordHorizontal d g.1,record deleted hd g.2⟩

noncomputable def decodeInput {m n q D : ℕ} (deleted : Finset (Fin q))
    (hd : deleted.card ≤ D) (base : Input m n q) (code : RecoveryCode m n D) : Input m n q :=
  ⟨restoreHorizontal code.1 base.1 code.2.1,restore deleted hd base.2 code.2.2⟩

theorem decode_encodeInput {m n q D : ℕ} (d : Decrements n D)
    (deleted : Finset (Fin q)) (hd : deleted.card ≤ D) (g base : Input m n q)
    (hh : ∀ i,d.val i=0 → base.1 i=g.1 i)
    (hv : ∀ i,i ∉ deleted → base.2 i=g.2 i) :
    decodeInput deleted hd base (encodeInput d deleted hd g)=g := by
  exact Prod.ext (horizontal_recovery d g.1 base.1 hh)
    (restore_record deleted hd g.2 base.2 hv)

end KroneckerInputRecovery
