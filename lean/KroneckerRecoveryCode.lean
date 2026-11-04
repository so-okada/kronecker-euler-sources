import KroneckerFiberBudget
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import KroneckerWeights

/- Original module: KroneckerDecrementSlack -/
section
/-! Total decrements are weak compositions with a slack coordinate. -/
set_option autoImplicit false
namespace KroneckerDecrementSlack
open scoped BigOperators

abbrev Decrements (n D : ℕ) := {d : Fin n → ℕ // ∑ i,d i ≤ D}
abbrev ExactDecrements (n D : ℕ) := {d : Fin n → ℕ // ∑ i,d i = D}

def addSlack {n D : ℕ} (d : Decrements n D) : ExactDecrements (n+1) D :=
  ⟨Fin.cons (D-∑ i,d.val i) d.val,by simp only [Fin.sum_cons]; omega⟩

def removeSlack {n D : ℕ} (d : ExactDecrements (n+1) D) : Decrements n D :=
  ⟨Fin.tail d.val,by
    have h := d.property
    rw [Fin.sum_univ_succ] at h
    change (∑ i : Fin n,d.val i.succ) ≤ D
    omega⟩

theorem remove_addSlack {n D : ℕ} (d : Decrements n D) :
    removeSlack (addSlack d)=d := by
  apply Subtype.ext
  funext i
  simp [removeSlack,addSlack]

theorem add_removeSlack {n D : ℕ} (d : ExactDecrements (n+1) D) :
    addSlack (removeSlack d)=d := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := d.property
    rw [Fin.sum_univ_succ] at h
    change D-(∑ j : Fin n,d.val j.succ)=d.val 0
    omega
  · simp [removeSlack,addSlack,Fin.tail]

end KroneckerDecrementSlack
end

/- Original module: KroneckerDecrementCardinality -/
section
/-! Stars and bars counts the full decrement budget, including unused allowance. -/
set_option autoImplicit false
namespace KroneckerDecrementCardinality
open KroneckerDecrementSlack

def slackEquiv (n D : ℕ) : Decrements n D ≃ ExactDecrements (n+1) D where
  toFun := addSlack
  invFun := removeSlack
  left_inv := remove_addSlack
  right_inv := add_removeSlack

noncomputable instance exactFintype (n D : ℕ) : Fintype (ExactDecrements n D) :=
  Fintype.ofEquiv (Sym (Fin n) D) (Sym.equivNatSumOfFintype (Fin n) D)

noncomputable instance decrementFintype (n D : ℕ) : Fintype (Decrements n D) :=
  Fintype.ofEquiv (ExactDecrements (n+1) D) (slackEquiv n D).symm

theorem exact_card (n D : ℕ) :
    Fintype.card (ExactDecrements n D)=(n+D-1).choose D := by
  rw [← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin n) D)]
  simp [Sym.card_sym_eq_choose]

theorem decrements_card (n D : ℕ) :
    Fintype.card (Decrements n D)=(n+D).choose D := by
  rw [Fintype.card_congr (slackEquiv n D),exact_card]
  congr 1
  omega

end KroneckerDecrementCardinality
end

/- Original module: KroneckerDecrementSupport -/
section
/-! At most D original horizontal entries can have a positive decrement. -/
set_option autoImplicit false
namespace KroneckerDecrementSupport
open KroneckerDecrementSlack
open scoped BigOperators

def support {n : ℕ} (d : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < d i)

theorem mem_support {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    i ∈ support d ↔ 0 < d i := by
  simp [support]

theorem support_card_le_sum {n : ℕ} (d : Fin n → ℕ) :
    (support d).card ≤ ∑ i,d i := by
  have h : (∑ i : Fin n,if 0 < d i then 1 else 0) ≤ ∑ i,d i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  simpa [support] using h

theorem support_card_le {n D : ℕ} (d : Decrements n D) :
    Fintype.card {i // i ∈ support d.val} ≤ D := by
  simpa using (support_card_le_sum d.val).trans d.property

end KroneckerDecrementSupport
end

/- Original module: KroneckerFinitePaletteSlots -/
section
/-! A palette assignment on at most D positions fits injectively into D fixed slots. -/
set_option autoImplicit false
namespace KroneckerFinitePaletteSlots
open KroneckerColoring

noncomputable def slotIndex {α : Type*} [Fintype α] {D : ℕ}
    (h : Fintype.card α ≤ D) (a : α) : Fin D :=
  ⟨(Fintype.equivFin α a).val,lt_of_lt_of_le (Fintype.equivFin α a).isLt h⟩

theorem slotIndex_injective {α : Type*} [Fintype α] {D : ℕ}
    (h : Fintype.card α ≤ D) : Function.Injective (slotIndex h) := by
  intro a b hab
  apply (Fintype.equivFin α).injective
  apply Fin.ext
  exact congrArg (fun x : Fin D => x.val) hab

noncomputable def pack {α : Type*} [Fintype α] {m D : ℕ}
    (h : Fintype.card α ≤ D) (g : α → Palette m) : Coloring m D :=
  Function.extend (slotIndex h) g (fun _ => zeroColor m)

theorem pack_read {α : Type*} [Fintype α] {m D : ℕ}
    (h : Fintype.card α ≤ D) (g : α → Palette m) (a : α) :
    pack h g (slotIndex h a)=g a :=
  (slotIndex_injective h).extend_apply g (fun _ => zeroColor m) a

theorem pack_injective {α : Type*} [Fintype α] {m D : ℕ}
    (h : Fintype.card α ≤ D) : Function.Injective (pack (m:=m) h) := by
  intro f g hfg
  funext a
  have h := congrFun hfg (slotIndex h a)
  simpa only [pack_read] using h

end KroneckerFinitePaletteSlots
end

/- Original module: KroneckerSparsePaletteRecovery -/
section
/-! Sparse old palette entries plus the retained output recover the complete original array. -/
set_option autoImplicit false
namespace KroneckerSparsePaletteRecovery
open KroneckerColoring KroneckerFinitePaletteSlots

noncomputable def record {α : Type*} [DecidableEq α] {m D : ℕ}
    (s : Finset α) (hs : s.card ≤ D) (g : α → Palette m) : Coloring m D :=
  pack (by simpa using hs) (fun i : {i // i ∈ s} => g i.val)

noncomputable def restore {α : Type*} [DecidableEq α] {m D : ℕ}
    (s : Finset α) (hs : s.card ≤ D) (base : α → Palette m)
    (code : Coloring m D) : α → Palette m :=
  fun i => if hi : i ∈ s then code (slotIndex (α:={i // i ∈ s}) (by simpa using hs) ⟨i,hi⟩) else base i

theorem record_read {α : Type*} [DecidableEq α] {m D : ℕ}
    (s : Finset α) (hs : s.card ≤ D) (g : α → Palette m) (i : α) (hi : i ∈ s) :
    record s hs g (slotIndex (α:={i // i ∈ s}) (by simpa using hs) ⟨i,hi⟩)=g i := by
  exact pack_read (by simpa using hs) (fun j : {j // j ∈ s} => g j.val) ⟨i,hi⟩

theorem restore_record {α : Type*} [DecidableEq α] {m D : ℕ}
    (s : Finset α) (hs : s.card ≤ D) (g base : α → Palette m)
    (hbase : ∀ i,i ∉ s → base i=g i) :
    restore s hs base (record s hs g)=g := by
  funext i
  by_cases hi : i ∈ s
  · simp only [restore,dite_eq_left hi,record_read]
  · simp only [restore,dite_eq_right hi,hbase i hi]

end KroneckerSparsePaletteRecovery
end

/- Original module: KroneckerHorizontalRecovery -/
section
/-! Total positive decrements select the only original horizontal palettes needing a record. -/
set_option autoImplicit false
namespace KroneckerHorizontalRecovery
open KroneckerColoring KroneckerDecrementSlack KroneckerDecrementSupport
open KroneckerSparsePaletteRecovery

noncomputable def recordHorizontal {m n D : ℕ} (d : Decrements n D)
    (g : Coloring m n) : Coloring m D :=
  record (support d.val) ((support_card_le_sum d.val).trans d.property) g

noncomputable def restoreHorizontal {m n D : ℕ} (d : Decrements n D)
    (base : Coloring m n) (code : Coloring m D) : Coloring m n :=
  restore (support d.val) ((support_card_le_sum d.val).trans d.property) base code

theorem horizontal_recovery {m n D : ℕ} (d : Decrements n D) (g base : Coloring m n)
    (hzero : ∀ i,d.val i=0 → base i=g i) :
    restoreHorizontal d base (recordHorizontal d g)=g := by
  apply restore_record
  intro i hi
  apply hzero i
  have h : ¬0 < d.val i := by simpa only [mem_support] using hi
  omega

theorem horizontal_record_eq {m n D : ℕ} (d : Decrements n D) (g h base : Coloring m n)
    (hg : ∀ i,d.val i=0 → base i=g i) (hh : ∀ i,d.val i=0 → base i=h i)
    (he : recordHorizontal d g=recordHorizontal d h) : g=h := by
  rw [← horizontal_recovery d g base hg,← horizontal_recovery d h base hh,he]

end KroneckerHorizontalRecovery
end

/- Original module: KroneckerRecoveryCode -/
section
/-! The exact finite code alphabet behind the manuscript's binomial/color budget. -/
set_option autoImplicit false
namespace KroneckerRecoveryCode
open KroneckerColoring KroneckerWeights KroneckerDecrementSlack KroneckerDecrementCardinality
open KroneckerFiberBudget

abbrev RecoveryCode (m n D : ℕ) := Decrements n D × Coloring m D × Coloring m D

theorem recoveryCode_card (m n D : ℕ) :
    Fintype.card (RecoveryCode m n D)=fiberBudget m n D := by
  simp only [RecoveryCode,Fintype.card_prod,decrements_card,coloring_card,fiberBudget]
  rw [← pow_add,← pow_mul]
  congr 2
  ring

theorem recoveryCode_zero_card (m n : ℕ) : Fintype.card (RecoveryCode m n 0)=1 := by
  rw [recoveryCode_card,fiberBudget_zero]

end KroneckerRecoveryCode
end
