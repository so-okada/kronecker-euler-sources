import Mathlib.RingTheory.Coprime.Lemmas
import KroneckerTight
import Mathlib.Data.Nat.ModEq

/- Original module: KroneckerFrame -/
section
/-!
The defect-one arithmetic in the finite-frame argument. The finite set of
components and its geometric inequalities are explicit hypotheses here.
Their construction from the maximal Dyck path, and the external enumeration
and Euler-characteristic identifications, are not asserted by these lemmas.
-/
set_option autoImplicit false
namespace KroneckerFrame





/-- The auxiliary dimensions have the required sizes once the modular
inverse has been chosen. Existence of that inverse is a separate step. -/
theorem ambient_sizes {a b t d₁ d₂ : ℤ} (ha : 2≤a) (hb : a<b)
    (ht : 1≤t) (hd₁ : d₁=a+t) (hdet : a*d₂-b*d₁ = -1) :
    a+1≤d₁ ∧ b+1≤d₂ := by
  constructor
  · omega
  · have hmul : b≤b*t := by nlinarith
    have hid : a*(d₂-b)=b*t-1 := by nlinarith [hdet]
    by_contra h
    have hle : d₂≤b := by omega
    have hnonpos : a*(d₂-b)≤0 := mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    nlinarith


theorem defect_one_coprime {a b d₁ d₂ : ℤ} (hdet : b*d₁-a*d₂=1) :
    Int.gcd d₁ d₂=1 := by
  have hdiv : (Int.gcd d₁ d₂ : ℤ) ∣ b*d₁-a*d₂ :=
    dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left d₁ d₂) b)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right d₁ d₂) a)
  rw [hdet] at hdiv
  have hn : Int.gcd d₁ d₂ ∣ 1 := by exact_mod_cast hdiv
  exact Nat.dvd_one.mp hn




theorem inverse_representative {a b : ℕ} (ha : 2≤a) (hc : Nat.Coprime a b) :
    ∃ t : ℤ, 1≤t ∧ t<(a:ℤ) ∧ (a:ℤ) ∣ (b:ℤ)*t-1 := by
  obtain ⟨x,y,hxy⟩ := hc.isCoprime
  let t : ℤ := y % (a:ℤ)
  have ha' : (0:ℤ)<a := by omega
  have ht : 0≤t := Int.emod_nonneg _ (ne_of_gt ha')
  have hlt : t<(a:ℤ) := Int.emod_lt_of_pos _ ha'
  have hdiv : (a:ℤ) ∣ (b:ℤ)*t-1 := by
    refine ⟨-x-(b:ℤ)*(y/(a:ℤ)),?_⟩
    dsimp [t]
    rw [Int.emod_def]
    nlinarith [hxy]
  have hp : 1≤t := by
    by_contra h
    have hz : t=0 := by omega
    have hd : (a:ℤ) ∣ 1 := by simpa [hz] using hdiv
    have hd' : a ∣ 1 := by exact_mod_cast hd
    have := Nat.dvd_one.mp hd'
    omega
  exact ⟨t,hp,hlt,hdiv⟩

theorem ambient_exists {a b : ℕ} (ha : 2≤a) (hb : a<b) (hc : Nat.Coprime a b) :
    ∃ t d₁ d₂ : ℤ, 1≤t ∧ t<(a:ℤ) ∧ d₁=(a:ℤ)+t ∧
      (a:ℤ)*d₂-(b:ℤ)*d₁ = -1 ∧ (a:ℤ)+1≤d₁ ∧ (b:ℤ)+1≤d₂ ∧
      Int.gcd d₁ d₂=1 := by
  obtain ⟨t,ht,hta,k,hk⟩ := inverse_representative ha hc
  let d₁ := (a:ℤ)+t
  let d₂ := (b:ℤ)+k
  have hdet : (a:ℤ)*d₂-(b:ℤ)*d₁ = -1 := by dsimp [d₁,d₂]; nlinarith [hk]
  have hsize := ambient_sizes (by exact_mod_cast ha) (by exact_mod_cast hb) ht rfl hdet
  refine ⟨t,d₁,d₂,ht,hta,rfl,hdet,hsize.1,hsize.2,?_⟩
  exact defect_one_coprime (a:=(a:ℤ)) (b:=(b:ℤ)) (by nlinarith [hdet])

end KroneckerFrame
end

/- Original module: KroneckerDyck -/
section
/-! The maximal Dyck path as its sequence of lattice coordinates.
The coordinate at the i-th edge is i*d₂ modulo d₁+d₂. Horizontal
edges add d₂ and vertical edges subtract d₁. -/
set_option autoImplicit false
namespace KroneckerDyck
open KroneckerColoring

def coord (d₁ d₂ i : ℕ) : ℕ := i*d₂ % (d₁+d₂)
def pathShape (d₁ d₂ : ℕ) (i : ℕ) : Bool := decide (coord d₁ d₂ i<d₁)

theorem coord_bound {d₁ d₂ : ℕ} (hD : 0<d₁+d₂) (i : ℕ) :
    coord d₁ d₂ i<d₁+d₂ := Nat.mod_lt _ hD

theorem coord_step {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (i : ℕ) :
    coord d₁ d₂ (i+1)=
      if coord d₁ d₂ i<d₁ then coord d₁ d₂ i+d₂ else coord d₁ d₂ i-d₁ := by
  have hmod : coord d₁ d₂ (i+1)=(coord d₁ d₂ i+d₂)%(d₁+d₂) := by
    simp [coord,Nat.add_mul,Nat.add_mod]
  rw [hmod]
  have hc := coord_bound (by omega : 0<d₁+d₂) i
  split
  next h => exact Nat.mod_eq_of_lt (by omega)
  next h =>
    rw [Nat.mod_eq_sub_mod (by omega : d₁+d₂≤coord d₁ d₂ i+d₂)]
    have he : coord d₁ d₂ i+d₂-(d₁+d₂)=coord d₁ d₂ i-d₁ := by omega
    rw [he,Nat.mod_eq_of_lt (by omega)]

theorem hedges_succ (shape : ℕ → Bool) (n : ℕ) :
    HEdges shape (n+1)=HEdges shape n+(if shape n then 1 else 0) := by
  simp only [HEdges,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

theorem vedges_succ (shape : ℕ → Bool) (n : ℕ) :
    VEdges shape (n+1)=VEdges shape n+(if shape n then 0 else 1) := by
  simp only [VEdges,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

theorem edge_count_sum (shape : ℕ → Bool) (n : ℕ) :
    HEdges shape n+VEdges shape n=(n:ℤ) := by
  induction n with
  | zero => simp [HEdges,VEdges]
  | succ n ih =>
    rw [hedges_succ,vedges_succ]
    cases shape n <;> simp_all <;> omega

theorem coordinate_identity {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (i : ℕ) :
    (coord d₁ d₂ i:ℤ)=
      HEdges (pathShape d₁ d₂) i*(d₂:ℤ)-VEdges (pathShape d₁ d₂) i*(d₁:ℤ) := by
  induction i with
  | zero => simp [coord,HEdges,VEdges]
  | succ i ih =>
    rw [coord_step h₁ h₂,hedges_succ,vedges_succ]
    by_cases h : coord d₁ d₂ i<d₁
    · simp only [ite_eq_left h,Nat.cast_add,pathShape,decide_eq_true h,ite_true]
      nlinarith
    · have he : ((coord d₁ d₂ i-d₁:ℕ):ℤ)=(coord d₁ d₂ i:ℤ)-(d₁:ℤ) :=
        Nat.cast_sub (by omega)
      simp only [ite_eq_right h,he,pathShape,decide_eq_false h,Bool.false_eq_true,ite_false]
      nlinarith

theorem path_dimensions {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) :
    HEdges (pathShape d₁ d₂) (d₁+d₂)=(d₁:ℤ) ∧
      VEdges (pathShape d₁ d₂) (d₁+d₂)=(d₂:ℤ) := by
  have hc := coordinate_identity h₁ h₂ (d₁+d₂)
  have hs := edge_count_sum (pathShape d₁ d₂) (d₁+d₂)
  simp only [coord,Nat.mul_mod_right,Nat.cast_zero] at hc
  push_cast at hs
  constructor <;> nlinarith

theorem coordinate_injective {d₁ d₂ : ℕ} (hc : Nat.Coprime d₁ d₂)
    {i j : ℕ} (hi : i<d₁+d₂) (hj : j<d₁+d₂)
    (he : coord d₁ d₂ i=coord d₁ d₂ j) : i=j := by
  have hg : Nat.gcd (d₁+d₂) d₂=1 := by simpa using hc
  have hm : Nat.ModEq (d₁+d₂) i j := Nat.ModEq.cancel_right_of_coprime hg he
  simpa [Nat.ModEq,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hm

/-- The last vertical edge of the proposed frame has coordinate d₁+d₂-1. -/
theorem frame_last_coordinate {a b d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    (hdet : (b:ℤ)*d₁-(a:ℤ)*d₂=1) :
    coord d₁ d₂ (a+b)=d₁+d₂-1 := by
  have hi : (a+b)*d₂+1=b*(d₁+d₂) := by exact_mod_cast (by nlinarith [hdet] :
      ((a:ℤ)+b)*d₂+1=(b:ℤ)*(d₁+d₂))
  have hD : 0<d₁+d₂ := by omega
  have hb : 0<b := by nlinarith
  have he : (a+b)*d₂=(b-1)*(d₁+d₂)+(d₁+d₂-1) := by
    have := Nat.sub_add_cancel (by omega : 1≤b)
    have := Nat.sub_add_cancel (by omega : 1≤d₁+d₂)
    nlinarith
  simp [coord,he,Nat.mod_eq_of_lt (by omega : d₁+d₂-1<d₁+d₂)]

theorem frame_edge_counts {a b d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    (hdet : (b:ℤ)*d₁-(a:ℤ)*d₂=1) :
    HEdges (pathShape d₁ d₂) (a+b+1)=(a:ℤ)+1 ∧
      VEdges (pathShape d₁ d₂) (a+b+1)=(b:ℤ) := by
  have hlast := frame_last_coordinate h₁ h₂ hdet
  have hc := coordinate_identity h₁ h₂ (a+b)
  have hs := edge_count_sum (pathShape d₁ d₂) (a+b)
  rw [hlast] at hc
  have hc' : ((d₁+d₂-1:ℕ):ℤ)=(d₁:ℤ)+d₂-1 := by omega
  rw [hc'] at hc
  have hv : pathShape d₁ d₂ (a+b)=false := by
    simp [pathShape,hlast]; omega
  rw [hedges_succ,vedges_succ,hv]
  simp only [Bool.false_eq_true,ite_false,add_zero]
  push_cast at hs
  constructor <;> nlinarith

/-- The j-th horizontal edge starts after j horizontal edges and
floor(j*d₂/d₁) vertical edges. -/
def boundary (d₁ d₂ j : ℕ) : ℕ := j+j*d₂/d₁

theorem boundary_coordinate {d₁ d₂ : ℕ} (h₁ : 0<d₁) (j : ℕ) :
    coord d₁ d₂ (boundary d₁ d₂ j)=j*d₂%d₁ := by
  have hr : j*d₂%d₁<d₁ := Nat.mod_lt _ h₁
  have he : boundary d₁ d₂ j*d₂=(j*d₂/d₁)*(d₁+d₂)+j*d₂%d₁ := by
    have h := Nat.mod_add_div (j*d₂) d₁
    dsimp [boundary]
    nlinarith
  simp [coord,he,Nat.mod_eq_of_lt (by omega : j*d₂%d₁<d₁+d₂)]

theorem boundary_horizontal {d₁ d₂ : ℕ} (h₁ : 0<d₁) (j : ℕ) :
    pathShape d₁ d₂ (boundary d₁ d₂ j)=true := by
  simp only [pathShape,boundary_coordinate h₁]
  exact decide_eq_true (Nat.mod_lt _ h₁)


theorem edge_counts_nonnegative (shape : ℕ → Bool) (i : ℕ) :
    0≤HEdges shape i ∧ 0≤VEdges shape i := by
  constructor
  · unfold HEdges
    apply Finset.sum_nonneg
    intro j _
    split <;> norm_num
  · unfold VEdges
    apply Finset.sum_nonneg
    intro j _
    split <;> norm_num

theorem horizontal_is_boundary {d₁ d₂ i : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    (hh : pathShape d₁ d₂ i=true) :
    i=boundary d₁ d₂ (HEdges (pathShape d₁ d₂) i).toNat := by
  have hc := coordinate_identity h₁ h₂ i
  have hs := edge_count_sum (pathShape d₁ d₂) i
  have hn := edge_counts_nonnegative (pathShape d₁ d₂) i
  let x := (HEdges (pathShape d₁ d₂) i).toNat
  let y := (VEdges (pathShape d₁ d₂) i).toNat
  have hx : (x:ℤ)=HEdges (pathShape d₁ d₂) i := Int.toNat_of_nonneg hn.1
  have hy : (y:ℤ)=VEdges (pathShape d₁ d₂) i := Int.toNat_of_nonneg hn.2
  have he : x*d₂=y*d₁+coord d₁ d₂ i := by
    have : (x:ℤ)*d₂=(y:ℤ)*d₁+(coord d₁ d₂ i:ℤ) := by rw [hx,hy]; omega
    exact_mod_cast this
  have hlt : coord d₁ d₂ i<d₁ := by simpa [pathShape] using hh
  have hdiv : x*d₂/d₁=y := Nat.div_eq_of_lt_le (by omega) (by nlinarith)
  have hsum : x+y=i := by
    have : (x:ℤ)+y=(i:ℤ) := by rw [hx,hy]; exact hs
    exact_mod_cast this
  change i=x+x*d₂/d₁
  rw [hdiv,hsum]

/-- Natural division gives the exact b-1 height of the a-th run boundary. -/
theorem frame_boundary {a b d₁ d₂ : ℕ} (h₁ : 0<d₁)
    (hdet : (b:ℤ)*d₁-(a:ℤ)*d₂=1) :
    a*d₂/d₁=b-1 ∧ boundary d₁ d₂ a=a+b-1 := by
  have hb : 0<b := by nlinarith
  have hprod : a*d₂+1=b*d₁ := by exact_mod_cast (by omega : (a:ℤ)*d₂+1=(b:ℤ)*d₁)
  have hdiv : a*d₂/d₁=b-1 := Nat.div_eq_of_lt_le
    (by have := Nat.sub_add_cancel (by omega : 1≤b); nlinarith)
    (by have := Nat.sub_add_cancel (by omega : 1≤b); nlinarith)
  exact ⟨hdiv,by dsimp [boundary]; rw [hdiv]; omega⟩

theorem hedges_monotone (shape : ℕ → Bool) : Monotone (HEdges shape) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [hedges_succ]
  split <;> omega

theorem boundary_edge_counts {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (j : ℕ) :
    HEdges (pathShape d₁ d₂) (boundary d₁ d₂ j)=(j:ℤ) ∧
      VEdges (pathShape d₁ d₂) (boundary d₁ d₂ j)=(j*d₂/d₁:ℕ) := by
  have hc := coordinate_identity h₁ h₂ (boundary d₁ d₂ j)
  have hs := edge_count_sum (pathShape d₁ d₂) (boundary d₁ d₂ j)
  rw [boundary_coordinate h₁] at hc
  have hd : ((j*d₂%d₁:ℕ):ℤ)+(d₁:ℤ)*(j*d₂/d₁:ℕ)=(j:ℤ)*d₂ := by
    exact_mod_cast Nat.mod_add_div (j*d₂) d₁
  change HEdges (pathShape d₁ d₂) (boundary d₁ d₂ j)+VEdges (pathShape d₁ d₂) (boundary d₁ d₂ j)=(j:ℤ)+(j*d₂/d₁:ℕ) at hs
  constructor <;> nlinarith

theorem between_boundaries_vertical {d₁ d₂ i j : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    (hi : boundary d₁ d₂ j < i) (hj : i < boundary d₁ d₂ (j+1)) :
    pathShape d₁ d₂ i=false := by
  by_contra hh
  have hh' : pathShape d₁ d₂ i=true := by cases h : pathShape d₁ d₂ i <;> simp_all
  have hlow := hedges_monotone (pathShape d₁ d₂) (by omega : boundary d₁ d₂ j+1 ≤ i)
  have hhigh := hedges_monotone (pathShape d₁ d₂) (by omega : i ≤ boundary d₁ d₂ (j+1))
  rw [hedges_succ,boundary_horizontal h₁,(boundary_edge_counts h₁ h₂ j).1] at hlow
  rw [(boundary_edge_counts h₁ h₂ (j+1)).1] at hhigh
  have hcount : HEdges (pathShape d₁ d₂) i=((j+1:ℕ):ℤ) := by
    simp only [ite_true] at hlow
    omega
  have he := horizontal_is_boundary h₁ h₂ hh'
  rw [hcount,Int.toNat_natCast] at he
  omega

def runLength (d₁ d₂ j : ℕ) : ℕ := (j+1)*d₂/d₁-j*d₂/d₁

theorem boundary_succ (d₁ d₂ j : ℕ) :
    boundary d₁ d₂ (j+1)=boundary d₁ d₂ j+1+runLength d₁ d₂ j := by
  have hdiv : j*d₂/d₁≤(j+1)*d₂/d₁ := Nat.div_le_div_right (by nlinarith)
  dsimp [boundary,runLength]
  omega

def shapePrefix (shape : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => shape i.val)

theorem shapePrefix_add (shape : ℕ → Bool) (s n : ℕ) :
    shapePrefix shape (s+n)=shapePrefix shape s++List.ofFn (fun i : Fin n => shape (s+i.val)) := by
  simp [shapePrefix,List.ofFn_add]

theorem path_run {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (j : ℕ) :
    List.ofFn (fun i : Fin (runLength d₁ d₂ j+1) =>
      pathShape d₁ d₂ (boundary d₁ d₂ j+i.val))=
      KroneckerStack.runShape (runLength d₁ d₂ j) := by
  simp only [List.ofFn_succ,Fin.val_zero,Nat.add_zero,boundary_horizontal h₁,
    KroneckerStack.runShape]
  congr 1
  have he : (fun i : Fin (runLength d₁ d₂ j) =>
      pathShape d₁ d₂ (boundary d₁ d₂ j+i.succ.val))=(fun _ => false) := by
    funext i
    apply between_boundaries_vertical (j:=j) h₁ h₂
    · simp
    · rw [boundary_succ]
      have := i.isLt
      simp only [Fin.val_succ]
      omega
  rw [he,List.ofFn_const]

theorem path_runs {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (a : ℕ) :
    shapePrefix (pathShape d₁ d₂) (boundary d₁ d₂ a)=
      (List.range a).flatMap (fun j => KroneckerStack.runShape (runLength d₁ d₂ j)) := by
  induction a with
  | zero => simp [shapePrefix,boundary]
  | succ a ih =>
    rw [boundary_succ,show boundary d₁ d₂ a+1+runLength d₁ d₂ a=
      boundary d₁ d₂ a+(runLength d₁ d₂ a+1) by omega,shapePrefix_add,path_run h₁ h₂,ih]
    simp [List.range_succ,List.flatMap_append]

/-- The prefix is exactly the a mechanical runs followed by R₁. -/
theorem frame_path_word {a b d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    (hdet : (b:ℤ)*d₁-(a:ℤ)*d₂=1) :
    shapePrefix (pathShape d₁ d₂) (a+b+1)=
      (List.range a).flatMap (fun j => KroneckerStack.runShape (runLength d₁ d₂ j))++
        KroneckerStack.runShape 1 := by
  have hboundary := (frame_boundary h₁ hdet).2
  have hb : 0<b := by nlinarith
  have hn : a+b+1=boundary d₁ d₂ a+2 := by omega
  rw [hn,shapePrefix_add,path_runs h₁ h₂]
  congr 1
  have hv : pathShape d₁ d₂ (boundary d₁ d₂ a+1)=false := by
    have hi : boundary d₁ d₂ a+1=a+b := by omega
    simp only [hi,pathShape,frame_last_coordinate h₁ h₂ hdet]
    apply decide_eq_false
    omega
  simp [List.ofFn_succ,boundary_horizontal h₁,hv,KroneckerStack.runShape]

theorem runLength_floor (d₁ d₂ j : ℕ) :
    (runLength d₁ d₂ j:ℤ)=
      ⌊((d₂:ℝ)/(d₁:ℝ))*((j+1:ℕ):ℝ)⌋-⌊((d₂:ℝ)/(d₁:ℝ))*(j:ℝ)⌋ := by
  have hf (i : ℕ) : ⌊((d₂:ℝ)/(d₁:ℝ))*(i:ℝ)⌋=((i*d₂/d₁:ℕ):ℤ) := by
    rw [show ((d₂:ℝ)/(d₁:ℝ))*(i:ℝ)=((i*d₂:ℕ):ℝ)/(d₁:ℝ) by push_cast; ring,
      Int.floor_div_natCast]
    simp only [Int.floor_natCast,Int.natCast_ediv]
  rw [hf,hf]
  exact Nat.cast_sub (Nat.div_le_div_right (by nlinarith))


end KroneckerDyck
end
