import KroneckerSourceGradingDictionary
import KroneckerFrameIdentity

/- Original module: KroneckerSourceMaximalPath -/
section
/-! The modular path is the maximal NE path, proved by height comparison.
At a fixed step index, x+y is fixed. Comparing y there is equivalent to
comparing crossings of the diagonals x+y=i; this also proves uniqueness. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceMaximalPath
open KroneckerColoring KroneckerDyck

def Below (d₁ d₂ : ℕ) (shape : ℕ → Bool) : Prop :=
  ∀i,i≤d₁+d₂→(d₁:ℤ)*VEdges shape i≤(d₂:ℤ)*HEdges shape i

def IsDyck (d₁ d₂ : ℕ) (shape : ℕ → Bool) : Prop :=
  HEdges shape (d₁+d₂)=(d₁:ℤ) ∧ VEdges shape (d₁+d₂)=(d₂:ℤ) ∧ Below d₁ d₂ shape

def Maximal (d₁ d₂ : ℕ) (shape : ℕ → Bool) : Prop :=
  IsDyck d₁ d₂ shape ∧ ∀other,IsDyck d₁ d₂ other→∀i,i≤d₁+d₂→VEdges other i≤VEdges shape i

def vertex (shape : ℕ → Bool) (i : ℕ) : ℤ × ℤ := (HEdges shape i,VEdges shape i)
def sourceCoordinate (d₁ d₂ : ℕ) (shape : ℕ → Bool) (i : ℕ) : ℤ :=
  (d₂:ℤ)*(vertex shape i).1-(d₁:ℤ)*(vertex shape i).2


theorem dyck_below {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) :
    Below d₁ d₂ (pathShape d₁ d₂) := by
  intro i _
  have h := coordinate_identity h₁ h₂ i
  have hnonneg : (0:ℤ)≤coord d₁ d₂ i := Int.natCast_nonneg _
  nlinarith

theorem height_window {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (i : ℕ) :
    ((d₁:ℤ)+d₂)*VEdges (pathShape d₁ d₂) i≤(i:ℤ)*d₂ ∧
    (i:ℤ)*d₂<((d₁:ℤ)+d₂)*(VEdges (pathShape d₁ d₂) i+1) := by
  have hc := coordinate_identity h₁ h₂ i
  have hs := edge_count_sum (pathShape d₁ d₂) i
  have hlo : (0:ℤ)≤coord d₁ d₂ i := Int.natCast_nonneg _
  have hhi : (coord d₁ d₂ i:ℤ)<(d₁:ℤ)+d₂ := by
    exact_mod_cast coord_bound (by omega : 0<d₁+d₂) i
  constructor <;> nlinarith

theorem below_height_le {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂)
    {shape : ℕ → Bool} (hb : Below d₁ d₂ shape) (i : ℕ) (hi : i≤d₁+d₂) :
    VEdges shape i≤VEdges (pathShape d₁ d₂) i := by
  have hs := edge_count_sum shape i
  have hb' := hb i hi
  have hw := (height_window h₁ h₂ i).2
  have hD : (0:ℤ)<(d₁:ℤ)+d₂ := by positivity
  by_contra h
  have hgap : VEdges (pathShape d₁ d₂) i+1≤VEdges shape i := by omega
  nlinarith

theorem dyck_maximal {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) :
    Maximal d₁ d₂ (pathShape d₁ d₂) := by
  refine ⟨⟨(path_dimensions h₁ h₂).1,(path_dimensions h₁ h₂).2,dyck_below h₁ h₂⟩,?_⟩
  intro other ho i hi
  exact below_height_le h₁ h₂ ho.2.2 i hi





theorem coordinate_matches_source {d₁ d₂ : ℕ} (h₁ : 0<d₁) (h₂ : 0<d₂) (i : ℕ) :
    sourceCoordinate d₁ d₂ (pathShape d₁ d₂) i=(coord d₁ d₂ i:ℤ) := by
  rw [coordinate_identity h₁ h₂]
  simp only [sourceCoordinate,vertex]
  ring

theorem zero_coordinate_origin {d₁ d₂ i : ℕ} (hc : Nat.Coprime d₁ d₂)
    (hi : i<d₁+d₂) (hz : coord d₁ d₂ i=0) : i=0 := by
  exact coordinate_injective hc hi (by omega) (by simpa [coord] using hz)


end KroneckerSourceMaximalPath
end
end

/- Original module: KroneckerSourcePeriodicSums -/
section
/-! Full-turn source totals are independent of the chosen cyclic cut. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourcePeriodicSums
open KroneckerStack KroneckerCompatibility KroneckerSourceIntervalCounts
open KroneckerSourceHorizontalShadow
open scoped BigOperators

theorem walk_add_period {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i)
    (f : Edge→ℤ) (i : ℕ) : walk f E (i+N)=walk f E i+walk f E N := by
  induction i with
  | zero => simp [walk]
  | succ i ih =>
    rw [show i+1+N=(i+N)+1 by omega,walk,ih,hp,walk]
    ring


theorem horizontal_weight_turn {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i) (u : ℕ) :
    hWeight E u (u+N)=hWeight E 0 N := by
  unfold hWeight
  rw [interval_walk _ E u (u+N) (by omega),interval_walk _ E 0 N (by omega),walk_add_period hp]
  simp [walk]

theorem vertical_weight_turn {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i) (u : ℕ) :
    vWeight E u (u+N)=vWeight E 0 N := by
  unfold vWeight
  rw [interval_walk _ E u (u+N) (by omega),interval_walk _ E 0 N (by omega),walk_add_period hp]
  simp [walk]

theorem horizontal_count_turn {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i) (u : ℕ) :
    KroneckerSourceIntervalCounts.hCount E u (u+N)=KroneckerSourceIntervalCounts.hCount E 0 N := by
  unfold KroneckerSourceIntervalCounts.hCount
  rw [interval_walk _ E u (u+N) (by omega),interval_walk _ E 0 N (by omega),walk_add_period hp]
  simp [walk]

theorem vertical_count_turn {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i) (u : ℕ) :
    KroneckerSourceIntervalCounts.vCount E u (u+N)=KroneckerSourceIntervalCounts.vCount E 0 N := by
  unfold KroneckerSourceIntervalCounts.vCount
  rw [interval_walk _ E u (u+N) (by omega),interval_walk _ E 0 N (by omega),walk_add_period hp]
  simp [walk]

theorem first_closure_every_cut {E : ℕ → Edge} {N u : ℕ} (hp : ∀i,E (i+N)=E i)
    (hN : 1≤N) (hu : PositiveH E u)
    (hTotal : hWeight E 0 N≤KroneckerSourceIntervalCounts.vCount E 0 N) :
    ∃e,e<u+N ∧ FirstClosure E u e := by
  apply first_exists hN hu
  rw [horizontal_weight_turn hp,vertical_count_turn hp]
  exact hTotal

end KroneckerSourcePeriodicSums
end
end

/- Original module: KroneckerSourceParameterGates -/
section
/-! Exact arithmetic and maximal-path hypotheses for the source application.
The source parameters p,q are the manuscript dimensions a,b, respectively. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceParameterGates
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights KroneckerDyck
open KroneckerFrameIdentity KroneckerSourceMaximalPath KroneckerSourceGradingDictionary
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility KroneckerSourcePeriodicSums

theorem source_hypotheses (p : Parameters) :
    0<p.a ∧ 0<p.b ∧ 0<p.d₁ ∧ 0<p.d₂ ∧ p.a≤p.d₁ ∧ p.b≤p.d₂ ∧
    Nat.gcd p.a p.b=1 ∧ (p.a:ℤ)*p.d₂-(p.b:ℤ)*p.d₁=-(Nat.gcd p.a p.b:ℕ) ∧
    ambientLength p=p.d₁+p.d₂ ∧ Nat.gcd p.a p.b≤p.d₁ ∧ Nat.gcd p.a p.b≤p.d₂ := by
  have ha := p.ha
  have hab := p.hab
  have hd₁ := p.hd₁
  have hd₂ := p.hd₂
  have hc := p.coprime.gcd_eq_one
  have hdet := p.determinant
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,hc,?_,p.length_eq,?_,?_⟩
  · rw [hc]
    norm_num
    linarith
  · omega
  · omega

theorem ambient_path_maximal (p : Parameters) : Maximal p.d₁ p.d₂ (frameShape p) :=
  dyck_maximal (source_hypotheses p).2.2.1 (source_hypotheses p).2.2.2.1

theorem source_coordinate (p : Parameters) (i : ℕ) :
    sourceCoordinate p.d₁ p.d₂ (frameShape p) i=(coord p.d₁ p.d₂ i:ℤ) :=
  coordinate_matches_source (source_hypotheses p).2.2.1 (source_hypotheses p).2.2.2.1 i




end KroneckerSourceParameterGates
end
end
