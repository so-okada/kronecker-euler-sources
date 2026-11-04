import Mathlib.RingTheory.PowerSeries.Basic
import KroneckerDyck

/- Original module: KroneckerWall -/
section
/-! The first-coefficient normalization used in the frame identity.
These are algebraic implications. The geometric interpretations of the
series are explicit hypotheses and are not asserted by this module. -/
set_option autoImplicit false
namespace KroneckerWall

theorem lattice_factor {a b : ℕ} (hc : Nat.Coprime a b) (m : ℕ) :
    Nat.gcd (m*a) (m*b)/Nat.gcd a b=m := by
  rw [Nat.gcd_mul_left,hc.gcd_eq_one]
  simp

theorem lattice_exponent {a b m : ℕ} (hc : Nat.Coprime a b) (hm : 0<m) :
    m*m/(Nat.gcd (m*a) (m*b)/Nat.gcd a b)=m := by
  rw [lattice_factor hc]
  exact Nat.mul_div_cancel _ hm

theorem first_coefficient_power {R : Type*} [CommRing R]
    (f : PowerSeries R) (m : ℕ) (h0 : PowerSeries.constantCoeff f=1) :
    PowerSeries.coeff 1 (f^m)=(m:R)*PowerSeries.coeff 1 f := by
  simp [PowerSeries.coeff_one_pow,h0]

/-- Once the weighted enumeration, wall normalization and primitive Euler
interpretation refer to the same series, their combination yields mE.
Each source-dependent equality remains visible in the statement. -/
theorem primitive_coefficient_identity {R : Type*} [CommRing R]
    (positive cluster : PowerSeries R) (m : ℕ) (weightedCount E : R)
    (h0 : PowerSeries.constantCoeff cluster=1)
    (hEnumeration : weightedCount=PowerSeries.coeff 1 positive)
    (hWall : positive=cluster^m)
    (hEuler : PowerSeries.coeff 1 cluster=E) :
    weightedCount=(m:R)*E := by
  rw [hEnumeration,hWall,first_coefficient_power cluster m h0,hEuler]

end KroneckerWall
end

/- Original module: KroneckerFrameIdentity -/
section
/-! The finite frame identity relative to explicitly listed results of
Burcroff--Lee--Mou--Musiker--Reineke. No internal frame, stack, coloring,
or coefficient argument is assumed. The source interfaces are mathematical
hypotheses, not Lean axioms. See SOURCE-BOUNDARY-20261008.md. -/
set_option autoImplicit false
namespace KroneckerFrameIdentity
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights
open KroneckerTight KroneckerDyck KroneckerWall

structure Parameters where
  m : ℕ
  a : ℕ
  b : ℕ
  d₁ : ℕ
  d₂ : ℕ
  k : ℕ
  hm : 3≤m
  ha : 2≤a
  hab : a<b
  coprime : Nat.Coprime a b
  hd₁ : a<d₁
  hd₂ : b<d₂
  determinant : (b:ℤ)*d₁-(a:ℤ)*d₂=1
  length_eq : a+b+1+k=d₁+d₂

abbrev frameLength (p : Parameters) : ℕ := p.a+p.b+1
abbrev ambientLength (p : Parameters) : ℕ := frameLength p+p.k
abbrev frameShape (p : Parameters) : ℕ → Bool := pathShape p.d₁ p.d₂

theorem parameters_exist (m a b : ℕ) (hm : 3≤m) (ha : 2≤a)
    (hab : a<b) (hc : Nat.Coprime a b) :
    ∃ p : Parameters,p.m=m ∧ p.a=a ∧ p.b=b ∧
      ∃ t : ℕ,1≤t ∧ t<a ∧ p.d₁=a+t := by
  obtain ⟨t,d₁,d₂,ht,hta,hd₁,hdet,hs₁,hs₂,_⟩ :=
    KroneckerFrame.ambient_exists ha hab hc
  have hc₁ : (d₁.toNat:ℤ)=d₁ := Int.toNat_of_nonneg (by omega)
  have hc₂ : (d₂.toNat:ℤ)=d₂ := Int.toNat_of_nonneg (by omega)
  have hct : (t.toNat:ℤ)=t := Int.toNat_of_nonneg (by omega)
  let p : Parameters := {
    m:=m, a:=a, b:=b, d₁:=d₁.toNat, d₂:=d₂.toNat,
    k:=d₁.toNat+d₂.toNat-(a+b+1), hm:=hm, ha:=ha, hab:=hab, coprime:=hc,
    hd₁:=by omega, hd₂:=by omega,
    determinant:=by rw [hc₁,hc₂]; linarith,
    length_eq:=by omega }
  refine ⟨p,rfl,rfl,rfl,t.toNat,by omega,by omega,?_⟩
  change d₁.toNat=a+t.toNat
  omega


/-- The source's maximal horizontal shadow and its support interval.
The endpoint indices lie in one period; closure may initially wrap.
For primitive negative determinant, the published position coordinates
are 0 and d₁+d₂-1. -/
def SourcePosition (p : Parameters) (E : ℕ → Edge) : Prop :=
  ∃ u v,u<ambientLength p ∧ v<ambientLength p ∧
    coord p.d₁ p.d₂ u=0 ∧ coord p.d₁ p.d₂ v=p.d₁+p.d₂-1 ∧
    PositiveH E u ∧
    debt E ((if u≤v then v else v+ambientLength p)+1)=debt E u ∧
    (∀ j,u<j→j<(if u≤v then v else v+ambientLength p)+1→debt E j≠debt E u) ∧
    (∀ j,j<ambientLength p→
      ¬ (if u≤v then u≤j ∧ j≤v else u≤j ∨ j≤v)→(E j).grade=0)

theorem ambient_coprime (p : Parameters) : Nat.Coprime p.d₁ p.d₂ := by
  have h := KroneckerFrame.defect_one_coprime p.determinant
  simpa using h

theorem source_position_localizes (p : Parameters)
    {g : Coloring p.m (ambientLength p)} (ht : Tight (frameShape p) p.a p.b g)
    (hp : SourcePosition p (trace (frameShape p) g)) :
    LocatedTight (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b g := by
  obtain ⟨u,v,hu,hv,hucoord,hvcoord,hpos,hclose,hfirst,hzero⟩ := hp
  have h₁ : 0<p.d₁ := by have := p.ha; have := p.hd₁; omega
  have h₂ : 0<p.d₂ := by have := p.ha; have := p.hab; have := p.hd₂; omega
  have hu0 : u=0 := coordinate_injective (ambient_coprime p)
    (by simpa [p.length_eq] using hu) (by omega) (by simpa [coord] using hucoord)
  have hvlast : v=p.a+p.b := coordinate_injective (ambient_coprime p)
    (by simpa [p.length_eq] using hv)
    (by have := p.hd₁; have := p.hd₂; omega)
    (by rw [hvcoord,frame_last_coordinate h₁ h₂ p.determinant])
  subst u
  subst v
  simp only [Nat.zero_le,ite_true] at hclose hfirst hzero
  have hr : RootComponent (trace (frameShape p) g) (frameLength p) := by
    apply (root_iff_first_return _ _).mpr
    refine ⟨by dsimp [frameLength]; omega,hpos,?_,?_⟩
    · simpa [debt,walk] using hclose
    · intro j hj hjn
      simpa [debt,walk] using hfirst j hj hjn
  refine ⟨ht,hr,?_⟩
  intro j
  have hjN : (Fin.natAdd (frameLength p) j).val<ambientLength p := (Fin.natAdd _ j).isLt
  have hz := hzero (Fin.natAdd (frameLength p) j).val hjN (by
    simp only [Fin.natAdd,frameLength]
    omega)
  rw [trace_before _ _ _ hjN,paint_grade] at hz
  exact hz

/-- Specialized statements from the cited paper. `position` is the
negative primitive case of Lemmas 4.12--4.13 and the definition of shadow;
`enumeration` is Theorem 4.10 for both incoming polynomials (1+x)^m;
`change_lattice` is Proposition 2.5; `euler` is the primitive equal-parameter
interpretation in Section 9.3. The series are over the rational numbers; no integrality assertion for higher coefficients is needed.
No field assumes the manuscript's frame identity or comparison estimates. -/
structure Literature (p : Parameters) (E : ℤ) where
  positive : PowerSeries ℚ
  cluster : PowerSeries ℚ
  constant : PowerSeries.constantCoeff cluster=1
  position : ∀ g : Coloring p.m (ambientLength p),
    Tight (frameShape p) p.a p.b g→SourcePosition p (trace (frameShape p) g)
  enumeration : (weightedCount (fun d : Grades p.m (ambientLength p) =>
    Tight (frameShape p) p.a p.b (representative d)):ℚ)=PowerSeries.coeff 1 positive
  change_lattice : positive=cluster^
    (p.m*p.m/(Nat.gcd (p.m*p.a) (p.m*p.b)/Nat.gcd p.a p.b))
  euler : PowerSeries.coeff 1 cluster=E

def tightEquivLocated (p : Parameters) (E : ℤ) (s : Literature p E) :
    {g : Coloring p.m (ambientLength p) // Tight (frameShape p) p.a p.b g} ≃
      {g : Coloring p.m (ambientLength p) //
        LocatedTight (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b g} where
  toFun g := ⟨g.val,source_position_localizes p g.property (s.position g.val g.property)⟩
  invFun g := ⟨g.val,g.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual finite colored bijection from the frame to all tight
gradings on the auxiliary maximal Dyck path. The only external input
used in this bijection is the support-position theorem. -/
def finiteFrameEquiv (p : Parameters) (E : ℤ) (s : Literature p E) :
    {g : Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} ≃
      {g : Coloring p.m (ambientLength p) // Tight (frameShape p) p.a p.b g} :=
  let h₁ : 0<p.d₁ := by have := p.ha; have := p.hd₁; omega
  let h₂ : 0<p.d₂ := by have := p.ha; have := p.hab; have := p.hd₂; omega
  (frameEquiv (frameShape p) p.a p.b (frame_edge_counts h₁ h₂ p.determinant).1
    (frame_edge_counts h₁ h₂ p.determinant).2).trans (tightEquivLocated p E s).symm

theorem finite_frame_identity (p : Parameters) (E : ℤ) (s : Literature p E) :
    (Nat.card {g : Coloring p.m (frameLength p) //
      Connected p.m (word (frameShape p) g) 0}:ℤ)=(p.m:ℤ)*E := by
  have hc := Nat.card_congr (finiteFrameEquiv p E s)
  have hwall : s.positive=s.cluster^p.m := by
    rw [s.change_lattice,lattice_exponent p.coprime (by have := p.hm; omega)]
  have hq : (Nat.card {g : Coloring p.m (frameLength p) //
      Connected p.m (word (frameShape p) g) 0}:ℚ)=(p.m:ℚ)*(E:ℚ) := by
    rw [hc,tight_count_weighted]
    exact primitive_coefficient_identity s.positive s.cluster p.m _ (E:ℚ)
      s.constant s.enumeration hwall s.euler
  exact_mod_cast hq

theorem finite_frame_word (p : Parameters) :
    shapePrefix (frameShape p) (frameLength p)=
      (List.range p.a).flatMap (fun j => runShape (runLength p.d₁ p.d₂ j))++runShape 1 := by
  apply frame_path_word
  · have := p.ha; have := p.hd₁; omega
  · have := p.ha; have := p.hab; have := p.hd₂; omega
  · exact p.determinant

end KroneckerFrameIdentity
end
