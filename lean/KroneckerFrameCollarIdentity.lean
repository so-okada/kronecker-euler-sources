import KroneckerExtractedRecovery
import KroneckerCollarSplit
import KroneckerMechanicalWordShift

section

/- Original module: KroneckerThreeGuards -/
section
/-! Exact decomposition of a word at three exterior guard runs. -/
set_option autoImplicit false
namespace KroneckerThreeGuards

theorem exists_three_prefix (X : List ℕ) (h : 3 ≤ X.length) :
    ∃ a b c Y, X = a::b::c::Y := by
  cases X with
  | nil => simp at h
  | cons a X =>
    cases X with
    | nil => simp at h
    | cons b X =>
      cases X with
      | nil => simp at h
      | cons c X => exact ⟨a,b,c,X,rfl⟩

theorem exists_three_suffix (X : List ℕ) (h : 3 ≤ X.length) :
    ∃ Y a b c, X = Y++[a,b,c] := by
  obtain ⟨c,b,a,Y,hY⟩ := exists_three_prefix X.reverse (by simpa only [List.length_reverse] using h)
  refine ⟨Y.reverse,a,b,c,?_⟩
  have hr := congrArg List.reverse hY
  simpa [List.reverse_cons, List.append_assoc] using hr

end KroneckerThreeGuards
end

/- Original module: KroneckerSixGuards -/
section
/-! Remove six exterior guard runs and identify every full slice of the middle. -/
set_option autoImplicit false
namespace KroneckerSixGuards
open KroneckerThreeGuards

theorem exists_six_guards (Z : List ℕ) (h : 6 ≤ Z.length) :
    ∃ a b c d e f X, Z = a::b::c::X++[d,e,f] ∧ X.length = Z.length-6 := by
  obtain ⟨a,b,c,T,hT⟩ := exists_three_prefix Z (by omega)
  have hlen : 3 ≤ T.length := by rw [hT] at h; simp only [List.length_cons] at h; omega
  obtain ⟨X,d,e,f,hX⟩ := exists_three_suffix T hlen
  refine ⟨a,b,c,d,e,f,X,by rw [hT,hX]; rfl,?_⟩
  rw [hT,hX]
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

theorem middle_slice (Z X : List ℕ) (a b c d e f i L : ℕ)
    (hZ : Z = a::b::c::X++[d,e,f]) (hfit : i+L ≤ X.length) :
    (Z.drop (3+i)).take L = (X.drop i).take L := by
  have hdrop : Z.drop 3 = X++[d,e,f] := by rw [hZ]; rfl
  rw [← List.drop_drop, hdrop, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

end KroneckerSixGuards
end

/- Original module: KroneckerFrameSlices -/
section
/-! Every full slice before the exceptional last frame run is mechanical. -/
set_option autoImplicit false
namespace KroneckerFrameSlices
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerMechanicalWords KroneckerMechanicalSlices

theorem frameWord_slice (a b d i L : ℕ) (hfit : i+L ≤ a) :
    ((frameWord a b d).drop i).take L = mechanicalWord (frameSlope a b d) 0 i L := by
  rw [frameWord, List.drop_append_of_le_length (by rw [mechanicalWord_length]; omega),
    List.take_append_of_le_length (by rw [List.length_drop, mechanicalWord_length]; omega),
    mechanicalWord_slice _ _ 0 a i L hfit]
  simp only [Nat.zero_add]

end KroneckerFrameSlices
end
end

section

set_option autoImplicit false
namespace KroneckerFrameCollarIdentity
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerMechanicalWords

theorem middle_of_collar_split (X L Y R : List ℕ) (u v P T : ℕ)
    (hX : X=L++(u::Y++[v])++R) (hL : L.length=P) (hY : Y.length=T) :
    (X.drop (P+1)).take T=Y := by
  have hdrop : X.drop (P+1)=Y++[v]++R := by
    rw [hX]
    simp [List.append_assoc,List.drop_append,hL,List.drop_eq_nil_of_le (show L.length ≤ P+1 by omega)]
  rw [hdrop,← hY]
  simp [List.append_assoc]

theorem frame_collar_identity (a b d P T : ℕ) (hsize : P+1+T+1+P=a+1) :
    ∃ L u v R, frameWord a b d=L++
      (u::mechanicalWord (frameSlope a b d) ((P+1 : ℕ) * frameSlope a b d) 0 T++[v])++R ∧
      L.length=P ∧ R.length=P := by
  obtain ⟨L,u,Y,v,R,hX,hL,hY,hR⟩ := KroneckerCollarSplit.split_three
    (frameWord a b d) P T P (by rw [KroneckerFrameWord.frameWord_length];omega)
  have hs := middle_of_collar_split (frameWord a b d) L Y R u v P T hX hL hY
  have hf := KroneckerFrameSlices.frameWord_slice a b d (P+1) T (by omega)
  have hmid : Y=mechanicalWord (frameSlope a b d) ((P+1 : ℕ)*frameSlope a b d) 0 T := by
    rw [hs] at hf
    rw [hf,KroneckerMechanicalWordShift.word_shift]
    simp
  exact ⟨L,u,v,R,by simpa only [hmid] using hX,hL,hR⟩

end KroneckerFrameCollarIdentity
end

