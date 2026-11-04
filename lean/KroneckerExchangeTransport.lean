import KroneckerCanonicalExchange
import KroneckerManuscriptNotationSync
import KroneckerExplicitShellCorrespondence

/-! The ordinal-preserving geometric edge bijection for every shell exchange. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeTransport
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerExplicitShellCorrespondence
open KroneckerManuscriptExchangeDefinitions

/-- Exchange the two adjacent zero-based edge positions. -/
def swapPos (i k : ℕ) : ℕ := if k = i then i+1 else if k = i+1 then i else k

@[simp] theorem swapPos_involutive (i k : ℕ) : swapPos i (swapPos i k) = k := by
  by_cases h : k = i
  · subst k; simp [swapPos]
  · by_cases h' : k = i+1
    · subst k; simp [swapPos]
    · simp [swapPos,h,h']

theorem swapPos_lt {i k n : ℕ} (hi : i+1 < n) (hk : k < n) : swapPos i k < n := by
  unfold swapPos
  split_ifs <;> omega

structure Pair (X Y : TNEPath) where
  pre : List Bool
  post : List Bool
  right : Bool
  source : X.steps = pre ++ right :: (!right) :: post
  target : Y.steps = pre ++ (!right) :: right :: post

namespace Pair
variable {X Y : TNEPath}

theorem length_eq (p : Pair X Y) : X.steps.length = Y.steps.length := by
  simp [p.source,p.target]

def indices (p : Pair X Y) : Edge X ≃ Edge Y where
  toFun k := ⟨swapPos p.pre.length k.val, by
    apply swapPos_lt
    · simp [p.target]
    · rw [← p.length_eq]; exact k.isLt⟩
  invFun k := ⟨swapPos p.pre.length k.val, by
    apply swapPos_lt
    · simp [p.source]
    · rw [p.length_eq]; exact k.isLt⟩
  left_inv k := Fin.ext (swapPos_involutive _ _)
  right_inv k := Fin.ext (swapPos_involutive _ _)

/-- The bijection on actual geometric edges, including translated paths. -/
def tau (p : Pair X Y) : GeomEdge X ≃ GeomEdge Y :=
  (edgeEquiv X).symm.trans (p.indices.trans (edgeEquiv Y))

def transported (p : Pair X Y) (f : Grading X) : Grading Y := f ∘ p.tau.symm

theorem directions (p : Pair X Y) (k : ℕ) :
    Y.steps[k]? = X.steps[swapPos p.pre.length k]? := by
  rw [p.source,p.target]
  by_cases h : k < p.pre.length
  · have hn : k ≠ p.pre.length := by omega
    have hn' : k ≠ p.pre.length+1 := by omega
    simp [swapPos,hn,hn',List.getElem?_append,h]
  · by_cases h0 : k = p.pre.length
    · subst k; simp [swapPos]
    · by_cases h1 : k = p.pre.length+1
      · subst k; simp [swapPos]
      · have hk : p.pre.length+2 ≤ k := by omega
        simp only [swapPos,ite_eq_right h0,ite_eq_right h1,List.getElem?_append,ite_eq_right h]
        have he : k-p.pre.length = (k-p.pre.length-2)+2 := by omega
        rw [he]
        simp

/-- Swapping transports grades together with their edges. -/
def swapWord (i : ℕ) (xs : List KroneckerStack.Edge) : List KroneckerStack.Edge :=
  List.ofFn (fun k : Fin xs.length => xs[swapPos i k.val]?.getD (.H 0))

theorem transported_word (p : Pair X Y) (f : Grading X) :
    gradedWord Y (p.transported f) = swapWord p.pre.length (gradedWord X f) := by
  apply List.ext_getElem
  · simp [swapWord,p.length_eq]
  · intro k hk hl
    have hkY : k < Y.steps.length := by simpa using hk
    have hs : swapPos p.pre.length k < X.steps.length := by
      apply swapPos_lt
      · simp [p.source]
      · rw [p.length_eq]; exact hkY
    have hd := p.directions k
    simp only [List.getElem?_eq_getElem hkY, List.getElem?_eq_getElem hs,
      Option.some.injEq] at hd
    simp only [gradedWord,swapWord,List.getElem_ofFn, List.length_ofFn, Fin.val_cast]
    have hg : (List.ofFn (fun k : Edge X => if X.steps[k.val] then
        KroneckerStack.Edge.H (f (edgeEquiv X k)) else
        KroneckerStack.Edge.V (f (edgeEquiv X k))))[swapPos p.pre.length k]? =
        some (if X.steps[swapPos p.pre.length k] then
          KroneckerStack.Edge.H (f (edgeEquiv X ⟨_,hs⟩)) else
          KroneckerStack.Edge.V (f (edgeEquiv X ⟨_,hs⟩))) := by
      simp [hs]
    rw [hg,Option.getD_some,hd]
    simp [transported,tau,indices]

/-- Direction and one-based ordinal characterize the edge lists in the paper. -/
theorem ordinal (p : Pair X Y) (k : Edge Y) :
    (Y.steps.take (k.val+1)).count Y.steps[k.val] =
      (X.steps.take ((p.indices.symm k).val+1)).count X.steps[(p.indices.symm k).val] := by
  have hd := p.directions k.val
  have hk : swapPos p.pre.length k.val < X.steps.length := (p.indices.symm k).isLt
  simp only [List.getElem?_eq_getElem k.isLt,List.getElem?_eq_getElem hk,
    Option.some.injEq] at hd
  change (Y.steps.take (k.val+1)).count Y.steps[k.val] =
      (X.steps.take (swapPos p.pre.length k.val+1)).count X.steps[swapPos p.pre.length k.val]
  rw [← hd]
  by_cases h : k.val < p.pre.length
  · have h0 : k.val ≠ p.pre.length := by omega
    have h1 : k.val ≠ p.pre.length+1 := by omega
    simp [swapPos,h0,h1,p.source,p.target,List.take_append,
      Nat.sub_eq_zero_of_le (by omega : k.val+1 ≤ p.pre.length)]
  · by_cases h0 : k.val = p.pre.length
    · simp (disch := omega) [swapPos,h0,p.source,p.target,List.take_append,List.take_of_length_le,Nat.add_assoc]
      cases p.right <;> simp
    · by_cases h1 : k.val = p.pre.length+1
      · simp (disch := omega) [swapPos,h1,p.source,p.target,List.take_append,List.take_of_length_le,Nat.add_assoc]
        cases p.right <;> simp
      · have he : k.val+1-p.pre.length = (k.val+1-p.pre.length-2)+2 := by omega
        simp only [swapPos,ite_eq_right h0,ite_eq_right h1,p.source,p.target,List.take_append]
        rw [he]
        simp only [List.take_succ_cons,List.count_append,List.count_cons]
        omega

theorem swapWord_pair (pre es : List KroneckerStack.Edge) (x y : KroneckerStack.Edge) :
    swapWord pre.length (pre ++ x::y::es) = pre ++ y::x::es := by
  apply List.ext_getElem
  · simp [swapWord,Nat.add_assoc]
  · intro k hk hl
    have hopt : (pre ++ y::x::es)[k]? =
        (pre ++ x::y::es)[swapPos pre.length k]? := by
      by_cases h : k < pre.length
      · simp [swapPos,show k ≠ pre.length by omega,show k ≠ pre.length+1 by omega,
          List.getElem?_append,h]
      · by_cases h0 : k = pre.length
        · subst k; simp [swapPos]
        · by_cases h1 : k = pre.length+1
          · subst k; simp [swapPos]
          · simp only [swapPos,ite_eq_right h0,ite_eq_right h1,List.getElem?_append,ite_eq_right h]
            rw [show k-pre.length = (k-pre.length-2)+2 by omega]
            simp
    simp only [swapWord,List.getElem_ofFn]
    rw [← hopt,List.getElem?_eq_getElem hl,Option.getD_some]

theorem swapWord_eq_swapEdges (xs : List KroneckerStack.Edge) (i : ℕ)
    (hi : i+1 < xs.length) :
    swapWord i xs = KroneckerCanonicalExchange.swapEdges i xs := by
  have he : xs = xs.take i ++ xs[i] :: xs[i+1] :: xs.drop (i+2) := by
    conv_lhs => rw [← List.take_append_drop i xs]
    rw [List.drop_eq_getElem_cons (by omega : i < xs.length),
      List.drop_eq_getElem_cons hi]
  have hl : (xs.take i).length = i := by simp; omega
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simpa only [hl] using (swapWord_pair (xs.take i) (xs.drop (i+2)) xs[i] xs[i+1]).trans
    (KroneckerCanonicalExchange.swapEdges_pair (xs.take i) (xs.drop (i+2)) xs[i] xs[i+1]).symm

/-- Full target encoding in the same list model as the exchange map. -/
theorem transported_word_exact (p : Pair X Y) (f : Grading X) :
    gradedWord Y (p.transported f) =
      KroneckerCanonicalExchange.swapEdges p.pre.length (gradedWord X f) := by
  rw [p.transported_word,swapWord_eq_swapEdges]
  simp [p.source]


end Pair

def shellPair (ξ : AdjShellExch) : Pair ξ.Y ξ.Y' where
  pre := [true] ++ List.replicate (ξ.u.val+1) false ++ [true] ++ ξ.P
  post := ξ.Q ++ [true] ++ List.replicate (ξ.v.val+1) false
  right := ξ.right
  source := by
    cases h : ξ.right <;>
      simp [AdjShellExch.Y,KroneckerManuscriptShell.path,
        KroneckerColoredShell.shellPath,KroneckerStack.runShape,
        AdjShellExch.source_steps,h,List.append_assoc]
  target := by
    cases h : ξ.right <;>
      simp [AdjShellExch.Y',AdjShellExch.X',KroneckerManuscriptShell.path,
        KroneckerColoredShell.shellPath,KroneckerStack.runShape,
        KroneckerExchangePath.targetPath,KroneckerExchangePath.sourcePath,h,List.append_assoc]

def tau (ξ : AdjShellExch) : GeomEdge ξ.Y ≃ GeomEdge ξ.Y' := (shellPair ξ).tau

def transportedShell (ξ : AdjShellExch) (f : Grading ξ.X) : Grading ξ.Y' :=
  (shellPair ξ).transported
    (KroneckerManuscriptShell.GShell ξ.X f (ξ.u.val+1) (ξ.v.val+1) 1 0)

theorem shell_pair_position (ξ : AdjShellExch) : (shellPair ξ).pre.length = ξ.r := by
  simp [shellPair,AdjShellExch.r]
  omega

/-- No decomposition of the graded input word is assumed. -/
theorem transported_shell_word (ξ : AdjShellExch) (f : Grading ξ.X) :
    gradedWord ξ.Y' (transportedShell ξ f) =
      Pair.swapWord ξ.r (gradedWord ξ.Y
        (KroneckerManuscriptShell.GShell ξ.X f (ξ.u.val+1) (ξ.v.val+1) 1 0)) := by
  have h := (shellPair ξ).transported_word
    (KroneckerManuscriptShell.GShell ξ.X f (ξ.u.val+1) (ξ.v.val+1) 1 0)
  rw [shell_pair_position] at h
  exact h

end KroneckerExchangeTransport

#print axioms KroneckerExchangeTransport.Pair.ordinal
#print axioms KroneckerExchangeTransport.transported_shell_word
