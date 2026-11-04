import KroneckerWrappedExchangeAssembly
import KroneckerRunWordSplice

/- Original module: KroneckerThreeCompleteInsertion -/
section
/-! Complete binary-run insertion at m=3, on the union of all surplus classes. -/
set_option autoImplicit false
namespace KroneckerThreeCompleteInsertion
open KroneckerColoring KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusColoringFinite
open KroneckerCompleteRunPalette KroneckerCompleteRunMap KroneckerCompleteRunInjection

def insertThree (r i : ℕ) (hr : 1≤r ∧ r≤2) (U : List Bool) (hi : 1 ≤ i ∧ i < U.length)
    (a : SurplusColorings 3 U) : SurplusColorings 3 (completePath r i U) :=
  ⟨a.1+1,completeRun r i a.1 (by omega) U hi a.2⟩

theorem insertThree_surplus (r i : ℕ) (hr : 1≤r ∧ r≤2) (U : List Bool) (hi : 1 ≤ i ∧ i < U.length)
    (a : SurplusColorings 3 U) : (insertThree r i hr U hi a).1=a.1+1 := rfl

theorem insertThree_injective (r i : ℕ) (hr : 1≤r ∧ r≤2) (U : List Bool) (hi : 1 ≤ i ∧ i < U.length) :
    Function.Injective (insertThree r i hr U hi) := by
  intro a b he
  apply surplusForget_injective 3 U
  apply completeColoring_injective r i (by omega) U (by omega)
  exact congrArg surplusForget he

end KroneckerThreeCompleteInsertion
end

/- Original module: KroneckerThreeMixedPrograms -/
section
/-! Actual mixed binary-run insertion and wrapped-exchange programs at m=3. -/
set_option autoImplicit false
namespace KroneckerThreeMixedPrograms
open KroneckerProgramExecution KroneckerCompleteRunPalette KroneckerThreeCompleteInsertion
open KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap

inductive ThreeProgram (U : List Bool) : List Bool → ℕ → ℕ → Type
  | nil : ThreeProgram U U 0 0
  | complete {V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
      (r i : ℕ) (hr : 1≤r ∧ r≤2) (hi : 1 ≤ i ∧ i < V.length) :
      ThreeProgram U (completePath r i V) (K+1) k
  | exchange {K k : ℕ} (s : ExchangeSpec 3) (p : ThreeProgram U s.source K k) :
      ThreeProgram U s.target K (k+1)

noncomputable def runThree {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (a : SurplusColorings 3 U) : SurplusColorings 3 V :=
  match p with
  | .nil => a
  | .complete p r i hr hi => insertThree r i hr _ hi (runThree p a)
  | .exchange s p => exchangeMap s (runThree p a)

theorem runThree_nil (U : List Bool) (a : SurplusColorings 3 U) :
    runThree (.nil : ThreeProgram U U 0 0) a=a := rfl

theorem three_program_surplus {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (a : SurplusColorings 3 U) : a.1+K≤(runThree p a).1 ∧ (runThree p a).1≤a.1+K+3*k := by
  induction p with
  | nil => simp [runThree]
  | complete p r i hr hi ih =>
    change a.1+_≤(runThree p a).1+1 ∧ (runThree p a).1+1≤_
    omega
  | exchange s p ih =>
    have hh := exchangeMap_surplus s (runThree p a)
    change a.1+_≤(exchangeMap s (runThree p a)).1 ∧ (exchangeMap s (runThree p a)).1≤_
    omega

end KroneckerThreeMixedPrograms
end

/- Original module: KroneckerThreeMixedRecovery -/
section
/-! Mixed programs need one palette code per exchange and none per complete-run insertion. -/
set_option autoImplicit false
namespace KroneckerThreeMixedRecovery
open KroneckerProgramExecution KroneckerThreeCompleteInsertion KroneckerThreeMixedPrograms
open KroneckerWrappedExchangeMap KroneckerWrappedExchangeRecovery KroneckerBinaryProgramCode

noncomputable def threeCode {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (a : SurplusColorings 3 U) : Code k :=
  match p with
  | .nil => ()
  | .complete p _ _ _ _ => threeCode p a
  | .exchange s p => (threeCode p a,exchangeCode s (runThree p a))

theorem three_target_code_injective {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k) :
    Function.Injective (fun a => (runThree p a,threeCode p a)) := by
  induction p with
  | nil => intro a b he; exact congrArg Prod.fst he
  | complete p r i hr hi ih =>
    intro a b he
    have hrun := insertThree_injective r i hr _ hi (congrArg Prod.fst he)
    exact ih (Prod.ext hrun (Prod.mk.inj he).2)
  | exchange s p ih =>
    intro a b he
    have ho := (Prod.mk.inj he).1
    have hc := (Prod.mk.inj he).2
    change (threeCode p a,exchangeCode s (runThree p a))=(threeCode p b,exchangeCode s (runThree p b)) at hc
    have hrun := exchange_target_code_injective s (Prod.ext ho (Prod.mk.inj hc).2)
    exact ih (Prod.ext hrun (Prod.mk.inj hc).1)

end KroneckerThreeMixedRecovery
end

/- Original module: KroneckerThreeMixedFiber -/
section
/-! The constructed mixed map has fibers at most8^k, independent of insertion count K. -/
set_option autoImplicit false
namespace KroneckerThreeMixedFiber
open KroneckerProgramExecution KroneckerSurplusColoringFinite KroneckerBinaryProgramCode
open KroneckerThreeMixedPrograms KroneckerThreeMixedRecovery

theorem three_program_fiber {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (b : SurplusColorings 3 V) : Nat.card {a // runThree p a=b}≤8^k := by
  classical
  have hi : Function.Injective (fun a : {a // runThree p a=b} => threeCode p a.val) := by
    intro a a' he
    apply Subtype.ext
    exact three_target_code_injective p (Prod.ext (a.property.trans a'.property.symm) he)
  have hh := Fintype.card_le_of_injective _ hi
  simpa only [Nat.card_eq_fintype_card,code_card] using hh

theorem three_program_count {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k) :
    Nat.card (SurplusColorings 3 U)≤8^k*Nat.card (SurplusColorings 3 V) := by
  have hh := Fintype.card_le_of_injective _ (three_target_code_injective p)
  simpa only [Fintype.card_prod,code_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

end KroneckerThreeMixedFiber
end

/- Original module: KroneckerThreeMixedZero -/
section
/-! Drain a mixed m=3 program using c+K+3k prescribed binary collar layers. -/
set_option autoImplicit false
namespace KroneckerThreeMixedZero
open KroneckerWordCounts KroneckerProgramExecution KroneckerThreeMixedPrograms
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroThree {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hs : c+K+3*k≤pairs.length)
    (g : ConnectedColorings 3 U c) : ConnectedColorings 3 (collarPath pairs V) 0 := by
  let a := runThree p ⟨c,g⟩
  have hr := (three_program_surplus p ⟨c,g⟩).2
  change (runThree p ⟨c,g⟩).1≤c+K+3*k at hr
  have hz : a.1-pairs.length=0 := by dsimp [a]; omega
  refine ⟨collarColoring (by decide) pairs hp a.1 V a.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by decide) pairs hp a.1 V a.2.val a.2.property

theorem zeroThree_recover {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hs : c+K+3*k≤pairs.length)
    (g : ConnectedColorings 3 U c) :
    recoverCollar pairs V (zeroThree p pairs hp c hs g).val=(runThree p ⟨c,g⟩).2.val :=
  recover_collarColoring (by decide) pairs hp _ _ _

end KroneckerThreeMixedZero
end

/- Original module: KroneckerThreeZeroRecovery -/
section
/-! The actual drained mixed map retains the same k exchange codes. -/
set_option autoImplicit false
namespace KroneckerThreeZeroRecovery
open KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusColoringFinite
open KroneckerThreeMixedPrograms KroneckerThreeMixedRecovery KroneckerThreeMixedZero
open KroneckerCollarColoring KroneckerCollarRecovery

theorem zeroThree_target_code_injective {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hs : c+K+3*k≤pairs.length) :
    Function.Injective (fun g => (zeroThree p pairs hp c hs g,threeCode p ⟨c,g⟩)) := by
  intro g h he
  have hout := (Prod.mk.inj he).1
  have hc := (Prod.mk.inj he).2
  have hh := congrArg (fun z : ConnectedColorings 3 (collarPath pairs V) 0 =>
    recoverCollar pairs V z.val) hout
  simp only [zeroThree_recover] at hh
  have hr : runThree p ⟨c,g⟩=runThree p ⟨c,h⟩ := surplusForget_injective 3 V hh
  have hin := three_target_code_injective p (Prod.ext hr hc)
  apply Subtype.ext
  exact congrArg surplusForget hin

end KroneckerThreeZeroRecovery
end

/- Original module: KroneckerThreeZeroCount -/
section
/-! The mixed insertion/exchange comparison on its actual constructed target. -/
set_option autoImplicit false
namespace KroneckerThreeZeroCount
open KroneckerWordCounts KroneckerBinaryProgramCode KroneckerThreeMixedPrograms
open KroneckerThreeMixedRecovery KroneckerThreeMixedZero KroneckerThreeZeroRecovery KroneckerCollarColoring

theorem zeroThree_count {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hs : c+K+3*k≤pairs.length) :
    pathCount 3 U c≤8^k*pathCount 3 (collarPath pairs V) 0 := by
  classical
  have hh := Fintype.card_le_of_injective _ (zeroThree_target_code_injective p pairs hp c hs)
  simpa only [pathCount,Fintype.card_prod,code_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

theorem zeroThree_real_count {U V : List Bool} {K k : ℕ} (p : ThreeProgram U V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hs : c+K+3*k≤pairs.length) :
    (pathCount 3 U c : ℝ)/(8 : ℝ)^k≤pathCount 3 (collarPath pairs V) 0 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<8^k)).mpr
  have hh := zeroThree_count p pairs hp c hs
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

end KroneckerThreeZeroCount
end

/- Original module: KroneckerThreeBufferedCount -/
section
/-! An initial preserving binary shell internalizes every later raw-middle insertion gap. -/
set_option autoImplicit false
namespace KroneckerThreeBufferedCount
open KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring KroneckerBinaryProgramCode
open KroneckerThreeMixedPrograms KroneckerThreeMixedRecovery KroneckerThreeMixedZero KroneckerThreeZeroRecovery

noncomputable def bufferedThree {u v : ℕ} {U V : List Bool} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : ThreeProgram (shellPath u v U) V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+3*k≤pairs.length)
    (g : ConnectedColorings 3 U 0) : ConnectedColorings 3 (collarPath pairs V) 0 :=
  zeroThree p pairs hp 0 (by simpa using hs) (unaryShell u v 0 (by decide) hu hv U g)

theorem buffered_target_code_injective {u v : ℕ} {U V : List Bool} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : ThreeProgram (shellPath u v U) V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+3*k≤pairs.length) :
    Function.Injective (fun g => (bufferedThree hu hv p pairs hp hs g,
      threeCode p ⟨0,unaryShell u v 0 (by decide) hu hv U g⟩)) := by
  intro g h he
  apply unaryShell_injective u v 0 (by decide) hu hv U
  exact zeroThree_target_code_injective p pairs hp 0 (by simpa using hs) he

theorem buffered_three_count {u v : ℕ} {U V : List Bool} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : ThreeProgram (shellPath u v U) V K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+3*k≤pairs.length) :
    pathCount 3 U 0≤8^k*pathCount 3 (collarPath pairs V) 0 := by
  classical
  have hh := Fintype.card_le_of_injective _ (buffered_target_code_injective hu hv p pairs hp hs)
  simpa only [pathCount,Fintype.card_prod,code_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

end KroneckerThreeBufferedCount
end

/- Original module: KroneckerThreeProgramLifts -/
section
/-! Operational constructors for middle insertions and literal run exchanges at m=3. -/
set_option autoImplicit false
namespace KroneckerThreeProgramLifts
open KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring KroneckerCompleteRunPalette
open KroneckerMiddleContext KroneckerMiddleCompleteLift KroneckerBufferedGaps
open KroneckerThreeMixedPrograms KroneckerBinaryExchangeShapes KroneckerBinaryExchangeSpec

def middleComplete {u v : ℕ} {U V : List Bool} {K k : ℕ} (pairs : List (ℕ×ℕ))
    (p : ThreeProgram (shellPath u v U) (collarPath pairs (shellPath u v V)) K k)
    (r i : ℕ) (hr : 1≤r ∧ r≤2) (hi : i≤V.length) :
    ThreeProgram (shellPath u v U) (collarPath pairs (shellPath u v (completePath r i V))) (K+1) k := by
  simpa only [complete_middle_path pairs u v r i V hi] using
    ThreeProgram.complete p r ((leftContext pairs u).length+i) hr (middle_complete_bounds pairs u v V i hi)

def runExchange {U : List Bool} {K k : ℕ} (right : Bool) (rs ts : List ℕ)
    (p : ThreeProgram U (runWord (rs++pairRuns right++ts)) K k) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    ThreeProgram U (runWord (u::(rs++pairRuns (!right)++ts)++[v])) K (k+1) := by
  have q : ThreeProgram U (binarySpec right rs ts u v hu hv).source K k :=
    (binary_spec_source right rs ts u v hu hv).symm ▸ p
  exact binary_spec_target right rs ts u v hu hv ▸ ThreeProgram.exchange (binarySpec right rs ts u v hu hv) q

theorem middle_complete_realized {u v : ℕ} {U V : List Bool} {K k : ℕ} (pairs : List (ℕ×ℕ))
    (p : ThreeProgram (shellPath u v U) (collarPath pairs (shellPath u v V)) K k)
    (r i : ℕ) (hr : 1≤r ∧ r≤2) (hi : i≤V.length) :
    Nonempty (ThreeProgram (shellPath u v U) (collarPath pairs (shellPath u v (completePath r i V))) (K+1) k) :=
  ⟨middleComplete pairs p r i hr hi⟩

end KroneckerThreeProgramLifts
end

/- Original module: KroneckerRawBinaryEdits -/
section
/-! Color-independent raw binary-run edit lists with insertions at both endpoints allowed. -/
set_option autoImplicit false
namespace KroneckerRawBinaryEdits
open KroneckerBinaryExchangeShapes

inductive RawBinary (R : List ℕ) : List ℕ → ℕ → ℕ → Type
  | nil : RawBinary R R 0 0
  | insert {pre post : List ℕ} {K k : ℕ} (p : RawBinary R (pre++post) K k)
      (r : ℕ) (hr : 1≤r ∧ r≤2) : RawBinary R (pre++r::post) (K+1) k
  | exchange {pre post : List ℕ} {K k : ℕ} (right : Bool)
      (p : RawBinary R (pre++pairRuns right++post) K k) :
      RawBinary R (pre++pairRuns (!right)++post) K (k+1)

theorem raw_binary_length {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k) :
    S.length=R.length+K := by
  induction p with
  | nil => simp
  | insert p r hr ih => simp only [List.length_append,List.length_cons] at ih ⊢; omega
  | exchange right p ih => cases right <;> simp [pairRuns] at ih ⊢ <;> omega

theorem raw_binary_sum {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k) :
    R.sum+K≤S.sum ∧ S.sum≤R.sum+2*K := by
  induction p with
  | nil => simp
  | insert p r hr ih => simp only [List.sum_append,List.sum_cons] at ih ⊢; omega
  | exchange right p ih => cases right <;> simp [pairRuns] at ih ⊢ <;> omega

end KroneckerRawBinaryEdits
end

/- Original module: KroneckerThreeMiddleExchange -/
section
/-! Lift a raw middle run exchange through every previously prescribed collar layer. -/
set_option autoImplicit false
namespace KroneckerThreeMiddleExchange
open KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring
open KroneckerThreeMixedPrograms KroneckerThreeProgramLifts KroneckerBinaryExchangeShapes

theorem framed_pair_path (pairs : List (ℕ×ℕ)) (u v : ℕ) (pre post : List ℕ) (right : Bool) :
    collarPath pairs (shellPath u v (runWord (pre++pairRuns right++post)))=
      runWord ((pairs.map Prod.fst++u::pre)++pairRuns right++(post++v::(pairs.map Prod.snd).reverse)) := by
  rw [shellPath_runWord,collarPath_runWord]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

def middleExchange {u v : ℕ} {U : List Bool} {K k : ℕ} (pairs : List (ℕ×ℕ))
    (pre post : List ℕ) (right : Bool)
    (p : ThreeProgram (shellPath u v U)
      (collarPath pairs (shellPath u v (runWord (pre++pairRuns right++post)))) K k)
    (x y : ℕ) (hx : 1≤x ∧ x≤2) (hy : 1≤y ∧ y≤2) :
    ThreeProgram (shellPath u v U)
      (collarPath ((x,y)::pairs) (shellPath u v (runWord (pre++pairRuns (!right)++post)))) K (k+1) := by
  have q := runExchange right (pairs.map Prod.fst++u::pre) (post++v::(pairs.map Prod.snd).reverse)
    (framed_pair_path pairs u v pre post right ▸ p) x y hx hy
  have ht : collarPath ((x,y)::pairs) (shellPath u v (runWord (pre++pairRuns (!right)++post)))=
      runWord (x::((pairs.map Prod.fst++u::pre)++pairRuns (!right)++(post++v::(pairs.map Prod.snd).reverse))++[y]) := by
    rw [collarPath,framed_pair_path,shellPath_runWord]
  exact ht.symm ▸ q

theorem middle_exchange_realized {u v : ℕ} {U : List Bool} {K k : ℕ} (pairs : List (ℕ×ℕ))
    (pre post : List ℕ) (right : Bool)
    (p : ThreeProgram (shellPath u v U)
      (collarPath pairs (shellPath u v (runWord (pre++pairRuns right++post)))) K k)
    (x y : ℕ) (hx : 1≤x ∧ x≤2) (hy : 1≤y ∧ y≤2) :
    Nonempty (ThreeProgram (shellPath u v U)
      (collarPath ((x,y)::pairs) (shellPath u v (runWord (pre++pairRuns (!right)++post)))) K (k+1)) :=
  ⟨middleExchange pairs pre post right p x y hx hy⟩

end KroneckerThreeMiddleExchange
end

/- Original module: KroneckerRawBinaryLift -/
section
/-! Realize every raw binary edit list with any prescribed k legal exchange-shell pairs. -/
set_option autoImplicit false
namespace KroneckerRawBinaryLift
open KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring
open KroneckerThreeMixedPrograms KroneckerThreeProgramLifts KroneckerThreeMiddleExchange
open KroneckerRawBinaryEdits KroneckerRunWordSplice

noncomputable def liftRawBinary {u v : ℕ} {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hlen : pairs.length=k) (hp : LegalPairs 3 pairs) :
    ThreeProgram (shellPath u v (runWord R)) (collarPath pairs (shellPath u v (runWord S))) K k := by
  induction p generalizing pairs with
  | nil =>
    have hnil : pairs=[] := List.length_eq_zero_iff.mp hlen
    subst pairs
    exact .nil
  | @insert pre post K k p r hr ih =>
    have q := middleComplete pairs (ih pairs hlen hp) r (runWord pre).length hr
      (by simp [runWord] : (runWord pre).length≤(runWord (pre++post)).length)
    simpa only [complete_runWord] using q
  | @exchange pre post K k right p ih =>
    cases pairs with
    | nil => simp at hlen
    | cons xy pairs =>
      have ht : pairs.length=k := by simpa using hlen
      have hp' : LegalPairs 3 pairs := fun z hz => hp z (by simp [hz])
      have hxy := hp xy (by simp)
      exact middleExchange pairs pre post right (ih pairs ht hp') xy.1 xy.2 hxy.1 hxy.2

theorem raw_binary_realized {u v : ℕ} {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hlen : pairs.length=k) (hp : LegalPairs 3 pairs) :
    Nonempty (ThreeProgram (shellPath u v (runWord R))
      (collarPath pairs (shellPath u v (runWord S))) K k) := ⟨liftRawBinary p pairs hlen hp⟩

end KroneckerRawBinaryLift
end

/- Original module: KroneckerThreeLayerBudget -/
section
/-! Reserve one prescribed shell per exchange and enough remaining layers to drain all insertion/exchange surplus. -/
set_option autoImplicit false
namespace KroneckerThreeLayerBudget
open KroneckerCollarColoring

theorem three_layer_lengths {K k : ℕ} (pairs : List (ℕ×ℕ)) (hs : K+4*k≤pairs.length) :
    (pairs.drop (pairs.length-k)).length=k ∧ K+3*k≤(pairs.take (pairs.length-k)).length := by
  simp only [List.length_drop,List.length_take]
  omega

theorem legal_pairs_sublist {m : ℕ} {small large : List (ℕ×ℕ)}
    (hs : small.Sublist large) (hp : LegalPairs m large) : LegalPairs m small :=
  fun p h => hp p (hs.subset h)

end KroneckerThreeLayerBudget
end

/- Original module: KroneckerThreePrescribedCount -/
section
/-! The actual mixed binary edit comparison with any prescribed sufficiently long collar. -/
set_option autoImplicit false
namespace KroneckerThreePrescribedCount
open KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring KroneckerPrescribedLayerSplit
open KroneckerRawBinaryEdits KroneckerRawBinaryLift KroneckerThreeLayerBudget KroneckerThreeBufferedCount

theorem three_prescribed_count {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k≤pairs.length) :
    runCount 3 R 0≤8^k*pathCount 3 (collarPath pairs (shellPath u v (runWord S))) 0 := by
  let n := pairs.length-k
  have hl := three_layer_lengths pairs hs
  have he := legal_pairs_sublist (List.drop_sublist n pairs) hp
  have hd := legal_pairs_sublist (List.take_sublist n pairs) hp
  have hh := buffered_three_count hu hv (liftRawBinary p (pairs.drop n) hl.1 he)
    (pairs.take n) hd hl.2
  simpa only [runCount,← collarPath_append,List.take_append_drop] using hh

theorem three_prescribed_real {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k≤pairs.length) :
    (runCount 3 R 0 : ℝ)/(8 : ℝ)^k≤pathCount 3 (collarPath pairs (shellPath u v (runWord S))) 0 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<8^k)).mpr
  have hh := three_prescribed_count hu hv p pairs hp hs
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

end KroneckerThreePrescribedCount
end

/- Original module: KroneckerThreePrescribedRuns -/
section
/-! The full mixed comparison on arbitrary prescribed equal-length binary left/right collars. -/
set_option autoImplicit false
namespace KroneckerThreePrescribedRuns
open KroneckerWordCounts KroneckerColoredShell KroneckerPrescribedCollars
open KroneckerRawBinaryEdits KroneckerThreePrescribedCount

theorem three_prescribed_run_count {u v P K k : ℕ} (R S A B : List ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (ha : A.length=P) (hb : B.length=P) (hP : K+4*k≤P) :
    runCount 3 R 0≤8^k*runCount 3 (A++(u::S++[v])++B) 0 := by
  have hlen : A.length=B.length := by omega
  have hh := three_prescribed_count hu hv p (pairCollars A B)
    (pairCollars_legal 3 A B hA hB) (by rw [pairCollars_length A B hlen,ha]; exact hP)
  simpa only [shellPath_runWord,pairCollars_path A B _ hlen,runCount] using hh

theorem three_prescribed_run_real {u v P K k : ℕ} (R S A B : List ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (ha : A.length=P) (hb : B.length=P) (hP : K+4*k≤P) :
    (runCount 3 R 0 : ℝ)/(8 : ℝ)^k≤runCount 3 (A++(u::S++[v])++B) 0 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<8^k)).mpr
  have hh := three_prescribed_run_count R S A B hu hv p hA hB ha hb hP
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

end KroneckerThreePrescribedRuns
end

/- Original module: KroneckerRawBinaryAlphabet -/
section
/-! The raw mixed edit program preserves the actual binary run alphabet. -/
set_option autoImplicit false
namespace KroneckerRawBinaryAlphabet
open KroneckerBinaryExchangeShapes KroneckerRawBinaryEdits

theorem pairRuns_legal (right : Bool) : ∀ r∈pairRuns right, 1≤r ∧ r≤2 := by
  cases right <;> simp [pairRuns]

theorem raw_binary_alphabet {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (hR : ∀ r∈R, 1≤r ∧ r≤2) : ∀ r∈S, 1≤r ∧ r≤2 := by
  induction p with
  | nil => exact hR
  | insert p r hr ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x (List.mem_append_left _ hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact ih x (List.mem_append_right _ hx)
  | exchange right p ih =>
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact ih x (by simp [hx])
    · exact pairRuns_legal (!right) x hx
    · exact ih x (by simp [hx])

end KroneckerRawBinaryAlphabet
end

/- Original module: KroneckerThreeFullComposition -/
section
/-! Full literal binary insertion/exchange composition with the stated K+4k shell budget. -/
set_option autoImplicit false
namespace KroneckerThreeFullComposition
open KroneckerWordCounts KroneckerRawBinaryEdits KroneckerRawBinaryAlphabet KroneckerThreePrescribedRuns

theorem three_full_composition {u v P K k : ℕ} (R S A B : List ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (hR : ∀ r∈R, 1≤r ∧ r≤2) (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (ha : A.length=P) (hb : B.length=P) (hP : K+4*k≤P) :
    (∀ r∈A++(u::S++[v])++B, 1≤r ∧ r≤2) ∧
      (runCount 3 R 0 : ℝ)/(8 : ℝ)^k≤runCount 3 (A++(u::S++[v])++B) 0 := by
  constructor
  · have hS := raw_binary_alphabet p hR
    intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (hr | ((rfl | hr) | rfl)) | hr
    · exact hA r hr
    · exact hu
    · exact hS r hr
    · exact hv
    · exact hB r hr
  · exact three_prescribed_run_real R S A B hu hv p hA hB ha hb hP

end KroneckerThreeFullComposition
end
