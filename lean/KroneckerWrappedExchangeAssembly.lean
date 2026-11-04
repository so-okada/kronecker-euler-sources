import KroneckerZeroBinaryProgram

/- Original module: KroneckerZeroBinaryRecovery -/
section
/-! Draining adds no recovery code: retain the same k palette entries for the zero-surplus map. -/
set_option autoImplicit false
namespace KroneckerZeroBinaryRecovery
open KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusColoringFinite
open KroneckerBinaryExchangeProgram KroneckerBinaryProgramCode KroneckerBinaryProgramRecovery
open KroneckerCollarColoring KroneckerCollarRecovery KroneckerZeroBinaryProgram

theorem zeroBinary_target_code_injective {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length) :
    Function.Injective (fun g => (zeroBinary p pairs hp c hsize g,programCode p ⟨c,g⟩)) := by
  intro g h he
  have hout := (Prod.mk.inj he).1
  have hc := (Prod.mk.inj he).2
  have hh := congrArg (fun z : ConnectedColorings 3 (collarPath pairs (runWord S)) 0 =>
    recoverCollar pairs (runWord S) z.val) hout
  simp only [zeroBinary_recover] at hh
  have hr : runBinary p ⟨c,g⟩=runBinary p ⟨c,h⟩ := surplusForget_injective 3 (runWord S) hh
  have hin := program_target_code_injective p (Prod.ext hr hc)
  apply Subtype.ext
  exact congrArg surplusForget hin

end KroneckerZeroBinaryRecovery
end

/- Original module: KroneckerZeroBinaryCount -/
section
/-! The actual zero-surplus comparison loses at most the factor 8^k. -/
set_option autoImplicit false
namespace KroneckerZeroBinaryCount
open KroneckerWordCounts KroneckerBinaryExchangeProgram KroneckerBinaryProgramCode
open KroneckerCollarColoring KroneckerZeroBinaryProgram KroneckerZeroBinaryRecovery

theorem zeroBinary_fiber {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length)
    (b : ConnectedColorings 3 (collarPath pairs (runWord S)) 0) :
    Nat.card {g // zeroBinary p pairs hp c hsize g=b}≤8^k := by
  classical
  have hi : Function.Injective (fun g : {g // zeroBinary p pairs hp c hsize g=b} => programCode p ⟨c,g.val⟩) := by
    intro g h he
    apply Subtype.ext
    exact zeroBinary_target_code_injective p pairs hp c hsize
      (Prod.ext (g.property.trans h.property.symm) he)
  have hh := Fintype.card_le_of_injective _ hi
  simpa only [Nat.card_eq_fintype_card,code_card] using hh

theorem zeroBinary_count {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length) :
    runCount 3 R c≤8^k*pathCount 3 (collarPath pairs (runWord S)) 0 := by
  classical
  have hh := Fintype.card_le_of_injective _ (zeroBinary_target_code_injective p pairs hp c hsize)
  simpa only [runCount,pathCount,Fintype.card_prod,code_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

end KroneckerZeroBinaryCount
end

/- Original module: KroneckerBinaryCollarComparison -/
section
/-! Literal run-word counting after exchanges and arbitrary prescribed draining collars. -/
set_option autoImplicit false
namespace KroneckerBinaryCollarComparison
open KroneckerWordCounts KroneckerBinaryExchangeProgram KroneckerCollarColoring KroneckerZeroBinaryCount

theorem binary_collar_comparison {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length) :
    runCount 3 R c≤8^k*runCount 3 (pairs.map Prod.fst++S++(pairs.map Prod.snd).reverse) 0 := by
  simpa only [collarPath_runWord,runCount] using zeroBinary_count p pairs hp c hsize

theorem binary_collar_real_comparison {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length) :
    (runCount 3 R c : ℝ)/(8 : ℝ)^k≤
      runCount 3 (pairs.map Prod.fst++S++(pairs.map Prod.snd).reverse) 0 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<8^k)).mpr
  have hh := binary_collar_comparison p pairs hp c hsize
  exact_mod_cast (by simpa only [Nat.mul_comm] using hh)

theorem binary_total_shell_budget {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+4*k≤k+pairs.length) :
    (runCount 3 R c : ℝ)/(8 : ℝ)^k≤
      runCount 3 (pairs.map Prod.fst++S++(pairs.map Prod.snd).reverse) 0 :=
  binary_collar_real_comparison p pairs hp c (by omega)

end KroneckerBinaryCollarComparison
end

/- Original module: KroneckerBinaryExchangeColors -/
section
/-! Ordered palette retention for the literal binary-run exchange map. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeColors
open KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusPathTransport
open KroneckerColoredEdgeDictionary KroneckerEdgeShell KroneckerExchangeColorOrder
open KroneckerBinaryExchangeShapes KroneckerBinaryExchangeSpec KroneckerBinaryExchangeMap
open KroneckerWrappedExchangeColors

theorem transport_edges {m : ℕ} {U V : List Bool} (h : U=V) (a : SurplusColorings m U) :
    ofColoring V (transport h a).2.val=ofColoring U a.2.val := by
  subst V
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem binary_horizontal_colors (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (a : SurplusColorings 3 (runWord (rs++pairRuns right++ts))) :
    horizontalColors (ofColoring (runWord (u::(rs++pairRuns (!right)++ts)++[v]))
      (binaryExchange right rs ts u v hu hv a).2.val)=
    horizontalColors (edgeShell u v (by omega) (by omega) (by decide)
      (ofColoring (runWord (rs++pairRuns right++ts)) a.2.val)) := by
  have hh := exchangeMap_horizontal_colors (binarySpec right rs ts u v hu hv)
    (transport (binary_spec_source right rs ts u v hu hv).symm a)
  simpa only [binaryExchange, transport_edges, binarySpec] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem binary_vertical_colors (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (a : SurplusColorings 3 (runWord (rs++pairRuns right++ts))) :
    OneChange (verticalColors (edgeShell u v (by omega) (by omega) (by decide)
      (ofColoring (runWord (rs++pairRuns right++ts)) a.2.val)))
      (verticalColors (ofColoring (runWord (u::(rs++pairRuns (!right)++ts)++[v]))
        (binaryExchange right rs ts u v hu hv a).2.val)) := by
  have hh := exchangeMap_vertical_colors (binarySpec right rs ts u v hu hv)
    (transport (binary_spec_source right rs ts u v hu hv).symm a)
  simpa only [binaryExchange, transport_edges, binarySpec] using hh

end KroneckerBinaryExchangeColors
end

/- Original module: KroneckerWrappedExchangeAssembly -/
section
/-! The wrapped-exchange lemma on literal colored run words, with all recovery and surplus requirements. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeAssembly
open KroneckerWordCounts KroneckerProgramExecution KroneckerColoredEdgeDictionary
open KroneckerEdgeShell KroneckerExchangeColorOrder KroneckerBinaryExchangeShapes
open KroneckerBinaryExchangeMap KroneckerBinaryExchangeBound KroneckerBinaryExchangeColors

theorem wrapped_exchange_theorem (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    (∀ a, a.1≤(binaryExchange right rs ts u v hu hv a).1 ∧
      (binaryExchange right rs ts u v hu hv a).1≤a.1+3) ∧
    (∀ b, Nat.card {a // binaryExchange right rs ts u v hu hv a=b}≤8) ∧
    (∀ a, horizontalColors (ofColoring (runWord (u::(rs++pairRuns (!right)++ts)++[v]))
      (binaryExchange right rs ts u v hu hv a).2.val)=
      horizontalColors (edgeShell u v (by omega) (by omega) (by decide)
        (ofColoring (runWord (rs++pairRuns right++ts)) a.2.val))) ∧
    (∀ a, OneChange (verticalColors (edgeShell u v (by omega) (by omega) (by decide)
        (ofColoring (runWord (rs++pairRuns right++ts)) a.2.val)))
      (verticalColors (ofColoring (runWord (u::(rs++pairRuns (!right)++ts)++[v]))
        (binaryExchange right rs ts u v hu hv a).2.val))) :=
  ⟨binary_exchange_surplus right rs ts u v hu hv,
    binary_exchange_fiber right rs ts u v hu hv,
    binary_horizontal_colors right rs ts u v hu hv,
    binary_vertical_colors right rs ts u v hu hv⟩

end KroneckerWrappedExchangeAssembly
end
