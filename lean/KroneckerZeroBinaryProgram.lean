import KroneckerCanonicalExchange
import KroneckerResidualColoringFinite

/- Original module: KroneckerBinaryExchangeShapes -/
section
/-! A binary-run 12/21 exchange is precisely the proved single-edge adjacent move. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeShapes
open KroneckerStack KroneckerWordCounts KroneckerExchangePath

def binaryPrefix : List ℕ → List Bool
  | [] => [false]
  | r::rs => List.replicate r false++(runWord rs++[true,false])

def pairRuns (right : Bool) : List ℕ := if right then [1,2] else [2,1]

theorem binary_source (right : Bool) (rs ts : List ℕ) :
    sourcePath right (binaryPrefix rs) (false::runWord ts)=runWord (rs++pairRuns right++ts) := by
  cases right <;> cases rs <;>
    simp [sourcePath,binaryPrefix,pairRuns,runWord,runShape,List.replicate_succ,List.append_assoc]

theorem binary_target (right : Bool) (rs ts : List ℕ) :
    targetPath right (binaryPrefix rs) (false::runWord ts)=runWord (rs++pairRuns (!right)++ts) :=
  binary_source (!right) rs ts

end KroneckerBinaryExchangeShapes
end

/- Original module: KroneckerWrappedExchangeWitness -/
section
/-! Choose only among actual constructed exchange witnesses on the union of all surplus classes. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeWitness
open KroneckerStack KroneckerColoring KroneckerColoredShell KroneckerColoredEdges
open KroneckerColoredEdgeDictionary KroneckerExchangePath KroneckerColoredExchangeRelation
open KroneckerEdgeShell KroneckerProgramExecution KroneckerWrappedRightExistence KroneckerWrappedLeftExistence

structure ExchangeSpec (m : ℕ) where
  right : Bool
  P : List Bool
  Q : List Bool
  u : ℕ
  v : ℕ
  hu : u+1≤m
  hv : v-1≤m
  hm : 2≤m
  hpos : 1≤v

def ExchangeSpec.source {m : ℕ} (s : ExchangeSpec m) : List Bool := sourcePath s.right s.P s.Q
def ExchangeSpec.target {m : ℕ} (s : ExchangeSpec m) : List Bool :=
  shellPath s.u s.v (targetPath s.right s.P s.Q)

structure Witness {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) where
  middle : List (CEdge m)
  code : Palette m
  delta : ℕ
  exchange : Exchange s.right (s.P.length+1) (ofColoring s.source a.2.val) middle code delta
  shape : coloredShape middle=targetPath s.right s.P s.Q
  connected : Connected m (coloredWord (edgeShell s.u s.v s.hu s.hv s.hm middle)) (a.1+delta)
  delta_exact : delta = KroneckerCanonicalExchange.repairDelta s.right (s.P.length+1)
    (coloredWord (ofColoring s.source a.2.val))

theorem witness_exists {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    Nonempty (Witness s a) := by
  have hc : Connected m (coloredWord (ofColoring s.source a.2.val)) a.1 := by
    rw [ofColoring_word]
    exact a.2.property
  have hs := ofColoring_shape s.source a.2.val
  have hh : ∃ ds code d, Exchange s.right (s.P.length+1) (ofColoring s.source a.2.val) ds code d ∧
      coloredShape ds=targetPath s.right s.P s.Q ∧
      Connected m (coloredWord (edgeShell s.u s.v s.hu s.hv s.hm ds)) (a.1+d) ∧
      d = KroneckerCanonicalExchange.repairDelta s.right (s.P.length+1)
        (coloredWord (ofColoring s.source a.2.val)) := by
    cases hr : s.right with
    | false =>
      obtain ⟨ds,code,d,he,hshape,hconn⟩ := wrapped_left_exists s.P s.Q s.u s.v s.hu s.hv s.hm _
        (by simpa [ExchangeSpec.source,hr] using hs) hc
      exact ⟨ds,code,d,he,hshape,hconn,KroneckerCanonicalExchange.left_delta he⟩
    | true =>
      exact KroneckerCanonicalExchange.wrapped_right_exact s.P s.Q s.u s.v s.hu s.hv s.hm _
        (by simpa [ExchangeSpec.source,hr] using hs) hc
  obtain ⟨ds,code,d,he,hshape,hconn,hd⟩ := hh
  exact ⟨⟨ds,code,d,he,hshape,hconn,hd⟩⟩

noncomputable def chosen {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) : Witness s a :=
  Classical.choice (witness_exists s a)

end KroneckerWrappedExchangeWitness
end

/- Original module: KroneckerWrappedExchangeMap -/
section
/-! The actual finite colored wrapped-exchange map, with its surplus interval. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeMap
open KroneckerColoring KroneckerColoredEdges KroneckerColoredEdgeDictionary KroneckerEdgeShell
open KroneckerColoredExchangeRelation KroneckerProgramExecution KroneckerWrappedExchangeWitness

theorem chosen_output_shape {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    coloredShape (edgeShell s.u s.v s.hu s.hv s.hm (chosen s a).middle)=s.target := by
  rw [edgeShell_shape _ _ _ _ _ s.hpos,(chosen s a).shape]
  rfl

noncomputable def exchangeMap {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    SurplusColorings m s.target :=
  ⟨a.1+(chosen s a).delta,
    ⟨toColoring _ (chosen_output_shape s a),by rw [toColoring_word]; exact (chosen s a).connected⟩⟩

noncomputable def exchangeCode {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) : Palette m :=
  (chosen s a).code

theorem exchangeMap_edges {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    ofColoring s.target (exchangeMap s a).2.val=edgeShell s.u s.v s.hu s.hv s.hm (chosen s a).middle :=
  of_toColoring _ (chosen_output_shape s a)

/-- The actual selected map uses the manuscript's deterministic repair word. -/
theorem exchangeMap_repairWord {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    coloredWord (ofColoring s.target (exchangeMap s a).2.val) =
      KroneckerCanonicalExchange.repairWord s.right (s.u+1+(s.P.length+1))
        (coloredWord (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring s.source a.2.val))) := by
  rw [exchangeMap_edges]
  have he := (chosen s a).exchange
  have hc := KroneckerCanonicalExchange.exchange_context he
    (edgePrefix m s.u s.hu) (edgeSuffix m s.v s.hv s.hm)
  have hd := (chosen s a).delta_exact.trans
    (KroneckerCanonicalExchange.repairDelta_context he
      (edgePrefix m s.u s.hu) (edgeSuffix m s.v s.hv s.hm)).symm
  have hh := KroneckerCanonicalExchange.exchange_word_exact hc hd
  simpa [edgeShell,edgePrefix] using hh

theorem exchangeMap_surplus {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    a.1≤(exchangeMap s a).1 ∧ (exchangeMap s a).1≤a.1+m := by
  have hd := exchange_budget (chosen s a).exchange
  change a.1≤a.1+(chosen s a).delta ∧ a.1+(chosen s a).delta≤a.1+m
  omega

end KroneckerWrappedExchangeMap
end

/- Original module: KroneckerWrappedExchangeRecovery -/
section
/-! Recover an input in the union of surplus classes from the wrapped output and one palette. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeRecovery
open KroneckerColoring KroneckerColoredEdges KroneckerColoredEdgeDictionary
open KroneckerColoredExchangeRelation KroneckerColoredExchangeRecovery KroneckerEdgeShellRecovery
open KroneckerProgramExecution KroneckerSurplusColoringFinite KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap

def decodeWrapped {m : ℕ} (s : ExchangeSpec m) (b : SurplusColorings m s.target) (p : Palette m) :
    List (CEdge m) :=
  decodeAt s.right (s.P.length+1) (unshell s.u s.source.length (ofColoring s.target b.2.val)) p

theorem chosen_middle_length {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    (chosen s a).middle.length=s.source.length := by
  have hh := exchange_length (chosen s a).exchange
  have hs := congrArg List.length (ofColoring_shape s.source a.2.val)
  simp only [coloredShape,List.length_map] at hs
  omega

theorem decode_exchangeMap {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    decodeWrapped s (exchangeMap s a) (exchangeCode s a)=ofColoring s.source a.2.val := by
  unfold decodeWrapped
  rw [exchangeMap_edges]
  have hh := unshell_edgeShell s.u s.v s.hu s.hv s.hm (chosen s a).middle
  rw [chosen_middle_length] at hh
  rw [hh]
  exact exchange_recovery (chosen s a).exchange

theorem exchange_target_code_injective {m : ℕ} (s : ExchangeSpec m) :
    Function.Injective (fun a : SurplusColorings m s.source => (exchangeMap s a,exchangeCode s a)) := by
  intro a b he
  have hh := Prod.mk.inj he
  apply surplusForget_injective m s.source
  apply ofColoring_injective s.source
  change ofColoring s.source a.2.val=ofColoring s.source b.2.val
  calc
    _=decodeWrapped s (exchangeMap s a) (exchangeCode s a) := (decode_exchangeMap s a).symm
    _=decodeWrapped s (exchangeMap s b) (exchangeCode s b) := by rw [hh.1,hh.2]
    _=_ := decode_exchangeMap s b

end KroneckerWrappedExchangeRecovery
end

/- Original module: KroneckerWrappedExchangeFiber -/
section
/-! The actual wrapped map has at most 2^m preimages, even across different input surpluss. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeFiber
open KroneckerColoring KroneckerWeights KroneckerProgramExecution KroneckerSurplusColoringFinite
open KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap KroneckerWrappedExchangeRecovery

theorem exchange_fiber_code_injective {m : ℕ} (s : ExchangeSpec m) (b : SurplusColorings m s.target) :
    Function.Injective (fun a : {a // exchangeMap s a=b} => exchangeCode s a.val) := by
  intro a a' he
  apply Subtype.ext
  apply exchange_target_code_injective s
  exact Prod.ext (a.property.trans a'.property.symm) he

theorem exchange_fiber_bound {m : ℕ} (s : ExchangeSpec m) (b : SurplusColorings m s.target) :
    Nat.card {a // exchangeMap s a=b}≤2^m := by
  classical
  rw [Nat.card_eq_fintype_card,← palette_card]
  exact Fintype.card_le_of_injective _ (exchange_fiber_code_injective s b)

theorem exchange_total_count {m : ℕ} (s : ExchangeSpec m) :
    Nat.card (SurplusColorings m s.source)≤2^m*Nat.card (SurplusColorings m s.target) := by
  have hh := Fintype.card_le_of_injective _ (exchange_target_code_injective s)
  simpa only [Fintype.card_prod,palette_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

theorem three_arrow_fiber (s : ExchangeSpec 3) (b : SurplusColorings 3 s.target) :
    Nat.card {a // exchangeMap s a=b}≤8 := by
  simpa using exchange_fiber_bound s b

end KroneckerWrappedExchangeFiber
end

/- Original module: KroneckerWrappedExchangeColors -/
section
/-! The actual map satisfies the manuscript's ordered color-retention statements. -/
set_option autoImplicit false
namespace KroneckerWrappedExchangeColors
open KroneckerColoredEdgeDictionary KroneckerEdgeShell KroneckerExchangeColorOrder
open KroneckerProgramExecution KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap

theorem exchangeMap_horizontal_colors {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    horizontalColors (ofColoring s.target (exchangeMap s a).2.val)=
      horizontalColors (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring s.source a.2.val)) := by
  rw [exchangeMap_edges]
  have hh := (exchange_horizontal_colors (chosen s a).exchange).symm
  simpa [edgeShell,horizontalColors] using hh

theorem exchangeMap_vertical_colors {m : ℕ} (s : ExchangeSpec m) (a : SurplusColorings m s.source) :
    OneChange (verticalColors (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring s.source a.2.val)))
      (verticalColors (ofColoring s.target (exchangeMap s a).2.val)) := by
  rw [exchangeMap_edges]
  have hh := exchange_vertical_colors (chosen s a).exchange
  simpa [edgeShell,verticalColors] using oneChange_append_left
    (oneChange_append_right hh (verticalColors (edgeSuffix m s.v s.hv s.hm)))
    (verticalColors (edgePrefix m s.u s.hu))

end KroneckerWrappedExchangeColors
end

/- Original module: KroneckerBinaryExchangeSpec -/
section
/-! Every binary outer-shell prescription instantiates the actual three-arrow exchange map. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeSpec
open KroneckerStack KroneckerWordCounts KroneckerColoredShell KroneckerExchangePath
open KroneckerBinaryExchangeShapes KroneckerWrappedExchangeWitness

def binarySpec (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) : ExchangeSpec 3 :=
  ⟨right,binaryPrefix rs,false::runWord ts,u,v,by omega,by omega,by decide,hv.1⟩

theorem binary_spec_source (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    (binarySpec right rs ts u v hu hv).source=runWord (rs++pairRuns right++ts) :=
  binary_source right rs ts

theorem binary_spec_target (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    (binarySpec right rs ts u v hu hv).target=runWord (u::(rs++pairRuns (!right)++ts)++[v]) := by
  change shellPath u v (targetPath right (binaryPrefix rs) (false::runWord ts))=_
  rw [binary_target,shellPath_runWord]

end KroneckerBinaryExchangeSpec
end

/- Original module: KroneckerSurplusPathTransport -/
section
/-! Transport the actual surplus coloring type across a proved path identity. -/
set_option autoImplicit false
namespace KroneckerSurplusPathTransport
open KroneckerProgramExecution

def transport {m : ℕ} {U V : List Bool} (h : U=V) (a : SurplusColorings m U) :
    SurplusColorings m V := h ▸ a

theorem transport_surplus {m : ℕ} {U V : List Bool} (h : U=V) (a : SurplusColorings m U) :
    (transport h a).1=a.1 := by subst V; rfl

theorem transport_inverse {m : ℕ} {U V : List Bool} (h : U=V) (a : SurplusColorings m U) :
    transport h.symm (transport h a)=a := by subst V; rfl

theorem transport_injective {m : ℕ} {U V : List Bool} (h : U=V) :
    Function.Injective (@transport m U V h) := by
  intro a b he
  have hh := congrArg (transport h.symm) he
  simpa only [transport_inverse] using hh

end KroneckerSurplusPathTransport
end

/- Original module: KroneckerBinaryExchangeMap -/
section
/-! The three-arrow map on the literal run words in the manuscript. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeMap
open KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusPathTransport
open KroneckerBinaryExchangeShapes KroneckerBinaryExchangeSpec
open KroneckerWrappedExchangeMap KroneckerWrappedExchangeRecovery

noncomputable def binaryExchange (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (a : SurplusColorings 3 (runWord (rs++pairRuns right++ts))) :
    SurplusColorings 3 (runWord (u::(rs++pairRuns (!right)++ts)++[v])) :=
  transport (binary_spec_target right rs ts u v hu hv)
    (exchangeMap (binarySpec right rs ts u v hu hv)
      (transport (binary_spec_source right rs ts u v hu hv).symm a))

noncomputable def binaryCode (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (a : SurplusColorings 3 (runWord (rs++pairRuns right++ts))) : KroneckerColoring.Palette 3 :=
  exchangeCode (binarySpec right rs ts u v hu hv)
    (transport (binary_spec_source right rs ts u v hu hv).symm a)

theorem binary_exchange_surplus (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (a : SurplusColorings 3 (runWord (rs++pairRuns right++ts))) :
    a.1≤(binaryExchange right rs ts u v hu hv a).1 ∧
      (binaryExchange right rs ts u v hu hv a).1≤a.1+3 := by
  simpa only [binaryExchange,transport_surplus] using
    exchangeMap_surplus (binarySpec right rs ts u v hu hv)
      (transport (binary_spec_source right rs ts u v hu hv).symm a)

theorem binary_target_code_injective (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    Function.Injective (fun a => (binaryExchange right rs ts u v hu hv a,binaryCode right rs ts u v hu hv a)) := by
  intro a b he
  apply transport_injective (binary_spec_source right rs ts u v hu hv).symm
  apply exchange_target_code_injective (binarySpec right rs ts u v hu hv)
  apply Prod.ext
  · exact transport_injective (binary_spec_target right rs ts u v hu hv) (congrArg Prod.fst he)
  · change binaryCode right rs ts u v hu hv a=binaryCode right rs ts u v hu hv b
    exact (Prod.mk.inj he).2

end KroneckerBinaryExchangeMap
end

/- Original module: KroneckerBinaryExchangeBound -/
section
/-! The literal 12/21 exchange has surplus increase at most three and fibers at most eight. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeBound
open KroneckerColoring KroneckerWeights KroneckerWordCounts KroneckerProgramExecution
open KroneckerSurplusColoringFinite KroneckerBinaryExchangeShapes KroneckerBinaryExchangeMap

theorem binary_exchange_fiber (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2)
    (b : SurplusColorings 3 (runWord (u::(rs++pairRuns (!right)++ts)++[v]))) :
    Nat.card {a // binaryExchange right rs ts u v hu hv a=b}≤8 := by
  classical
  have hi : Function.Injective (fun a : {a // binaryExchange right rs ts u v hu hv a=b} =>
      binaryCode right rs ts u v hu hv a.val) := by
    intro a a' he
    apply Subtype.ext
    apply binary_target_code_injective right rs ts u v hu hv
    exact Prod.ext (a.property.trans a'.property.symm) he
  have hh := Fintype.card_le_of_injective _ hi
  simpa only [palette_card, Nat.card_eq_fintype_card, show (2 : ℕ)^3 = 8 from rfl] using hh

theorem binary_exchange_count (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
    Nat.card (SurplusColorings 3 (runWord (rs++pairRuns right++ts)))≤
      8*Nat.card (SurplusColorings 3 (runWord (u::(rs++pairRuns (!right)++ts)++[v]))) := by
  have hh := Fintype.card_le_of_injective _ (binary_target_code_injective right rs ts u v hu hv)
  simpa only [Fintype.card_prod, palette_card, Nat.card_eq_fintype_card,
    show (2 : ℕ)^3 = 8 from rfl, Nat.mul_comm] using hh

end KroneckerBinaryExchangeBound
end

/- Original module: KroneckerBinaryExchangeProgram -/
section
/-! Prescribed finite programs of actual binary exchanges, with their own prescribed shells. -/
set_option autoImplicit false
namespace KroneckerBinaryExchangeProgram
open KroneckerWordCounts KroneckerProgramExecution KroneckerBinaryExchangeShapes KroneckerBinaryExchangeMap

inductive BinaryProgram (R : List ℕ) : List ℕ → ℕ → Type
  | nil : BinaryProgram R R 0
  | step {k : ℕ} (right : Bool) (rs ts : List ℕ)
      (p : BinaryProgram R (rs++pairRuns right++ts) k) (u v : ℕ)
      (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) :
      BinaryProgram R (u::(rs++pairRuns (!right)++ts)++[v]) (k+1)

noncomputable def runBinary {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (a : SurplusColorings 3 (runWord R)) : SurplusColorings 3 (runWord S) :=
  match p with
  | .nil => a
  | .step right rs ts p u v hu hv => binaryExchange right rs ts u v hu hv (runBinary p a)

theorem runBinary_nil (R : List ℕ) (a : SurplusColorings 3 (runWord R)) :
    runBinary (.nil : BinaryProgram R R 0) a=a := rfl

theorem binary_program_run_length {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k) :
    S.length=R.length+2*k := by
  induction p with
  | nil => simp
  | step right rs ts p u v hu hv ih =>
    cases right <;> simp [pairRuns] at ih ⊢ <;> omega

end KroneckerBinaryExchangeProgram
end

/- Original module: KroneckerBinaryProgramCode -/
section
/-! Exactly one eight-valued palette code per prescribed binary exchange. -/
set_option autoImplicit false
namespace KroneckerBinaryProgramCode
open KroneckerColoring KroneckerWeights KroneckerWordCounts KroneckerProgramExecution
open KroneckerBinaryExchangeMap KroneckerBinaryExchangeProgram

def Code : ℕ → Type
  | 0 => Unit
  | k+1 => Code k × Palette 3

instance codeFinite (k : ℕ) : Finite (Code k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ k ih => exact inferInstanceAs (Finite (Code k × Palette 3))

noncomputable instance codeFintype (k : ℕ) : Fintype (Code k) := Fintype.ofFinite _

theorem code_card (k : ℕ) : Fintype.card (Code k)=8^k := by
  induction k with
  | zero =>
    let : Unique (Code 0) := inferInstanceAs (Unique Unit)
    exact Fintype.card_unique
  | succ k ih =>
    calc
      Fintype.card (Code (k+1))=Fintype.card (Code k × Palette 3) := Fintype.card_congr (Equiv.refl _)
      _=8^(k+1) := by
        rw [Fintype.card_prod,ih,palette_card]
        norm_num [pow_succ]

noncomputable def programCode {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (a : SurplusColorings 3 (runWord R)) : Code k :=
  match p with
  | .nil => ()
  | .step right rs ts p u v hu hv =>
    (programCode p a,binaryCode right rs ts u v hu hv (runBinary p a))

theorem programCode_nil (R : List ℕ) (a : SurplusColorings 3 (runWord R)) :
    programCode (.nil : BinaryProgram R R 0) a=() := rfl

end KroneckerBinaryProgramCode
end

/- Original module: KroneckerBinaryProgramRecovery -/
section
/-! Reverse each actual exchange to recover the entire original surplus coloring. -/
set_option autoImplicit false
namespace KroneckerBinaryProgramRecovery
open KroneckerWordCounts KroneckerProgramExecution KroneckerBinaryExchangeMap
open KroneckerBinaryExchangeProgram KroneckerBinaryProgramCode

theorem program_target_code_injective {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k) :
    Function.Injective (fun a => (runBinary p a,programCode p a)) := by
  induction p with
  | nil =>
    intro a b he
    exact congrArg Prod.fst he
  | step right rs ts p u v hu hv ih =>
    intro a b he
    have hout := congrArg Prod.fst he
    have hcode := congrArg Prod.snd he
    change (programCode p a,binaryCode right rs ts u v hu hv (runBinary p a))=
      (programCode p b,binaryCode right rs ts u v hu hv (runBinary p b)) at hcode
    have hlast : runBinary p a=runBinary p b :=
      binary_target_code_injective right rs ts u v hu hv (Prod.ext hout (Prod.mk.inj hcode).2)
    exact ih (Prod.ext hlast (Prod.mk.inj hcode).1)

end KroneckerBinaryProgramRecovery
end

/- Original module: KroneckerBinaryProgramSurplus -/
section
/-! The actual surplus increase of k prescribed exchanges is at most 3k. -/
set_option autoImplicit false
namespace KroneckerBinaryProgramSurplus
open KroneckerWordCounts KroneckerProgramExecution KroneckerBinaryExchangeMap KroneckerBinaryExchangeProgram

theorem binary_program_surplus {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (a : SurplusColorings 3 (runWord R)) : a.1≤(runBinary p a).1 ∧ (runBinary p a).1≤a.1+3*k := by
  induction p with
  | nil => simp [runBinary]
  | step right rs ts p u v hu hv ih =>
    have hh := binary_exchange_surplus right rs ts u v hu hv (runBinary p a)
    change a.1≤(binaryExchange right rs ts u v hu hv (runBinary p a)).1 ∧
      (binaryExchange right rs ts u v hu hv (runBinary p a)).1≤_
    omega

end KroneckerBinaryProgramSurplus
end

/- Original module: KroneckerBinaryProgramFiber -/
section
/-! A program of k actual exchanges has at most 8^k preimages across all surplus classes. -/
set_option autoImplicit false
namespace KroneckerBinaryProgramFiber
open KroneckerWordCounts KroneckerProgramExecution KroneckerSurplusColoringFinite
open KroneckerBinaryExchangeProgram KroneckerBinaryProgramCode KroneckerBinaryProgramRecovery

theorem binary_program_fiber {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (b : SurplusColorings 3 (runWord S)) : Nat.card {a // runBinary p a=b}≤8^k := by
  classical
  have hi : Function.Injective (fun a : {a // runBinary p a=b} => programCode p a.val) := by
    intro a a' he
    apply Subtype.ext
    exact program_target_code_injective p (Prod.ext (a.property.trans a'.property.symm) he)
  have hh := Fintype.card_le_of_injective _ hi
  simpa only [Nat.card_eq_fintype_card,code_card] using hh

theorem binary_program_count {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k) :
    Nat.card (SurplusColorings 3 (runWord R))≤8^k*Nat.card (SurplusColorings 3 (runWord S)) := by
  have hh := Fintype.card_le_of_injective _ (program_target_code_injective p)
  simpa only [Fintype.card_prod,code_card,Nat.card_eq_fintype_card,Nat.mul_comm] using hh

end KroneckerBinaryProgramFiber
end

/- Original module: KroneckerZeroBinaryProgram -/
section
/-! Drain the actual exchange-program output using enough prescribed binary collar layers. -/
set_option autoImplicit false
namespace KroneckerZeroBinaryProgram
open KroneckerWordCounts KroneckerProgramExecution KroneckerBinaryExchangeProgram KroneckerBinaryProgramSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroBinary {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length)
    (g : ConnectedColorings 3 (runWord R) c) : ConnectedColorings 3 (collarPath pairs (runWord S)) 0 := by
  let r := runBinary p ⟨c,g⟩
  have hr := (binary_program_surplus p ⟨c,g⟩).2
  change (runBinary p ⟨c,g⟩).1≤c+3*k at hr
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by decide) pairs hp r.1 (runWord S) r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by decide) pairs hp r.1 (runWord S) r.2.val r.2.property

theorem zeroBinary_recover {R S : List ℕ} {k : ℕ} (p : BinaryProgram R S k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (c : ℕ) (hsize : c+3*k≤pairs.length)
    (g : ConnectedColorings 3 (runWord R) c) :
    recoverCollar pairs (runWord S) (zeroBinary p pairs hp c hsize g).val=(runBinary p ⟨c,g⟩).2.val :=
  recover_collarColoring (by decide) pairs hp _ _ _

end KroneckerZeroBinaryProgram
end
