import KroneckerHoleChains

/- Original module: KroneckerScaffoldBases -/
section
/-! Four singleton-hole shell contexts used by the scaffold induction. -/
set_option autoImplicit false
namespace KroneckerScaffoldBases
open KroneckerHoleGrammar

def FourContexts (w : List Piece) : Prop :=
  (∀ a b c d, Realized (.guard a :: .guard b :: w ++ [.guard c, .guard d])) ∧
  (∀ a b c, Realized (.guard a :: .guard b :: w ++ [.guard c])) ∧
  (∀ a b c d, Realized (.guard a :: w ++ [.guard b, .guard c, .guard d])) ∧
  (∀ a b c d e, Realized (.guard a :: .guard b :: .guard c :: w ++ [.guard d, .guard e]))

theorem singleton_four_contexts (X : List ℕ) : FourContexts [.hole X] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    exact Realized.unary a d (Realized.unary b c (Realized.hole X))
  · intro a b c
    exact Realized.binary a c (Realized.one b) (Realized.hole X)
  · intro a b c d
    exact Realized.binary a d (Realized.hole X) (Realized.two b c)
  · intro a b c d e
    exact Realized.unary a e (Realized.binary b d (Realized.one c) (Realized.hole X))

end KroneckerScaffoldBases
end

/- Original module: KroneckerScaffoldInduction -/
section
/-! Simultaneous realization of the four scaffold boundary states. -/
set_option autoImplicit false
namespace KroneckerScaffoldInduction
open KroneckerHoleGrammar KroneckerHoleChains KroneckerScaffoldBases

theorem chain_four_contexts (n : ℕ) : ∀ w, Chain w n → FourContexts w := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hc
    cases hc with
    | one X => exact singleton_four_contexts X
    | @prepend X p q r tail k ht =>
      have hk := chain_positive ht
      have htail := ih k (by omega) tail ht
      have hwhole := Chain.prepend X p q r ht
      obtain ⟨pre,s,t,u,Y,hpre,heq⟩ := chain_last hwhole (by omega)
      have hprefix := ih k (by omega) pre (by simpa using hpre)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a b c d
        have hx := Realized.unary b p (Realized.hole X)
        have hy := htail.2.1 q r c
        simpa [List.append_assoc] using Realized.binary a d hx hy
      · intro a b c
        rw [heq]
        have hx := hprefix.2.2.1 b s t u
        simpa [List.append_assoc] using Realized.binary a c hx (Realized.hole Y)
      · intro a b c d
        have hy := htail.2.2.2 p q r b c
        simpa [List.append_assoc] using Realized.binary a d (Realized.hole X) hy
      · intro a b c d e
        rw [heq]
        have hx := hprefix.1 b c s t
        have hy := Realized.unary u d (Realized.hole Y)
        simpa [List.append_assoc] using Realized.binary a e hx hy

end KroneckerScaffoldInduction
end

/- Original module: KroneckerScaffoldCounts -/
section
/-! The three-guard scaffold has at least the product of all independent
zero-surplus hole counts. -/
set_option autoImplicit false
namespace KroneckerScaffoldCounts
open KroneckerWordCounts KroneckerHoleGrammar KroneckerHoleChains KroneckerScaffoldInduction

theorem choices_eq_holes_prod (m : ℕ) (w : List Piece) :
    choices m w = ((holes w).map (fun X => runCount m X 0)).prod := by
  induction w with
  | nil => simp [choices, holes]
  | cons t w ih =>
    cases t with
    | guard r => simpa [choices, holes, pieceChoices] using ih
    | hole X =>
      change runCount m X 0 * choices m w =
        runCount m X 0 * ((holes w).map (fun Y => runCount m Y 0)).prod
      rw [ih]

theorem scaffold_realized {w : List Piece} {n : ℕ} (hw : Chain w n) (a b c d e f : ℕ) :
    Realized (.guard a :: .guard b :: .guard c :: w ++ [.guard d, .guard e, .guard f]) := by
  simpa [List.append_assoc] using
    Realized.unary a f ((chain_four_contexts n w hw).1 b c d e)

theorem scaffold_product_bound (m : ℕ) (hm : 3 ≤ m) {w : List Piece} {n : ℕ}
    (hw : Chain w n) (a b c d e f : ℕ)
    (hlegal : Legal m (.guard a :: .guard b :: .guard c :: w ++ [.guard d, .guard e, .guard f])) :
    ((holes w).map (fun X => runCount m X 0)).prod ≤
      runCount m (a :: b :: c :: expand w ++ [d,e,f]) 0 := by
  have h := grammar_count_bound m hm (scaffold_realized hw a b c d e f) hlegal
  have hchoices := choices_eq_holes_prod m w
  simp only [choices, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
    List.prod_append, List.prod_nil, pieceChoices, mul_one, one_mul] at h
  rw [← choices, hchoices] at h
  simpa [expand, pieceWord] using h

end KroneckerScaffoldCounts
end
