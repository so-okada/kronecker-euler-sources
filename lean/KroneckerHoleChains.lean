import KroneckerBinaryShell
import KroneckerTwoRun

/- Original module: KroneckerHoleGrammar -/
section
/-! A shell grammar with ordered, independently filled holes. Its lower bound
is a product of the actual colored counts of the hole words. -/
set_option autoImplicit false
namespace KroneckerHoleGrammar
open KroneckerWordCounts KroneckerColoredShell KroneckerBinaryShell

inductive Piece where
  | guard : ℕ → Piece
  | hole : List ℕ → Piece

def pieceWord : Piece → List ℕ
  | .guard r => [r]
  | .hole rs => rs

def expand (w : List Piece) : List ℕ := w.flatMap pieceWord

noncomputable def pieceChoices (m : ℕ) : Piece → ℕ
  | .guard _ => 1
  | .hole rs => runCount m rs 0

noncomputable def choices (m : ℕ) (w : List Piece) : ℕ := (w.map (pieceChoices m)).prod

def Legal (m : ℕ) (w : List Piece) : Prop :=
  ∀ t ∈ w, match t with
    | .guard r => 1 ≤ r ∧ r ≤ m-1
    | .hole _ => True

inductive Realized : List Piece → Prop where
  | hole (rs : List ℕ) : Realized [.hole rs]
  | one (r : ℕ) : Realized [.guard r]
  | two (u v : ℕ) : Realized [.guard u, .guard v]
  | unary (u v : ℕ) {w : List Piece} : Realized w → Realized (.guard u :: w ++ [.guard v])
  | binary (u v : ℕ) {w z : List Piece} :
      Realized w → Realized z → Realized (.guard u :: (w ++ z) ++ [.guard v])

theorem expand_append (w z : List Piece) : expand (w ++ z) = expand w ++ expand z := by
  simp [expand]

theorem choices_append (m : ℕ) (w z : List Piece) : choices m (w ++ z) = choices m w * choices m z := by
  simp [choices, List.prod_append]

theorem grammar_count_bound (m : ℕ) (hm : 3 ≤ m) {w : List Piece} (hw : Realized w)
    (hlegal : Legal m w) : choices m w ≤ runCount m (expand w) 0 := by
  induction hw with
  | hole rs => simp [choices, pieceChoices, expand, pieceWord]
  | one r =>
    have hr := hlegal (.guard r) (by simp)
    have h := KroneckerOneRun.one_run_lower_bound (m := m) (r := r) hr.1 (by omega)
    simpa [choices, pieceChoices, expand, pieceWord] using (show 1 ≤ runCount m [r] 0 by omega)
  | two u v =>
    have hu := hlegal (.guard u) (by simp)
    have hv := hlegal (.guard v) (by simp)
    have h := KroneckerTwoRun.two_run_lower_bound hm hu hv
    simpa [choices, pieceChoices, expand, pieceWord] using (show 1 ≤ runCount m [u,v] 0 by omega)
  | @unary u v w hw ih =>
    have hu := hlegal (.guard u) (by simp)
    have hv := hlegal (.guard v) (by simp)
    have hin := ih (fun t ht => hlegal t (by simp [ht]))
    have hout := unary_runCount_le u v 0 hm hu hv (expand w)
    simpa [choices, pieceChoices, expand, pieceWord] using hin.trans hout
  | @binary u v w z hw hz ihw ihz =>
    have hu := hlegal (.guard u) (by simp)
    have hv := hlegal (.guard v) (by simp)
    have hinw := ihw (fun t ht => hlegal t (by simp [ht]))
    have hinz := ihz (fun t ht => hlegal t (by simp [ht]))
    have hprod := Nat.mul_le_mul hinw hinz
    have hout := binary_runCount_bound u v 0 0 hm hu hv (expand w) (expand z)
    simpa [choices, pieceChoices, expand, pieceWord, List.prod_append] using hprod.trans hout

end KroneckerHoleGrammar
end

/- Original module: KroneckerHoleChains -/
section
/-! Ordered holes separated by three arbitrary guard runs. -/
set_option autoImplicit false
namespace KroneckerHoleChains
open KroneckerHoleGrammar

inductive Chain : List Piece → ℕ → Prop where
  | one (X : List ℕ) : Chain [.hole X] 1
  | prepend (X : List ℕ) (a b c : ℕ) {w : List Piece} {n : ℕ} :
      Chain w n → Chain (.hole X :: .guard a :: .guard b :: .guard c :: w) (n+1)

def holes (w : List Piece) : List (List ℕ) := w.flatMap fun t => match t with
  | .guard _ => []
  | .hole X => [X]

theorem chain_positive {w : List Piece} {n : ℕ} (h : Chain w n) : 1 ≤ n := by
  cases h <;> omega

theorem chain_holes_length {w : List Piece} {n : ℕ} (h : Chain w n) : (holes w).length = n := by
  induction h with
  | one X => simp [holes]
  | @prepend X a b c w n h ih =>
    change (holes w).length+1 = n+1
    omega

theorem chain_last {w : List Piece} {n : ℕ} (h : Chain w n) (hn : 2 ≤ n) :
    ∃ p a b c X, Chain p (n-1) ∧ w = p ++ [.guard a, .guard b, .guard c, .hole X] := by
  induction h with
  | one X => omega
  | @prepend X a b c w n hw ih =>
    have hnpos := chain_positive hw
    by_cases hn1 : n = 1
    · subst n
      cases hw with
      | one Y => exact ⟨[.hole X], a, b, c, Y, Chain.one X, rfl⟩
      | @prepend Y d e f z k hz =>
        have hk := chain_positive hz
        omega
    · obtain ⟨p,d,e,f,Y,hp,heq⟩ := ih (by omega)
      refine ⟨.hole X :: .guard a :: .guard b :: .guard c :: p, d,e,f,Y, ?_, ?_⟩
      · have hnew := Chain.prepend X a b c hp
        have hsub : n-1+1=n := by omega
        simpa [hsub] using hnew
      · simp [heq]

end KroneckerHoleChains
end
