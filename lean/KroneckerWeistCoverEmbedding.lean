import Mathlib.GroupTheory.FreeGroup.Basic
import KroneckerUniversalWordBaseProjection

/- Original module: KroneckerWeistSignedWords -/
section
/-! Signed free-group words for Weist's universal-cover presentation.
An arrow appends its generator on the right at a source and its inverse at a
sink. This module embeds the project's reduced-color tree faithfully. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistSignedWords
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerWordParity

abbrev GroupWord := FreeGroup Color

def signed (c : Color) (n : ℕ) : GroupWord :=
  if n % 2 = 0 then FreeGroup.of c else (FreeGroup.of c)⁻¹

theorem signed_succ (c : Color) (n : ℕ) : signed c (n+1) = (signed c n)⁻¹ := by
  have hn : n % 2 < 2 := Nat.mod_lt n (by decide)
  by_cases h : n % 2 = 0
  · have h' : (n+1)%2 ≠ 0 := by omega
    simp [signed,h,h']
  · have h' : (n+1)%2 = 0 := by omega
    simp [signed,h,h']

def encodeList : List Color → GroupWord
  | [] => 1
  | c::l => encodeList l * signed c l.length

def encode (w : Word) : GroupWord := encodeList w.val

theorem encode_toggleList (c : Color) (l : List Color) :
    encodeList (toggleList c l) = encodeList l * signed c l.length := by
  cases l with
  | nil => simp [toggleList,encodeList]
  | cons d l =>
    by_cases h : c=d
    · subst d
      simp [toggleList,encodeList,signed_succ,mul_assoc]
    · simp [toggleList,h,encodeList]

theorem encode_toggle (c : Color) (w : Word) :
    encode (toggle c w) = encode w * signed c w.val.length :=
  encode_toggleList c w.val

def generatorPerm (c : Color) : Equiv.Perm Word where
  toFun := toggle c
  invFun := toggle c
  left_inv := toggle_involution c
  right_inv := toggle_involution c

def decode (g : GroupWord) : Word := (FreeGroup.lift generatorPerm g⁻¹) root

theorem decode_mul_signed (g : GroupWord) (c : Color) (n : ℕ) :
    decode (g * signed c n) = toggle c (decode g) := by
  by_cases h : n%2=0 <;>
    simp [decode,signed,h,map_mul,Equiv.Perm.mul_apply,generatorPerm] <;> rfl

theorem decode_encodeList (l : List Color) : decode (encodeList l) = normal l := by
  induction l with
  | nil => simp [encodeList,decode,normal,act]
  | cons c l ih =>
    rw [encodeList,decode_mul_signed,ih]
    rfl

theorem decode_encode (w : Word) : decode (encode w) = w :=
  (decode_encodeList w.val).trans (normal_reduced w)

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

end KroneckerWeistSignedWords
end
end

/- Original module: KroneckerWeistCoverEmbedding -/
section
/-! Weist's (vertex, free word) cover, with right-appended arrow generators.
The project's connected cover embeds as an actual color-preserving quiver map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistCoverEmbedding
open KroneckerWeistSignedWords KroneckerReducedColorWords KroneckerWordParity
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerUniversalWordBaseProjection

def cover : TypedQuiver where
  V := Fin 2 × GroupWord
  A := Color × GroupWord
  source e := (0,e.2)
  target e := (1,e.2 * FreeGroup.of e.1)

def vertex (w : Word) : cover.V := (baseVertex w,encode w)

theorem source_step (c : Color) (w : Word) (h : parity w = 0) :
    encode (toggle c w) = encode w * FreeGroup.of c := by
  rw [encode_toggle]
  change encode w * (if parity w = 0 then _ else _) = _
  rw [ite_eq_left h]

theorem sink_step (c : Color) (w : Word) (h : parity w = 1) :
    encode (toggle c w) = encode w * (FreeGroup.of c)⁻¹ := by
  rw [encode_toggle]
  change encode w * (if parity w = 0 then _ else _) = _
  rw [ite_eq_right (by omega)]

def embedding : QuiverMap coloredCoverQuiver cover where
  vertex := vertex
  arrow e := (e.1,encode e.2.val)
  source e := by
    apply Prod.ext
    · apply Fin.ext
      exact e.2.property.symm
    · rfl
  target e := by
    apply Prod.ext
    · apply Fin.ext
      simp [cover,coloredCoverQuiver,vertex,baseVertex,toggle_parity,e.2.property]
    · exact (source_step e.1 e.2.val e.2.property).symm

theorem vertex_injective : Function.Injective vertex := by
  intro u v h
  exact encode_injective (congrArg Prod.snd h)

theorem arrow_injective : Function.Injective embedding.arrow := by
  intro e f h
  change (e.1,encode e.2.val) = (f.1,encode f.2.val) at h
  apply Prod.ext
  · exact congrArg (fun p : Color × GroupWord => p.1) h
  · apply Subtype.ext
    exact encode_injective (congrArg Prod.snd h)

theorem preserves_base (w : Word) : (vertex w).1 = baseVertex w := rfl

theorem preserves_color (e : coloredCoverQuiver.A) : (embedding.arrow e).1 = e.1 := rfl

end KroneckerWeistCoverEmbedding
end
end
