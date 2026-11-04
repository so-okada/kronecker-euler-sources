import KroneckerReducedColorWords
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
namespace KroneckerGraphColorWords
open SimpleGraph KroneckerReducedColorWords

structure EdgeColoring {V : Type*} (G : SimpleGraph V) where
  color : ∀ {u v}, G.Adj u v → Color
  symm : ∀ {u v} (h : G.Adj u v), color h.symm = color h
  proper : ∀ {u v w} (h : G.Adj u v) (k : G.Adj u w), color h = color k → v = w

variable {V : Type*} {G : SimpleGraph V} (C : EdgeColoring G)

def colors {u v : V} : G.Walk u v → List Color
  | .nil => []
  | .cons h p => C.color h :: colors p

theorem colors_length {u v : V} (p : G.Walk u v) : (colors C p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [colors, List.length_cons, Walk.length_cons, ih]

theorem colors_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    colors C (p.append q) = colors C p ++ colors C q := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.cons_append, colors, List.cons_append, ih]

theorem colors_reverse {u v : V} (p : G.Walk u v) : colors C p.reverse = (colors C p).reverse := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.reverse_cons, colors_append, colors, List.reverse_cons, ih]
    rw [show C.color (G.symm.symm _ _ h) = C.color h from C.symm h]

theorem path_colors_reduced {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Reduced (colors C p) := by
  induction p with
  | nil => exact List.isChain_nil
  | @cons u v w h p ih =>
    have ht := (Walk.cons_isPath_iff h p).mp hp
    cases p with
    | nil => exact List.isChain_singleton _
    | @cons v z w k q =>
      refine List.isChain_cons_cons.mpr ⟨?_, ih ht.1⟩
      intro hc
      have hz : u = z := C.proper h.symm k ((C.symm h).trans hc)
      subst z
      exact ht.2 (by simp)

theorem endpoint_of_colors {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
    (h : colors C p = colors C q) : v = w := by
  induction p generalizing w with
  | nil =>
    cases q with
    | nil => rfl
    | cons k q => cases h
  | @cons u v z e p ih =>
    cases q with
    | nil => cases h
    | @cons u w y k q =>
      have hh := List.cons.inj h
      have hw := C.proper e k hh.1
      subst w
      exact ih q hh.2

theorem walk_eq_of_colors {u v : V} (p q : G.Walk u v)
    (h : colors C p = colors C q) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons k q => cases h
  | @cons u v z e p ih =>
    cases q with
    | nil => cases h
    | @cons u w z k q =>
      have hh := List.cons.inj h
      have hw := C.proper e k hh.1
      subst w
      cases ih q hh.2
      rfl

end KroneckerGraphColorWords
