import KroneckerManuscriptFurtherDefinitions
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions.Quiver

/-- All vertex and arrow choices in a lift, before its initial vertex is prescribed. -/
structure LiftSpace {Q T : Quiver} (p : Covering Q T) (u v : T.Vert) where
  Data : Type
  start : Data → Q.Vert
  finish : Data → Q.Vert
  start_over : ∀ l, p.vertex (start l) = u
  finish_over : ∀ l, p.vertex (finish l) = v

def liftSpace {Q T : Quiver} (p : Covering Q T) {u v : T.Vert}
    (γ : Traversal T u v) : LiftSpace p u v :=
  match γ with
  | .nil .(u) =>
    { Data := {x : Q.Vert // p.vertex x = u}
      start := Subtype.val
      finish := Subtype.val
      start_over := Subtype.property
      finish_over := Subtype.property }
  | .forward γ a ha =>
    let L := liftSpace p γ
    { Data := Σ l : L.Data, {b : Q.Arrow // Q.source b = L.finish l ∧ p.edge b = a}
      start := fun l => L.start l.1
      finish := fun l => Q.target l.2.val
      start_over := fun l => L.start_over l.1
      finish_over := fun l => by rw [← p.map_target, l.2.property.2] }
  | .backward γ a ha =>
    let L := liftSpace p γ
    { Data := Σ l : L.Data, {b : Q.Arrow // Q.target b = L.finish l ∧ p.edge b = a}
      start := fun l => L.start l.1
      finish := fun l => Q.source l.2.val
      start_over := fun l => L.start_over l.1
      finish_over := fun l => by rw [← p.map_source, l.2.property.2] }

theorem unique_traversal_lift {Q T : Quiver} (p : Covering Q T) {u v : T.Vert}
    (γ : Traversal T u v) (x : Q.Vert) (hx : p.vertex x = u) :
    ∃! l : (liftSpace p γ).Data, (liftSpace p γ).start l = x := by
  induction γ with
  | nil =>
    exact ⟨⟨x,hx⟩,rfl,fun l hl => Subtype.ext hl⟩
  | @forward v γ a ha ih =>
    obtain ⟨l,hl,hu⟩ := ih
    obtain ⟨b,hb,unique⟩ := p.unique_outgoing ((liftSpace p γ).finish l) a
      (ha.trans ((liftSpace p γ).finish_over l).symm)
    refine ⟨⟨l,⟨b.val,b.property,hb⟩⟩,hl,?_⟩
    rintro ⟨m,c⟩ hm
    have he : m=l := hu m hm
    subst m
    have hc : c.val=b.val := congrArg Subtype.val (unique ⟨c.val,c.property.1⟩ c.property.2)
    have hc' : c=⟨b.val,b.property,hb⟩ := Subtype.ext hc
    cases hc'
    rfl
  | @backward v γ a ha ih =>
    obtain ⟨l,hl,hu⟩ := ih
    obtain ⟨b,hb,unique⟩ := p.unique_incoming ((liftSpace p γ).finish l) a
      (ha.trans ((liftSpace p γ).finish_over l).symm)
    refine ⟨⟨l,⟨b.val,b.property,hb⟩⟩,hl,?_⟩
    rintro ⟨m,c⟩ hm
    have he : m=l := hu m hm
    subst m
    have hc : c.val=b.val := congrArg Subtype.val (unique ⟨c.val,c.property.1⟩ c.property.2)
    have hc' : c=⟨b.val,b.property,hb⟩ := Subtype.ext hc
    cases hc'
    rfl

def Lift {Q T : Quiver} (p : Covering Q T) {u v : T.Vert}
    (γ : Traversal T u v) (x : Q.Vert) (hx : p.vertex x=u) : (liftSpace p γ).Data :=
  (unique_traversal_lift p γ x hx).choose
def liftedTraversal {Q T : Quiver} (p : Covering Q T) {u v : T.Vert}
    (γ : Traversal T u v) : (l : (liftSpace p γ).Data) →
    Traversal Q ((liftSpace p γ).start l) ((liftSpace p γ).finish l) :=
  match γ with
  | .nil .(u) => fun l => .nil l.val
  | .forward γ a ha => fun l => .forward (liftedTraversal p γ l.1) l.2.val l.2.property.1
  | .backward γ a ha => fun l => .backward (liftedTraversal p γ l.1) l.2.val l.2.property.1
theorem lift_start {Q T : Quiver} (p : Covering Q T) {u v : T.Vert}
    (γ : Traversal T u v) (x : Q.Vert) (hx : p.vertex x=u) :
    (liftSpace p γ).start (Lift p γ x hx)=x :=
  (unique_traversal_lift p γ x hx).choose_spec.1
end KroneckerManuscriptQuiverDefinitions.Quiver
