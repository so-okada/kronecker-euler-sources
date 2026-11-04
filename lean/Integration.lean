import CurrentManuscriptCheck
import KroneckerManuscriptTreeBridge

open KroneckerManuscriptQuiverDefinitions
example (Q : Quiver) : CategoryTheory.Category (Representation Q) := inferInstance
example {C : Type} (Q : ColoredQuiver C) : CategoryTheory.Category (ColRep Q) := inferInstance
#check Graph.SourceTrivalentTree.source_dimension_bound
#check Graph.SourceTrivalentTree.coordinate_vanishes
#check Graph.SourceTrivalentTree.induced_forest
#print axioms KroneckerReadableMain.main
#print axioms KroneckerReadableMain.semantic_main
