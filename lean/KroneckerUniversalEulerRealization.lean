import KroneckerBoundedWordEulerRealization

/- Original module: KroneckerUniversalStableRealization -/
section
/-! A stable direct-sum representation at depth3B+1 and total at most B has
an actual stable realization on the universal colored-word cover. The SAME
full support embedding preserves every matrix, positive dimension, original
source/sink total and original color, with no source-root existence assumption. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalStableRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullSupportRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable


end KroneckerUniversalStableRealization
end
end

/- Original module: KroneckerUniversalEulerRealization -/
section
/-! Every nonzero bounded stable direct-sum object at depth3B+1 has an
actual universal-word realization with identical original dimensions and
self-Euler form. This is a realization statement, not yet a quotient or
geometric-localization theorem. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalEulerRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
open KroneckerFullSupportRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable


end KroneckerUniversalEulerRealization
end
end
