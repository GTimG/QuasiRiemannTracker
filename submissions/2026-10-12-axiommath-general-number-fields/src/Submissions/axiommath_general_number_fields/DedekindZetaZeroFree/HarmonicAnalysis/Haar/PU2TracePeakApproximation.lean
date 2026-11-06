/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/PU2TracePeakApproximation.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.RankOne.PU2CharactersAndQuotientTopology

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion

open MeasureTheory

open scoped Matrix.Norms.L2Operator InnerProductSpace

instance su2NormBridgeCompactSpace : CompactSpace RawU2 := cover_compactSpace

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion

end
