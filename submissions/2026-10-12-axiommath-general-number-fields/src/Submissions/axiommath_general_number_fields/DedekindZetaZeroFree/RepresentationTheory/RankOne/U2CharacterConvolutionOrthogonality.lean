/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/U2CharacterConvolutionOrthogonality.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.IrreducibleClassification
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Compact.IntegratedOperators
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Compact.CompactCharacterProjectors
public import Mathlib

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation

open MeasureTheory
open scoped Matrix.Norms.L2Operator InnerProductSpace

abbrev RawU2 := Matrix.unitaryGroup (Fin 2) ℂ

abbrev RawHarmonicType (d : ℕ) := Fin d → ℕ

noncomputable def rawSymmetricPowerTrace (n : ℕ) (g : RawU2) : ℂ :=
  match n with
  | 0 => 1
  | 1 => Matrix.trace g.val
  | n + 2 => Matrix.trace g.val * rawSymmetricPowerTrace (n + 1) g -
      Matrix.det g.val * rawSymmetricPowerTrace n g

noncomputable def rawRankOneCharacter (ℓ : ℕ) (g : RawU2) : ℂ :=
  rawSymmetricPowerTrace (2 * ℓ) g / Matrix.det g.val ^ ℓ

noncomputable def rawCharacter {d : ℕ} (ℓ : RawHarmonicType d)
    (g : Fin d → RawU2) : ℂ :=
  ∏ j, rawRankOneCharacter (ℓ j) (g j)

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation

end
