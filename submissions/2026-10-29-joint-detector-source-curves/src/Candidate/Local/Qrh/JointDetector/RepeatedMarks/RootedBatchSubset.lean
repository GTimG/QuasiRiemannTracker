/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

/-- Restrict only the actual row set. Every common coefficient, slot,
root mask and character dictionary stays unchanged. -/
def RootedBatch.restrict {Label Slot : Type*}
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal O}
    {W : ℝ→ℂ} {U Aroot : ℝ}
    (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot)
    (rows : Finset FreeRow) (hrows : rows⊆B.rows) :
    RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot :=
  { B with
    rows := rows
    rowNorm := fun u hu=>B.rowNorm u (hrows hu)
    embeddingNorm := fun u hu=>B.embeddingNorm u (hrows hu)
    idealCoefficients := fun u hu=>B.idealCoefficients u (hrows hu)
    elementCoefficients := fun u hu=>B.elementCoefficients u (hrows hu)
    retained := fun u hu=>B.retained u (hrows hu)
    plainIdentity := fun u hu=>B.plainIdentity u (hrows hu)
    inverseIdentity := fun u hu=>B.inverseIdentity u (hrows hu) }

end
end Qrh.JointDetector.RepeatedMarks
