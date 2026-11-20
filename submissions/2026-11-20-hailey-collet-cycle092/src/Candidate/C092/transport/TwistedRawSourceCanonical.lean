/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The canonical native tuple source with two independent ordinary colors. -/
import Candidate.C092.transport.TwistedRawSourceColumns
set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumCanonicalDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

/-- The native canonical pools, full puncture and seed-one source, with the
    two fixed ordinary characters still attached to their own live ideals. -/
def canonicalSource (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) : ℂ :=
  ∑ v ∈ Fintype.piFinset
      (MixedTupleRows.pools pool
        (plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)))
        (plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)))),
    MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct S H) v *
      ordinaryColor ω₁ ω₂ v *
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v *
      idealCoeff χ (finiteTupleProduct v)

end
end QRH.Cycle092.TwistedRawSource
