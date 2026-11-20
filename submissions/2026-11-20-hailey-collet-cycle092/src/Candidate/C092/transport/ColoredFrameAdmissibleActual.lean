/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
A genuine H5 supplier for BOTH actual colored class label sets. -/
import Candidate.C092.transport.ColoredFrameAdmissibleFibre
import Candidate.C092.transport.RegularColoredFrameEnergy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.ColoredFrameAdmissible
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The true fixed and regular class sets are both admissible, uniformly over
all later colors, literal classes, source heights, columns and dyad vectors.
Weighted original-row divisor fibres and the logarithmic dyad width are supplied
internally by native subpower theorems; Fits is derived from actual source caps. -/
theorem eventually_actual_class_admissible (Mmin Mmax ε mesh:ℝ)
    (hMmax:0≤ Mmax+2) (hε:0< ε) (hmesh:0< mesh) (L:ℝ) (θ:GData L) :
    ∀ᶠZ:ℝ in atTop,∀(η:Character)(s:Source (Fin θ.N) θ.a θ.b)(ha:0< θ.a)
      (ω₁ ω₂ ψ:Character)(χ₀:RayCharacter)(Q:Id)(m:O)(t Kc R H:ℝ)
      (rs:GSrc θ mesh Z)(j₀:DictIdx)(ξ:RayCharacter)
      (g:Lab (coloredCarrier s ha ω₁ ω₂)→Id),IsColumn (coloredCarrier s ha ω₁ ω₂) g →
    ∀(n:Fin 4→ℤ)(χ:RayCharacter),s.H=∅ → (24:ℝ)≤ θ.Bmask →
      (s.R.absNorm:ℝ)≤ Z^(8:ℝ) →
      (∀I∈coloredCarrier s ha ω₁ ω₂,(I.absNorm:ℝ)≤ Z^(8:ℝ)) →
      Mmin≤ commonH rs → commonH rs≤ Mmax →
    QRH.SilDensitySplit.CubeFree.Second.AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε Z rs
      (QRH.Cycle092.FixedPhysicalClassLedger.actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ)
      (commonH rs) ∧
    QRH.SilDensitySplit.CubeFree.Second.AdmissibleGroup
      (QRH.Cycle092.RegularColoredForward.frameSideFrame L θ mesh ω₁ ω₂ η Z) Mmin Mmax mesh ε Z rs
      (QRH.Cycle092.ColoredGaussFrameProvider.actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ)
      (commonH rs) := by
  filter_upwards [eventually_fibreAt 2 (Mmax+2) θ.Bmask ε hMmax θ.hBmask hε,
    eventually_logb_two_le mesh hmesh] with Z hfib hlog
  intro η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g hg n χ hH hB hR hX hlo hhi
  constructor
  · apply image_admissible η s ha ω₁ ω₂ rs j₀ ξ g hg n χ
      ((QRH.Cycle092.FixedPhysicalClassLedger.actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n).sigma
        (labelPool (coloredCarrier s ha ω₁ ω₂))) _ Mmin Mmax ε ⟨hlo,hhi⟩ hlog hfib
    exact QRH.Cycle092.FixedPhysicalClassLedger.actualFrameLabels_fits_caps
      η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g hg n χ hH hB hR hX
  · change QRH.SilDensitySplit.CubeFree.Second.AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε Z rs
      (QRH.Cycle092.ColoredGaussFrameProvider.actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ)
      (commonH rs)
    apply image_admissible η s ha ω₁ ω₂ rs j₀ ξ g hg n χ
      ((QRH.Cycle092.ColoredGaussFrameProvider.actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n).sigma
        (labelPool (coloredCarrier s ha ω₁ ω₂))) _ Mmin Mmax ε ⟨hlo,hhi⟩ hlog hfib
    exact QRH.Cycle092.ColoredGaussFrameProvider.actualFrameLabels_fits_caps
      η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g hg n χ hH hB hR hX

end
end QRH.Cycle092.ColoredFrameAdmissible
#print axioms QRH.Cycle092.ColoredFrameAdmissible.eventually_actual_class_admissible
