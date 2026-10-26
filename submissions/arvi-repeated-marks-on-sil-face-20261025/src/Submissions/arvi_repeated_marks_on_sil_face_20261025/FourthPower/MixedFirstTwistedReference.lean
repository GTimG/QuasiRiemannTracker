/- Copyright (c) 2026 Sil. Apache-2.0.
Reference normalization for the ACTUAL twisted first block. Nonvanishing
of an untwisted block is never inferred. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstReferencePair

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstTwistedReference
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstMixedAllowance CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalFamily
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open MixedPrincipalPair MixedPrincipalWindow MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Any literal multiplicative twist retains the source support, including
its natural zero set. No bound on the twist is needed for reference geometry. -/
theorem multiplied_support (s : Source ι a b) (ha : 0<a) (seed : Id)
    (twist : Id→ℂ) (I : Id)
    (h : sourceCoefficient s ha seed I*twist I≠0) :
    sourceCoefficient s ha seed I≠0 := (mul_ne_zero_iff.mp h).1

/-- The same quantitative reference conclusion as actual_source_reference_pair,
applied directly to the actual beta. The only extra input is exact support
containment; it is not an energy or analytic estimate. -/
theorem twisted_source_reference_pair (s : Source ι a b) (ha : 0<a)
    (seed : Id) (β : Id→ℂ)
    (hβ : ∀I,β I≠0→sourceCoefficient s ha seed I≠0)
    (η : Character) (m A : O) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (U : Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hZ : 1<Z)
    (hEL : 0≤EL) (hER : 0≤ER) (hwin : ∀i y,U i y≠0→|y|≤M)
    (hn : block η m A t (sourceColumns s) β
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0) :
    ‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(sourceVolume s/(C.absNorm:ℝ))^2*
        Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(sourceVolume s/(D.absNorm:ℝ))^2*
        Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
        (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER) := by
  have ha' : 0<a^2/pairNorm s.d := div_pos (sq_pos_of_pos ha) (pairNorm_pos s.hd.1 s.hd.2)
  obtain ⟨hl,hr⟩ := block_reference_lower η m A t (sourceColumns s) β
    C D hC hD E rows W U K K₀ H₀ A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M
    hA hB (fun I hI=>source_coefficient_lower s ha seed I (hβ I hI)) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E η ξ₁ ξ₂ F
    K A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M Z EL ER
    hK hA hB ha' (sourceVolume_pos s) hZ hEL hER hl hr

end
end Candidate.FourthPower.MixedFirstTwistedReference
