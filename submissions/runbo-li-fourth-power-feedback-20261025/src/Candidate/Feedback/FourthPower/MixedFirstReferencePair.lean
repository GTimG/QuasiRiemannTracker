/- Copyright (c) 2026 Sil. Apache-2.0.
First physical reference normalization for the actual restricted source.
Its lower support is proved from the source, and full prefixes survive.
-/
import Candidate.Feedback.FourthPower.MixedInnerExceptionalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedFirstReferencePair
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

/-- A direct application of the baseline paired reference theorem to
our actual weighted, fifth-free column. The only EL/ER inputs are the
two numerical residual costs; no energy estimate is claimed here. -/
theorem actual_source_reference_pair (s : Source ι a b) (ha : 0<a)
    (seed : Id) (η : Character) (m A : O) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (U : Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hZ : 1<Z)
    (hEL : 0≤EL) (hER : 0≤ER) (hwin : ∀i y,U i y≠0→|y|≤M)
    (hn : block η m A t (sourceColumns s) (sourceCoefficient s ha seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0) :
    ‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(sourceVolume s/(C.absNorm:ℝ))^2*
        Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(sourceVolume s/(D.absNorm:ℝ))^2*
        Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
        (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER) := by
  have ha' : 0<a^2/pairNorm s.d := div_pos (sq_pos_of_pos ha) (pairNorm_pos s.hd.1 s.hd.2)
  obtain ⟨hl,hr⟩ := block_reference_lower η m A t (sourceColumns s) (sourceCoefficient s ha seed)
    C D hC hD E rows W U K K₀ H₀ A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M
    hA hB (fun I hI=>source_coefficient_lower s ha seed I hI) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E η ξ₁ ξ₂ F
    K A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M Z EL ER
    hK hA hB ha' (sourceVolume_pos s) hZ hEL hER hl hr

end
end Candidate.Feedback.FourthPower.MixedFirstReferencePair
