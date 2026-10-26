/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected centered saving is capped at one without any lower bound on
the positive raw scales. Both analytic bounds are obtained from checked sources. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedCenteredCapped
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentAbsoluteEnergy
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O

theorem corrected_fixed_inducing_source_control
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η : Character,
      ∀m A z : O,m≠0 →A≠0 →z≠0 →goodLambda∣m →(2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^Bχ →
      FixedInducingRow η Q m A z →
      ∀A₁ A₂ D M : Ideal O,A₁≠0 →A₂≠0 →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →(∀p∈P,¬p∣M) →
      2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      (∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ rowWeight η m A z t (n.1*n.2)≠0→
        IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
          (idealDividingPool P (D*(M*n.1*n.2))).card<P.card) →
      ‖correctedCenteredRow P D M A₁ A₂ (rowWeight η m A z t) W₁ W₂ b X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*(max 1 L)^(-α) := by
  obtain ⟨J,S,hS,hsource⟩ := corrected_centered_source_control_capped
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex A₁ A₂ D M
    hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget t X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ :=
    CenteredMomentHeckeVolume.fixedInducingRow_controlled η Q m A z hm hA hz hml hm2 hex
  have hnorm : (χ.modulus.absNorm:ℝ)≤Z^Bχ :=
    (show (χ.modulus.absNorm:ℝ)≤HeckeRowClosure.rowConductorBound η m 1 (A*z) by
      exact_mod_cast hχ).trans hcond
  exact hsource W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow A₁ A₂ D M
    hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget t X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_fixed_inducing_source_control
