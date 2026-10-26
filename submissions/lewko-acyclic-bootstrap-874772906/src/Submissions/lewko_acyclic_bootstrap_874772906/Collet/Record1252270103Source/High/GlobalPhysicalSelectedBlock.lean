/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Generalizes the checked Cycle61 restricted-kernel transport to explicit row selectors.
The finite coefficient, divisor mask and actual positive energy are retained. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondIdealBlockBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedKernel

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.Record1252270103GlobalSelected
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_selected_block_bound (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ r : ℝ,0<r →
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
        (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C=primeSupport D →
      ∀ (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
        (ρ x : O→ℝ) (u : sectorPool C hC.1 S→ℝ) (v : sectorPool D hD.1 S→ℝ)
        (keep : RayCharacter→O→Prop),
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
      (∀ χ : RayCharacter,∀ z∈rows,keep χ z) →
      (∀ χ : RayCharacter,∀ z∈rows,keep χ (-z)) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀ z : O,0≤(Φ (normValue z/H)).re) →
      (∀ z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀ E₁ E₂ : Ideal O→ℝ,
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₁ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₂ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (keep χ) Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) Φ H≤
              (E₁ L*(1+‖w‖)^J₁)^2) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (keep χ) Finset.univ (sectorElement D hD.1 S)
          (fun J=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient A (sectorElement D hD.1 S) d) χ J*star (columnPhase logAnnulus (v J) w)) Φ H≤
              (E₂ L*(1+‖w‖)^J₂)^2) →
      (1+r)^decay*‖∑ z∈rows,retainedScalar C D U R z*
        ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤
        B*∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(E₁ L*E₂ L) := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_selected_second_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num)) (fun _ x hx=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure x hx)
    decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v keep
  dsimp only
  intro hkeep₁ hkeep₂ Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun J=>β (D*J)*heightCoeff η t J) u v ρ x keep hkeep₁ hkeep₂
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _)
    Φ H hH (by simpa only [normValue_eq_embedding] using hΦ)
    (by simpa only [normValue_eq_embedding] using hmajor) E₁ E₂
    (by simpa only [sectorElement_span] using hE₁) (by simpa only [sectorElement_span] using hE₂)
    (by simpa only [sectorElement_span] using hleft) (by simpa only [sectorElement_span] using hright)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.Record1252270103GlobalSelected

end

end OAI

#print axioms OAI.SevenEighths.Record1252270103GlobalSelected.actual_selected_block_bound
