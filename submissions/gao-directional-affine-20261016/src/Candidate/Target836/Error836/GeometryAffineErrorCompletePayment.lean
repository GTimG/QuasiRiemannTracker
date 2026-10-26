import Candidate.Target836.Error836.GeometryAffineErrorSpecs
import Candidate.Target836.SourceProvider.ErrorMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target836.Error836.GeometryAffineErrorPayment

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentAmplificationErrorEnergy CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeElements CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentLogDyadic RayFourExpansion
open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

variable {α : Type}[Fintype α]

/-- Increasing the positive numerator preserves the exact ratio-fiber bound. -/
theorem affine_error_second_normalized_envelope_mono
    {Label : Type*}[Fintype Label][DecidableEq α]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E E' Hratio : ℤ→ℝ)
    (hH : ∀r∈secondRatioBins (fun l=>(d l).block),0 < Hratio r)
    (hE : ∀r∈secondRatioBins (fun l=>(d l).block),E r ≤ E' r)
    (h : SecondNormalizedBound W degree windowDegree d w E Hratio) :
    SecondNormalizedBound W degree windowDegree d w E' Hratio := by
  intro r hr reflected t u
  have he : (if reflected then E r/Hratio r else E r*Hratio r) ≤ 
      (if reflected then E' r/Hratio r else E' r*Hratio r) := by
    cases reflected
    · exact mul_le_mul_of_nonneg_right (hE r hr) (hH r hr).le
    · exact div_le_div_of_nonneg_right (hE r hr) (hH r hr).le
  exact (h r hr reflected t u).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity))

/-- The original selected datum and coefficient are preserved by an envelope increase. -/
theorem geometry_affine_error_normalized_receipt_mono
    (degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1 < Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator numerator' : ℝ)
    (hle : numerator ≤ numerator')
    (h : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator) :
    GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator' := by
  obtain ⟨χ,Hratio,hH,hn⟩:=h
  refine ⟨χ,Hratio,hH,?_⟩
  exact affine_error_second_normalized_envelope_mono _ degree windowDegree _ _ _ _ _
    hH (fun _ _=>hle) hn

private theorem affine_error_complete_profile_zero (p : Profiles (1/4) (9/4))(i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorCompletePaymentFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Conditional adapter from the exact uniform normalized-family callback to
paid original retained error. The callback is the remaining analytic obligation. -/
theorem actual_affine_error_complete_payment
    (T : Finset α)(A degree windowDegree dN : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0 < εaffine)
    (hmesh : mesh < (902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix ≤ Ideal.span {(72:O)})
    (SN : Finset (ℕ×ℕ))(Cn : ℝ)(hCn : 0 ≤ Cn)
    (hnormalized : ∀ᶠZ : ℝ in atTop,
      GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
        degree windowDegree Qfix SN dN Cn Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  obtain ⟨K,hK,SE,dE,hpaid⟩:=actual_affine_error_uniform_component_payment (α:=α) rayM H hH
    A degree windowDegree hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 Cn hCn
  let S:=SE∪SN
  let D:=max dE dN
  have hSE : SE⊆S := Finset.subset_union_left
  have hSN : SN⊆S := Finset.subset_union_right
  have hdE : dE ≤ D := le_max_left _ _
  have hdN : dN ≤ D := le_max_right _ _
  refine ⟨S,D,K,hK,?_⟩
  filter_upwards [hpaid,hnormalized] with Z hp hn
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ N δ amp P control υ hυ
  letI : DecidableEq T:=Classical.decEq T
  have hsource:=hn hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone reflected key firstHeight height hheight hfreq υ hυ
  have hside : 0 ≤ geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hprofile := pow_le_pow_left₀ (p.control_nonneg SN) (Cycle63Physical.profile_control_mono p hSN) 2
  have hbase : (1+|firstHeight|+height)^dN ≤ (1+|firstHeight|+height)^D :=
    pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdN
  have hcontrol : (p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN ≤ control := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprofile hside) hbase
      (pow_nonneg (by positivity) _) (by positivity)
  let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))
  have hnum : Cn*((p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN)*Z^exponent ≤ Cn*control*Z^exponent :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrol hCn)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hreceipt := geometry_affine_error_normalized_receipt_mono degree windowDegree reflected s Ψ
    Z amp (μ/64) (μ/8) firstHeight hZ key P υ (affine_error_complete_profile_zero p 0)
    (affine_error_complete_profile_zero p 1) Qfix fixedBadMask _ _ hnum hsource
  exact hp.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone S D hSE hdE Ψ reflected key firstHeight height hheight υ hυ hreceipt

/-- Conditional finite-carrier adapter. Each exact normalized callback fixes
its constants before Z and all moving sources, then the original error is paid. -/
theorem actual_affine_error_uniform_paid_of_normalized
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0 < εaffine)
    (hmesh : mesh < (902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix ≤ Ideal.span {(72:O)})
    (hnormalized : ∀T : Finset α,∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0 ≤ Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hn⟩:=hnormalized T
  exact actual_affine_error_complete_payment rayM H hH T A degree windowDegree dN hc hs
    Sbad hbad W hW hWs Ψ ηseed η₀ εaffine mesh hε hmesh Qfix hQ hQt hQ72 SN Cn hCn hn

end
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.affine_error_second_normalized_envelope_mono
#print axioms OAI.SevenEighths.Target836ErrorPayment.geometry_affine_error_normalized_receipt_mono

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_affine_error_complete_payment

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_affine_error_uniform_paid_of_normalized
