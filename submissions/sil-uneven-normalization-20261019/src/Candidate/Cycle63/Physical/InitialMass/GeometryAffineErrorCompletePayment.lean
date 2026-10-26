import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorRatioPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalErrorLoss
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRetainedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorNormalized

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorPayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
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

/-- The exact global ordinary normalized family required by the retained
contraction. A receipt must be obtained from the actual normalized/menu proof. -/
def GeometryErrorNormalizedFamilyReceipt
    (degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator : ℝ) : Prop :=
  let selected:=GeometryJointErrorSelectedIndex (α:=α) reflected s 1 1 Z 1 amp ξ reserve
    (9/4) t hZ key P υ hz₁ hz₂
  let d:=geometryJointErrorDatum (α:=α) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
  let phase:=fun c=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ c)
  let coeff:=geometryJointErrorWeight (α:=α) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ
    1 (Real.logb Z (volume s)) phase hz₁ hz₂
  ∃(χ : selected→RayCharacter)(Hratio : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0<Hratio r) ∧
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (d j) (χ j) Qfix m) coeff (fun _=>numerator) Hratio

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight

/-- Join the exact normalized receipt and the proved finite ratio envelope.
The conclusion is the original retained sum, with its prime average once. -/
theorem geometry_affine_error_paid_source_of_receipts
    (A degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(box : Finset (Fin 4→ℤ))
    (εratio exponent target Cb C Ce Co control cap : ℝ)
    (hCb : 0≤Cb)(hC : 0≤C)(hCo : 0≤Co)(hcontrol : 0≤control)
    (hcontract : GeometryErrorSourceRetainedSpec A degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m cap Co)
    (hnormalized : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m (C*control*Z^exponent))
    (hratio : GeometryErrorBoxRatioSpec
      (geometryJointErrorDatum (α:=α) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂)
      box Cb εratio Z)
    (hexceptional : cap≤Ce*control*Z^target)(hexponent : exponent+εratio≤target) :
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp ξ reserve t hZ reflected key P υ‖≤
      (Ce+Co*Cb*C)*control*Z^target := by
  letI : DecidableEq α:=Classical.decEq α
  obtain ⟨χ,Hratio,hH,hnorm⟩:=hnormalized
  have hnum : 0≤C*control*Z^exponent := by positivity
  have hc:=hcontract χ (fun _=>C*control*Z^exponent) Hratio (fun _ _=>hnum) hH hnorm
  have hr:=hratio.2.2.1 (C*control*Z^exponent) hnum A
  have hp:=geometry_affine_error_contracted_payment Z εratio exponent target Cb C Ce Co
    control ((56/(P.card:ℝ))*‖geometryAffineErrorRetainedContractSum reflected s Ψ Z amp ξ reserve t hZ key P υ‖)
    cap (∑r∈secondRatioBins (fun j=>(geometryJointErrorDatum (α:=α) reflected s 1 1 Z 1 amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂ j).block), (C*control*Z^exponent)/(1+dyadicScale r)^A)
    hZ hCb hC hCo hcontrol hc hexceptional hr hexponent
  rwa [geometry_affine_error_retained_contract_sum_eq_original] at hp

/-- The common ambient rate pays projector, the explicit menu box cardinality,
allocation, shell and finite ratio losses. Common scalar loss and ratio fee are δ. -/
theorem geometry_affine_error_final_source_exponent (εaffine : ℝ)(N : ℕ)(hε : 0<εaffine) :
    let μ:=geometryLossUnit 1 εaffine
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    (2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))+δ≤-(7/120000000:ℝ) := by
  intro μ δ
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hp:=hb.2.2.2.2.2.1
  change 130*δ+3*(3*((N:ℝ)+2))*δ+δ+8*δ≤μ at hp
  have paid : (2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))+δ≤
      -(7/60000000:ℝ)+μ := by linarith only [hp,hb.1]
  exact paid.trans (geometry_final_error_exponent_saving εaffine)

private theorem affine_error_paid_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorPaidFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

/-- Genuine affine exceptional and ratio payments close the original retained
error after the exact named normalized-family receipt is supplied. -/
theorem actual_affine_error_uniform_component_payment
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (C : ℝ)(hC : 0≤C) :
    ∃K : ℝ,0≤K ∧ ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤mesh) →
      (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B →
      ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ Z amp (μ/64) (μ/8)
        firstHeight hZ key P υ (affine_error_paid_plain_zero p 0) (affine_error_paid_plain_zero p 1)
        Qfix fixedBadMask (C*control*Z^exponent) →
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8) firstHeight
        hZ reflected key P υ‖≤K*control*Z^(-(7/120000000:ℝ)) := by
  let μ:=geometryLossUnit 1 εaffine
  let N:=Fintype.card α
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hδ : 0<δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)).1
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW hWs
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_error_retained_contraction (α:=α)
    rayM H hH A degree windowDegree hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
  obtain ⟨Cb,hCb,hratio⟩:=eventual_actual_geometry_affine_error_ratio_payment N (μ/8) (μ/64) δ
    (by positivity) (by linarith) hδ
  let K:=Ce+Co*Cb*C
  refine ⟨K,by dsimp only [K];positivity,SE,dE,?_⟩
  filter_upwards [hcaps,hcontract,hratio,eventual_geometry_small_frequency μ hμ] with Z hz hcZ hrZ hfZ
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone S D hSE hdE Ψ reflected key firstHeight height hheight s μ' N' δ' amp P control exponent υ hυ
  letI : DecidableEq T:=Classical.decEq T
  intro hnormalized
  have caps:=hz.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hcpaid:=hcZ.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight υ hυ
  have hside : 0<geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤control:=by dsimp only [control];positivity
  have hcell:=Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  have hb:=Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp:=(Cycle63.Arithmetic.amp_pos hb).le
  have hamp : |amp|≤3:=by
    rw [abs_of_nonneg hamp0]
    exact (Cycle63.Arithmetic.amp_bounds hb).2.trans (by norm_num)
  have homega : |frequencyLoss Z 32 (μ/64)+μ/8|≤3:=by
    rw [abs_of_nonneg hfZ.2.1]
    have hmucap:=(geometry_loss_unit_reserve 1 εaffine 1 le_rfl).2
    linarith [hfZ.2.2]
  have hp (pp : elementPool P) : pp.val≠0:=
    (actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ _ hb pp).1
  have hbox:=hrZ.2 reflected s (1:Ideal O) (1:Ideal O) p Cs amp (μ/8) firstHeight hZ key
    caps squarefree_one hamp homega P hp υ
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤Ce*control*Z^(-(7/120000000:ℝ)) := by
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (Cycle63Physical.profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by norm_num : -(1/100:ℝ)≤-(7/120000000:ℝ))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    convert hm using 1;dsimp only [control];ring
  have hexponent : exponent+δ≤-(7/120000000:ℝ):=
    geometry_affine_error_final_source_exponent εaffine N hε
  exact geometry_affine_error_paid_source_of_receipts A degree windowDegree reflected s Ψ Z amp
    (μ/64) (μ/8) firstHeight hZ key P υ (affine_error_paid_plain_zero p 0) (affine_error_paid_plain_zero p 1)
    Qfix fixedBadMask (geometryErrorAbsoluteBox Z N 3 (μ/8) (9/4)) δ exponent
    (-(7/120000000:ℝ)) Cb C Ce Co control _ hCb.le hC hCo.le hcontrol hcpaid hnormalized hbox hex hexponent

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_error_paid_source_of_receipts
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_error_final_source_exponent

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_error_uniform_component_payment
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorCompletePayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
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
    (hH : ∀r∈secondRatioBins (fun l=>(d l).block),0<Hratio r)
    (hE : ∀r∈secondRatioBins (fun l=>(d l).block),E r≤E' r)
    (h : SecondNormalizedBound W degree windowDegree d w E Hratio) :
    SecondNormalizedBound W degree windowDegree d w E' Hratio := by
  intro r hr reflected t u
  have he : (if reflected then E r/Hratio r else E r*Hratio r)≤
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
    (Z amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator numerator' : ℝ)
    (hle : numerator≤numerator')
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
local instance affineErrorCompleteFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

/-- Explicit conditional callback: the uniform exact normalized-family estimate.
Constants and profiles precede every actual moving source and original character family. -/
def GeometryAffineErrorNormalizedSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (degree windowDegree : ℕ)(Qfix : Ideal O)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cn Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤mesh) →
      (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height → (∀i,|freq i|≤height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ Z amp (μ/64) (μ/8)
        firstHeight hZ key P υ (affine_error_complete_profile_zero p 0) (affine_error_complete_profile_zero p 1)
        Qfix fixedBadMask (Cn*control*Z^exponent)

/-- The original retained error paid by its prime average exactly once. -/
def GeometryAffineErrorPaidSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Ce Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤mesh) →
      (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height → (∀i,|freq i|≤height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8) firstHeight
        hZ reflected key P υ‖≤Ce*control*Z^(-(7/120000000:ℝ))

/-- Conditional adapter from the exact uniform normalized-family callback to
paid original retained error. The callback is the remaining analytic obligation. -/
theorem actual_affine_error_complete_payment
    (T : Finset α)(A degree windowDegree dN : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (SN : Finset (ℕ×ℕ))(Cn : ℝ)(hCn : 0≤Cn)
    (hnormalized : ∀ᶠZ : ℝ in atTop,
      GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
        degree windowDegree Qfix SN dN Cn Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  obtain ⟨K,hK,SE,dE,hpaid⟩:=actual_affine_error_uniform_component_payment (α:=α) rayM H hH
    A degree windowDegree hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 Cn hCn
  let S:=SE∪SN
  let D:=max dE dN
  have hSE : SE⊆S := Finset.subset_union_left
  have hSN : SN⊆S := Finset.subset_union_right
  have hdE : dE≤D := le_max_left _ _
  have hdN : dN≤D := le_max_right _ _
  refine ⟨S,D,K,hK,?_⟩
  filter_upwards [hpaid,hnormalized] with Z hp hn
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ N δ amp P control υ hυ
  letI : DecidableEq T:=Classical.decEq T
  have hsource:=hn hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone reflected key firstHeight height hheight hfreq υ hυ
  have hside : 0≤geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hprofile := pow_le_pow_left₀ (p.control_nonneg SN) (Cycle63Physical.profile_control_mono p hSN) 2
  have hbase : (1+|firstHeight|+height)^dN≤(1+|firstHeight|+height)^D :=
    pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdN
  have hcontrol : (p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN≤control := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprofile hside) hbase
      (pow_nonneg (by positivity) _) (by positivity)
  let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))
  have hnum : Cn*((p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN)*Z^exponent≤Cn*control*Z^exponent :=
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
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (hnormalized : ∀T : Finset α,∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hn⟩:=hnormalized T
  exact actual_affine_error_complete_payment rayM H hH T A degree windowDegree dN hc hs
    Sbad hbad W hW hWs Ψ ηseed η₀ εaffine mesh hε hmesh Qfix hQ hQt hQ72 SN Cn hCn hn

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_error_second_normalized_envelope_mono
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_error_normalized_receipt_mono

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_error_complete_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_error_uniform_paid_of_normalized
end
