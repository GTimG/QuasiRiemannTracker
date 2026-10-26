import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorContraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorRatioPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalErrorLoss
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineRetainedPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorNormalized
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
attribute [local instance] geometryErrorOrdinaryContractionDecidable

variable {α : Type}[Fintype α]

/-- The exact global ordinary normalized family required by the retained
contraction of a parent with first puncture `R`, seed `seed` and radial scale `Z^Mrow`.
A receipt must be obtained from the actual normalized/menu proof. -/
def GeometryErrorNormalizedFamilyReceipt
    (degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator : ℝ) : Prop :=
  let selected:=GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z Mrow amp ξ reserve
    (9/4) t hZ key P υ hz₁ hz₂
  let d:=geometryJointErrorDatum (α:=α) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
  let phase:=fun c=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ c)
  let coeff:=geometryJointErrorWeight (α:=α) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ
    Mrow (Real.logb Z (volume s)) phase hz₁ hz₂
  ∃(χ : selected→RayCharacter)(Hratio : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0<Hratio r) ∧
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (d j) (χ j) Qfix m) coeff (fun _=>numerator) Hratio

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight

/-- Join the exact normalized receipt and the proved finite ratio envelope.
The conclusion is the original retained sum, with its prime average once. -/
theorem geometry_affine_error_paid_source_of_receipts
    (A degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(box : Finset (Fin 4→ℤ))
    (εratio exponent target Cb C Ce Co control cap : ℝ)
    (hCb : 0≤Cb)(hC : 0≤C)(hCo : 0≤Co)(hcontrol : 0≤ control)
    (hcontract : GeometryErrorSourceRetainedSpec A degree windowDegree reflected s R seed Ψ
      Z Mrow amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m cap Co)
    (hnormalized : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ
      Z Mrow amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m (C*control*Z^exponent))
    (hratio : GeometryErrorBoxRatioSpec
      (geometryJointErrorDatum (α:=α) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂)
      box Cb εratio Z)
    (hexceptional : cap≤Ce*control*Z^target)(hexponent : exponent+εratio≤target) :
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow amp ξ reserve t hZ reflected key P υ‖≤
      (Ce+Co*Cb*C)*control*Z^target := by
  let : DecidableEq α:=Classical.decEq α
  obtain ⟨χ,Hratio,hH,hnorm⟩:=hnormalized
  have hnum : 0≤C*control*Z^exponent := by positivity
  have hc:=hcontract χ (fun _=>C*control*Z^exponent) Hratio (fun _ _=>hnum) hH hnorm
  have hr:=hratio.2.2.1 (C*control*Z^exponent) hnum A
  have hp:=geometry_affine_error_contracted_payment Z εratio exponent target Cb C Ce Co
    control ((56/(P.card:ℝ))*‖geometryAffineErrorRetainedContractSum reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key P υ‖)
    cap (∑r∈secondRatioBins (fun j=>(geometryJointErrorDatum (α:=α) reflected s R seed Z Mrow amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂ j).block), (C*control*Z^exponent)/(1+dyadicScale r)^A)
    hZ hCb hC hCo hcontrol hc hexceptional hr hexponent
  rwa [geometry_affine_error_retained_contract_sum_eq_original] at hp

variable [Cycle63.AffineLedger] in
/-- The common ambient rate pays projector, the explicit menu box cardinality,
allocation, shell and finite ratio losses. Common scalar loss and ratio fee are δ.
The radial deficit `1 - Mrow` is carried unchanged. -/
theorem geometry_affine_error_final_source_exponent (εaffine Mrow : ℝ)(N : ℕ)(hε : 0<εaffine) :
    let μ:=geometryLossUnit 1 εaffine
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    ((2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))+(1-Mrow))+δ≤
      -((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow) := by
  intro μ δ
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hp:=hb.2.2.2.2.2.1
  change 130*δ+3*(3*((N:ℝ)+2))*δ+δ+8*δ≤μ at hp
  have hs:=geometry_final_error_exponent_saving εaffine
  linarith only [hp,hb.1,hs]

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorPaidFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

set_option maxHeartbeats 800000 in
variable [Cycle63.AffineLedger] in
/-- Genuine affine exceptional and ratio payments close the original retained error of
every parent input after the exact named normalized-family receipt is supplied. -/
theorem actual_affine_error_uniform_component_payment
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(εaffine mesh Cs : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (C : ℝ)(hC : 0≤C) :
    ∃K : ℝ,0≤K ∧ ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
      (η₀ : Character)(θ : T→RayQuotient.Characters rayM H)(w σ freq : T→ℝ),
      Matches rayM H hH s η₀ θ w σ freq W 2 Z →
      ∀(R seed : Ideal O)(Mrow : ℝ),R≠0 → Squarefree seed →
      (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤ Mrow → Mrow≤1 →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16 →
      (∀j,w j≤ mesh) →
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B →
      ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
      ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.AffineLedger.amp beta
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))+(1-Mrow)
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s R seed
        (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
        elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ Z Mrow amp (μ/64) (μ/8)
        firstHeight hZ key P υ caps.zero₁ caps.zero₂ Qfix fixedBadMask
        (C*control*Z^exponent/(seed.absNorm:ℝ)) →
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow amp (μ/64) (μ/8) firstHeight
        hZ reflected key P υ‖≤
        K*control*Z^(-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow))/(seed.absNorm:ℝ) := by
  let μ:=geometryLossUnit 1 εaffine
  let N:=Fintype.card α
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hδ : 0<δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)).1
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_error_retained_contraction (α:=α)
    rayM H hH A degree windowDegree hc hs Sbad hbad W εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Cs
  obtain ⟨Cb,hCb,hratio⟩:=eventual_actual_geometry_affine_error_ratio_payment N (μ/8) (μ/64) δ
    (by positivity) (by linarith) hδ
  let K:=Ce+Co*Cb*C
  refine ⟨K,by dsimp only [K];positivity,SE,dE,?_⟩
  filter_upwards [hcontract,hratio,eventual_geometry_small_frequency μ hμ] with Z hcZ hrZ hfZ
  refine ⟨hcZ.1,?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot haff
    beta hbeta S D hSE hdE Ψ reflected key firstHeight height hheight μ' N' δ' amp P control exponent υ hυ
  let : DecidableEq T:=Classical.decEq T
  intro hnormalized
  have hcpaid:=hcZ.2 hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit
    hwm hzslot haff beta hbeta Ψ reflected key firstHeight υ hυ
  have hside : 0<geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤ control:=by dsimp only [control];positivity
  have hn : (0:ℝ)<seed.absNorm:=CenteredMomentFirstScale.norm_pos seed hseed.ne_zero
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp:=(Cycle63.AffineLedger.amp_pos hb).le
  have hamp : |amp|≤3:=by
    rw [abs_of_nonneg hamp0]
    exact (Cycle63.AffineLedger.amp_bounds hb).2.trans (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have homega : |frequencyLoss Z 32 (μ/64)+μ/8|≤3:=by
    rw [abs_of_nonneg hfZ.2.1]
    have hmucap:=(geometry_loss_unit_reserve 1 εaffine 1 le_rfl).2
    have hlow := Cycle63.AffineLedger.lowReserve_le
    linarith [hfZ.2.2]
  have hMrow3 : |Mrow|≤3:=by
    rw [abs_of_nonneg hMrow]
    linarith only [hMrow1]
  have hp (pp : elementPool P) : pp.val≠0:=
    (actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ _ hb pp).1
  have capsN : GeometryAffineExceptionalSourceGates s p N Cs Z:=
    {caps with card:=Fintype.card_le_of_injective _ Subtype.val_injective}
  have hbox:=hrZ.2 reflected s R seed p Cs Mrow amp (μ/8) firstHeight hZ key
    capsN hseed hMrow3 hamp homega P hp υ
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)≤
      Ce*(control/(seed.absNorm:ℝ))*Z^(-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow)) := by
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (Cycle63Physical.profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by
        have hlow := Cycle63.AffineLedger.lowReserve_le
        linarith : -(1/100:ℝ)+(1-Mrow)≤-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=div_le_div_of_nonneg_right
      (mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)) hn.le
    convert hm using 1;dsimp only [control];ring
  have hexponent : exponent+δ≤-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow):=
    geometry_affine_error_final_source_exponent εaffine Mrow N hε
  have hnormalized' : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ Z Mrow
      amp (μ/64) (μ/8) firstHeight hZ key P υ caps.zero₁ caps.zero₂ Qfix fixedBadMask
      (C*(control/(seed.absNorm:ℝ))*Z^exponent) := by
    rw [show C*(control/(seed.absNorm:ℝ))*Z^exponent=C*control*Z^exponent/(seed.absNorm:ℝ) by ring]
    exact hnormalized
  exact (geometry_affine_error_paid_source_of_receipts A degree windowDegree reflected s R seed Ψ Z Mrow amp
    (μ/64) (μ/8) firstHeight hZ key P υ caps.zero₁ caps.zero₂
    Qfix fixedBadMask (geometryErrorAbsoluteBox Z N 3 (μ/8) (9/4)) δ exponent
    (-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow)) Cb C Ce Co (control/(seed.absNorm:ℝ)) _
    hCb.le hC hCo.le (div_nonneg hcontrol hn.le) hcpaid hnormalized' hbox hex hexponent).trans_eq
    (by dsimp only [K];ring)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
