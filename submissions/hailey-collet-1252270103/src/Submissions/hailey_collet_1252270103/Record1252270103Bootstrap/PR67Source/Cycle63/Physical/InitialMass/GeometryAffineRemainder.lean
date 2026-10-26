import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAmplifiedRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The main source before retained contraction, with the original allocation
weights and the actual slot cardinality in its Fourier scale. -/
def geometryAffineMainSourceTotal (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let phase := fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)
  ∑q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ hK key,
    geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2 *
    actualMainSource (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK key t q)
      (geometryBranch reflected s R seed (Z^Mrow) Z ξ hK key q.1.val) Z (3*amp) 1 ξ reserve

variable [Cycle63.AffineLedger] in
/-- The small losses in the zero term of a parent with radial scale `Z^Mrow` leave the strict saving of the ledger, less the radial
deficit `1 - Mrow`. -/
theorem geometry_affine_zero_loss (Z μ A beta Mrow : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    zeroPaymentExponent Z 1 Mrow A (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow) := by
  have hpaid := geometry_zero_exponent_saving Z 1 Mrow A (Cycle63.AffineLedger.amp beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/380 := by nlinarith
  linarith only [hpaid hbudget]

variable [Cycle63.AffineLedger] in
/-- Genuine source and cone receipts pay the complete zero and tail terms of a parent with puncture `R`, seed `seed` and radial
scale `Z^Mrow`. Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_parent_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀(R seed : Ideal O)(Mrow : ℝ),Squarefree seed → 0≤Mrow → Mrow≤1 →
    ∀beta : ℝ,Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s)≤Cycle63.AffineLedger.totalA beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      geometryAffineMainSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)+
      ‖geometryMainRetainedSum reflected s R seed Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (ι:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128)
    (Cycle63.AffineLedger.zeroSaving:ℝ)
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+zconst+tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop ((9/4:ℝ)^(Fintype.card ι)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone Ψ t reflected key
  have ha := (Cycle63.AffineLedger.amp_pos hb).le
  have haB : Cycle63.AffineLedger.amp beta≤3 := (Cycle63.AffineLedger.amp_bounds hb).2.trans (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have hh := hr.2 s R seed Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1 Mrow
    (Cycle63.AffineLedger.amp beta) (μ/8) (μ/128) t hZ hb (by norm_num) hMrow (by linarith only [hMrow1])
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad hseed hseed.ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta Mrow hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith only [hMrow1] : -(Cycle63.AffineLedger.zeroSaving:ℝ)≤
      -(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hseedNorm : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  have hzconst : 0≤zconst := by dsimp [zconst];positivity
  have htconst : 0≤tconst := by dsimp [tconst];positivity
  have h₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)) hseedNorm.le
  have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htail
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)) hseedNorm.le
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))/(seed.absNorm:ℝ) := by
    positivity
  have hnorm : geometryAffineMainSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 Mrow (Real.logb Z (volume s)) (Cycle63.AffineLedger.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))/(seed.absNorm:ℝ)+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ))/(seed.absNorm:ℝ)+
      ‖geometryMainRetainedSum reflected s R seed Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineMainSourceTotal,geometryMainRetainedSum,
        geometryLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient]; ring
  simp only [div_eq_mul_inv] at h₁ h₂ hrest hnorm ⊢
  nlinarith only [hnorm,h₁,h₂,hrest]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
