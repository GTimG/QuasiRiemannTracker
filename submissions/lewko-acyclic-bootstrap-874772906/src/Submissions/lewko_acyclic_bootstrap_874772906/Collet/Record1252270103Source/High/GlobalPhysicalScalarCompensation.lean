import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalScalarSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryScalarCompensation

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths Cycle61InitialMass QRH.Record12518109Assembly
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSourceReduction CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]
/-- Literal physical D lies in the frozen dyadic interval. -/
theorem actual_geometry_D_compensation (s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)(K Z ξ B : ℝ)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s modifier R seed K Z ξ key) :
    geometryDCompensator key≤(q.val.1.val.2.absNorm:ℝ) ∧
      (q.val.1.val.2.absNorm:ℝ)<2*geometryDCompensator key := by
  have hn := (actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource q.val 1).1
  have hn' : 0<geometryNorms s modifier R seed K Z ξ q.val 1 := zero_lt_one.trans_le hn
  have hi := congrFun (congrArg Prod.snd q.property) (1 : Fin 5)
  change ⌊Real.logb 2 (geometryNorms s modifier R seed K Z ξ q.val 1)⌋=key.2 1 at hi
  have hlo := Int.floor_le (Real.logb 2 (geometryNorms s modifier R seed K Z ξ q.val 1))
  have hhi := Int.lt_floor_add_one (Real.logb 2 (geometryNorms s modifier R seed K Z ξ q.val 1))
  rw [hi] at hlo hhi
  have hpow := Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1) hn'
  have hl := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hlo
  have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hhi
  rw [hpow] at hl hh
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one] at hh
  constructor
  · exact hl
  · simpa [geometryDCompensator,geometryNorms,geometryIdeals,mul_comm] using hh
/-- The actual left allocation mass retains only the frozen physical-D
factor and a small power; its entire side exponent remains in the denominator. -/
theorem actual_geometry_left_mass_compensation [DecidableEq ι]
    (s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M Z ξ B ε : ℝ)(hZ : 1<Z)
    (hε : 0≤ε)(hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)
    (a₁ a₂ : ℝ)(ha₁ : 0<a₁)(ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x)(hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    ‖balancedColumnScalar false s modifier R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      hK key (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^M) Z ξ q)) j‖^2*
      ((geometryColumnIdeal false s modifier R seed (Z^M) Z ξ hK key j).absNorm:ℝ)^(ε-1)≤
      (2*(4/((∏i,s.lo i)*a₁*a₂))^2*geometryDCompensator key)*Z^(B*ε)/
        Z^(balancedLeft (Real.logb Z (volume s.toData))
          (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val)) := by
  intro hK
  have hc := actual_geometry_norm_caps s modifier R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val 0
  have hd := actual_geometry_D_compensation s modifier R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource key j.1
  have hcp : 0<(j.1.val.1.val.1.absNorm:ℝ) := zero_lt_one.trans_le hc.1
  have hscalar := actual_geometry_left_scalar_sq s modifier R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j
  have hh := mul_le_mul_of_nonneg_right hscalar
    (Real.rpow_nonneg hcp.le (ε-1))
  apply hh.trans
  exact scalar_left_compensation Z _ _ _ _ _ ε B hZ.le hcp (Nat.cast_nonneg _)
    hd.2.le hε hc.2

/-- Reflection changes the selected ideal but not the physical-D
compensator, so the right allocation mass supplies its reciprocal. -/
theorem actual_geometry_right_mass_compensation (s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)
    (K Z ξ M A B ε : ℝ)(hK : 0<K)(hZ : 1<Z)(hε : 0≤ε)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK key)) :
    ‖balancedColumnScalar true s modifier R seed K Z ξ M A hK key weight j‖^2*
      ((geometryColumnIdeal true s modifier R seed K Z ξ hK key j).absNorm:ℝ)^(ε-1)≤
      (Z^(B*ε)/Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ j.1.val)))/
        geometryDCompensator key := by
  have hd := actual_geometry_D_compensation s modifier R seed K Z ξ B hs hz₁ hz₂ hsource key j.1
  have hc := (actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 1).2
  have he : ‖balancedColumnScalar true s modifier R seed K Z ξ M A hK key weight j‖^2=
      1/Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ j.1.val)) := by
    simp only [balancedColumnScalar,ite_true,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,
      Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),one_div]
  rw [he]
  exact scalar_right_compensation Z _ _ _ ε B hZ.le (geometryDCompensator_pos key) hd.1 hε hc

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_D_compensation
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_left_mass_compensation
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_right_mass_compensation
