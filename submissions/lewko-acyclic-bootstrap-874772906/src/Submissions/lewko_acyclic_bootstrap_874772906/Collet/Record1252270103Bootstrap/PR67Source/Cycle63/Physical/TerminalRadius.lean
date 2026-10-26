import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Physical
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentDescentLedger CenteredMomentCommonRadiusSaving
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

/-- The side allowance is its own positive-part cost, not the sum of the
two sides' allowances. The literal main radius uses sigma=3a. -/
theorem actual_main_side_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (U : Finset (CommonIndex I J)) (K X Z j a δ reserve : ℝ) (hZ : 1 < Z)
    (hmod : τ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) U*
        activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K₀ := nominalLog I J E K X Z
    2*c/3-4*a-5*(δ+reserve)/6 ≤
      firstSaving c (d+K₀-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (max (3*c-5*d-R) 0/6)
        (Real.logb Z (mainCommonRadius Z d K₀ c (3*a) δ reserve)-j) a := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  have hg := canonical_saving_gates η τ m I J hI hJ U Z hZ hmod
  have hq := canonical_active_log_le η τ m I J U Z hZ hmod
  dsimp only at hg hq
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have hs := main_saving_lower
    (Real.logb Z ((commonPart I J).absNorm:ℝ))
    (Real.logb Z ((commonPart J I).absNorm:ℝ))
    (nominalLog I J E K X Z-j) (Real.logb Z (τ.modulus.absNorm:ℝ))
    (max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)
    (3*a) δ reserve hg.1 hq.1 (by positivity) (by linarith [hq.2])
  convert hs using 1 <;> congr 1 <;> ring

/-- The actual extracted common parts supply the primewise balance used
after the two joint side-energy estimates. -/
theorem actual_joint_side_exponent (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (Z M A E : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let Bc := max (3*c-5*d-R) 0/6
    let Bd := max (3*d-5*c-R) 0/6
    M-A-R/2-E+((p+A-c+R+E+Bc)+(p+A-d+R+E+Bd))/2 ≤ M := by
  dsimp only
  have hb := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hb
  linarith

end
end Cycle63.Physical

end Record1252270103Bootstrap.PR67
