import Candidate.Target830.Source.CellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorRemainder
import Candidate.Target830.Source.Reconstruction.GeometryErrorRemainder
import Candidate.Target830.Source.Reconstruction.ZeroScalar
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target830.Source.Reconstruction.GeometryAffineRemainder

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Target830.Source.Reconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
open CenteredMomentPrimeElements CenteredMomentAmplificationErrorEnergy RayFourExpansion
local notation "O" => HeckeFamily.O
variable {plane : SourcePlane}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineErrorRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _



/-- All extracted zero and tail terms are paid after the single literal
prime average. The exact retained norm keeps its own 56/P factor. -/
theorem eventual_actual_affine_error_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,widthLower≤beta ∧ beta≤widthUpper →
      Real.logb Z (volume s)≤plane.total beta →
    ∀P : Finset (Ideal O),P.Nonempty →
      (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^(plane.amp beta)) →
      (∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I) →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    ∀υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
          elementPool P→Fin 3→RayCharacter→Character,
      (56/(P.card:ℝ))*geometryAffineErrorSourceTotal s Ψ Z (plane.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z (plane.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_error_remainder (plane:=plane) (α:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128) 1
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+168*zconst+56*tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop (geometry (Fintype.card ι) (9/4) (9/4) (9/4)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  have ha := (Source.amplifier_pos plane hb).le
  have haB : plane.amp beta≤3 := (Source.source_guards plane hb).2.2.2.1.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (plane.amp beta) (μ/8) (μ/128) t (9/4) (9/4) hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) (by norm_num) (by norm_num) caps.endpoints hpad squarefree_one one_ne_zero
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap P hp hbad hpcap hcop reflected key υ
  have hn : (1:ℝ)≤P.card := by exact_mod_cast hne.card_pos
  have haverageNonneg : 0≤56/(P.card:ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have haverage : 56/(P.card:ℝ)≤56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hzero := actual_error_zero_prime_average P Z (μ/128) hne hZ (by positivity) hp hbad
  have hz := geometry_affine_zero_loss (plane:=plane) Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤zconst := by dsimp [zconst];positivity
  have htconst : 0≤tconst := by dsimp [tconst];positivity
  change 56/(P.card:ℝ)*errorZeroPrimeWeight Z (μ/128) P≤168 at hzero
  have hzavg := mul_le_mul hzero hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤168)
  have htavg := mul_le_mul haverage htail (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤56)
  have h₁ := mul_le_mul_of_nonneg_left hzavg
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htavg
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  have hnorm : geometryAffineErrorSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
      t hZ reflected key P υ≤
      zconst*(p.control {(0,0)})^2*errorZeroPrimeWeight Z (μ/128) P*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (plane.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖geometryAffineErrorRetainedSum s Ψ Z (plane.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineErrorSourceTotal,geometryAffineErrorRetainedSum,
        geometryLowFirstChild,zconst,tconst,map_one,Nat.cast_one,div_one];
      first | rfl | (ring_nf; rfl)
  have hnorm' := mul_le_mul_of_nonneg_left hnorm haverageNonneg
  nlinarith only [hnorm',h₁,h₂,hrest]

end
end OAI.SevenEighths.Target830.Source.Reconstruction
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.eventual_actual_affine_error_remainder
