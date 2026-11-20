/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B137
import Candidate.Bundles.B154
import Candidate.Bundles.B155
import Candidate.Bundles.B156
import Candidate.Bundles.B158
import Candidate.Bundles.B159

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRemainder; sha256 90e2e23cc5b3098e8dee7fe13852572508808f6ff421a04891ef87a43fb7e6b9 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                              
                                                                   
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
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
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The main source before retained contraction, with the original allocation
weights and the actual slot cardinality in its Fourier scale. -/
def geometryAffineMainSourceTotal (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ) (hZ : 1< Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let phase := fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
  ∑q : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key,
    geometryAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2 *
    actualMainSource (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t q)
      (geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key q.1.val) Z (3*amp) 1 ξ reserve

/-- The small losses in the width-one zero term leave a fixed strict saving. -/
theorem geometry_affine_zero_loss (Z μ A beta : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : 3401/100000≤ beta ∧ beta≤1/25)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    zeroPaymentExponent Z 1 A (Cycle61.Arithmetic.amp beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(1/20:ℝ) := by
  have hpaid := geometry_zero_exponent_saving Z 1 A (Cycle61.Arithmetic.amp beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/100 := by nlinarith
  simpa only [neg_div] using hpaid hbudget

/-- Genuine source and cone receipts pay the complete zero and tail terms.
Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_remainder
    (Cs μ : ℝ) (hCs : 1≤ Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,3401/100000≤ beta ∧ beta≤1/25 →
      Real.logb Z (volume s)≤ Cycle61.Arithmetic.totalA beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      geometryAffineMainSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (ι:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128) 1
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+zconst+tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop ((9/4:ℝ)^(Fintype.card ι)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps beta hb hcone Ψ t reflected key
  have ha := (Cycle61.Arithmetic.amp_pos hb).le
  have haB : Cycle61.Arithmetic.amp beta≤3 := (Cycle61.Arithmetic.amp_bounds hb).2.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (Cycle61.Arithmetic.amp beta) (μ/8) (μ/128) t hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad squarefree_one one_ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤ zconst := by dsimp [zconst];positivity
  have htconst : 0≤ tconst := by dsimp [tconst];positivity
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htail
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  simp only [map_one,Nat.cast_one,div_one] at hh
  have hnorm : geometryAffineMainSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (Cycle61.Arithmetic.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineMainSourceTotal,geometryMainRetainedSum,
        geometryLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,one_mul]; ring
  nlinarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_zero_loss
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_main_remainder

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorRemainder; sha256 4b65b57100a97a8f904a66c78aefc41f13739406379490cac168eada8ed75165 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                           

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineErrorRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

section Source
variable (s : Input ι) (Ψ : 𝓢(ℝ,ℂ)) (Z amp ξ reserve t : ℝ) (hZ : 1< Z)
  (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) (P : Finset (Ideal O))
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
local notation "AFIndex" => GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key
variable (υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
    elementPool P→ Fin 3→ RayCharacter→ Character)
local notation "phase" => (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
local notation "first" => geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t
local notation "g" => (fun f : AFIndex=>geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key (Subtype.val (Sigma.fst f)))
local notation "w" => (fun f : AFIndex=>geometryAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
  (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) (Subtype.val (Sigma.fst f)) (Sigma.snd f))

/-- The complete extracted source before the prime average. First allocation
weights remain undivided. -/
def geometryAffineErrorSourceTotal : ℝ :=
  ∑f : AFIndex,w f*actualErrorSources (ι:=liveIndices f.2.val) (first f) (g f) Z (3*amp) 1 ξ reserve P (υ f)

/-- The exact retained term, using the original extracted Fourier cutoff. -/
def geometryAffineErrorRetainedSum : ℂ :=
  jointErrorRetained (First:=AFIndex) (fun f : AFIndex=>liveIndices f.2.val) first g w ballProfile
    Z (3*amp) ξ reserve P υ
    (fun f q i=>firstErrorTailFourier (Fintype.card ι) (9/4) (volume s)
      (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key (Subtype.val (Sigma.fst f)))
      q.val (errorIndex i+1)
      (firstErrorTailRadius reflected (geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hK key (Subtype.val (Sigma.fst f)))
        Z 1 (volume s) amp (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)))
end Source

/-- All extracted zero and tail terms are paid after the single literal
prime average. The exact retained norm keeps its own 56/P factor. -/
theorem eventual_actual_affine_error_remainder
    (Cs μ : ℝ) (hCs : 1≤ Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,3401/100000≤ beta ∧ beta≤1/25 →
      Real.logb Z (volume s)≤ Cycle61.Arithmetic.totalA beta →
    ∀P : Finset (Ideal O),P.Nonempty →
      (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^(Cycle61.Arithmetic.amp beta)) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    ∀υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
          elementPool P→ Fin 3→ RayCharacter→ Character,
      (56/(P.card:ℝ))*geometryAffineErrorSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_error_remainder (α:=ι)
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
  have ha := (Cycle61.Arithmetic.amp_pos hb).le
  have haB : Cycle61.Arithmetic.amp beta≤3 := (Cycle61.Arithmetic.amp_bounds hb).2.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (Cycle61.Arithmetic.amp beta) (μ/8) (μ/128) t (9/4) (9/4) hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) (by norm_num) (by norm_num) caps.endpoints hpad squarefree_one one_ne_zero
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap P hp hbad hpcap hcop reflected key υ
  have hn : (1:ℝ)≤ P.card := by exact_mod_cast hne.card_pos
  have haverageNonneg : 0≤56/(P.card:ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have haverage : 56/(P.card:ℝ)≤56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hzero := actual_error_zero_prime_average P Z (μ/128) hne hZ (by positivity) hp hbad
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤ zconst := by dsimp [zconst];positivity
  have htconst : 0≤ tconst := by dsimp [tconst];positivity
  have hzavg := mul_le_mul hzero hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤168)
  have htavg := mul_le_mul haverage htail (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤56)
  have h₁ := mul_le_mul_of_nonneg_left hzavg
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htavg
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  have hnorm : geometryAffineErrorSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta) (μ/64) (μ/8)
      t hZ reflected key P υ≤
      zconst*(p.control {(0,0)})^2*errorZeroPrimeWeight Z (μ/128) P*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (Cycle61.Arithmetic.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖geometryAffineErrorRetainedSum s Ψ Z (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineErrorSourceTotal,geometryAffineErrorRetainedSum,
        geometryLowFirstChild,zconst,tconst,map_one,Nat.cast_one,div_one];
      first | rfl | (ring_nf; rfl)
  have hnorm' := mul_le_mul_of_nonneg_left hnorm haverageNonneg
  nlinarith only [hnorm',h₁,h₂,hrest]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_remainder

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedAssembly; sha256 cef246d8c092f92299eba29bf10d4a061b3b9bba5d1c8c53cced79677612702b -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                           

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError
local notation "O" => HeckeFamily.O
local instance errorNormalizedAssemblyDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- The genuine ordinary filter admits either ray of the full physical
pair. Its complete row set is independent of which ray names the filter. -/
theorem actual_error_ordinary_rows_eq (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) :
    partRows false η χ Q fixedBadMask C D U R=
      partRows false η ψ Q fixedBadMask C D U R := by
  ext z
  exact (actual_error_ordinary_rows_neg η χ 1 Q hQ C D U R z).symm.trans
    (actual_error_ordinary_rows_neg η ψ 1 Q hQ C D U R z)

/-- Right columns sum over the literal negated physical row. Reindexing
this entire set occurs before either common allocation or residual ideal. -/
theorem actual_error_complete_right_rows (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (f : O→ℝ) :
    (∑z∈partRows false η χ Q fixedBadMask C D U R,f (-z))=
      ∑z∈partRows false η ψ Q fixedBadMask C D U R,f z := by
  apply Finset.sum_bij (fun z _=>-z)
  · intro z hz
    exact (actual_error_ordinary_rows_neg η χ ψ Q hQ C D U R z).mpr hz
  · intro z hz z' hz' heq
    exact neg_inj.mp heq
  · intro z hz
    refine ⟨-z,(actual_error_ordinary_rows_neg η ψ χ Q hQ C D U R z).mpr hz,?_⟩
    exact neg_neg z
  · intro z hz
    rfl

/-- Complete actual columns use the admitted ray-specific ordinary sets,
with the right inverse ray at its original negative height shift. -/
theorem actual_error_complete_column_rows {ι : Type*}[Fintype ι]
    (s : Input ι)(τ : RayCharacter→ Character)
    (C D : Ideal O)(hC : Supported C)(hD : Supported D)
    (U : Finset (CommonIndex C D))(R seed L Q : Ideal O)(radius : ℝ)
    (hQ : Q≤ Ideal.span {(72:O)})(χ₀ χ ψ : RayCharacter)(second : Bool)(t u : ℝ) :
    (∑z∈partRows false s.η χ₀ Q fixedBadMask C D U radius,
      if second then
        ‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L (-z)‖^2
      else
        ‖normalizedColumn (withHeight s (τ χ) (s.t+2*Real.pi*(u-t))) C hC R seed L z‖^2)=
    if second then
      ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask C D U radius,
        ‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L z‖^2
    else
      ∑z∈partRows false s.η χ Q fixedBadMask C D U radius,
        ‖normalizedColumn (withHeight s (τ χ) (s.t+2*Real.pi*(u-t))) C hC R seed L z‖^2 := by
  cases second
  · simp only [Bool.false_eq_true,ite_false]
    rw [actual_error_ordinary_rows_eq s.η χ₀ χ Q hQ C D U radius]
  · simp only [ite_true]
    exact actual_error_complete_right_rows s.η χ₀ ψ⁻¹ Q hQ C D U radius
      (fun z=>‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L z‖^2)

/-- The degree, profile control and threshold precede the moving finite
block family. Each column comes from the genuine paid error estimate. -/
theorem actual_paid_error_column_family_after_threshold {α : Type*}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hJ : 0< J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀{Label : Type*}[Fintype Label],∀q : Label→ Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4≤ Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→ Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→ RayFourExpansion.RayCharacter)(hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun j=>retainedState Z Bmask hZ ((g j).τ (χ j)) (internalQ Q η₀)
      ((q j).R₂*(q j).E₂) (hP j) (hPN j) (g j).radius (g j).C (g j).D (g j).U
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→ Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀(Ds : Label→ Finset (Ideal O))(T : Label→ℝ),(∀j,1≤ T j) →
      (∀j,∀D∈Ds j,Squarefree D ∧ T j≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T j) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤ weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
      Cg*∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
        ((src j).toData.profileFactor*(∏a,(src j).M a)^2*
          QuadraticInitialBound.diagonalControl (st j).radial.profile*(p.control Sp)^2*
          (1+|v|+height)^degree*((q j).E₂.absNorm:ℝ)^(εshell-1)*(2*T j)^(3*εshell)*
          Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
            εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)) := by
  obtain ⟨degree,Sp,hbound⟩ := actual_paid_error_column_uniform (α:=α) M H hH W A B ap bp
    Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp hBmask hL hMcap
    hεold hloss hmargin hbeta ηseed bs J εwidth εpad Mmin window pad εshell
    hwindow hpad heshell hbs hJ hew hep hmin
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hZs⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hZs] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap' hslot haff
    cell amp Label _ q hk hprime g χ hP hPN st src p hp₁ hp₂ seed hE₂ hseed Ds T hT hDs P weight
    hwgt coefficient rows
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hrow (z : O) (hz : z∈rows j) := actual_error_complete_row_admission s (q j)
    Z Mrow amp omega ξ bs J (g j) Bmask hZ (χ j) (internalQ Q η₀) (hP j) (hPN j) z hz
  have hcol := hz.2 hZ s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL
    hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap'
    hslot haff (q j) (hk j) (hprime j) (g j) (χ j) (hP j) (hPN j) p hp₁ hp₂
    (seed j) (hE₂ j) (hseed j) (Ds j) (T j) (hT j) (hDs j) (rows j) (fun _=>1)
    (fun _ _=>zero_le_one) (fun z hz=>(hrow z hz).1) (fun z hz=>(hrow z hz).2)
  simp only [one_mul] at hcol
  have hc : 0≤ coefficient j := by
    dsimp only [coefficient]
    have hv := volume_pos (src j)
    have hn : 0≤(P.card:ℝ) := Nat.cast_nonneg _
    have hwj := hwgt j
    positivity
  apply error_column_paid_restore (q j).p (q j).k Z (coefficient j) _ Cg _
    (zero_lt_one.trans hZ) hc
  convert hcol using 1
  dsimp only [src,st]
  ring_nf


/-- Literal positive normalized source sum with the exact prime coefficient,
now expressed in the complete ordinary columns admitted by the paid theorem. -/
theorem actual_error_full_normalized_to_admitted_columns {α : Type*} [Fintype α] [DecidableEq α]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤ weight) (p : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (hcard : Fintype.card α≤ N) (hlower : a≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x) (hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : rows→ RayCharacter) (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
    (reflected : Bool) (t u : ℝ) :
    let d := fun n : rows=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK n.val
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) p i
    let w := fun n : rows=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ n.val
    secondNormalizedSum reflected datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      (c*(K/lowerFactor N a ap))*
      ∑n : rows,∑χ : RayCharacter,∑ψ : RayCharacter,
        normalizer (d n).C (d n).D (d n).inactive*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if reflected then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
  intro d datum c w
  apply (actual_error_full_normalized_to_columns slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
    rows P weight hw p i N a ap ha hap hcard hlower hW₁ hW₂ W χ₀ Q reflected t u).trans_eq
  apply congrArg (fun r : ℝ=>(c*(K/lowerFactor N a ap))*r)
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  apply congrArg (fun r : ℝ=>normalizer (d n).C (d n).D (d n).inactive*r)
  apply Finset.sum_congr rfl
  intro D hD
  exact actual_error_complete_column_rows s (d n).τ (d n).C (d n).D (d n).hC (d n).hD
    (d n).inactive R seed D Q (d n).radius hQ (χ₀ n) χ ψ reflected t u


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_ordinary_rows_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_complete_right_rows
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_complete_column_rows

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_paid_error_column_family_after_threshold

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_full_normalized_to_admitted_columns


end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedAssembly -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondProjectorShell; sha256 85e4628b7948a2f64eff89e8c37f3b73ef5945f19e0d86deee1bbf086a46caad -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid CompletedGauss
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance projectorShellSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Union before taking norm dyads: its size never counts the moving labels. -/
def sharedProjectors {Label : Type*} [Fintype Label] (Ds : Label→ Finset (Ideal O)) :
    Finset (Ideal O) := Finset.univ.biUnion Ds

lemma mem_sharedProjectors {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O)) (l : Label) (D : Ideal O) (hD : D∈Ds l) :
    D∈sharedProjectors Ds := Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hD⟩

/-- Squarefree projectors have their literal common dyadic shell, with T≥1. -/
theorem shared_projector_shell_gates {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell (sharedProjectors Ds) n) :
    Squarefree D ∧ D≠0 ∧ dyadicScale n≤(D.absNorm:ℝ) ∧
      (D.absNorm:ℝ)<2*dyadicScale n := by
  have h:=shell_member_data _ _ _ hD
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- Exact common-shell reindexing retains the per-label membership filter. -/
theorem shared_projector_shell_sum {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O)) (hs : ∀l D,D∈Ds l→ Squarefree D)
    (cost : Label→ Ideal O→ℝ) :
    (∑l,∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),∑l,
        ∑D∈shell (sharedProjectors Ds) n,if D∈Ds l then cost l D else 0 := by
  have hpoint (l : Label) : (∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),
        ∑D∈shell (sharedProjectors Ds) n,if D∈Ds l then cost l D else 0 := by
    have hsum := sum_norm_moebius_shells (sharedProjectors Ds)
      (fun D=>if D∈Ds l then cost l D else 0)
    have hm (D : Ideal O) (hD : D∈Ds l) : ‖(moebius D:ℂ)‖=1 :=
      squarefree_moebius_norm D (hs l D hD)
    have hleft : (∑D∈sharedProjectors Ds,‖(moebius D:ℂ)‖*
        (if D∈Ds l then cost l D else 0))=∑D∈Ds l,cost l D := by
      simp only [mul_ite,mul_zero]
      rw [←Finset.sum_filter]
      apply (Finset.sum_congr ?_ ?_)
      · ext D
        simp only [Finset.mem_filter]
        exact ⟨fun h=>h.2,fun h=>⟨mem_sharedProjectors Ds l D h,h⟩⟩
      · intro D hD
        rw [hm D hD,one_mul]
    rw [hleft] at hsum
    apply hsum.trans
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hd : D∈Ds l
    · simp only [hd,ite_true,hm D hd,one_mul]
    · simp only [hd,ite_false,mul_zero]
  simp_rw [hpoint]
  exact Finset.sum_comm

/-- Enlarge a positive cost to the shared shell, without paying label count. -/
theorem shared_projector_shell_sum_le {Label : Type*} [Fintype Label]
    (Ds : Label→ Finset (Ideal O)) (hs : ∀l D,D∈Ds l→ Squarefree D)
    (cost : Label→ Ideal O→ℝ) (hc : ∀l D,0≤ cost l D) :
    (∑l,∑D∈Ds l,cost l D)≤
      ∑n∈selectedShells (sharedProjectors Ds),∑l,∑D∈shell (sharedProjectors Ds) n,cost l D := by
  rw [shared_projector_shell_sum Ds hs cost]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro D hD
  split_ifs
  · exact le_rfl
  · exact hc l D

/-- Constants precede every finite family. One extra small power pays the
union of projector norm dyads; the four source-block dyads are separate. -/
theorem shared_projector_shell_subpower (L ε : ℝ) (hL : 0≤ L) (he : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{Label : Type*}[Fintype Label](Ds : Label→ Finset (Ideal O)),
      (∀l D,D∈Ds l→(D.absNorm:ℝ)≤ Z^L) →
      ((selectedShells (sharedProjectors Ds)).card:ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L ε hL he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ Ds hcap
  apply hz.2
  intro D hD _
  obtain ⟨l,_,hl⟩:=Finset.mem_biUnion.mp hD
  exact hcap l D hl

/-- A scalar estimate for each entire shared shell pays the full projector
sum. No allocation or source is selected after an individual row. -/
theorem shared_projector_shell_payment (L ε : ℝ) (hL : 0≤ L) (he : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{Label : Type*}[Fintype Label](Ds : Label→ Finset (Ideal O)),
      (∀l D,D∈Ds l→ Squarefree D) →
      (∀l D,D∈Ds l→(D.absNorm:ℝ)≤ Z^L) →
      ∀(cost : Label→ Ideal O→ℝ)(E : ℝ),(∀l D,0≤ cost l D) → 0≤ E →
      (∀n∈selectedShells (sharedProjectors Ds),
        (∑l,∑D∈shell (sharedProjectors Ds) n,cost l D)≤ E) →
      (∑l,∑D∈Ds l,cost l D)≤ C*Z^ε*E := by
  obtain ⟨C,hC,hbound⟩:=shared_projector_shell_subpower L ε hL he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ Ds hs hcap cost E hc hE hpay
  apply (shared_projector_shell_sum_le Ds hs cost hc).trans
  calc
    _≤∑n∈selectedShells (sharedProjectors Ds),E := Finset.sum_le_sum (fun n hn=>hpay n hn)
    _=((selectedShells (sharedProjectors Ds)).card:ℝ)*E := by simp
    _≤ _ := mul_le_mul_of_nonneg_right (hz.2 Ds hcap) hE

/-- Literal second divisors are divisors of padded sector ideals, so the
bound covers zero coefficients as well as retained ordinary blocks. -/
theorem second_block_projector_norm (s : SecondBlockSource) (Y : ℝ)
    (hpool : ∀I∈s.pool,(I.absNorm:ℝ)≤ Y) (D : Ideal O) (hD : D∈s.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤ Y := by
  apply divisorPool_nonzero_norm Finset.univ
    (fun J : sectorPool s.D s.hD.1 s.pool=>(J:Ideal O))
    (fun J _=>(sectorPool_supported s.D s.hD.1 s.pool J).1) Y _ D hD
  intro J _
  have hj := (mem_residualPool s.D s.hD.1 (supportedColumns s.pool) J.val).mp
    (Finset.mem_filter.mp J.property).1
  have hne : s.D*J.val≠0 := (Finset.mem_filter.mp hj).2.1
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le J.val (s.D*J.val) hne
    (dvd_mul_left _ _)).trans (hpool _ (Finset.mem_filter.mp hj).1)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Actual datum projector cap from its literal independent source pools. -/
theorem second_datum_projector_cap (d : SecondInputDatum α) (N : ℕ) (Z U : ℝ)
    (hN : Fintype.card d.slots≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀i I,I∈d.input.pools i→(I.absNorm:ℝ)≤ Z^U)
    (D : Ideal O) (hD : D∈d.block.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) :=
  second_block_projector_norm d.block _ (actual_finite_pool_cap d.input N Z U hN hZ hU hpool) D hD

/-- Ordinary row restriction does not change the residual projector pool. -/
theorem ordinary_second_projectors (d : SecondInputDatum α)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O) :
    (ordinarySecondDatum d χ Q m).block.divisors=d.block.divisors := rfl

/-- The common-allocation child keeps original slot pools and takes literal
ideal quotients for its plains; quotient norms cannot grow. -/
theorem actual_child_pool_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t Y : ℝ)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Y) :
    ∀i I,I∈(child s C R B τ t).pools i→(I.absNorm:ℝ)≤ Y := by
  intro i I hI
  cases i with
  | inl j => exact hpool (Sum.inl j.val) I hI
  | inr j =>
    fin_cases j
    · have hj := (mem_residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁ I).mp hI
      have hne := (child s C R B τ t).pools_ne _ I hI
      apply (CenteredMomentFirstSourceConductorCaps.divisor_norm_le I _
        (mul_ne_zero (alloc_ne s C B _) hne) (dvd_mul_left _ _)).trans
      exact hpool (Sum.inr 0) _ hj
    · have hj := (mem_residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂ I).mp hI
      have hne := (child s C R B τ t).pools_ne _ I hI
      apply (CenteredMomentFirstSourceConductorCaps.divisor_norm_le I _
        (mul_ne_zero (alloc_ne s C B _) hne) (dvd_mul_left _ _)).trans
      exact hpool (Sum.inr 1) _ hj

/-- Every selected shared shell has its genuine common scale in [1,Z^L]. -/
theorem shared_projector_shell_scale {Label : Type*}[Fintype Label]
    (Ds : Label→ Finset (Ideal O))(Z L : ℝ)
    (hcap : ∀l D,D∈Ds l→(D.absNorm:ℝ)≤ Z^L)
    (n : ℤ)(hn : n∈selectedShells (sharedProjectors Ds)) :
    1≤ dyadicScale n ∧ dyadicScale n≤ Z^L := by
  apply selected_scale_bounds (sharedProjectors Ds) (Z^L) _ n hn
  intro D hD _
  obtain ⟨l,_,hl⟩:=Finset.mem_biUnion.mp hD
  exact hcap l D hl

/-- First projector union with its exact retained arithmetic identity. -/
def firstProjectorSet {ι : Type*}[Fintype ι]
    (s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ))
    (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) :
    Finset (Ideal O) := rows.image (fun j=>j.2.1.val)

theorem actual_first_projector_set_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(N : ℕ)(R seed : Ideal O)(K Z ξ U : ℝ)(hK : 0< K)
    (hN : Fintype.card ι≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U)
    (key : ℤ×(Fin 5→ℤ))
    (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) :
    ∀D∈firstProjectorSet s R seed K Z ξ hK key rows,(D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  intro D hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact actual_geometry_projector_cap s N R seed K Z ξ U hK hN hZ hU hpool key j

/-- The additional first-projector shell count is uniform before sources,
labels, allocation choices and Mellin heights. -/
theorem actual_first_projector_shell_subpower (N : ℕ)(U ε : ℝ)
    (hU : 0≤ U)(he : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),Fintype.card ι≤ N →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))),
      ((selectedShells (firstProjectorSet s R seed K Z ξ hK key rows)).card:ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower (((N:ℝ)+2)*U) ε (by positivity) he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hN hpool R seed K ξ hK key rows
  exact hz.2 _ (fun D hD _=>actual_first_projector_set_cap s N R seed K Z ξ U hK
    hN hz.1.le hU hpool key rows D hD)

/-- Original actual block constructor has the padded-pool projector cap. -/
theorem actual_second_block_projector_cap (slots : Finset α)(s : Input slots)(N : ℕ)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ U : ℝ)(hK : 0< K)(hN : Fintype.card slots≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)(D : Ideal O)
    (hD : D∈(actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) :=
  second_datum_projector_cap _ N Z U hN hZ hU hpool D hD

/-- Ordinary blocks have exactly the same projector cap, even if their
restricted physical block vanishes. -/
theorem ordinary_second_projector_cap (d : SecondInputDatum α)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card d.slots≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀i I,I∈d.input.pools i→(I.absNorm:ℝ)≤ Z^U)
    (χ : RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)(D : Ideal O)
    (hD : D∈(ordinarySecondDatum d χ Q m).block.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) :=
  second_datum_projector_cap d N Z U hN hZ hU hpool D hD

/-- Uniform shared second-projector shell count for all moving block labels,
using literal source-pool caps and no arithmetic-label cardinality. -/
theorem actual_second_projector_shell_subpower (N : ℕ)(U ε : ℝ)
    (hU : 0≤ U)(he : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{Label : Type*}[Fintype Label](d : Label→ SecondInputDatum α),
      (∀l,Fintype.card (d l).slots≤ N) →
      (∀l i I,I∈(d l).input.pools i→(I.absNorm:ℝ)≤ Z^U) →
      ((selectedShells (sharedProjectors (fun l=>(d l).block.divisors))).card:ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=shared_projector_shell_subpower (((N:ℝ)+2)*U) ε (by positivity) he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ d hN hpool
  exact hz.2 _ (fun l D hD=>(second_datum_projector_cap (d l) N Z U (hN l)
    hz.1.le hU (hpool l) D hD).2)

/-- Exact per-label subset of the common shell. Allocator dependence on D
may remain in cost; neither the label nor the projector is identified. -/
def sharedLabelProjectorShell {Label : Type*}[Fintype Label]
    (Ds : Label→ Finset (Ideal O))(l : Label)(n : ℤ) : Finset (Ideal O) :=
  (shell (sharedProjectors Ds) n).filter (fun D=>D∈Ds l)

theorem shared_label_projector_shell_gates {Label : Type*}[Fintype Label]
    (Ds : Label→ Finset (Ideal O))(l : Label)(n : ℤ)(D : Ideal O)
    (hD : D∈sharedLabelProjectorShell Ds l n) :
    D∈Ds l ∧ Squarefree D ∧ dyadicScale n≤(D.absNorm:ℝ) ∧
      (D.absNorm:ℝ)<2*dyadicScale n := by
  obtain ⟨hd,hl⟩:=Finset.mem_filter.mp hD
  have hg:=shared_projector_shell_gates Ds n D hd
  exact ⟨hl,hg.1,hg.2.2⟩

theorem shared_label_projector_shell_sum {Label : Type*}[Fintype Label]
    (Ds : Label→ Finset (Ideal O))(hs : ∀l D,D∈Ds l→ Squarefree D)
    (cost : Label→ Ideal O→ℝ) :
    (∑l,∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),∑l,
        ∑D∈sharedLabelProjectorShell Ds l n,cost l D := by
  rw [shared_projector_shell_sum Ds hs cost]
  simp only [sharedLabelProjectorShell,Finset.sum_filter]

/-- Native child block cap from ORIGINAL pool caps, without any surviving
coefficient or row premise. Fixed original N also bounds live child slots. -/
theorem actual_child_second_projector_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(N : ℕ)(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁)
    (χ : Character)(t : ℝ)(Z U : ℝ)(hN : Fintype.card ι≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U)
    (R seed C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
    (heq : primeSupport C₂=primeSupport D₂)(V : Finset (CommonIndex C₂ D₂))
    (radius : ℝ)(rows : Finset O)(hrows : ∀z∈rows,z≠0)(K : ℝ)(hK : 0< K)(n : Fin 4→ℤ)
    (D : Ideal O)
    (hD : D∈(originalSecondBlock (child s C₁ R₁ B₁ χ t) R seed C₂ D₂ hC₂ hD₂ heq
      V radius rows hrows K hK n).divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  have hcard : Fintype.card (liveIndices B₁.val)≤ N := by
    apply le_trans _ hN
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices B₁.val)
  exact second_block_projector_norm _ _
    (actual_finite_pool_cap (child s C₁ R₁ B₁ χ t) N Z U hcard hZ hU
      (actual_child_pool_cap s C₁ R₁ B₁ χ t (Z^U) hpool)) D hD

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.shared_projector_shell_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.shared_projector_shell_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_datum_projector_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_pool_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_projector_shell_subpower
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_projector_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_second_projector_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_projector_shell_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.shared_label_projector_shell_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_second_projector_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondProjectorShell -/
