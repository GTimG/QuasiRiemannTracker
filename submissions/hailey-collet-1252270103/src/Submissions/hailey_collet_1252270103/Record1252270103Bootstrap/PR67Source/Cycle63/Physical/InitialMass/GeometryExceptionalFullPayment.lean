import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalClosure
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFirstExceptionalChildPaid
open CenteredMomentSecondExceptionalFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocationCost CenteredMomentSourceMass CenteredMomentLogDyadic
open CenteredMomentSecondEnergySplit CenteredMomentAmplificationErrorEnergy
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildSourceCaps
open CenteredMomentPrimeElements
open CenteredMomentPrimePool
open CenteredMomentFirstPhysicalSource CenteredMomentRankinRadical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance fullExceptionalSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
theorem actual_geometry_full_error_reference
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (M Z ξ amp reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    (Mprime : Ideal O) [NeZero Mprime] (Hprime : Subgroup (O⧸Mprime)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^amp)))
    (i : Fin 3)
    (Bp : actualAllocations (child s
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) R B
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) t).pools
      ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    let src := geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    geometryExceptionalErrorReference τ I (if reflected then src.C else src.D)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      (Z^M) (geometryExceptionalVolume s) Z (3*amp) (frequencyLoss Z 32 ξ) reserve
      (inputCap Z (twiceChild s I R B τ t (Ideal.span {p}) (errorIndex i+1) Bp υ v))
      p (errorIndex i+1)≤
      Z^(Real.logb Z (geometryExceptionalVolume s)-
        (M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
  have hk : errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7 := by
    fin_cases i <;> norm_num [errorIndex]
  have hp' : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^((3*amp)/3))) := by
    simpa only [show (3*amp)/3=amp by ring] using hp
  have hklog : Real.logb Z (Z^M)=M := Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hm := actual_geometry_column_modulus reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  cases reflected
  · have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter false s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.C src.D
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hC src.hD src.sameSupport src.inactive rfl s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh
  · have hm' : (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus=
        s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
          Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.D src.C=>q.val)
            (swapSubset src.C src.D src.inactive)*activeConductor src.D src.C} := by
      rw [swapped_modulus_factor]
      exact hm
    have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.D src.C
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hD src.hC src.sameSupport.symm (swapSubset src.C src.D src.inactive)
      (by rw [swapSubset_generator]) s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm'
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
