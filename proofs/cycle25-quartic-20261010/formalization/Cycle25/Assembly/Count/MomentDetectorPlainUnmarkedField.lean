import Cycle25.Assembly.Count.Parameters
import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import Cycle25.Assembly.Count.MomentDetectorPlainMomentParameters
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25ProbeDetectorPlainUnmarkedField
open ProbeDetectorPlainUnmarkedField Cycle25ProbeFinalAssembly
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch Cycle25ProbeHighRowFamily
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open Cycle25CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def weighted_radialSupportUpper : ℝ := Classical.choose weighted_radialMajorant_support_bound

theorem weighted_radialSupportUpper_spec : 0<weighted_radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic weighted_radialSupportUpper :=
  Classical.choose_spec weighted_radialMajorant_support_bound

lemma weighted_unmarked_power_eq (U m e:ℝ)(hU:1 ≤ U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0<U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1 ≤ 2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m ≤ 1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'


theorem weighted_retained_unmarked_bound (D:Cycle25.Weighted.MomentData)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1<U)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^(weighted_delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (weighted_stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    weighted_retainedSourceEnergy (weighted_initialKeep η Q) F η ∅ j k σ t radialMajorant  ≤ 
      A*diagonalControl radialMajorant*(weighted_detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+weighted_delta D+weighted_stageError D) := by
  let s:=state F η Q radialMajorant weighted_radialSupportUpper (weighted_delta D) hU.le
    (weighted_fixed_parameters D).1.le weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=weighted_unmarked_state_admission D F η Q radialMajorant weighted_radialSupportUpper hU
    weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+weighted_delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width ≤ 2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1 ≤ U^F.m ∧ U^F.m ≤ U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (weighted_detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  change retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤ _
  rw [actual_source_eq F η Q radialMajorant weighted_radialSupportUpper (weighted_delta D) hU.le
    (weighted_fixed_parameters D).1.le weighted_radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one, weighted_detectorProfiles, detectorProfiles] using hz

end SevenEighths.Cycle25ProbeDetectorPlainUnmarkedField

end

end OAI
