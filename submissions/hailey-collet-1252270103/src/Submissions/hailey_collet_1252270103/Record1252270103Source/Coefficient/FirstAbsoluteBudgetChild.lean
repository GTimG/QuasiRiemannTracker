/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal allocated child polynomial has a uniform absolute bound at
every character and height, with the original ordinary profile control. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudgetPolynomial
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalChildBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization QuadraticInitialBound
open Record1252270103Source QRH.Record1252270103Source.ForcedCost
open QRH.Record1252270103Source.SecondAbsoluteEnvelope
local notation "O"=>HeckeFamily.O
local instance absoluteChildSumDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem child_dyadic_absolute {ι:Type*} [Fintype ι]
    (N:ℕ) (Cs hi whi wlo X Y:ℝ) (hCs:1≤Cs) (hhi:1≤hi)
    (hwhi:0≤whi) (hwlo:0<wlo) (hX:1≤X) (hY:0≤Y)
    (s:Input ι) (modifier:Tuple ι→ℂ)
    (hN:Fintype.card ι≤N) (hM:∀i,s.M i≤Cs)
    (hslot0:∀i,1≤s.hi i) (hslot:∀i,s.hi i≤hi) (hP:∀i,1≤s.P i)
    (hb₁:0≤s.b₁) (hb₂:0≤s.b₂) (hsource:sourceRadius s≤Y)
    (hmod:∀v,‖modifier v‖≤2)
    (W₁ W₂:𝓢(ℝ,ℂ)) (he₁:s.W₁=W₁) (he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (C R L:Ideal O) (B:actualAllocations s.pools C) (τ:Character) (t:ℝ)
    (n:ℤ) (hscale:dyadicScale n≤X) :
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖High.CoupledFirst.childPolynomial s modifier C R L B τ t (volume s) z‖^2)≤
      diagonalControl ballProfile*X*Y*(massConstant N Cs hi whi)^2*
        (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s := by
  let s':=child s C R B τ t
  let mod':=pulledModifier B.val modifier
  let S:=finiteColumns (Fintype.piFinset s'.pools)
  let β:=High.CoupledFirst.coefficient s' mod' (R*C) L
  have hn:Fintype.card (liveIndices B.val)≤N := by
    calc
      _≤Fintype.card ι := by simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices B.val)
      _≤N:=hN
  have hm:∀v∈Fintype.piFinset s'.pools,‖mod' v‖≤2 := by
    intro v _
    exact hmod _
  have hv:volume s'≤volume s := (child_volume_ordinary_bound s C R B τ t hP).trans
    (div_le_self (volume_pos s).le (ordinaryNorm_ge_one s C B))
  have hmass: (∑I∈S,‖β I‖)≤massConstant N Cs hi whi*
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*volume s := by
    apply (modified_coefficient_mass N Cs hi whi wlo hCs hhi hwhi hwlo s' mod' (R*C) L
      hn (fun i=>hM i.val) (fun i=>hslot i.val) hm W₁ W₂ he₁ he₂ hs₁ hs₂).trans
    exact mul_le_mul_of_nonneg_left hv (mul_nonneg (massConstant_nonneg N Cs hi whi
      (zero_le_one.trans hCs) (zero_le_one.trans hhi))
      (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  have zeroW (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi) : W 0=0 := by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  have hz₁:s'.W₁ 0=0 := by change s.W₁ 0=0;rw [he₁];exact zeroW W₁ hs₁
  have hz₂:s'.W₂ 0=0 := by change s.W₂ 0=0;rw [he₂];exact zeroW W₂ hs₂
  have hcap:∀I∈S,β I≠0→(I.absNorm:ℝ)≤Y := by
    intro I _ hI
    exact (High.CoupledFirst.original_column_norm s' mod' (R*C) L I hz₁ hz₂ hI).2.trans
      ((InitialPhysical.child_source_radius_le s C R B τ t hslot0 hP hb₁ hb₂).trans hsource)
  change (∑'z:O,dyadicWeight n (normValue z)*
    ‖CenteredMomentGaussEnergy.gaussPolynomial Finset.univ
      (CenteredMomentSourceRow.sourceGenerator S) (CenteredMomentSourceRow.sourceGenerator_supported S)
      (fun I:CenteredMomentSourceRow.supportedColumns S=>(Real.sqrt (volume s):ℂ)⁻¹*
        (β I*CenteredMomentHeckeExpansion.rowWeight τ CenteredMomentSecondHeightFamily.fixedBadMask 1 1 t I)) z‖^2)≤_
  apply (normalized_dyadic_source S β τ t Y (volume s) X hY (volume_pos s) hX hcap n hscale).trans
  calc
    _≤diagonalControl ballProfile*X*(Y/volume s*
        (massConstant N Cs hi whi*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*volume s)^2) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hmass 2)
          (div_nonneg hY (volume_pos s).le))
      exact mul_nonneg (diagonalControl_nonneg _) (zero_le_one.trans hX)
    _=_ := by field_simp

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.child_dyadic_absolute
