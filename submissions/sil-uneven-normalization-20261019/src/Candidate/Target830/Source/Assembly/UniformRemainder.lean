import Candidate.Target830.Source.CellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryMainTail
import Candidate.Target830.Source.Reconstruction.GeometryZeroPayment
import Candidate.Target830.Source.Assembly.BalancedSecondSplit
import Candidate.Target830.Source.Reconstruction.GeometryMainRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Candidate.Target830.Source.Assembly.BalancedRetained
import Candidate.Target830.Source.Reconstruction.ZeroScalar
import Candidate.Target830.Source.Reconstruction.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
import Candidate.Target830.Source.Reconstruction.GeometryAffineExceptionalGates
import Candidate.Target830.Source.Reconstruction.GeometryAffineErrorRemainder

/- Original module: Candidate.Target830.Source.Assembly.BalancedMainRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Cycle63InitialMass Reconstruction
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {plane : SourcePlane}
local instance mainRemainderDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

open EisensteinSchwartzPoisson CenteredMomentSecondLocalization
/-- The actual amplified main source is reduced to its single joint retained
sum. The full zero and discarded contributions are paid uniformly from the
original profiles, with the physical-D and seed factors preserved. -/
theorem eventual_actual_geometry_main_remainder {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hlo : 0< lo)(hhi : 0≤ hi)(hslotlo : 0< slotlo)
    (hB : 0≤ B)(hU : 0≤ U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0< Czero ∧ 0< Ctail ∧
    ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤ N → (∀j,s.M j≤ Cs) → s.upper≤ b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1< Z),
      widthLower≤ beta ∧ beta≤ widthUpper →
      0≤ M → M≤ B → 0≤ a → a≤ B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤ B →
      Real.logb Z (volume s)≤ M*plane.total beta →
      a≤ M*plane.amp beta → b^N≤ Z^padding →
      Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=> logAnnulus)
    let C := fun j : rows=> geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let source := fun (j : rows)(alloc : actualAllocations s.pools (C j))=>
      child s (C j) R alloc (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
    let radius := fun j : rows=> firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
    let Fourier := fun j : rows=> firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*a) reserve b N
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
    let weight := fun q=> normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let scalar : (j : rows) → actualAllocations s.pools (C j) → ℝ := fun j alloc=>
      balancedAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),scalar j alloc*
      actualMainSource (source j alloc) (geometryBranch reflected s R seed (Z^M) Z ξ hK key j.val)
        Z (3*a) 1 ξ reserve)≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier ballProfile 0‖*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(Reconstruction.zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ)+
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(-saving)/(seed.absNorm:ℝ)+
      ‖∑j : rows,∑alloc : actualAllocations s.pools (C j),
        ((scalar j alloc/volume (source j alloc):ℝ):ℂ)*
          secondRetainedEnergy (source j alloc).η (source j alloc).t
            (original (source j alloc) (R*C j) j.val.2.1.val).columns
            (original (source j alloc) (R*C j) j.val.2.1.val).beta
            ballProfile (radius j) (Fourier j) Z ξ‖ := by
  obtain ⟨F,Ct,hCt,htail⟩ := eventual_actual_geometry_main_tail (ι:=ι)
    N Cs b lo hi slotlo B U ξ εmass εcount saving hCs hb hlo hhi hslotlo hB hU hξ hem hec
  obtain ⟨Cz,hCz,hzero⟩ := OAI.SevenEighths.Target830.Source.Reconstruction.eventual_actual_geometry_main_zero_with_window (ι:=ι)
    N Cs b lo hi slotlo B B U ξ εzero εmass εcount hCs hb hlo hhi hslotlo hB hB hU hξ.le hez hem hec
  refine ⟨F,Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [htail,hzero] with Z ht hz
  refine ⟨ht.1,?_⟩
  intro s R seed W hn hm hs hl p hp₁ hp₂ beta M a reserve padding t hZ hbeta hM hMB ha haB
    hreserve hω hvol hamp hpadding hseed hseed0 hsource hcap hA hpool reflected key
    hK A rows C source radius Fourier weight scalar
  have hzt := hz.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ beta M a reserve padding t hZ
    hbeta hM hvol hamp (abs_le.mp hA).2 hpadding hseed hseed0 hsource hcap hpool reflected key
  have htt := ht.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ M a reserve t hZ
    hM hMB ha haB hreserve hω hseed hseed0 hsource hcap hA hpool reflected key
  have hh := actual_geometry_main_second_split reflected s R seed (Z^M) Z ξ M A
    (3*a) reserve b t N hK (zero_lt_one.trans hZ) key weight
    (fun q=> Fourier q.1)
  simp only [Fintype.sum_sigma,mul_add,Finset.sum_add_distrib] at hh
  apply hh.trans
  refine add_le_add ?_ (le_refl _)
  apply add_le_add
  · simp only [geometryHighFactor,one_div] at hzt ⊢
    apply le_trans ?_ hzt
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro alloc _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (volume_pos _).le
    exact actual_balanced_allocation_weight_le reflected s R seed (Z^M) Z ξ M A hK hZ key weight N b j.val alloc
  · apply le_trans ?_ htt
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro alloc _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (volume_pos _).le
    exact actual_balanced_allocation_weight_le reflected s R seed (Z^M) Z ξ M A hK hZ key weight N b j.val alloc

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.eventual_actual_geometry_main_remainder
end

/- Original module: Candidate.Target830.Source.Assembly.BalancedAffineRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Reconstruction
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
local notation "O" => HeckeFamily.O
variable {plane : SourcePlane}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The main source before retained contraction, with the original allocation
weights and the actual slot cardinality in its Fourier scale. -/
def balancedAffineMainSourceTotal (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ) (hZ : 1< Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let phase := fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
  ∑q : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key,
    balancedAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2 *
    actualMainSource (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t q)
      (geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key q.1.val) Z (3*amp) 1 ξ reserve

/-- The small losses in the width-one zero term leave a fixed strict saving. -/
theorem geometry_affine_zero_loss (Z μ A beta : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : widthLower≤ beta ∧ beta≤ widthUpper)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    Reconstruction.zeroPaymentExponent Z 1 A (plane.amp beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(1/20:ℝ) := by
  have hpaid := geometry_zero_exponent_saving (plane:=plane) Z 1 A (plane.amp beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/380 := by nlinarith
  simpa only [Reconstruction.zeroPaymentExponent, Cycle63InitialMass.zeroPaymentExponent, neg_div] using hpaid hbudget

/-- Genuine source and cone receipts pay the complete zero and tail terms.
Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_remainder
    (Cs μ : ℝ) (hCs : 1≤ Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,widthLower≤ beta ∧ beta≤ widthUpper →
      Real.logb Z (volume s)≤ plane.total beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      balancedAffineMainSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 (plane.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (plane:=plane) (ι:=ι)
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
  have ha := (Source.amplifier_pos plane hb).le
  have haB : plane.amp beta≤3 := (Source.source_guards plane hb).2.2.2.1.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (plane.amp beta) (μ/8) (μ/128) t hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad squarefree_one one_ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss (plane:=plane) Z μ (Real.logb Z (volume s)) beta hμ hcap
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
  have hnorm : balancedAffineMainSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(Reconstruction.zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (plane.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 (plane.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [balancedAffineMainSourceTotal,balancedMainRetainedSum,
        balancedLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,one_mul]; ring
  nlinarith

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_affine_zero_loss
#print axioms OAI.SevenEighths.Target830.Source.Assembly.eventual_actual_affine_main_remainder
end

/- Original module: Candidate.Target830.Source.Assembly.UniformRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500

namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
variable {plane : SourcePlane}
open Reconstruction
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CanonicalQuadraticSieve CenteredMomentPrimeElements RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Constants and thresholds are fixed before choosing the original live subset.
Each subset retains its actual cardinality in its source and Fourier cutoff. -/
theorem uniform_actual_affine_main_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, widthLower ≤ beta ∧ beta ≤ widthUpper →
      Real.logb Z (volume s) ≤ plane.total beta →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
      balancedAffineMainSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 (plane.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ := by
  have data (T : Finset α) := eventual_actual_affine_main_remainder (plane:=plane) (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone Ψ t reflected key
  apply (hz T hZ s p caps beta hb hcone Ψ t reflected key).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

/-- The extracted source and retained norm keep the same single prime average
while constants and thresholds are collected over original slot subsets. -/
theorem uniform_actual_affine_error_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, widthLower ≤ beta ∧ beta ≤ widthUpper →
      Real.logb Z (volume s) ≤ plane.total beta →
    ∀ P : Finset (Ideal O), P.Nonempty →
      (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^(plane.amp beta)) →
      (∀ q : elementPool P, ∀ i I, I ∈ s.slots i → IsCoprime (Ideal.span {q.val}) I) →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
    ∀ υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1 : ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)) key →
          elementPool P → Fin 3 → RayCharacter → Character,
      (56/(P.card : ℝ)) * geometryAffineErrorSourceTotal s Ψ Z (plane.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      (56/(P.card : ℝ)) * ‖geometryAffineErrorRetainedSum s Ψ Z (plane.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  have data (T : Finset α) := Reconstruction.eventual_actual_affine_error_remainder (plane:=plane) (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  apply (hz T hZ s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

end
end OAI.SevenEighths.Target830.Source.Assembly

#print axioms OAI.SevenEighths.Target830.Source.Assembly.uniform_actual_affine_main_remainder
#print axioms OAI.SevenEighths.Target830.Source.Assembly.uniform_actual_affine_error_remainder
end
