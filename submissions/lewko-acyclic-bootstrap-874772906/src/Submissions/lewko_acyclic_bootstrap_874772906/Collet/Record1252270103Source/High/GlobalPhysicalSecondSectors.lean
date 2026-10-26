/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual normalized corrected second energy split after the complete original
zero filter. Both complementary row sectors retain the literal coefficient. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecond
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondTail
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization
open CenteredMomentOriginalChildEnergy
open CenteredMomentSecondRetainedRows CenteredMomentSecondLiveBlock CenteredMomentSupportedTailAggregate
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance secondSectorSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def selectedSecondBlock (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : ℝ) (q : BlockIndex s modifier R seed H Tsec Z ξ)
    (keep : O→Prop) : ℂ :=
  physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools))
    (CoupledFirst.coefficient s modifier R seed) q.1.val.val.1 q.1.val.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)) _ _ q.1.val.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)) _ _ q.1.val.property).2 q.2.1
    (frequencyRadius Tsec Z ξ)
    ((liveRows q.1.val.val.1 q.1.val.val.2 q.2.1 (frequencyRadius Tsec Z ξ)
      (blockRows _ _ q.2.1 (frequencyRadius Tsec Z ξ))).filter keep)
    W H (fun i=>(q.2.2 i:ℤ))

theorem original_second_block_split (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : ℝ) (q : BlockIndex s modifier R seed H Tsec Z ξ)
    (keep : O→Prop) :
    Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q=
      selectedSecondBlock s modifier R seed W H Tsec Z ξ q keep+
      selectedSecondBlock s modifier R seed W H Tsec Z ξ q (fun z=>¬keep z) := by
  unfold Record1252270103Second.originalBlock selectedSecondBlock
  convert physical_block_keep_split s.η s.t (finiteColumns (Fintype.piFinset s.pools))
    (CoupledFirst.coefficient s modifier R seed) q.1.val.val.1 q.1.val.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)) _ _ q.1.val.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)) _ _ q.1.val.property).2 q.2.1
    (frequencyRadius Tsec Z ξ) (blockRows _ _ q.2.1 (frequencyRadius Tsec Z ξ))
    W H (fun i=>(q.2.2 i:ℤ)) keep using 1 <;> congr 1
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- This is a finite norm reduction, with no bound on any sector energy
assumed. The original complete-zero filter remains outside the split. -/
theorem actual_second_energy_sector_bound (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : ℝ) (hH : 0<H)
    (keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop) :
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=CoupledFirst.coefficient s modifier R seed
    (gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>β I*((Real.sqrt T:ℂ)⁻¹*rowWeight s.η fixedBadMask 1 1 s.t I)) W H).re≤
      (‖((H:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t‖+
        (∑q∈(Finset.univ:Finset (BlockIndex s modifier R seed H Tsec Z ξ)).filter
          (fun q=>Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0),
          ‖blockWeight s modifier R seed H Tsec Z ξ q‖*
            (‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (keep q)‖+
             ‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (fun z=>¬keep q z)‖))+
        ‖secondDiscardedEnergy s.η s.t S β W H Tsec Z ξ‖)/T := by
  intro S β
  dsimp only [S,β]
  apply (Complex.re_le_norm _).trans
  rw [actual_normalized_second_transform s modifier R seed hz₁ hz₂ T hT W H Tsec Z ξ hH,
    norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT,←div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ hT.le
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_mul,original_second_block_split s modifier R seed W H Tsec Z ξ q (keep q)]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.original_second_block_split
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_second_energy_sector_bound
