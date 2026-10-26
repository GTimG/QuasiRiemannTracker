/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual coupled first-block data and exact joint Fourier expression. Original
finite source columns are retained inside the physical FirstBlockSource. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstRemainder
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.JointBlock
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open CenteredMomentCanonicalFirst ConcretePrimeRowBridge CenteredMomentSmooth
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentFirstSectors CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedRows CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondRetainedAggregate Cycle61InitialMass CenteredMomentFirstWholeKernel
open CenteredMomentFirstPhysicalActiveDictionary
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledFirstLabelsDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O) :=
  CenteredMomentSecondBlockAggregate.ActiveLabel
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)

def localRadius (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s modifier R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ :=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

abbrev SourceBlocks (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s modifier R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s modifier R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s modifier R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s modifier R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s modifier R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

lemma physicalMass_eq_sum (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ=
      ∑p:Labels s modifier R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s modifier R seed K Z ξ p E,‖originalBlock s modifier R seed W K Z ξ p E n‖:=by
  unfold physicalMass
  apply Finset.sum_congr rfl
  intro p hp
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  rfl

abbrev SourceCoordinate (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) :=
  (p : Labels s modifier R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) ×
      SourceBlocks s modifier R seed K Z ξ p E.val

def coordinateBlock (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) : ℂ :=
  originalBlock s modifier R seed W K Z ξ q.1 q.2.1.val q.2.2

theorem physicalMass_eq_coordinate_sum (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask *
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ =
      ∑ q : SourceCoordinate s modifier R seed K Z ξ, ‖coordinateBlock s modifier R seed W K Z ξ q‖ := by
  rw [physicalMass_eq_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Fintype.sum_sigma]
  simpa only [coordinateBlock] using
    (Finset.sum_coe_sort (inactiveSubsets p.val.1 p.val.2)
      (fun E => ∑ n : SourceBlocks s modifier R seed K Z ξ p E,
        ‖originalBlock s modifier R seed W K Z ξ p E n‖)).symm

theorem actual_physical_mass_joint_sum (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(K Z ξ:ℝ) :
    physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ=
      ‖∑q:SourceCoordinate s modifier R seed K Z ξ,
        normPhase (coordinateBlock s modifier R seed W K Z ξ q)*
          coordinateBlock s modifier R seed W K Z ξ q‖ := by
  simp_rw [normPhase_mul]
  rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  exact physicalMass_eq_coordinate_sum s modifier R seed W K Z ξ

def originalFirstBlock (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (q : SourceCoordinate s modifier R seed K Z ξ) : FirstBlockSource where
  character := s.η
  mask := CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R
  height := s.t
  pool := finiteColumns (Fintype.piFinset s.pools)
  beta := coefficient s modifier R seed
  C := q.1.val.1
  D := q.1.val.2
  hC := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ q.1.property).1
  hD := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ q.1.property).2
  sameSupport := (CenteredMomentFirstSectors.commonLabels_data _ _ _ _ q.1.property).2.2
  inactive := q.2.1.val
  rows := retainedRows (localRadius s modifier R seed K Z ξ q.1 q.2.1.val) 1
  rows_ne := CenteredMomentFirstPhysicalDyadicAssembly.retained_rows_nonzero _
  K := K
  K0 := dyadicScale (q.2.2 0)
  H0 := dyadicScale (q.2.2 1)
  A0 := dyadicScale (q.2.2 2)
  B0 := dyadicScale (q.2.2 3)
  K_pos := hK
  K0_pos := dyadicScale_pos _
  H0_pos := dyadicScale_pos _
  A0_pos := dyadicScale_pos _
  B0_pos := dyadicScale_pos _

lemma originalFirstBlock_value (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (K Z ξ : ℝ) (hK : 0<K) (q : SourceCoordinate s modifier R seed K Z ξ) :
    (originalFirstBlock s modifier R seed K Z ξ hK q).value W (fun _ => logAnnulus) =
      coordinateBlock s modifier R seed W K Z ξ q := rfl

/-- The complete original physical mass is this joint first-sector expression.
The phase aligns the actual blocks and costs at most one. -/
theorem actual_physical_mass_first_sector_expression (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    let phase := fun q => normPhase (coordinateBlock s modifier R seed W K Z ξ q)
    physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ =
      ‖∑ q : FirstSector source, firstJointWeight source q*
        (∑ i : (source q.1).LeftIndex, ∑ j : (source q.1).RightIndex,
          (firstJointLeft source phase q i*star (firstJointRight source q j))*
          wholeKernel W (fun _ => logAnnulus) (source q.1).ratio
            (firstRho source q) (firstX source q)
            (firstLeftLog (source q.1) i) (firstRightLog (source q.1) j))‖ := by
  dsimp only
  rw [← actual_first_block_joint_expression]
  simp_rw [originalFirstBlock_value]
  exact actual_physical_mass_joint_sum s modifier R seed W K Z ξ

/-- The coefficient may change cancellation, but never the original finite pool. -/
theorem active_columns_card_le (s:Input ι)(modifier:Tuple ι→ℂ)(R seed C D:Ideal O)(hD:D≠0) :
    (columns C D hD (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed))).card≤
    (columns C D hD (finiteColumns (Fintype.piFinset s.pools))).card := by
  rw [columns_active]
  exact Finset.card_filter_le _ _

theorem labels_card_le (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O) :
    Fintype.card (Labels s modifier R seed)≤
      (finiteColumns (Fintype.piFinset s.pools)).card^2 := by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let T:=supportedColumns (activeSource S (coefficient s modifier R seed))
  have hT : T⊆S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hT
  change Fintype.card ↥(commonLabels T T)≤S.card^2
  rw [Fintype.card_coe]
  calc
    _≤(T.product T).card := Finset.card_image_le
    _=T.card^2 := by simp only [Finset.product,Finset.card,pow_two]; exact Multiset.card_product T.val T.val
    _≤S.card^2 := Nat.pow_le_pow_left hc 2

theorem firstBlock_left_card (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (K Z ξ:ℝ)(hK:0<K)(q:SourceCoordinate s modifier R seed K Z ξ) :
    Fintype.card (originalFirstBlock s modifier R seed K Z ξ hK q).LeftIndex=
      (columns q.1.val.1 q.1.val.1
        (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s modifier R seed)) _ _ q.1.property).1.1
        (finiteColumns (Fintype.piFinset s.pools))).card := by
  exact Fintype.card_coe _

theorem firstBlock_right_card (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (K Z ξ:ℝ)(hK:0<K)(q:SourceCoordinate s modifier R seed K Z ξ) :
    Fintype.card (originalFirstBlock s modifier R seed K Z ξ hK q).RightIndex=
      (columns q.1.val.1 q.1.val.2
        (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s modifier R seed)) _ _ q.1.property).2.1
        (finiteColumns (Fintype.piFinset s.pools))).card := by
  exact Fintype.card_coe _

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_first_sector_expression
#print axioms QRH.Record1252270103Source.High.CoupledFirst.firstBlock_left_card
#print axioms QRH.Record1252270103Source.High.CoupledFirst.firstBlock_right_card
