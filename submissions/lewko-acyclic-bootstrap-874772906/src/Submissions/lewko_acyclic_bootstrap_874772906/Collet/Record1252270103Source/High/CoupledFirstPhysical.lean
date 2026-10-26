/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual first Poisson/retained physical reduction for the literal coupled source.
The generic OpenAI/Hailey Collet finite kernels accept this coefficient directly. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstRetainedNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentCommonRadialData
open CenteredMomentActiveSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
theorem coupled_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0<K):
    retainedInfiniteBlock s.η m A t S
      (coefficient s modifier Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (coefficient s modifier Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(original_column_norm s modifier Rbad seed I hz₁ hz₂ hI).2)

def sector (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (coefficient s modifier Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (coefficient s modifier Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

omit [DecidableEq ι] in
theorem sector_norm (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    ‖sector s modifier Rbad seed m A t S C D hC hD W K X Z ξ‖≤
      sectorMass s modifier Rbad seed m A t S C D hC hD W K X Z ξ:=by
  unfold sector sectorMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro E hE
  exact norm_sum_le _ _

theorem original_retained_physical
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S
      (coefficient s modifier Rbad seed) W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
          sector s modifier Rbad seed m A t S p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg
  unfold infiniteSector sector
  apply Finset.sum_congr rfl
  intro E hE
  exact coupled_retained_dyadic s modifier Rbad seed hz₁ hz₂ m A t S p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2 E W K _ hK

theorem original_active_sectors (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=coefficient s modifier Rbad seed
    let T:=activeSource S β
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ=
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
        sector s modifier Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [←retained_energy_active s.η m A t S _ W K X Z ξ]
  exact original_retained_physical s modifier Rbad seed hz₁ hz₂ m A t _ W K X Z ξ hK

theorem original_retained_norm (s:CenteredMomentCommonRadialData.Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=coefficient s modifier Rbad seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s modifier Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [original_active_sectors s modifier Rbad seed hz₁ hz₂ m A t S W K X Z ξ hK]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  have hw:‖rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)‖≤1:=by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).1.1)).trans
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).2.1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (sector_norm s modifier Rbad seed m A t _ _ _ _ _ W K X Z ξ)

theorem original_sectorMass_active (s : Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s modifier R seed m A t
        (activeSource S (coefficient s modifier R seed))
        C D hC hD W K X Z ξ=
      sectorMass s modifier R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem original_retained_full_sectorMass (s : Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    let β:=coefficient s modifier R seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s modifier R seed m A t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ := by
  dsimp only
  apply (original_retained_norm s modifier R seed hz₁ hz₂ m A t S W K X Z ξ hK).trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s modifier R seed m A t S _ _ _ _ W K X Z ξ


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_retained_full_sectorMass
