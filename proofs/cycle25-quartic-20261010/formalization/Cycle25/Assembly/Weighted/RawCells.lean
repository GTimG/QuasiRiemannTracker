import Cycle25.Assembly.Weighted.CellGeometry
import Cycle25.Assembly.Weighted.Input

/-! Instantiate a uniform arithmetic source-row estimate on the literal cells.
The general source-row estimate is an explicit input, not asserted here. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Cycle25WeightedHighFinalAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
open Cycle25
open Cycle25ProbeHighRowFamily

/-- Raw source estimate after summing all masks and amplitude classes and
applying the numerical certificate, but before absorbing the height degree. -/
def RawSourceDyadBound {Δ : ℝ} (D : Cycle25.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (Jw Cw C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),
    (1/2:ℝ) ≤ d → d ≤ Cycle25.h+3*D.t →
    (51/100:ℝ) < a → a ≤ 7/8 → (1/3:ℝ) ≤ 2*a-1 → i ≤ n →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    (∀u∈rows,(Z^d)^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
    (∀u∈rows,Z^(d-2*D.t) ≤ rowNorm u) →
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
    (∀u∈rows,a ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*i:ℕ)*Z^τ)) →
    ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows
        (Cycle25.Numerator.sourcePrimePool F Z)
        (fun j=>Cycle25.Numerator.source_prime_pool_outside F Z j)
        (fun _=>F.W) (fun j=>Z^(D.ell j)) F.W (Z^Cycle25.ly)
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
        Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          (3+((3*i+1:ℕ):ℝ)*Z^τ)^Jw*
          Z^(Cycle25.weightedTarget-weightedSourceSZExponent a D.e-D.t)

/-- All actual row geometry, height absorption, and source-profile matching
needed after the general arithmetic row estimate. -/
theorem integrated_cells_of_raw_source {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (Jw τ : ℝ) (n : ℕ) (hJw : 0 ≤ Jw) (hτ : 0 < τ)
    (hbudget : 2*τ*(1+Jw) ≤ D.t) :
    ∀ᶠZ : ℝ in atTop,∀(η : Character) (Cw C0 : ℝ),0 ≤ Cw → 0 ≤ C0 →
      RawSourceDyadBound D F η Z τ n Jw Cw C0 →
      IntegratedWeightedCellsAt D F η Z τ n Cw C0 := by
  filter_upwards [weighted_source_cell_geometry D F,
    weighted_source_height_absorption Jw D.t τ n hJw D.t_pos hτ hbudget] with Z hgeo hheight
  intro η Cw C0 hCw hC0 hraw
  unfold IntegratedWeightedCellsAt
  intro idx grid
  dsimp only
  intro hlabels hnext hcurrent k hk i hi j hj hne hd hdelta htop q hq
  have hg := hgeo.2 η τ n idx grid hlabels hnext hcurrent k i j hi hne
  have hb := hraw (weightedCellRows D F Z idx grid k i j)
    (sourceDyadConductor Z D.t k) (51/100+D.e*j) i hd.le htop hg.a_lower hg.a_upper
    hdelta.le hg.index_le hg.rows_source hg.rows_moment hg.rows_nonprincipal hg.rows_frequency
    hg.next hg.current q hq
  have hs := weighted_source_absorb_height _ Z
    (Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)) (((3*i+1:ℕ):ℝ)*Z^τ) Jw
    (Cycle25.weightedTarget-weightedSourceSZExponent (51/100+D.e*j) D.e)
    D.t (zero_lt_one.trans hgeo.1) (by positivity) (hheight i hg.index_le) hb
  rw [Cycle25.Numerator.source_real_profile_eq F]
  exact hs

/-- Quantifiers required of the general source-row theorem.  This definition
does not assert that theorem; in particular the degree precedes tau. -/
def RawFullWAnalyticInput : Prop :=
  ∀_hβ : Cycle25.theta < HeckeZeroSupremum.beta,
  ∀D : Cycle25.HighParameters.HighData (HeckeZeroSupremum.beta-Cycle25.theta),
  (∀j,D.ell j ≤ sourceMesh D.t/200) →
  ∀F : WeightedSourceData D.toMomentData,
  ∀counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t,
  ∃Jw : ℝ,0 ≤ Jw ∧
  ∀τ : ℝ,0 < τ → τ < (1/200:ℝ)/2 → 4*τ < (1/200)*D.cost →
    τ < D.t → 2*τ ≤ D.t → τ*(2+4*D.eps) < D.t → 2*τ*(1+Jw) ≤ D.t →
  ∀n : ℕ,∀η : Character,∃Cw : ℝ,0 ≤ Cw ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1 ≤ C0 →
    weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
    RawSourceDyadBound D F η Z τ n Jw Cw C0

theorem integrated_input_of_raw_source (hinput : RawFullWAnalyticInput) :
    IntegratedFullWAnalyticInput := by
  intro hβ D hfine F counts
  obtain ⟨Jw,hJw,hsource⟩ := hinput hβ D hfine F counts
  refine ⟨Jw,hJw,?_⟩
  intro τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  obtain ⟨Cw,hCw,hsource⟩ := hsource τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  refine ⟨Cw,hCw,?_⟩
  filter_upwards [hsource,integrated_cells_of_raw_source D F Jw τ n hJw hτ hτJ]
    with Z hs hfinish
  intro C0 hC0 hmom
  exact hfinish η Cw C0 hCw (zero_le_one.trans hC0) (hs C0 hC0 hmom)

/-- Complete source geometry, height absorption, remaining Mellin integration,
and actual normalization, conditional only on the displayed raw row theorem. -/
theorem fullW_input_of_raw_source (hinput : RawFullWAnalyticInput) : FullWAnalyticInput :=
  fullW_input_of_integrated_input (integrated_input_of_raw_source hinput)

end SevenEighths.Cycle25WeightedHighFinalAssembly
end
end OAI
