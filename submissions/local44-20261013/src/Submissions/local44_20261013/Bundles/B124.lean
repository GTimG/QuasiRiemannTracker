/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B036
import Submissions.local44_20261013.Bundles.B040
import Submissions.local44_20261013.Bundles.B041
import Submissions.local44_20261013.Bundles.B050
import Submissions.local44_20261013.Bundles.B072
import Submissions.local44_20261013.Bundles.B081
import Submissions.local44_20261013.Bundles.B088
import Submissions.local44_20261013.Bundles.B107
import Submissions.local44_20261013.Bundles.B123

/- BEGIN ORIGINAL MODULE Global.Numerator.LocalSourceSelection ; sha256 70c71163008e68514a6538937c430ccf0c7523a875735b7fca7b6d67f39c6ef3 -/
section

noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator OAI OAI.SevenEighths HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification
open _root_.Local44.Physical OAI.SevenEighths.Local44.Physical
theorem source_class_main_transport_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (hfine : ∀j,D.ell j ≤ transportMomentMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (hbare : BareWindow (1-ly/d))
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d)
      (fun u j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=> D.ell j/d) (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧ ∃selected : Finset (Fin D.N),selected⊆main ∧
      (∑j∈selected,D.ell j/d) ≤ transportCapacity (1-ly/d) v ∧
      ∀u∈rows',
        (Z^d)^(2*q*transportCapacity (1-ly/d) v-
          δ*transportMomentMesh D.t) ≤ ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t)) →
          ‖∏j∈main,Q u j‖ ≤ (Z^d)^(q*(ell/d)+D.t*(ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0 ≤ g j ∧ g j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hspike⟩ :=
    highData_transport_selection D hfine d v δ hd hv hδ hbare main
      (maskedGain main g) hg (fun j hj=> by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.ell j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.ell j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_bounds j).1 hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=> D.ell j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_bounds j).1 hdpos).le)
      (by rw [hL];exact div_pos ell_pos hdpos) (by
        intro j hj
        calc
          _ ≤ (Z^(D.ell j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh



end Submission20261012.Global.Numerator
end
/- END ORIGINAL MODULE Global.Numerator.LocalSourceSelection -/

/- BEGIN ORIGINAL MODULE Global.Numerator.Scalar.SourcePacket ; sha256 676af252e54c8906504186c23f97d08797b244d109e47429a6bfed827b6ef32a -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/



noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator.Scalar

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) =
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ))) =
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=> mul_comm _ _)
  simpa only [hm] using Cycle25.Numerator.error_main_source_scale J Z hZ lengths

/-- Collapse the physical front, frequency, count and packet powers using
the same moment parameter as the detector count. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d delta q epsilon eps t mesh C Ccount C0 B : ℝ)
    (hZ : 0 < Z) (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (C*(Ccount*C0*Z^(3*t))*B*((Z^d)^(ly/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(t+q*(ell/d)-q*((2*(ly/d)-1)/(6*kap)-t/(3*kap))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+2*t)/4+
        delta*mesh/4+delta*t/4+t*(ell/d))) =
    (C*Ccount*C0*B)*Z^(numeratorExponent kap d delta (q/delta)+
      weightedSourceLoss kap d delta q epsilon eps t mesh t (2*t) t t) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E : ℝ := t+q*(ell/d)-q*((2*(ly/d)-1)/(6*kap)-t/(3*kap))/2+
    (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
      159*epsilon+9*t)+1+2*t)/4+delta*mesh/4+delta*t/4+t*(ell/d)
  calc
    _ = (C*Ccount*C0*B)*
        ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
          Z^(-(4/25:ℝ)*ell)*Z^(3*t)*((Z^d)^(ly/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = (C*Ccount*C0*B)*Z^(d*(2*eps)+d*(-(17/50:ℝ))+(17/25)*t+
        -(4/25:ℝ)*ell+3*t+(d*(ly/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←weighted_source_packet_exponent kap d delta q epsilon eps t mesh t (2*t) t t hk hd hdelta]
      dsimp only [E]
      field_simp
      ring

end Submission20261012.Global.Numerator.Scalar
end
/- END ORIGINAL MODULE Global.Numerator.Scalar.SourcePacket -/

/- BEGIN ORIGINAL MODULE Global.Weighted.RawCells ; sha256 f209d7088e9646b0b7d211f493c4051233f33ddfd3ddacac728384ade6906ad6 -/
section



/-! Instantiate a uniform arithmetic source-row estimate on the literal cells.
The general source-row estimate is an explicit input, not asserted here. -/
namespace Submission20261012.Global
open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators
open Filter
namespace ProbeAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
open Submission20261012.Global
open Cycle25ProbeHighRowFamily

/-- Raw source estimate after summing all masks and amplitude classes and
applying the numerical certificate, but before absorbing the height degree. -/
def RawSourceDyadBound {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (Jw Cw C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),
    (1/2:ℝ) ≤ d → d ≤ Submission20261012.Global.h+3*D.t →
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
        (fun j=> Cycle25.Numerator.source_prime_pool_outside F Z j)
        (fun _=> F.W) (fun j=> Z^(D.ell j)) F.W (Z^Submission20261012.Global.ly)
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
        Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          (3+((3*i+1:ℕ):ℝ)*Z^τ)^Jw*
          Z^(Submission20261012.Global.weightedTarget-weightedSourceSZExponent a D.e-D.t)

/-- All actual row geometry, height absorption, and source-profile matching
needed after the general arithmetic row estimate. -/
theorem integrated_cells_of_raw_source {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
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
    (Submission20261012.Global.weightedTarget-weightedSourceSZExponent (51/100+D.e*j) D.e)
    D.t (zero_lt_one.trans hgeo.1) (by positivity) (hheight i hg.index_le) hb
  rw [Cycle25.Numerator.source_real_profile_eq F]
  exact hs

/-- Quantifiers required of the general source-row theorem.  This definition
does not assert that theorem; in particular the degree precedes tau. -/
def RawFullWAnalyticInput : Prop :=
  ∀_hβ : Submission20261012.Global.theta < HeckeZeroSupremum.beta,
  ∀D : Submission20261012.Global.HighParameters.HighData (HeckeZeroSupremum.beta-Submission20261012.Global.theta),
  (∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200) →
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

end ProbeAssembly
end
end Submission20261012.Global

#print axioms Submission20261012.Global.ProbeAssembly.fullW_input_of_raw_source
end
/- END ORIGINAL MODULE Global.Weighted.RawCells -/

/- BEGIN ORIGINAL MODULE Physical.LocalRetainedFixed ; sha256 fefac189e19275cdaea74240cf4ec8780b4bda779cf4d0428af3326c36667402 -/
section



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Physical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open Cycle25WeightedNumeratorPhysical
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 800000

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem certified_transport_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (G:𝓢(ℝ,ℂ)) (loss Cscale Ccond xi:ℝ)
    (hloss:0 < loss) (hCscale:0 < Cscale) (hCcond:0 < Ccond) (hxi:0 < xi) :
    ∃degree:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (X:rows→ℝ) (m n:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      _root_.Local44.Physical.BareWindow n → n ≤ m+xi →
      (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 < width i) →
      (∀i, width i ≤ transportMomentMesh D.t) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (∑i,width i) ≤ _root_.Local44.Physical.transportCapacity n (m+xi-n) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := certified_transport_actual_retained_fourth F hbeta hbetaTop (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by have := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G; dsimp [B]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m n he hX hm hmmax hn hnm hred hcombined T width z height
    hw hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=> G) X m n B (K*U) he hX hm hmmax hn hnm hB hGB
    hRcap hred' hcombined T width z height hw hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end SevenEighths.Local44.Physical
end
end OAI


/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The original restoration and tail proofs are retained; the certified physical
moment now uses the local/old/empty transport capacity. -/

#print axioms OAI.SevenEighths.Local44.Physical.certified_transport_retained_fixed_profile
end
/- END ORIGINAL MODULE Physical.LocalRetainedFixed -/

/- BEGIN ORIGINAL MODULE Global.Final.CommonProbe ; sha256 83ade38917e3ac2c10eab44cebfa83ed14bf0f617b909974715cfddf38e8c7b4 -/
section




/-! Actual common-probe assembly with both source moment families. Adapted
from weighted upstream HighRows/ConditionalFinal, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace Submission20261012.Global.ProbeAssembly
open OAI OAI.SevenEighths
noncomputable section
open scoped Classical
open Filter Asymptotics HeckeFamily ProbePhysical PrincipalSignalComparison
open Cycle25ProbeFinalAssembly Submission20261012.Global.FinalAssembly

theorem common_probe_of_fullW_input (hinput : FullWAnalyticInput) :
    Cycle25.UniformCommonProbe Submission20261012.Global.theta signalShift := by
  intro hβ
  obtain ⟨P⟩ := exists_chosen_data hβ
  obtain ⟨Jw,hJw,hinput⟩ := hinput hβ P.D P.fine_transport P.F P.counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hτJw,hsource⟩ :=
    chosen_data_height P.D P.F P.counts P.oldcounts P.J P.Jo Jw
      P.J_nonneg P.Jo_nonneg hJw P.moments P.old_moments
  obtain ⟨n,hn,C,hC,hhigh⟩ := fixed_high_bound_of_fullW hβ baseline_beta
    P.D P.F P.oldcounts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-Submission20261012.Global.theta)/2
  have hloss : 0 < loss := by dsimp [loss];linarith only [hβ]
  have hlossgap : loss < HeckeZeroSupremum.beta-Submission20261012.Global.theta := by
    dsimp [loss];linarith only [hβ]
  refine ⟨loss,P.D.sigma,hloss,hlossgap,P.D.sigma_pos,?_⟩
  apply source_contract P.D P.F loss hloss
  intro η
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  obtain ⟨Cw,hCw,hcells⟩ := hinput τ hτ hτd hτcost hτt hτ2 hτeps hτJw n η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*(2+Cw)*Cm*(η.modulus.absNorm:ℝ)^(2*P.D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource,hcells] with Z hh hs hc
  simpa only [signalShift,sub_eq_add_neg,neg_div] using
    hh Cm hCm Cw hCw hs.2 (hc Cm hCm hs.1)

/-- The analytic raw source contract suffices for the same actual common probe. -/
theorem common_probe_of_raw_fullW_input (hinput : RawFullWAnalyticInput) :
    Cycle25.UniformCommonProbe Submission20261012.Global.theta signalShift :=
  common_probe_of_fullW_input (fullW_input_of_raw_source hinput)
end
end Submission20261012.Global.ProbeAssembly

#print axioms Submission20261012.Global.ProbeAssembly.common_probe_of_raw_fullW_input
end
/- END ORIGINAL MODULE Global.Final.CommonProbe -/

/- BEGIN ORIGINAL MODULE Global.Numerator.OldSourceMask ; sha256 fb6e27522bcdd8456548a679a40f6f9acd8c0e4691481d038690042e07795382 -/
section






/-! Actual physical mask contributions on the original full amplitude classes.
The certified moment is already discharged by SourceClass. Count and calibrated
scalar bounds are kept explicit so the same source constants apply to every mask. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator Scalar
open Cycle25.Numerator
open Cycle25 (sourceMesh)
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class_old (D:HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hgap:theta < HeckeZeroSupremum.beta)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hfine:∀j,D.ell j≤ _root_.Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z → (1/2:ℝ)≤ d → d< Endpoint.junction → d≤ h+3*D.t → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤ a → a≤7/8 → 1/3≤2*a-1 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i P,P∈sourcePrimePool F Z i→(4:ℝ)≤ P.val.absNorm) →
      (∀i,∀P∈F.S,(P.absNorm:ℝ)≤ Z^(D.ell i)) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=> D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀Cs K C0:ℝ,0≤ Cs → 1≤ K → 1≤ C0 →
      (rows'.card:ℝ)≤ K*C0*Z^(3*D.t)*U^(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t) →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖sourceMaskContribution F η rows' J Z x z (Z^ly)‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((degree:ℝ)+2*D.eps)*
          Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
  obtain ⟨degree,C,hC,hclass⟩ := source_packet_amplitude_class D F hbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdold hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=> D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := by linarith
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hY : U^(ly/d)=Z^ly := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hdwide : d ≤ h+rowExtension := hdmax.trans (by linarith [D.weighted_top])
  have hb := hclass.2 Z d hZ hd hdwide hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=> source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=> F.W) (fun s=> Z^(D.ell s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^ly) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) x z F.W (Z^ly)*
      (∏s∈main,Q u s)‖) ≤
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
        (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*_root_.Cycle25.sourceMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) x z F.W (Z^ly)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^ly) hS A _ hA hscalar hlabel
  have hselection := source_class_main_selection D F hfine Z d 0 (2*a-1) hZ hd (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0≤ q := hselection.1
  have hqmax : q≤(2*a-1)/2 := hselection.2.1
  have he := source_packet_multiplicative_identity J D.ell D.slots_sum Z D.momentKappa d (2*a-1) q D.ε D.eps D.t
    (_root_.Cycle25.sourceMesh D.t) C K C0 ((1+height)^degree) hZ0 (by linarith [D.momentKappa_lo]) hd0.ne' hδ.ne'
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
        (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*_root_.Cycle25.sourceMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(1+height)^degree*
        Z^(numeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
          weightedSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t (_root_.Cycle25.sourceMesh D.t) D.t (2*D.t) D.t D.t) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps))*
          (((Z^d)^(2*D.eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(ly/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
              (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
              (2*a-1)*_root_.Cycle25.sourceMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)))) := by ring
      _ = _ := by rw [he];ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree ≤ (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := source_packet_certificate D hgap d a q hd hdmax hδlow hatop hq0 hqmax
  simp only [piecewiseNumeratorExponent,piecewiseSourceLoss,if_neg (not_le_of_gt hdold)] at hcert
  apply hphysical'.trans
  calc
    _ ≤ (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(3+height)^(degree:ℝ)*
        Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*D.eps)];ring

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Uses the Cycle25 gap-dependent certificate. -/
end
/- END ORIGINAL MODULE Global.Numerator.OldSourceMask -/
