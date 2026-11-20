/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Constructs the original detector Batch on the derived measured medium cells,
so the same-zero fibers feed the actual ordinary/inverse source counts. -/
import Candidate.C092.transport.MediumWitnessSharedBatch
import Submissions.hailey_collet_1252270103.Record1252270103Return.RetainedBatches

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorBatch HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- Literal construction at a preselected cutoff. The whole source Batch uses the supplied selected indices, without selecting
a second bin budget or second row partition. Its cutoff is the original
amplitude-class cutoff function, fixed before scale and physical cells. -/
theorem original_medium_batches_of_selected (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (cutoff : ℝ → ℝ → ℝ)
    (hcutoff : ∀ δ p : ℝ, 0 ≤ δ → δ ≤ 3/4 → 0 ≤ p → p ≤ 1/2 →
      1 ≤ cutoff δ p ∧ cutoff δ p ≤ 3/2) (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ (d threshold : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ (i k : ℕ) (z : Fin D.N → ℂ),(∀ j,(z j).re=17/50) →
      (∀ j,|(z j).im| ≤ (3*i+1 : ℕ)*Z^τ) →
      let rows := mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _ => z) i k
      rows.Nonempty → CommonBand D F η (Z^(Geometry.h+padding)) Z τ d threshold n idx grid (cellHeights idx i z) i k ∧
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
      (amplitudeCell D F Z d (bandLower D k) rows z bin).Nonempty →
      ∃ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (Fin D.N) (Z^d) (bandLower D k) D.ε (cutoff (2*bandLower D k-1) ((HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*bandLower D k-1)/2) D.t (fun j => D.length j/d) bin)/(2*bandLower D k-1))) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i,
        B.rows=amplitudeCell D F Z d (bandLower D k) rows z bin ∧
        B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η ∧
        B.reverse=sourceMomentReverse F.modulus ⊤ ∧ B.slots=Finset.univ ∧
        B.widths=(fun j => D.length j/d) ∧ B.profile=(fun _ x => (F.w x : ℂ)) ∧
        B.upper=(fun _ => 2) ∧ B.external=z ∧ B.mesh=P.mesh ∧ B.binWidth=D.t ∧
        (∀ u∈B.rows,∀ j,B.family u j=originalFamily D F η u j) ∧
        (∀ u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*bandLower D k-1)/2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical F.modulus ⊤ (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external (Z^d)) u =
          HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*bandLower D k-1)/2) D.t
            (fun j => D.length j/d) bin) := by
  have hband := actual_common_band D F P τ n hτ hheight
  have hbatch := GenericCount.actual_source_amplitude_batches_at_cutoff F.modulus ⊤ le_top
    F.S F.exclusions F.maximal η (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t P.mesh D.t n
    cutoff hcutoff
    (by norm_num) (by norm_num) hτ (witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos P.mesh_pos.le D.t_pos D.detector_budget
  filter_upwards [hband,hbatch] with Z hband hbatch
  refine ⟨hband.1,?_⟩
  intro idx grid hsel
  intro d threshold hd hd' hthreshold i k z hz hzim
  dsimp only
  intro hne
  have hgateRe : ∀ u j,(cellHeights idx i z u j).re=17/50 := by
    intro u j
    by_cases h : idx u=i <;> simp [cellHeights,h,hz]
  have hgateIm : ∀ u j,|(cellHeights idx i z u j).im| ≤ (3*idx u+1 : ℕ)*Z^τ := by
    intro u j
    by_cases h : idx u=i
    · simpa [cellHeights,h] using hzim j
    · norm_num [cellHeights,h]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_lt_one.trans hband.1).le _)
  have hne' := hne
  rw [←mediumRows_cellHeights D F (Z^(Geometry.h+padding)) Z d threshold idx grid z i k] at hne'
  have hb := hband.2 d padding (Z^(Geometry.h+padding)) threshold hd hd' hthreshold
    η idx grid hsel (cellHeights idx i z) hgateRe hgateIm i k hne'
  refine ⟨hb,?_⟩
  intro bin hneBin
  have hrows := hb.rows_band
  have hcal := hb.calibration
  have hrow := hb.conductor
  have hnext := hb.next
  have hcurrent := hb.current
  rw [mediumRows_cellHeights] at hrows hcal hrow hnext hcurrent
  have hsmall (j : Fin D.N) : D.length j ≤ (1/200 : ℝ)*P.mesh := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using P.slots_mesh j
  have hsum : (7/37 : ℝ)*(7/8) ≤ ∑ j,D.length j := by
    rw [D.slots_sum]
    linarith [Geometry.sixth_lt_ell]
  obtain ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (Z^(Geometry.h+padding))
      (mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _ => z) i k)
      hne hrows hcal hrow (bandLower D k) i hb.index_bound hb.nonfloor hb.a_upper hnext hcurrent
      D.N D.length D.slots_pos hsmall hsum (fun _ x => (F.w x : ℂ)) (fun _ => 2) z bin hneBin
  exact ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,(fun u hu j => hFam u (hBr ▸ hu) j),hMean⟩

/-- Complete source Batch producer at the shared LowActual normalization.
The source constants and thresholds are uniform in the subsequently chosen
low payment, and both attaining-zero spikes remain those of the same Batch. -/
theorem original_shared_batches_of_selected (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (cutoff : ℝ → ℝ → ℝ)
    (hcutoff : ∀ δ p : ℝ, 0 ≤ δ → δ ≤ 3/4 → 0 ≤ p → p ≤ 1/2 →
      1 ≤ cutoff δ p ∧ cutoff δ p ≤ 3/2) (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ (d threshold lowPay : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ (i k : ℕ) (z : Fin D.N → ℂ),(∀ j,(z j).re=17/50) →
      (∀ j,|(z j).im| ≤ (3*i+1 : ℕ)*Z^τ) →
      let rows := sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k
      rows.Nonempty → threshold ≤ squaredBand D k ∧ squaredBand D k ≤ 3/4 ∧
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
      (amplitudeCell D F Z d (bandLower D k) rows z bin).Nonempty →
      ∃ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (Fin D.N) (Z^d) (bandLower D k) D.ε (cutoff (2*bandLower D k-1) ((HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*bandLower D k-1)/2) D.t (fun j => D.length j/d) bin)/(2*bandLower D k-1))) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i,
        B.rows=amplitudeCell D F Z d (bandLower D k) rows z bin ∧
        B.rows ⊆ rows ∧
        B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η ∧
        B.reverse=sourceMomentReverse F.modulus ⊤ ∧ B.slots=Finset.univ ∧
        B.widths=(fun j => D.length j/d) ∧ B.profile=(fun _ x => (F.w x : ℂ)) ∧
        B.upper=(fun _ => 2) ∧ B.external=z ∧ B.mesh=P.mesh ∧ B.binWidth=D.t ∧
        (∀ u∈B.rows,∀ j,B.family u j=originalFamily D F η u j) ∧
        (∀ u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*bandLower D k-1)/2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical F.modulus ⊤ (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external (Z^d)) u =
          HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*bandLower D k-1)/2) D.t
            (fun j => D.length j/d) bin) := by
  have hsupplier := original_medium_batches_of_selected D F P padding τ hτ hheight cutoff hcutoff n η
  filter_upwards [hsupplier] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro idx grid hsel
  have hrest := hZ.2 idx grid hsel
  intro d threshold lowPay hd hd' hthreshold i k z hz hzim
  dsimp only
  intro hne
  have hsub := sharedRows_subset_mediumRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k hZ.1
  obtain ⟨hband,hbatch⟩ := hrest d threshold hd hd' hthreshold i k z hz hzim (hne.mono hsub)
  refine ⟨hband.response_lower,hband.band_upper,?_⟩
  intro bin hneBin
  have hsubAmp := amplitudeCell_mono D F Z d (bandLower D k) _ _ z bin hsub
  obtain ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFamily,hMean⟩ :=
    hbatch bin (hneBin.mono hsubAmp)
  have hrestrict : amplitudeCell D F Z d (bandLower D k)
      (sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k) z bin ⊆ B.rows := by
    rw [hBr]
    exact hsubAmp
  let B' := restrictBatch B _ hrestrict
  refine ⟨B',rfl,?_,hData,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,?_,?_⟩
  · exact Finset.filter_subset _ _
  · intro u hu j
    exact hFamily u (hrestrict hu) j
  · intro u hu
    exact hMean u (hrestrict hu)

end QRH.Cycle092.MediumWitness
#print axioms QRH.Cycle092.MediumWitness.original_medium_batches_of_selected
#print axioms QRH.Cycle092.MediumWitness.original_shared_batches_of_selected
