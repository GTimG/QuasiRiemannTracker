/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Physical class counts from the actual count parameters, without a fixed-fee
schedule premise. Adapted from PR137 SourceCountInitial and PhysicalSourceCount
(Sil, Hailey Collet and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveMaskedCount
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.PhysicalSourceCount

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record12518109Count QRH.Record1252270103Return.GenericCount
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition Cycle25DetectorRowCount HeckeDetectorFixedAmplitudeCount
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily Cycle25WeightedHighRowFamily
open ProbeFinalAssembly ProbeHighRowFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots
local notation "O" => HeckeFamily.O
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem selected_source_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ)
    (counts : Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.CountParameters M H εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (κplain a ε ν C q : ℝ) (i : ℕ), i ≤ n →
      51/100 < a → 2*a-1 ≤ 3/4 → a ≤ 1 → 0 ≤ ε → ε ≤ 1/10000000 →
      7/10 ≤ κplain → κplain ≤ 3/4 → 0 < ν → ν ≤ 1/10000000 → 0 ≤ C →
      ∀ {Slot : Type}
        (B : Batch M H Label Slot (Z^d) a ε
          (Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.selectedCutoff κplain (2*a-1) (q/(2*a-1)))
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z^d)) u = q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain
          counts.co counts.κo (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ
          counts.ca counts.κa (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ w ∈ scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedMoments line (B.fiber bin label left right hne)
          ν (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card : ℝ) ≤ K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope κplain
          (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  let Ko := counts.Ko
  let Ka := counts.Ka
  have hcount := counts.counted
  obtain ⟨Ko',hKo',ho⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth Ko hdmin hdmax hl (by linarith) hb
  obtain ⟨Ka',hKa',haff⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth Ka hdmin hdmax hl (by linarith) hb
  refine ⟨Ko'+Ka',by positivity,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,ho,haff,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,eventually_ge_atTop (1:ℝ)]
    with Z hcount ho haff hfreq hU hZ
  intro d hd hd' κplain a ε ν C q i hi ha haδ ha' hε hεsmall hk hkhi hν hνhi hC
    Slot B hslots hbin hne hq oldmom newmom rawmom impmom
  have hc := hcount d hd κplain a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hεsmall hk hkhi hν hνhi
    (by positivity) (by positivity) (hfreq d hd' i hi) B hne hq oldmom newmom rawmom impmom
  have hpref : (Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2*
      max (fiberConstant (C*Z^momentCost) (Z^heightCost) Ko)
        (fiberConstant (C*Z^momentCost) (Z^heightCost) Ka)*(Fintype.card B.Bin:ℝ) ≤
      (Ko'+Ka')*C*Z^(logCost+heightCost+momentCost) := by
    have ho' := ho d hd hd' C a ε _ _ _ i hC ha' B hslots hbin
    have haff' := haff d hd hd' C a ε _ _ _ i hC ha' B hslots hbin
    rcases le_total (fiberConstant (C*Z^momentCost) (Z^heightCost) Ko)
      (fiberConstant (C*Z^momentCost) (Z^heightCost) Ka) with hx | hx
    · rw [max_eq_right hx]
      apply haff'.trans
      gcongr
      linarith
    · rw [max_eq_left hx]
      apply ho'.trans
      gcongr
      linarith
  exact hc.trans (mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg (by positivity) _))

theorem physical_source_amplitude_count (D : QRH.Record1252270103Return.GenericPhysical.BaselineData)
    (F : SourceData)
    (counts : Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.CountParameters
      F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d a C0 : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀ z : ℂ, z.re = 17/50 → |z.im| ≤ Z^(2*τ) →
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow => u.val) (fun _ y => (F.w y:ℂ))
        (fun _ => 2) (fun j => D.length j/d) (fun _ => z) (Z^d)
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
        (fun j => D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j => D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧ (rows'.card : ℝ) ≤ C*C0*Z^(3*D.t)*
        (Z^d)^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope D.momentKappa
          (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := selected_source_count F.modulus ⊤ D.t counts
    (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := GenericCount.actual_source_amplitude_batches_at_cutoff F.modulus ⊤ le_top
    F.S F.exclusions F.maximal η (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t D.t D.t n
    (Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.selectedCutoff D.momentKappa)
    (fun delta p hd hdhi hp hphi => Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.selectedCutoff_bounds
      D.momentKappa_lo D.momentKappa_hi ⟨hd,hdhi⟩ ⟨hp,hphi⟩)
    (by norm_num) (by norm_num) hτ hτzero hτheight D.epsilon_pos D.e_pos D.e_small
    D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le D.t_pos D.t_pos.le D.t_pos
    (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow => u.val) (fun _ y => (F.w y:ℂ))
    (fun _ => 2) (fun j => D.length j/d) (fun _ => z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j => D.length j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j => D.length j/d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hband : rows ⊆ rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu => (hrows u hu).2.2.1) (fun u hu => (hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.length D.slots_pos D.slots_small
      (by rw [D.slots_sum]; linarith [Geometry.sixth_lt_ell,Geometry.ell_lt_fifth])
      (fun _ y => (F.w y:ℂ)) (fun _ => 2) (fun _ => z) bin hne
  have hBsub : B.rows ⊆ rows := hBr ▸ hsub
  have hBfam : ∀ u ∈ B.rows, ∀ j, B.family u j =
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hν1 : D.t ≤ 1/10000000 := by linarith [D.t_small]
  have hcard := hc d hd hd' D.momentKappa a D.ε D.t C0 q i hi ha (by linarith) (by linarith)
    D.epsilon_pos.le D.epsilon_count_small D.momentKappa_lo D.momentKappa_hi D.t_pos hν1
    (by linarith) B (by rw [hSlots]; simp) hBin (hBr.symm ▸ hne) hMean
    (fun bin j J K hne => (hraw bin j J K hne).1)
    (fun bin j J K hne => (hraw bin j J K hne).2.1)
    (fun w hw bin j J K hne => (hraw bin j J K hne).2.2.1 w hw)
    (fun bin j J K hne => (hraw bin j J K hne).2.2.2)
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j => D.length j/d) Q bin (by linarith)
    (fun j _ => (div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos Geometry.ell_pos hdpos) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have he : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope D.momentKappa
      (2*a-1) (q/(2*a-1))+159*D.ε+D.t+D.t+7*D.t =
      Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope D.momentKappa
      (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t) := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope
      D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.physical_source_amplitude_count
