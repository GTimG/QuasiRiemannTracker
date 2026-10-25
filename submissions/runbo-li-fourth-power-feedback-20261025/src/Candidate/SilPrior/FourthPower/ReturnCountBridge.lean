/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Actual pinned proof bodies with their unnecessary old Bounds/PhysicalSchedule
section parameters removed. Original definitions/data and explicit analytical
inputs are retained. No old Bounds instance, new axiom or replacement estimate.

-/
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceCountInitial
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.CanonicalCount
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.PhysicalSourceCount
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.PublicCount
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MaskedCount
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MaskedSourceCount
import Candidate.SilPrior.FourthPower.ReturnMomentBridge

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Candidate.SilPrior.FourthPower.ReturnCountBridge
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
variable [scheme : QRH.Record1252270103Return.CountScheme]
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return.GenericArithmetic
open QRH.Record12518109Count
open QRH.Record1252270103Return
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount
open OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count OAI OAI.SevenEighths
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily Cycle25WeightedHighRowFamily
open ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open OAI.SevenEighths.Cycle25DetectorRowCount
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open Cycle25DetectorRowCount HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceCountInitial; original data types unchanged. -/
theorem selected_source_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ)
    (counts : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.CountParameters M H εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃ K : ℝ, 0<K ∧
      ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ (κplain a ε ν C q : ℝ) (i : ℕ), i≤n →
      51/100<a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C →
      ∀ {Slot : Type}
        (B : Batch M H Label Slot (Z^d) a ε (GenericCount.selectedCutoff κplain (2*a-1) (q/(2*a-1))) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀ u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain counts.co counts.κo (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ counts.ca counts.κa (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ w∈scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ) ≤ K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(GenericCount.envelope κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  let Ko := counts.Ko
  let Ka := counts.Ka
  have hcount := counts.counted
  obtain ⟨Ko',hKo',ho⟩ := ProbeHighRowFamily.source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth Ko hdmin hdmax hl (by linarith) hb
  obtain ⟨Ka',hKa',haff⟩ := ProbeHighRowFamily.source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth Ka hdmin hdmax hl (by linarith) hb
  refine ⟨Ko'+Ka',by positivity,?_⟩
  filter_upwards [ProbeHighRowFamily.eventually_all_rpow_ge hcount dmin hdmin,ho,haff,
    ProbeHighRowFamily.source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    ProbeHighRowFamily.eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount ho haff hfreq hU hZ
  intro d hd hd' κplain a ε ν C q i hi ha haδ ha' hε hεsmall hk hkhi hν hνhi hC
    Slot B hslots hbin hne hq oldmom newmom rawmom
  have hc := hcount d hd κplain a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hεsmall hk hkhi
    hν hνhi (by positivity) (by positivity) (hfreq d hd' i hi) B hne hq oldmom newmom rawmom
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

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.CanonicalCount; original data types unchanged. -/
theorem physical_eq_canonical (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.SourceData) (Z d : ℝ)
    (hZ : 0<Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.PhysicalSourceCount; original data types unchanged. -/
theorem physical_source_amplitude_count (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.SourceData)
    (counts : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := selected_source_count F.modulus ⊤ D.t counts
    (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n
    (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := GenericCount.actual_source_amplitude_batches_at_cutoff F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t D.t D.t n (GenericCount.selectedCutoff D.momentKappa)
    (fun δ p hδ hδhi hp hphi=>GenericCount.selectedCutoff_bounds D.momentKappa_lo D.momentKappa_hi ⟨hδ,hδhi⟩ ⟨hp,hphi⟩)
    (by norm_num) (by norm_num) hτ hτzero hτheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=>D.length j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.length D.slots_pos
      D.slots_small (by rw [D.slots_sum]; linarith [Geometry.sixth_lt_ell,Geometry.ell_lt_fifth]) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hν1 : D.t ≤ 1/10000000 := by linarith [D.t_small]
  have hcard := hc d hd hd' D.momentKappa a D.ε D.t C0 q i hi ha (by linarith)
    (by linarith) D.epsilon_pos.le D.epsilon_count_small D.momentKappa_lo D.momentKappa_hi
    D.t_pos hν1 (by linarith) B (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean
    (fun bin j J K hne=>(hraw bin j J K hne).1)
    (fun bin j J K hne=>(hraw bin j J K hne).2.1)
    (fun w hw bin j J K hne=>(hraw bin j J K hne).2.2 w hw)
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j=>D.length j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos (show (0:ℝ)<ell by linarith [Geometry.ell_pos,Geometry.ell_lt_fifth]) hdpos) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have he : GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+159*D.ε+D.t+D.t+7*D.t=GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t) := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.PublicCount; original data types unchanged. -/
theorem canonical_source_count_with_error (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.SourceData)
    (counts : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤σ) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨C,hC,hcount⟩ := physical_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hdp : 0<d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [physical_eq_canonical D F Z d hZp hdp.ne'] at hb
  have hbound := hb bin hne
  refine ⟨hbound.1,hbound.2.1,?_⟩
  apply hbound.2.2.trans
  apply Cycle61DetectorCount.source_error_absorption Z d D.t D.ε _ σ (C*C0) hZ.le hd D.t_pos.le
  · exact mul_nonneg (by linarith) (by linarith)
  · exact herror

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MaskedCount; original data types unchanged. -/
theorem envelope_count_antitone {δ κ x y : ℝ}
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hδ : 0≤δ) (hδhi : δ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) :
    GenericCount.envelope κ δ y ≤ GenericCount.envelope κ δ x := by
  apply QRH.Record12518109Return.finiteEnvelope_antitone
    QRH.Record12518109Return.countingR GenericCount.admittedBranches hxy hy
  rw [QRH.Record12518109Return.countingR_eq_actual hk,
    QRH.Record12518109Return.countingR_eq_actual hk]
  exact rowCount_antitone hδ hδhi hk hk1 hx hxy hy

theorem masked_amplitude_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(QRH.Record1252270103Return.GenericCount.envelope κ δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(QRH.Record1252270103Return.GenericCount.envelope κ δ (q/δ)+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply envelope_count_antitone hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    have h' : HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin ≤ δ/2 := hqtop
    linarith

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MaskedSourceCount; original data types unchanged. -/
theorem source_masked_count_with_error (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.SourceData)
    (counts : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤ σ) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count_with_error D F counts τ σ n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0< d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  have hm := masked_amplitude_class_count rows Finset.univ main
    (Z^d) (2*a-1) D.momentKappa D.t D.t_pos (fun j=>D.length j/d)
    (canonicalFamily D F Z z) bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le) (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos (show (0:ℝ)<ell by linarith [Geometry.ell_pos,Geometry.ell_lt_fifth]) hdpos)
    (K*C0) σ (by positivity) hne hcard
  exact hm

end
end Candidate.SilPrior.FourthPower.ReturnCountBridge
