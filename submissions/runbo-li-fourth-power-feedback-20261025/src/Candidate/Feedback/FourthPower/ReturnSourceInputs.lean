/- REVIEW STATUS: Natural tail now follows from the ORIGINAL Sil endpoint 0.8746935; the second-stage target is not its own prior. -/
/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Joint detector and source data, common source meshes, both amplifiers,
masked-count moments, and the full-domain physical input. The source
assumption is UniformUnitFaceSource fullSourceFace.

Detector construction and moment assembly use PR69 GenericData and
PhysicalDirect.SourceMoments. Geometry.Parameters is combined with the
parameter-specific counting and transport bounds.
-/
import Candidate.Feedback.FourthPower.ReturnActualCount
import Candidate.Feedback.FourthPower.ReturnIntermediateBound
import Candidate.Feedback.FourthPower.ReturnPhysicalActive
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceMoments
import Candidate.Feedback.FourthPower.ReturnMomentBridge
import Candidate.Feedback.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReturnSourceInputs
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open ReturnWindows ReturnSourceFaces ReturnOldCount ReturnActualCount
open ReturnPhysicalInput ReturnPhysicalActive ReturnPhysicalSchedule
open QRH.Record12518109Existence QRH.Record12518109Count
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator.PhysicalTail
open Cycle25.Weighted.Numerator Cycle25.Numerator HeckeInverseAmplification ProbeHighRowFamily

open ProbeRowRadicalConductor (fixedConductorConstant)

noncomputable def parameters : QRH.Record1252270103Return.Geometry.Parameters where
  theta := Candidate.Feedback.FourthPower.theta
  ell := Candidate.Feedback.FourthPower.ell
  x := Candidate.Feedback.FourthPower.x
  y := Candidate.Feedback.FourthPower.y
  ell_pos := by norm_num [ell,theta]
  sixth_lt_ell := by norm_num [ell,theta]
  ell_lt_fifth := by norm_num [ell,theta]
  ell_lt_x := by norm_num [x,ell,theta,h]
  x_lt_y := by norm_num [x,y,ell,theta,h]
  y_lt_half := by norm_num [y,ell,theta,h]
  x_add_y := geometry_identities.1
  dilation_gap := by norm_num [x,y,ell,theta,h]
  tuple_margin_neg := by norm_num [x,y,ell,theta,h]
  signal_boundary := geometry_identities.2

local instance : QRH.Record1252270103Return.Geometry.Parameters := parameters
local instance : QRH.Record1252270103Return.CountScheme := countScheme

abbrev Detector := QRH.Record1252270103Return.GenericPhysical.BaselineData
abbrev Source (D : Detector) :=
  QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D

/-- Actual data, not an abstract energy/count contract. The two source inputs
are literally the original source theorem on the same positive mesh. -/
structure JointData (sigma affineError extraMesh : ℝ) where
  D : Detector
  F : Source D
  mesh : ℝ
  mesh_pos : 0 < mesh
  mesh_extra : mesh≤extraMesh
  fine_source : ∀j,D.length j ≤ mesh/200
  fine_natural : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  moment_exact : D.momentKappa=contraryKappa
  count_error : 159*D.ε+609*D.t ≤ sigma
  count_unit : UnitFaceSource fullSourceFace mesh D.t
  physical_unit : UnitFaceSource fullSourceFace mesh affineError
  counts : SavedParameters F

/-- Meshes precede D, its finite slot system, F, both saved amplifier pairs,
eta and every future height cutoff. The physical and count errors can differ. -/
theorem exists_joint_data
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta)
    (sigma affineError extraMesh : ℝ) (hsigma : 0 < sigma)
    (herror : 0<affineError) (hextra : 0<extraMesh) :
    Nonempty (JointData sigma affineError extraMesh) := by
  have hg := contrary_gates hbeta
  obtain ⟨physicalMesh,hphysicalMesh,hphysical⟩ := hsource affineError herror
  choose rawMesh hrawMesh hraw using
    fun t : {t : ℝ // 0<t}=>hsource t.val t.property
  let mesh : ℝ→ℝ := fun t=>if ht : 0<t then
    min (rawMesh ⟨t,ht⟩) (min physicalMesh extraMesh) else 1
  have hm : ∀t,0<t→0 < mesh t := by
    intro t ht
    simp only [mesh,dif_pos ht]
    exact lt_min (hrawMesh ⟨t,ht⟩) (lt_min hphysicalMesh hextra)
  obtain ⟨D,hk,hcount,hfine,hsourceFine⟩ :=
    QRH.Record1252270103Return.GenericPhysical.exists_baseline_data_common_mesh
      hg.1 hg.2.1 hsigma mesh hm
  obtain ⟨F⟩ := QRH.Record1252270103Return.GenericPhysical.exists_baseline_source D
  obtain ⟨counts⟩ := exists_saved_parameters F
  have hmraw : mesh D.t≤rawMesh ⟨D.t,D.t_pos⟩ := by
    simp only [mesh,dif_pos D.t_pos]
    exact min_le_left _ _
  have hmphys : mesh D.t≤physicalMesh := by
    simp only [mesh,dif_pos D.t_pos]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmextra : mesh D.t≤extraMesh := by
    simp only [mesh,dif_pos D.t_pos]
    exact (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨{
    D := D
    F := F
    mesh := mesh D.t
    mesh_pos := hm D.t D.t_pos
    mesh_extra := hmextra
    fine_source := hsourceFine
    fine_natural := hfine
    moment_exact := hk
    count_error := hcount
    count_unit := (hraw ⟨D.t,D.t_pos⟩).mono_mesh hmraw
    physical_unit := hphysical.mono_mesh hmphys
    counts := counts }⟩

variable {sigma affineError extraMesh : ℝ}

theorem actual_affine_inputs (A : JointData sigma affineError extraMesh) :
    ∀w∈countScheme.windows,WeightedAffineFineInput A.F w.face := by
  intro w hw
  have hw' : w∈List.ofFn admittedWindow := hw
  obtain ⟨i,hi⟩ := (List.mem_ofFn' admittedWindow w).mp hw'
  subst w
  apply QRH.Record1252270103Return.detector_affine_of_unit A.F
    (admittedWindow i).face (by rfl) A.mesh A.mesh_pos A.fine_source
  exact unit_source_to_branch (ReturnFinite.window i).branch A.count_unit

/-- PR67 -> the actual C30 intermediate return -> the fixed natural tail
needed by OUR seventeen windows. The full source remains the sole analytic
premise; the desired theta bound is not fed into its own return. -/
theorem natural_tail_from_full_source (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : UniformUnitFaceSource fullSourceFace) :
    2*HeckeZeroSupremum.beta-1≤ReturnWindows.naturalKappa := by
  have hi := ReturnIntermediateBound.incumbent_from_full_source hPrior hsource
  dsimp only [ReturnWindows.naturalKappa]
  linarith

/-- Genuine moment fields for the actual SAME D/F, both amplifier choices,
and every improved window. No moment/count estimate is an input. -/
theorem actual_count_moments (hPrior : OlderIncumbentContract.OlderIncumbentInput) (A : JointData sigma affineError extraMesh)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta) :
    ∀η : Character,∃J : ℝ,0≤J ∧ ∃C : ℝ,0<C ∧
      ∀tau : ℝ,0<tau→tau≤1→∀ᶠZ : ℝ in atTop,
        QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound
          A.D (QRH.Record1252270103Return.GenericPhysical.baselineSource A.D A.F)
          A.counts η Z tau (C*(1+Z^(2*tau))^J) (Z^(2*tau)) := by
  have hg := contrary_gates hbeta
  exact Candidate.Feedback.FourthPower.ReturnMomentBridge.actual_source_moments
    A.D A.F A.counts hg.2.2
    (by rw [A.moment_exact]; exact le_rfl)
    (natural_tail_from_full_source hPrior hsource) A.fine_natural (actual_affine_inputs A)

/-- The physical input is also actually supplied, on the same mesh and source.
The radial support and all Fourier/profile constants precede U and its rows. -/
theorem actual_physical_input (A : JointData sigma affineError extraMesh) :
    ∃bPhi : ℝ,2≤bPhi ∧
      Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi ∧
      ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
        ∀ᶠU : ℝ in atTop,FullPhysicalAt A.F bPhi A.mesh affineError U degree control C := by
  obtain ⟨b,hb⟩ := radialMajorant_compact.isCompact.bddAbove
  let bPhi : ℝ := max 2 b
  have htop : 2≤bPhi := le_max_left _ _
  have hs : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi := by
    intro x hx
    exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)
  exact ⟨bPhi,htop,hs,full_input_of_unit A.F bPhi A.mesh affineError htop A.physical_unit⟩

/-- Output notation only. This is the literal active fourth-moment sum from
ReturnPhysicalActive; no theorem below takes this estimate as a hypothesis. -/
def ActiveFourthBound (A : JointData sigma affineError extraMesh)
    (G : 𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b U C : ℝ) (degree : ℕ) : Prop :=
  1<U ∧ ∀rows : Finset FreeRow,
    (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U)→
    ∀data : ∀i:rows,PhysicalReflectionData A.F.S A.F.exclusions.prime i.val,
    ∀N : rows→ℝ,(∀i,0<N i)→∀d : ℝ,ds≤d→d≤dplus→
    ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
    ∀T : Finset (Fin A.D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0<width i)→(∀i,width i≤A.mesh)→
      (∀i,width i≤Cycle25.sourceMesh A.D.t)→
      (∀i,(z i).re=17/50)→0≤height→(∀i,|(z i).im|≤height)→
      (∑i,width i) ≤ scheduledCapacity d (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack))→
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
        A.F.W 2 (U^(width s)) (z s)‖≤U)→
    let Y:=U^(y/d)
    let Lc (i:rows):=(data i).combinedConductor/
      ((fixedConductorConstant A.F.S:ℝ)*rowNorm i.val)
    (∑i:rows,‖if N i≤b*Y ∧
        dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
      then HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val)
        false G (Y/N i) 0 0 else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W 2
          (U^(width s)) (z s)‖^2)≤
      C*(1+height)^degree*U^(1+A.D.t+affineError+loss)

/-- Applies the complete finite-pair/Fourier/hybrid/reflection/active chain
to the actual source. Cutoff1/250 and the full downward face remain unchanged. -/
theorem actual_active_fourth (A : JointData sigma affineError extraMesh)
    (hbeta : theta<HeckeZeroSupremum.beta) (herror : 0<affineError)
    (G : 𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b : ℝ)
    (hloss : 0<loss) (hbox : 0<boxWidth) (hann : 0<annulusSlack) (hb : 0<b)
    (hsmall : 2*boxWidth+annulusSlack≤1/2) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      ActiveFourthBound A G loss boxWidth annulusSlack b U C degree := by
  have hg := contrary_gates hbeta
  obtain ⟨bPhi,_,hs,di,control,Ci,hCi,hi⟩ := actual_physical_input A
  exact full_active_box_fourth A.F contraryKappa hg.1 hg.2.1 le_rfl hg.2.2
    bPhi A.mesh affineError herror hs di control Ci hCi hi
    G loss boxWidth annulusSlack b hloss hbox hann hb hsmall

end
end Candidate.Feedback.FourthPower.ReturnSourceInputs
