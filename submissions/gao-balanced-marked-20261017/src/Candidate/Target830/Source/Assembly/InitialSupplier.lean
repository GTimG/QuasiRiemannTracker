/- Actual arbitrary detector-label supplier for .874830.
Character identities and predecessor attribution retained; Apache-2.0. -/
import Candidate.Affine.Supply
import Candidate.Target830.Source.Assembly.SourceMesh
import Candidate.Target830.Source.Assembly.ErrorMono
import Candidate.Target830.Physical.AffineInput
import Candidate.Target830.High.MainUniform
import Candidate.Target830.Source.Assembly.PaidComponents
import Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorCompletePayment
import Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
open Cycle25WeightedNumeratorPhysical CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentLogDyadic
open Cycle63MarkedPlain Cycle63InitialMass
local notation "O" => HeckeFamily.O
/-- The initial affine moment for one detector label. -/
theorem detector_label_initial_affine_capped (plane : SourcePlane) {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0< ε) (hεcap : ε≤1/10000000000000000) (mesh : ℝ) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ chosenMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  let W:=fun x=>conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (S.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact S.complex_support (by intro hz;exact hx (by change conj (S.W x)=0;rw [hz];simp))
  obtain ⟨hm0,hmcomp,hmcommon,hmmu,hmamp,hmmarked⟩:=chosen_mesh_admission ε hε
  have hmeshlt : mesh<Source.amplifierMinimum/2:=hmesh.trans_lt hmamp
  have hmeshμ : mesh≤geometryLossUnit 1 (ε/4)/8:=hmesh.trans hmmu
  have hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8):=
    hmesh.trans hmcommon
  have hmarkedmesh : mesh≤Marked830Plain.rawMesh830*Marked830Plain.rawCore830:=hmesh.trans hmmarked
  have hε4 : 0< ε/4 := by positivity
  let row := naturalRowOf ηl (detector_label_modulus S η label)
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=TargetHigh830.actual_affine_main_uniform_paid (plane:=plane) (α:=Fin D.N)
    S.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad
    W hW hs hβlo hβhi ηl 1 row 1 (by norm_num) (ε/4) mesh bΦ hε4 (by linarith) hmeshlt hmesh0.le
    hmeshμ hmeshcap hmarkedmesh hbΦ
  have hp:=hpaid (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2
  have hex : excluded row.character 1 = ηl := detector_label_excluded S η label
  rw [hex] at hp
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          ErrorReconstruction.GeometryAffineErrorPaidSpec (plane:=plane) S.modulus ⊤ le_top S.S W hW.continuous hs Ψ ηl ηl mesh (ε/4)
            T Se De Ce Z := by
    intro Ψ _ _
    apply ErrorReconstruction.actual_affine_error_uniform_paid_of_normalized (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad W hW.continuous hs Ψ ηl ηl (ε/4) mesh
      hε4 hmeshlt (internalQ (weighted_sourceFixedIdeal S) ηl) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2
    exact ErrorReconstruction.actual_affine_error_normalized_family (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      S.S S.exclusions.bad W hW hs hβlo Ψ ηl ηl (weighted_sourceFixedIdeal S)
      (weighted_sourceFixedIdeal_le_modulus S) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2 (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error (plane:=plane) S.modulus ⊤ le_top S.S S.exclusions.bad
    W hW.continuous hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  obtain ⟨degree,Sd,C,hC,hev⟩ := literal_geometry_initial_affine (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
    W hW hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hmcomp) hβlo (by linarith) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1 (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget
  exact ⟨degree,Sd,C,hC,hev⟩

/-- The actual source is proved at a smaller capped error and then enlarged;
all masks, profiles, heights and the fixed mesh are unchanged. -/
theorem detector_label_initial_affine (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0<ε) (mesh : ℝ) (hmesh0 : 0 < mesh)
    (hmesh : mesh ≤ sourceMesh ε) (bΦ : ℝ) (hbΦ : 2≤bΦ) :
    let ηl:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  have hs:=capped_error_bounds hε
  obtain ⟨degree,Sd,C,hC,hev⟩:=detector_label_initial_affine_capped plane S η label hβlo hβhi
    (cappedError ε) hs.1 hs.2.2 mesh hmesh0 hmesh bΦ hbΦ
  refine ⟨degree,Sd,C,hC,?_⟩
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hu hU
  exact initial_affine_error_mono (α:=Fin D.N) S.modulus ⊤ le_top plane
    (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (cappedError ε) ε U ηl ηl (weighted_sourceFixedIdeal S) degree Sd C hC.le hU hs.2.1 hu

/-- Complete genuine arbitrary detector-label moments for both finite planes.
The common strictly positive source mesh precedes the slot dictionary. -/
theorem actual_label_initial_moments (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t) :
    Physical.InitialTransport.LabelInitialMoments plane S mesh := by
  intro η bΦ hbΦ label
  exact detector_label_initial_affine plane S η label hβlo hβhi D.t D.t_pos mesh hmesh0 hmesh bΦ hbΦ

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.detector_label_initial_affine_capped

#print axioms OAI.SevenEighths.Target830.Source.Assembly.detector_label_initial_affine
#print axioms OAI.SevenEighths.Target830.Source.Assembly.actual_label_initial_moments
