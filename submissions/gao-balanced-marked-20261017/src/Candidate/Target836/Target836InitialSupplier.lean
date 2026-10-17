/- Actual arbitrary detector-label supplier for .874836.
Character identities and predecessor attribution retained; Apache-2.0. -/
import Candidate.Affine.Supply
import Candidate.Target836.Target836ChosenSetup
import Candidate.Target836.Target836DetectorInput
import Candidate.Target836.Source836.GeometryAffineMainUniform
import Candidate.Target836.Source836.GeometryAffinePaidComponents
import Candidate.Target836.Error836.GeometryAffineErrorCompletePayment
import Candidate.Target836.Error836.GeometryAffineErrorFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target836InitialSupplier
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
theorem detector_label_initial_affine {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0< ε) (mesh : ℝ) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ Target836.FinalAssembly.geometryChosenMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      Target836Moment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  let W:=fun x=>conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (S.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact S.complex_support (by intro hz;exact hx (by change conj (S.W x)=0;rw [hz];simp))
  have hm := Target836.FinalAssembly.geometry_chosen_mesh_admission ε hε
  have hmeshlt : mesh<(902420521/120632400000:ℝ)/2 := hmesh.trans_lt hm.2.2.2.2
  have hmeshμ : mesh≤ geometryLossUnit 1 (ε/4)/8 := hmesh.trans hm.2.2.2.1
  have hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8) :=
    hmesh.trans hm.2.2.1
  have hmarkedmesh : mesh ≤ markedRawMesh*markedCoreMin :=
    hmesh.trans (Target836.FinalAssembly.geometry_chosen_marked_mesh ε)
  have hε4 : 0< ε/4 := by positivity
  let row := naturalRowOf ηl (detector_label_modulus S η label)
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=Target836SourceAssembly.actual_affine_main_uniform_paid (α:=Fin D.N)
    S.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad
    W hW hs hβlo hβhi ηl 1 row 1 (by norm_num) (ε/4) mesh bΦ hε4 hmeshlt hmesh0.le
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
          Target836ErrorPayment.GeometryAffineErrorPaidSpec S.modulus ⊤ le_top S.S W hW.continuous hs Ψ ηl ηl mesh (ε/4)
            T Se De Ce Z := by
    intro Ψ _ _
    apply Target836ErrorPayment.actual_affine_error_uniform_paid_of_normalized (α:=Fin D.N) S.modulus ⊤ le_top
      0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad W hW.continuous hs Ψ ηl ηl (ε/4) mesh
      hε4 hmeshlt (internalQ (weighted_sourceFixedIdeal S) ηl) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2
    exact Target836ErrorPayment.actual_affine_error_normalized_family (α:=Fin D.N) S.modulus ⊤ le_top
      S.S S.exclusions.bad W hW hs hβlo Ψ ηl ηl (weighted_sourceFixedIdeal S)
      (weighted_sourceFixedIdeal_le_modulus S) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2 (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := Target836SourceAssembly.literal_affine_geometry_budget_of_main_error S.modulus ⊤ le_top S.S S.exclusions.bad
    W hW.continuous hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  obtain ⟨degree,Sd,C,hC,hev⟩ := Target836SourceAssembly.literal_geometry_initial_affine (α:=Fin D.N) S.modulus ⊤ le_top
    W hW hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hm.2.1) hβlo (by linarith) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1 (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget
  exact ⟨degree,Sd,C,hC,hev⟩


/-- Every live dictionary label now has the actual source moment. -/
theorem actual_detector_affine_input : Target836InitialTransport.DetectorAffineInput := by
  intro D S hbetaLo hbetaHi hfine
  apply Target836InitialTransport.actual_detector_affine_input836_of_initial S
    (DetectorAffine.detectorMesh D.t) (DetectorAffine.detectorMesh_pos D.t_pos) hfine
  intro eta bPhi hbPhi label
  apply detector_label_initial_affine S eta label hbetaLo hbetaHi D.t D.t_pos
    (DetectorAffine.detectorMesh D.t) (DetectorAffine.detectorMesh_pos D.t_pos) _ bPhi hbPhi
  exact le_of_eq (detectorMesh_eq D.t)
end
end OAI.SevenEighths.Target836InitialSupplier
#print axioms OAI.SevenEighths.Target836InitialSupplier.detector_label_initial_affine
#print axioms OAI.SevenEighths.Target836InitialSupplier.actual_detector_affine_input
