/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual inverse/prime-product count on the original common supported-witness
fiber, retaining the credited imported OpenAI/Collet/Gao dictionary. -/
import Candidate.C092.transport.DirectCountInverse
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

/-- Actual inverse marked count: the original source inverse-field theorem
supplies the literal inverse-polynomial/prime-product moment. No inverse moment
or cardinality estimate remains as a premise. -/
theorem source_marked_inverse_fiber_count (D : Cycle25.Weighted.MomentData)
    (S : WeightedSourceData D) :
    ∃ J : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε tstar T allowance i),
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
    B.widths=(fun s => D.ell s/d) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height z : ℝ, 0 ≤ height → 1/2 ≤ a →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    0 ≤ z → z ≤ 7/37 → F.r+2*z < 1 → 2*F.r+8*z < 3 →
    (F.rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+D.t) := by
  obtain ⟨J,hfield⟩ := QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields
    S.modulus ⊤ le_top S 1 1 (by norm_num) (by norm_num)
  refine ⟨J,?_⟩
  intro η
  obtain ⟨C,hC,hfield⟩ := hfield η
  refine ⟨C,hC,?_⟩
  filter_upwards [hfield] with Z hfield
  refine ⟨hfield.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height z hheight ha hfreq
  dsimp only
  intro hz hzmax hcap1 hcap2
  let F := B.fiber bin label left right hne
  have hU : 1 < Z^d := Real.one_lt_rpow hfield.1 (by linarith)
  have hinv := hfield.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hheight
  exact inverse_fiber_count S.modulus ⊤ F.rows F.nonempty F.family (Z^d) a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z D.t
    (C*(1+height)^J) height F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh
    (by linarith [F.supply]) hz (hzmax.trans F.supply) F.fixed_bin (by positivity) hheight hfreq
    hcap1 hcap2 hinv.2
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.source_marked_inverse_fiber_count
