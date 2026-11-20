/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original unmarked ordinary source count, using the credited Cycle25/Collet
zero-slot source and the original supported-witness plain energy kernel. -/
import Candidate.C092.transport.DirectCountMarkedInverse
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.PlainInput
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorNoSlotPlainCount
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open Cycle25ProbeFinalAssembly Cycle25ProbeDetectorPlainMarkedFineField

/-- Genuine ordinary unmarked count, including the original m≥1/2 tail.
The zero-slot source theorem supplies the moment on the original source fiber. -/
theorem source_unmarked_plain_fiber_count (D : Cycle25.Weighted.MomentData)
    (S : WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ) :
    ∃ J : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a D.ε tstar T allowance i),
    B.rows ⊆ rows → B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → 0 ≤ a →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    (F.rows.card : ℝ) ≤ (192*(1+height)*(C*(1+height)^J))*
      (Z^d)^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*D.ε+D.t) := by
  have hzero := terminal_zero_input S κ hκlo hκhi hβ hκβ
  obtain ⟨J,hfield⟩ := Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked
    D S hzero
  refine ⟨J,?_⟩
  intro η
  obtain ⟨C,hC,hfield⟩ := hfield η
  refine ⟨C,hC,?_⟩
  filter_upwards [hfield] with Z hfield
  refine ⟨hfield.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight ha hfreq
  dsimp only
  let F := B.fiber bin label left right hne
  have hU : 1 < Z^d := Real.one_lt_rpow hfield.1 (by linarith)
  have hplain := hfield.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight
  exact no_slot_plain_count F.rows F.family (Z^d) a D.ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    D.t (C*(1+height)^J) height (by positivity) hheight hfreq
    (fun j k hjk σ hσ t ht => (hplain j k hjk σ hσ t ht).1)
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.source_unmarked_plain_fiber_count
