/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original no-slot inverse count on authentic source Batch fibers. Retains the
OpenAI inverse-amplifier and Collet/Gao source inverse-field transport. -/
import Candidate.C092.transport.DirectCountFiber
import Submissions.hailey_collet_1252270103.Record12518109Count.PhysicalDirect.InverseFields
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorNoSlotInverseCount
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

/-- A genuine inverse cardinality supplier on the same original supported-zero
fiber used by the ordinary count. The original inverse raw moment is supplied
by the source dictionary; no inverse moment or count is a premise. -/
theorem source_inverse_fiber_count (D : Cycle25.Weighted.MomentData)
    (S : WeightedSourceData D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ J : ℕ, ∀ η : Character,
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε tstar T allowance i),
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
    B.widths=(fun s => D.ell s/d) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → 1/2 ≤ a →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    0 ≤ F.r → F.r ≤ 2 →
    (F.rows.card : ℝ) ≤ (12*(1+height)*((C*(1+height)^J)*K))*
      (Z^d)^(HeckeInverseAmplification.sourceExponent F.r-(2*a-1)*F.r+2*ε+D.t) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,hcount⟩ := no_slot_inverse_count
    S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support
    (fun y => (S.bounded y).1) S.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) S.support (fun y => (S.bounded y).2) 2 D.t (by norm_num) D.t_pos
  obtain ⟨J,hfield⟩ := QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields
    S.modulus ⊤ le_top S c κ hc hκ
  refine ⟨K,hK,J,?_⟩
  intro η
  obtain ⟨C,hC,hfield⟩ := hfield η
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hcount
  have hscaled : ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, (1/200 : ℝ) ≤ d →
      U0 ≤ Z^d := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : 0 < (1/200 : ℝ))).eventually
      (eventually_ge_atTop U0),eventually_ge_atTop (1 : ℝ)] with Z hZ hZone
    intro d hd
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hZone hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [hfield,hscaled] with Z hfield hscaled
  refine ⟨hfield.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hheight ha hfreq
  dsimp only
  intro hr hr2
  let F := B.fiber bin label left right hne
  have hU : 1 < Z^d := Real.one_lt_rpow hfield.1 (by linarith)
  have hinv := hfield.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hheight
  exact hU0 (Z^d) (hscaled d hd) F.rows F.family a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right hr hr2 F.rowData F.reverse (C*(1+height)^J) height (by positivity)
    hheight hfreq F.row_norm F.row_coeff hinv.1
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.source_inverse_fiber_count
