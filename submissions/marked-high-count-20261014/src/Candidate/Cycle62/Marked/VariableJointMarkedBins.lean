import Candidate.Cycle62.Marked.JointMarkedBins

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource Cycle62Moment
local notation "O" => HeckeFamily.O

/-- Genuine two-stage multiplicity and the four geometric exponent bins
lift a distinct-row marked max-product estimate. The physical slot width
cancels its normalization before the geometric reserve is paid. -/
theorem actual_variable_joint_marked_binned_bound (B loss : ℝ) (hB : 0≤B) (hloss : 0<loss) :
    ∃Cmult : ℝ,0<Cmult ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→O,
      ∀Z : ℝ,2≤Z→∀{κ Slot Dict : Type}[Nonempty κ][Fintype Slot][DecidableEq Slot][Fintype Dict]
      (key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key→
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(energy : κ→ℝ)
        (slots : κ→Finset Slot)(index : κ→Dict)(amplitude : κ→Slot→ℂ)(w : Slot→ℝ)
        (δ qmin Q width Bbox Craw err target reserve : ℝ)(gain : Finset Slot→ℝ→ℝ),
      Cycle62.Arithmetic.q0≤δ→δ≤3/4→0≤Craw→0<width→(∀s,Monotone (gain s))→
      (∀l∈labels,∀j,-Bbox≤x l j ∧ x l j≤Bbox)→
      (∀l∈labels,qmin≤x l 2 ∧ x l 2+width≤Q)→
      (∀l∈labels,retainedHighExponent δ (gain (slots l)) (x l)≤target-reserve)→
      (∀l∈labels,energy l≤Z^(x l 0+δ*(x l 3-∑s∈slots l,w s))*(∏s∈slots l,max 1 ‖amplitude l s‖)^2)→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^(x l 2))→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^B)→
      (∀l∈labels,Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2≠0 ∧
        Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2≠0)→
      (∀l∈labels,primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 ∧
        primeSupport (key l).val.2.1.1=primeSupport (key l).val.2.1.2)→
      (∀l∈labels,((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.2.1.2.absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^(x l 1))→
      (∀(j : Dict)(s : Finset Slot)(rows : Finset κ),rows⊆labels.filter (fun l=>index l=j ∧ slots l=s)→
        Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set κ)→
        ∀q : ℝ,qmin≤q→q≤Q→
        (∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^q)→
        (∑l∈rows,(∏k∈s,max 1 ‖amplitude l k‖)^2)≤
          Craw*Z^(unmarkedDensity δ*q+δ*(∑k∈s,w k)-gain s q+err))→
      (∑l∈labels,energy l)≤
        (Fintype.card Dict:ℝ)*(2:ℝ)^(Fintype.card Slot)*
        (((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
          (Cmult*Craw*Z^(target-reserve+4*width+loss+err))) := by
  obtain ⟨C,hC,hbound⟩:=actual_joint_marked_binned_bound B loss hB hloss
  refine ⟨C,hC,?_⟩
  intro left u₀ unit Z hZ κ Slot Dict _ _ _ _ key hinj labels x energy slots index amplitude w
    δ qmin Q width Bbox Craw err target reserve gain hδ hδ' hCraw hw hgain hx hq hpoint
    hfactor hnorm hraw hsupp heq hsupport hideals hmissing hcount
  apply fixed_dictionary_slot_partition labels index slots energy
  intro j s
  let rows:=labels.filter (fun l=>index l=j ∧ slots l=s)
  have hmem (l : κ)(hl : l∈rows):l∈labels:=(Finset.mem_filter.mp hl).1
  have hslots (l : κ)(hl : l∈rows):slots l=s:=(Finset.mem_filter.mp hl).2.2
  apply hbound left u₀ unit Z hZ key hinj rows x
    (fun l=>(∏k∈s,max 1 ‖amplitude l k‖)^2) energy δ (∑k∈s,w k)
    qmin Q width Bbox Craw err target reserve (gain s) hδ hδ' hCraw hw (hgain s)
    (fun l hl=>hx l (hmem l hl)) (fun l hl=>hq l (hmem l hl))
    (fun l hl=>by simpa only [hslots l hl] using hpoint l (hmem l hl))
    (fun _ _=>sq_nonneg _)
    (fun l hl=>by simpa only [hslots l hl] using hfactor l (hmem l hl))
    (fun l hl=>hnorm l (hmem l hl)) (fun l hl=>hraw l (hmem l hl))
    (fun l hl=>hsupp l (hmem l hl)) (fun l hl=>heq l (hmem l hl))
    (fun l hl=>hsupport l (hmem l hl)) (fun l hl=>hideals l (hmem l hl))
    (fun l hl=>hmissing l (hmem l hl))
  exact fun selected hselected hselinj q hq0 hq1 hnorm=>hcount j s selected hselected hselinj q hq0 hq1 hnorm

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_variable_joint_marked_binned_bound
