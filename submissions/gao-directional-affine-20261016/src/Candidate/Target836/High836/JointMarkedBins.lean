import Candidate.Cycle63.Marked.JointWeightedFamily
import Candidate.Target836.High836.MarkedBins

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource Cycle63Moment
local notation "O" => HeckeFamily.O

/-- Genuine two-stage multiplicity and the four geometric exponent bins
lift a distinct-row marked max-product estimate. The physical slot width
cancels its normalization before the geometric reserve is paid. -/
theorem actual_joint_marked_binned_bound (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0<loss) :
    ∃Cmult : ℝ,0<Cmult ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→O,
      ∀Z : ℝ,2 ≤ Z→∀{κ : Type}[Nonempty κ]
      (key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key→
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(amplitude energy : κ→ℝ)
        (δ live qmin Q width Bbox Craw err target reserve : ℝ)(gain : ℝ→ℝ),
      Named.q ≤ δ→δ ≤ 3/4→0 ≤ Craw→0<width→Monotone gain→
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox)→
      (∀l∈labels,qmin ≤ x l 2 ∧ x l 2+width ≤ Q)→
      (∀l∈labels,retainedHighExponent δ gain (x l) ≤ target-reserve)→
      (∀l∈labels,0 ≤ amplitude l)→
      (∀l∈labels,energy l ≤ Z^(x l 0+δ*(x l 3-live))*amplitude l)→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^(x l 2))→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^B)→
      (∀l∈labels,Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2≠0 ∧
        Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2≠0)→
      (∀l∈labels,primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 ∧
        primeSupport (key l).val.2.1.1=primeSupport (key l).val.2.1.2)→
      (∀l∈labels,((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm:ℝ) ≤ Z^B)→
      (∀l∈labels,((key l).val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm:ℝ) ≤ Z^B ∧ ((key l).val.2.1.1.absNorm:ℝ) ≤ Z^B ∧
        ((key l).val.2.1.2.absNorm:ℝ) ≤ Z^B)→
      (∀l∈labels,((firstSourceMissing left (key l).val.1).absNorm:ℝ) ≤ Z^(x l 1))→
      (∀rows : Finset κ,rows⊆labels→
        Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set κ)→
        ∀q : ℝ,qmin ≤ q→q ≤ Q→
        (∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q)→
        (∑l∈rows,amplitude l) ≤ Craw*Z^(unmarkedDensity δ*q+δ*live-gain q+err))→
      (∑l∈labels,energy l) ≤ 
        ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
          (Cmult*Craw*Z^(target-reserve+4*width+loss+err)) := by
  obtain ⟨Cm,hCm,hmult⟩:=actual_joint_weighted_family_bound B loss hB hloss
  refine ⟨Cm,hCm,?_⟩
  intro left u₀ unit Z hZ κ _ key hinj labels x amplitude energy δ live qmin Q width Bbox Craw err
    target reserve gain hδ hδ' hCraw hw hgain hx hq hpoint hamp hfactor hnorm hraw hsupp heq hsupport
    hideals hmissing hcount
  have hZ1 : 1 ≤ Z:=by linarith
  have hZp : 0<Z:=by linarith
  have hd0 : 0 ≤ δ:=by norm_num [Named.q] at hδ;linarith
  have hbin (b : Fin 4→ℤ) (hb : b∈labels.image (fun l=>exponentBin width (x l))) :
      (∑l∈labels.filter (fun l=>exponentBin width (x l)=b),energy l) ≤ 
        (Cm*Craw*Z^(loss+err))*Z^(retainedHighExponent δ gain (exponentBinUpper width b)) := by
    let rows:=labels.filter (fun l=>exponentBin width (x l)=b)
    let u:=exponentBinUpper width b
    have hmem (l : κ)(hl : l∈rows):l∈labels:=(Finset.mem_filter.mp hl).1
    have hround (l : κ)(hl : l∈rows)(j : Fin 4):x l j ≤ u j ∧ u j ≤ x l j+width:=by
      have he:=exponent_bin_enclosure width hw (x l) j
      rw [(Finset.mem_filter.mp hl).2] at he
      exact he
    obtain ⟨l₀,hl₀,hb₀⟩:=Finset.mem_image.mp hb
    have hl₀' : l₀∈rows:=Finset.mem_filter.mpr ⟨hl₀,hb₀⟩
    have hqlo : qmin ≤ u 2:=(hq l₀ hl₀).1.trans (hround l₀ hl₀' 2).1
    have hqhi : u 2 ≤ Q:=(hround l₀ hl₀' 2).2.trans (hq l₀ hl₀).2
    have hnorm' (l : κ)(hl : l∈rows) : rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^(u 2):=
      (hnorm l (hmem l hl)).trans (Real.rpow_le_rpow_of_exponent_le hZ1 (hround l hl 2).1)
    have hs:=hmult left u₀ unit Z hZ (u 1)
      (Craw*Z^(unmarkedDensity δ*u 2+δ*live-gain (u 2)+err)) key hinj rows amplitude
      (fun l hl=>hamp l (hmem l hl)) (fun l hl=>hraw l (hmem l hl))
      (fun l hl=>hsupp l (hmem l hl)) (fun l hl=>heq l (hmem l hl))
      (fun l hl=>hsupport l (hmem l hl)) (fun l hl=>hideals l (hmem l hl))
      (fun l hl=>(hmissing l (hmem l hl)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ1 (hround l hl 1).1)) (by
        intro selected hselected hselinj
        exact hcount selected (hselected.trans (Finset.filter_subset _ _)) hselinj (u 2) hqlo hqhi
          (fun l hl=>hnorm' l (hselected hl)))
    calc
      _ ≤ ∑l∈rows,Z^(u 0+δ*(u 3-live))*amplitude l := by
        apply Finset.sum_le_sum
        intro l hl
        apply (hfactor l (hmem l hl)).trans
        apply mul_le_mul_of_nonneg_right _ (hamp l (hmem l hl))
        apply Real.rpow_le_rpow_of_exponent_le hZ1
        have hh:=mul_le_mul_of_nonneg_left (hround l hl 3).1 hd0
        linarith [(hround l hl 0).1]
      _=Z^(u 0+δ*(u 3-live))*(∑l∈rows,amplitude l) := (Finset.mul_sum ..).symm
      _ ≤ Z^(u 0+δ*(u 3-live))*(Cm*Z^(u 1+loss)*
          (Craw*Z^(unmarkedDensity δ*u 2+δ*live-gain (u 2)+err))) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hZp.le _)
      _=_ := by
        have hex : (u 0+δ*(u 3-live))+(u 1+loss)+
            (unmarkedDensity δ*u 2+δ*live-gain (u 2)+err)=
            (loss+err)+retainedHighExponent δ gain u := by
          dsimp only [retainedHighExponent,highExponentValue]
          ring
        calc
          _=Cm*Craw*(Z^(u 0+δ*(u 3-live))*Z^(u 1+loss)*
              Z^(unmarkedDensity δ*u 2+δ*live-gain (u 2)+err)) := by ring
          _=Cm*Craw*Z^((loss+err)+retainedHighExponent δ gain u) := by
            rw [←Real.rpow_add hZp,←Real.rpow_add hZp,hex]
          _=_ := by rw [Real.rpow_add hZp];ring
  have hh:=retained_high_binned_sum labels x energy width Bbox δ Z (Cm*Craw*Z^(loss+err))
    target reserve hw hZ1 (by positivity) ⟨hδ,hδ'⟩ gain hgain hx hpoint hbin
  apply hh.trans_eq
  congr 1
  rw [mul_assoc,←Real.rpow_add hZp]
  congr 1
  congr 1
  ring

end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.actual_joint_marked_binned_bound
