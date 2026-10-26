/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified first labels and residual projectors are counted after the
complete-cost selection has supplied an injective arithmetic key. Reuses the
coefficient-independent Cycle61 first-label and reciprocal-projector counts. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalGeometryBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryZeroPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentLogDyadic CenteredMomentSecondCanonical CenteredMomentRankinRadical
open CompletedGauss CenteredMomentSecondRetainedAggregate
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Only a scalar cost is bounded here. All labels are from the actual
modified source, and the final inverse norm is that of its original seed.
The prior complete-cost selection has already paid the dyads and rays. -/
theorem eventual_selected_modified_payment (B L ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι)(modifier : Tuple ι→ℂ)(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)
      (bin : ℤ×(Fin 5→ℤ)),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
    ∀(J : Type*)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column j),
        (column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^L)→
    ∀(factor E : ℝ)(cost : J→ℝ),0≤factor→
      (∀j,cost j≤factor*Z^(E-geometryExponents s modifier R seed K Z ξ (column j).1.val 2)/
        ((column j).2.1.val.absNorm:ℝ))→
      (∑j,cost j)≤C*factor*Z^(E+2*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩:=eventual_first_zero_label_projector_payment B L ε hB hL hε
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s modifier R seed K ξ hK bin hs hs0 hz₁ hz₂ hsource J _ column hinj hlive hcap factor E cost hf hcost
  let code:=fun j:J=>(FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column j),(column j).2.1.val)
  let pairs:=Finset.univ.image code
  let labels:=pairs.image Prod.fst
  let Ds:=pairs.image Prod.snd
  let p₀:ℝ:=(bin.2 2:ℝ)*Real.logb Z 2
  let p₁:ℝ:=min B (((bin.2 2:ℝ)+1)*Real.logb Z 2)
  have hw (q : FirstSourceLabel×Ideal O) (hq:q∈pairs):∃j:J,code j=q := by
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hq
    exact ⟨j,hj⟩
  have hlw (l:FirstSourceLabel) (hl:l∈labels):
      ∃j:J,FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column j)=l := by
    obtain ⟨q,hq,hq'⟩:=Finset.mem_image.mp hl
    obtain ⟨j,hj⟩:=hw q hq
    exact ⟨j,(congrArg Prod.fst hj).trans hq'⟩
  have hcommon (j:J):=FirstFamily.label_common_bounds s modifier R seed K Z ξ hK bin hs hz₁ hz₂ (column j)
  have hlabel (j:J):=FirstFamily.label_supported s modifier R seed K Z ξ hK bin (column j)
  have hrange (j:J):=actual_geometry_fiber_range s modifier R seed K Z ξ B hz.1 hs hz₁ hz₂ hsource bin (column j).1 2
  have hrad (j:J):((commonRadical (code j).1.1.1 (code j).1.1.2).absNorm:ℝ)≤Z^p₁ := by
    have hn:=actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource (column j).1.val 2
    have hp:geometryNorms s modifier R seed K Z ξ (column j).1.val 2≤
        Z^(((bin.2 2:ℝ)+1)*Real.logb Z 2) := by
      have hh:=Real.rpow_le_rpow_of_exponent_le hz.1.le (hrange j).2.le
      rw [QRH.Record1252270103Source.High.CoupledFirst.geometryExponents,
        Real.rpow_logb (zero_lt_one.trans hz.1) hz.1.ne' (zero_lt_one.trans_le hn.1)] at hh
      exact hh
    dsimp only [p₁]
    rcases le_total B (((bin.2 2:ℝ)+1)*Real.logb Z 2) with h|h
    · rw [min_eq_left h];exact hn.2
    · rw [min_eq_right h];exact hp
  have hbudget:=hz.2 p₁ (E+p₁-p₀) factor (min_le_left _ _) hf seed hs hs0 labels
    (by intro l hl;obtain ⟨j,rfl⟩:=hlw l hl;exact ⟨(hlabel j).1,(hlabel j).2.1⟩)
    (by intro l hl;obtain ⟨j,rfl⟩:=hlw l hl;exact (hlabel j).2.2)
    (by intro l hl;obtain ⟨j,rfl⟩:=hlw l hl;exact ⟨(hcommon j).1,(hcommon j).2.1⟩)
    (by intro l hl;obtain ⟨j,rfl⟩:=hlw l hl;exact ⟨(hcommon j).2.2.1.trans hsource,(hcommon j).2.2.2.trans hsource⟩)
    (by intro l hl;obtain ⟨j,rfl⟩:=hlw l hl;exact hrad j) Ds
    (by
      intro D hd;obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hd
      obtain ⟨j,rfl⟩:=hw q hq
      exact FirstFamily.live_projector_squarefree s modifier R seed K Z ξ hK bin _ (column j) (hlive j))
    (by
      intro D hd;obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hd
      obtain ⟨j,rfl⟩:=hw q hq;exact hcap j)
  have hpower:Z^(E+p₁-p₀+2*ε)≤2*Z^(E+2*ε) := by
    have hp:p₁-p₀≤Real.logb Z 2 := by
      have hm:=min_le_right B (((bin.2 2:ℝ)+1)*Real.logb Z 2)
      dsimp only [p₁,p₀];linarith
    have hh:=Real.rpow_le_rpow_of_exponent_le hz.1.le
      (show E+p₁-p₀+2*ε≤E+2*ε+Real.logb Z 2 by linarith)
    apply hh.trans_eq
    rw [Real.rpow_add (zero_lt_one.trans hz.1),Real.rpow_logb
      (zero_lt_one.trans hz.1) hz.1.ne' (by norm_num : (0:ℝ)<2)]
    ring
  have hselected:(∑j:J,factor*Z^(E-p₀)/((code j).2.absNorm:ℝ))=
      ∑q∈pairs,factor*Z^(E-p₀)/(q.2.absNorm:ℝ) := by
    dsimp only [pairs]
    rw [Finset.sum_image]
    exact fun j _ k _ h=>hinj h
  calc
    _≤∑j:J,factor*Z^(E-p₀)/((code j).2.absNorm:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply (hcost j).trans
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz.1.le (by have hh:=(hrange j).1;dsimp only [p₀];linarith)) hf)
        (Nat.cast_nonneg _)
    _=∑q∈pairs,factor*Z^(E-p₀)/(q.2.absNorm:ℝ) := hselected
    _≤∑l∈labels,∑D∈Ds,factor*Z^(E-p₀)/(D.absNorm:ℝ) := by
      rw [←Finset.sum_coe_sort pairs (fun q=>factor*Z^(E-p₀)/(q.2.absNorm:ℝ))]
      exact selected_zero_pairs pairs _ (mul_nonneg hf (Real.rpow_nonneg (zero_lt_one.trans hz.1).le _))
    _=∑l∈labels,∑D∈Ds,factor*Z^((E+p₁-p₀)-p₁)/(D.absNorm:ℝ) := by
      rw [show (E+p₁-p₀)-p₁=E-p₀ by ring]
    _≤C*factor*Z^(E+p₁-p₀+2*ε)/(seed.absNorm:ℝ) := hbudget
    _≤C*factor*(2*Z^(E+2*ε))/(seed.absNorm:ℝ) := by gcongr
    _=_ := by ring

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.eventual_selected_modified_payment
