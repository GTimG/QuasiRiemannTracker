/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B002
import Submissions.local44_20261013.Bundles.B003
import Submissions.local44_20261013.Bundles.B009
import Submissions.affine_local_20261013.Bundles.B014
import Submissions.affine_local_20261013.Bundles.B017
import Submissions.affine_local_20261013.Bundles.B018
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePaddedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceShift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferenceDeletedEnergy ; sha256 1aed5d04ec091e9405c716b5aa1a2155cbd94cba123cb29c6772cef834f89f6d -/
section





namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=> HeckeFamily.O

theorem weighted_deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=> livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=> livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem weighted_deleted_source_energy {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)(hab:ao ≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0< C ∧ 1< U₀ ∧
    ∀U:ℝ,U₀ ≤ U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι ≤ K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0 ≤ ell i) → (∀i,(ζ i).re ≤ 1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=> livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)< U^(ell i)) →
    ∀r:ℝ,0 ≤ r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2 ≤ U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=> F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2) ≤ 
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀ ≤ U:=(le_max_left _ _).trans hU
  have hUone:1< U:=hU₀.trans_le hU0
  have hUp:0< U:=zero_lt_one.trans hUone
  have hjshift: r-eta ≤ shiftedExponent data U r j ∧ shiftedExponent data U r j ≤ r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=> livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=> star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖ ≤ 1:=
    weighted_deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=> weighted_deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=> by rw [hqset];exact (hg i P hP).2.1)
    (fun _=> F.W) (fun _=> F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=> raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [weighted_deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferenceDeletedEnergy -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.HighData ; sha256 3a5f7d4a45e99294329af20a8ba2391baf6ac3c1e0a9c0c8478f3b99c2db42fa -/
section





noncomputable section
open scoped BigOperators
namespace Cycle25.HighParameters

structure HighData (Δ : ℝ) where
  momentKappa : ℝ
  momentKappa_lo : 7/10 ≤ momentKappa
  momentKappa_hi : momentKappa ≤ 3/4
  momentKappa_beta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ momentKappa
  momentKappa_exact : momentKappa = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t<Δ/4
  t_gap : t ≤ Δ/100000
  t_small : t≤1/100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=Cycle25.ell
  slots_bounds : ∀j,0 < ell j ∧ (7/8)*rmin ≤ ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps≤1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  central_budget : (159*ε+t+t+7*t)+(12*e+eps*(N+8))+
    (t+t+t+t+t*Cycle25.ell+(13243/1000)*e)+2*t ≤ Δ/100
  geometric_budget : sigma+8*e+t/8 ≤ 1/20
  principal_budget : sigma+t/8 ≤ 1/4000
  window_budget : sigma+e ≤ Cycle25.theta*((7/8)*rmin)
  floor_budget : 26*e+(N+8)*eps+t+t*Cycle25.ell+t/8+sigma ≤ 1/100
  high_saving : sigma+t/8+t/8 ≤ Δ/100
  weighted_top : 3*t ≤ Cycle25.rowExtension
  height_choice : ∀J : ℝ,0 ≤ J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ < t ∧ 2*τ*(1+J) ≤ t ∧ τ*(2+4*eps) < t

def HighData.toMomentData {Δ : ℝ} (D : HighData Δ) : Cycle25.Weighted.MomentData where
  N := D.N
  ell := D.ell
  t := D.t
  ε := D.ε
  e := D.e
  t_pos := D.t_pos
  t_small := D.t_small
  slots_injective := D.slots_injective
  slots_bounds := fun j=>⟨(D.slots_bounds j).1,by
    have hh := (D.slots_bounds j).2.2
    linarith only [hh,D.t_small]⟩
  epsilon_pos := D.epsilon_pos
  epsilon_small := D.epsilon_small
  e_pos := D.e_pos

end Cycle25.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the actual moment parameter and a loss budget relative to beta-theta. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.HighData -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceLowBranchGeometry ; sha256 08b2701d6d2ac12224f669ae906eccfc5d693f2e42a5f0127ab1be08e23ff569 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowBranchGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands Cycle25CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget Cycle25CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=> HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1< Z)(hX:0< X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤ X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤ M)(hell:0≤ ell)(hk:7/10≤ kappa)
    (hlarge:5*M/6≤ total+ell)(hcap:total+ell+(6*kappa-1)*ell≤ M):
    ell≤5*M/96 ∧ (6*kappa-1)*ell≤ M/6:=by
  have hkell:16/5*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤ M)(_hs:0≤ short)(hsM:short≤ M/4)(_hell:0≤ ell)(_hz:0≤ z)(hze:z≤ ell)
    (hk:7/10≤ kappa)(he:ell≤5*M/96)(hbudget:(6*kappa-1)*ell≤ M/6)(hxi:0≤ xi)
    (hhigh:5*M/6< short+max 0 along+z)
    (href:reflected≤ max 0 (M-along+xi)):
    0< along ∧ reflected+short+z≤37*M/48+xi ∧
      reflected+short+6*kappa*z≤15*M/16+xi:=by
  have haz:0< along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤ M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤5*M/96:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:7/10≤ kappa)(hxi:0≤ xi)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤ M) ∨
    (0< Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤37*M/48+xi ∧ reflected+short+6*kappa*z≤15*M/16+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤ comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤ M/16)(ht:reflected+short+z≤37*M/48+xi)
    (hc:reflected+short+6*kappa*z≤15*M/16+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤ M:=by
  constructor <;> linarith

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceLowBranchGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.FullWReconstruction ; sha256 d42fb02e80902c8e69b45ff0e792387c4381308f46bcbdfb54c206e672cbe5f6 -/
section



/-! The complete numerator integral is taken before any row amplitude estimate. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

def sourceSZWeight (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z

def rowNumeratorIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∫t : ℝ,(Y:ℂ)^((1/2:ℂ)+t*I-1)*mellin W1 ((1/2:ℂ)+t*I)*
    calibratedTupleValue S hS hmax η u P hPS W Yp s ((1/2:ℂ)+t*I) z

def integratedRowValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  frequencyWeight z ⟨u.val,u.property.1⟩ *
    rowNumeratorIntegral S hS hmax η u P hPS W Yp W1 Y s z

lemma weightedRow_w_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r : ℝ) (q : ℝ×ℝ) :
    (∫t : ℝ,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r (q,t))=
      sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
        integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I) := by
  unfold integratedRowValue rowNumeratorIntegral
  rw [←mul_assoc,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold weightedRowOnLines sourceMellinWeight sourceSZWeight
  norm_num only [ofReal_div,ofReal_one,ofReal_ofNat]
  ring

lemma fullW_inner_integrable (H : ℝ) (f : HeightSpace→ℂ)
    (hf : IntegrableOn f (fullWSlab H) heightMeasure) :
    IntegrableOn (fun q : ℝ×ℝ=>∫t : ℝ,f (q,t)) (szRectangle H) (volume.prod volume) := by
  have hi : Integrable f (((volume.prod volume).restrict (szRectangle H)).prod volume) := by
    simpa only [IntegrableOn,fullWSlab,heightMeasure,←Measure.prod_restrict,Measure.restrict_univ] using hf
  exact hi.integral_prod_left

lemma fullW_factored_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r H : ℝ)
    (hf : IntegrableOn (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r)
      (fullWSlab H) heightMeasure) :
    let F := fun q : ℝ×ℝ=> sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      (∫p in fullWSlab H,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r p
        ∂heightMeasure) = ∫q in szRectangle H,F q ∂(volume.prod volume) := by
  constructor
  · simpa only [weightedRow_w_integral] using fullW_inner_integrable H _ hf
  · rw [fullWSlab_fubini H _ hf]
    simp_rw [weightedRow_w_integral]

def integratedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),integratedRowValue S hS hmax η u (fun i=>(P i).val)
    (fun i=> hT i _ (P i).property) W Yp W1 Y s z

theorem finiteFullW_reconstruction {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)< a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let F := fun q : ℝ×ℝ=> sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=> a) (fun _=> H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫q in szRectangle H,F q ∂(volume.prod volume)) := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun j=>(P j).val) (fun j=> hT j _ (P j).property) η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50)
  let g (u : FreeRow) (P : ∀i,T i) (q : ℝ×ℝ) :=
    sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
        W Yp W1 Y (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : IntegrableOn (f u P) (fullWSlab H) heightMeasure := by
    have hh := fullWWeightedRow_integrable e a B H i he he' ha haTop hB hH S hS hmax hfirst
      (fun j=>(P j).val) (fun j=> hT j _ (P j).property) η u (hR u hu) (ψ u) (hbin u hu)
      W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    change Integrable ((fullWSlab H).indicator (f u P)) heightMeasure at hh
    exact (integrable_indicator_iff (fullWSlab_measurable H)).mp hh
  have hg (u : FreeRow) (hu : u∈R) (P : ∀i,T i) :
      IntegrableOn (g u P) (szRectangle H) (volume.prod volume) ∧
        (∫p in fullWSlab H,f u P p ∂heightMeasure)=∫q in szRectangle H,g u P q ∂(volume.prod volume) := by
    have hh := fullW_factored_integral S hS hmax η u (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
      W Yp W0 W1 X Y Z (a+16*e) (17/50) H (hi u hu P)
    simpa only [g,f,ofReal_div,ofReal_ofNat] using hh
  have hgi (u : FreeRow) (hu : u∈R) :
      IntegrableOn (fun q=>∑P:(∀i,T i),g u P q) (szRectangle H) (volume.prod volume) :=
    integrable_finsetSum _ (fun P _=>(hg u hu P).1)
  have hF : (fun q : ℝ×ℝ=> sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I))=
      (fun q=>∑u∈R,∑P:(∀i,T i),g u P q) := by
    funext q
    simp only [integratedDyadValue,Finset.mul_sum,g]
  dsimp only
  rw [hF]
  refine ⟨integrable_finsetSum _ hgi,?_⟩
  rw [integral_finsetSum R hgi,Finset.mul_sum]
  unfold finiteCentralFullWRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>(hg u hu P).1),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [←(hg u hu P).2]
  have hh := fullWWeightedRow_integral S hS hmax (fun j=>(P j).val)
    (fun j=> hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H
  rw [show (∫p,fullWWeightedRow S hS hmax (fun j=>(P j).val)
      (fun j=> hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H p ∂heightMeasure)=
      ∫p in fullWSlab H,f u P p ∂heightMeasure by
        exact integral_indicator (fullWSlab_measurable H)] at hh
  exact hh.symm

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.FullWReconstruction -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorMass ; sha256 e74a11337084380177dd82718ac14c570ec3fca9e7546bb7fa1f25958b39b010 -/
section


/-! Absolute coefficient bounds for the quotient-free local errors. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

def ramifiedErrorCoefficients (eta a rho x z : ℂ) (j : ℕ) : CubicCoefficients :=
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  let d := ramifiedStrictCoefficient p hp hg eta a rho x z j
  ⟨c.a, c.b + d, c.c, 0⟩

theorem ramified_error_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      (ramifiedErrorCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hr := ramified_regular_expansion p hp hg eta a rho x w z j
  have hs := ramified_strict_expansion p hp hg eta a rho x w z j
  rw [hs] at hr
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.eval,cubic]
  rw [eq_add_of_sub_eq hr]
  dsimp only [QuadraticCoefficients.eval,quadratic]
  ring

theorem ramified_error_mass_le (eta a rho x z : ℂ) (j : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (ramifiedErrorCoefficients p hp hg eta a rho x z j).mass r ≤
      (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass r +
      ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ * r := by
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.mass,cubicMass,
    QuadraticCoefficients.mass,quadraticMass]
  simp only [norm_zero,zero_mul,add_zero]
  have hh := mul_le_mul_of_nonneg_right
    (norm_add_le (ramifiedRegularCoefficients p hp hg eta a rho x z j).b
      (ramifiedStrictCoefficient p hp hg eta a rho x z j)) hr
  linarith

/-- Only repeated ramified labels cost a factor Q^rho on the left line. -/
theorem ramified_error_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a phase x z : ℂ) (alpha eps rho : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hphase : phase ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) (j : ℕ) (hj : j < 6) :
    (ramifiedErrorCoefficients p hp hg eta a phase x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(1 / 2 - rho))) ≤
      1161 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) *
        (if 2 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ rho else 1) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0 < Q := by dsimp only [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp only [Q]; linarith
  have hR := ramified_regular_coefficient_mass p hp hg hc eta a phase x z
    alpha eps (1 / 2 - rho) hQ heta ha hphase halpha halpha1 heps heps1 hx hz hline j hj
  have hM := ramified_error_mass_le p hp hg eta a phase x z j
    (Q ^ (-(1 / 2 - rho))) (Real.rpow_nonneg hQ0.le _)
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hz' : (17 / 50 : ℝ) ≤ z.re := hz.ge
  by_cases hj2 : 2 ≤ j
  · rw [if_pos hj2]
    have hS := ramified_strict_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j hj
    have he : Q ^ (1 - (1 / 2 - rho)) = Q ^ (1 / 2 : ℝ) * Q ^ rho := by
      rw [←Real.rpow_add hQ0]
      congr 1
      ring
    change _ ≤ 6 * Q ^ (1 - (1 / 2 - rho)) at hS
    rw [he] at hS
    have hpow : 1 ≤ Q ^ rho := Real.one_le_rpow hQ1 hrho
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ) * Q ^ rho
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    nlinarith [Real.rpow_nonneg hQ0.le (1 / 2 : ℝ)]
  · rw [if_neg hj2,mul_one]
    have hS := ramified_boundary_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j (by omega)
    have hpow : Q ^ (-(1 / 2 - rho)) ≤ Q ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    change _ ≤ 6 * Q ^ (-(1 / 2 - rho)) at hS
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ)
    linarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorMass -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorEulerExpansion ; sha256 14efb7182bf6695aecca20f88310a0f04137e590c4e6a2d8b7578155b3da2022 -/
section




/-! Absolutely convergent expansion of a product of local polynomials.  Indexing
by finite prime subsets and their degree choices retains an explicit positive
scale for every term; regrouping equal ideals is unnecessary for Mellin inversion.
-/
noncomputable section
open scoped BigOperators NNReal
namespace Cycle25.Weighted.Numerator

def EulerIndex (ι : Type*) (n : ℕ) := Σ s : Finset ι, (s → Fin n)

def eulerTerm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (e : EulerIndex ι n) : ℂ :=
  ∏ p : e.1, f p.val (e.2 p)

def localMass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (p : ι) : ℝ :=
  ∑ j, ‖f p j‖

theorem euler_fiber_mass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, ‖eulerTerm f ⟨s, j⟩‖) = ∏ p ∈ s, localMass f p := by
  classical
  simp only [tsum_fintype, eulerTerm, norm_prod, localMass]
  exact (Fintype.prod_sum (fun p : s => fun j : Fin n => ‖f p.val j‖)).symm.trans
    (Finset.prod_coe_sort s (fun p => ∑ j, ‖f p j‖))

/-- Absolute convergence is obtained from summable local coefficient masses. -/
theorem euler_expansion_summable_norm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) : Summable (fun e : EulerIndex ι n => ‖eulerTerm f e‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro s
    exact (hasSum_fintype _).summable
  · simpa only [euler_fiber_mass, localMass] using
      summable_finsetProd_of_summable_nonneg
        (fun p => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hf

theorem euler_fiber_sum {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, eulerTerm f ⟨s, j⟩) = ∏ p ∈ s, ∑ j, f p j := by
  classical
  simp only [tsum_fintype, eulerTerm]
  rw [← Fintype.prod_sum]
  exact Finset.prod_coe_sort s (fun p => ∑ j, f p j)

/-- Exact product expansion, with no change to the original local factors. -/
theorem euler_expansion_hasProd {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    HasProd (fun p => 1 + ∑ j, f p j) (∑' e : EulerIndex ι n, eulerTerm f e) := by
  have hs := (euler_expansion_summable_norm f hf).of_norm
  have hsum := hs.hasSum.sigma (fun s => (hs.sigma_factor s).hasSum)
  simp only [euler_fiber_sum] at hsum
  exact hasProd_one_add_of_hasSum_prod hsum

theorem euler_expansion_eq_tprod {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∏' p, (1 + ∑ j, f p j)) = ∑' e : EulerIndex ι n, eulerTerm f e :=
  (euler_expansion_hasProd f hf).tprod_eq

theorem euler_expansion_mass_le_exp {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∑' e : EulerIndex ι n, ‖eulerTerm f e‖) ≤ Real.exp (∑' p, localMass f p) := by
  classical
  have hnonneg (p : ι) : 0 ≤ localMass f p :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs := euler_expansion_summable_norm f hf
  change (∑' e : (Σ s : Finset ι, s → Fin n), ‖eulerTerm f e‖) ≤ _
  rw [hs.tsum_sigma]
  simp only [euler_fiber_mass]
  apply (summable_finsetProd_of_summable_nonneg hnonneg hf).tsum_le_of_sum_le
  intro T
  calc
    (∑ s ∈ T, ∏ p ∈ s, localMass f p) ≤
        ∑ s ∈ (T.biUnion id).powerset, ∏ p ∈ s, localMass f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hs)
      · intro s hs hst
        exact Finset.prod_nonneg (fun p _ => hnonneg p)
    _ = ∏ p ∈ T.biUnion id, (1 + localMass f p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p ∈ T.biUnion id, localMass f p) :=
      Real.prod_one_add_le_exp_sum _ hnonneg
    _ ≤ _ := Real.exp_le_exp.mpr (hf.sum_le_tsum _ (fun _ _ => hnonneg _))

def positiveCpowHom (w : ℂ) : ℝ≥0 →* ℂ where
  toFun q := (q : ℂ) ^ w
  map_one' := by simp
  map_mul' q r := by
    convert! Complex.mul_cpow_ofReal_nonneg q.property r.property w using 1
    simp only [NNReal.coe_mul, Complex.ofReal_mul]
    rfl

def eulerScale {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0) (e : EulerIndex ι n) : ℝ≥0 :=
  ∏ p : e.1, Q p.val ^ (e.2 p).val

def eulerCoefficient {ι : Type*} {n : ℕ} (c : ι → Fin n → ℂ)
    (e : EulerIndex ι n) : ℂ := ∏ p : e.1, c p.val (e.2 p)

def localMellinTerm {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (p : ι) (j : Fin n) : ℂ :=
  c p j * ((Q p : ℂ) ^ (-w)) ^ j.val

theorem eulerTerm_mellin {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (e : EulerIndex ι n) :
    eulerTerm (localMellinTerm Q c w) e =
      eulerCoefficient c e * (eulerScale Q e : ℂ) ^ (-w) := by
  classical
  unfold eulerTerm localMellinTerm eulerCoefficient eulerScale
  rw [Finset.prod_mul_distrib]
  congr 1
  have he := map_prod (positiveCpowHom (-w)) (fun p : e.1 => Q p.val ^ (e.2 p).val)
    Finset.univ
  simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at he
  exact he.symm

theorem eulerScale_one_le {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (e : EulerIndex ι n) : 1 ≤ eulerScale Q e := by
  apply Finset.one_le_prod
  intro p hp
  exact one_le_pow₀ (hQ p.val)

theorem euler_coefficient_weight_eq {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ) (e : EulerIndex ι n) :
    ‖eulerTerm (localMellinTerm Q c (sigma : ℂ)) e‖ =
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma) := by
  rw [eulerTerm_mellin, norm_mul]
  have hpos : 0 < (eulerScale Q e : ℝ) := by
    have h := eulerScale_one_le Q hQ e
    exact lt_of_lt_of_le zero_lt_one h
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Complex.ofReal_re]

theorem euler_coefficients_summable_weight {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ)
    (hf : Summable (localMass (localMellinTerm Q c (sigma : ℂ)))) :
    Summable (fun e : EulerIndex ι n =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) := by
  simpa only [euler_coefficient_weight_eq Q hQ c sigma] using
    euler_expansion_summable_norm (localMellinTerm Q c (sigma : ℂ)) hf

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorEulerExpansion -/
