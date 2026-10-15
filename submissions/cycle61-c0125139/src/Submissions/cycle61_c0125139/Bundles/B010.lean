/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B009
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceReflection

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceDivisors; sha256 92aa526bae2378a1391371dff4458b74fa78382f1b5dd33e5ddd833be134bd92 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceDivisors.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                             

                                    

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceDivisors
open HeckeFamily CenteredMomentEnergyState Cycle25CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1<Z)(hY:0<Y)(hN:0<N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L Y:ℝ)(hwidth:s.width≤L)(hY:1≤Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤short ∧ -Bmask≤long ∧ s.width≤(L+Bmask)+long ∧
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^long=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hfirst:Real.logb Z (comparisonFirst Z s.width)=s.width/4:=by
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hs:=divisor_reflection_range s hZ L (comparisonFirst Z s.width) hwidth hg.2.1 D₁ hD₁
  have hl:=divisor_reflection_range s hZ L (comparisonSecond Z s.width X₁ X₂) hwidth
    (hg.2.1.trans hg.2.2.1) D₂ hD₂
  dsimp only at hs hl ⊢
  rw [hfirst] at hs
  rw [hg.2.2.2.1] at hl
  exact ⟨hs.1,hl.1,hl.2.1,hs.2.2,hl.2.2⟩

end SevenEighths.Cycle25CenteredMomentEnergyReferenceDivisors

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceDivisors -/

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceDeletionCapacity; sha256 b93455388cf46c59dc4c8c64136dfff9ad629cbad536d6ebd8c0631815835d65 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceDeletionCapacity.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                                 
                                    
                                               

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionCapacity
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentLiveCapacity

local notation "O"=>HeckeFamily.O

lemma deleted_short_length (Z M:ℝ)(hZ:1<Z)(hM:0≤M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

theorem deleted_reflection_excess {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:7/10≤κ)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    excess J w (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ≤
      xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=by
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hn₂p:0<((∏I∈D₂,I).absNorm:ℝ):=zero_lt_one.trans_le hn₂
  have hlog:0≤Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=Real.logb_nonneg hZ hn₂
  have hell:0≤∑i∈F,w i:=Finset.sum_nonneg hw
  have hY₂:0<comparisonSecond Z M X₁ X₂:=by
    unfold comparisonSecond
    exact div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  rw [Real.logb_div hY₂.ne' hn₂p.ne'] at href
  have hb:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+
      (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)):=by linarith
  have hh:=(balanced_reflection_margins Z M X₁ X₂ (∑i∈F,w i) κ
    (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)) reflected hZ hM hX₁ hX₂ hell hκ hlarge hcap hb).2
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hsum:(∑i∈J,w i)≤∑i∈F,w i:=
    Finset.sum_le_sum_of_subset_of_nonneg hJF (fun i hi _=>hw i hi)
  have hks:=mul_le_mul_of_nonneg_left hsum (by linarith:0≤6*κ)
  unfold excess
  apply max_le _ (add_nonneg hxi hlog)
  nlinarith

theorem deleted_reflection_removal {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected mesh:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:7/10≤κ)(hxi:0≤xi)(hm:0≤mesh)(hwm:∀i∈J,w i≤mesh)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    ∃removed:Finset α,removed⊆J ∧
      (removed=J ∨ length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+reflected+
        6*κ*(∑i∈J\removed,w i)≤M) ∧
      κ*(∑i∈removed,w i)≤xi/6+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)/6+κ*mesh:=by
  obtain ⟨removed,hr,hcapacity,hcost⟩:=removal_excess_cost J w
    (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ mesh
    (by linarith) hm (fun i hi=>hw i (hJF hi)) hwm
  refine ⟨removed,hr,hcapacity,?_⟩
  have he:=deleted_reflection_excess F J hJF w hw Z M X₁ X₂ κ xi reflected
    hZ hM hX₁ hX₂ hκ hxi hlarge hcap D₁ D₂ hD₁ hD₂ href
  linarith

lemma paid_divisor_power (Z cost xi kappa mesh : ℝ) (hZ : 1 < Z)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (hcost : cost ≤ xi/6 + Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6 + kappa*mesh) :
    Z^cost ≤ Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < ((∏ I ∈ D, I).absNorm:ℝ) :=
    zero_lt_one.trans_le (product_norm_ge_one D hD)
  calc
    Z^cost ≤ Z^((xi/6+kappa*mesh)+Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
      rw [Real.rpow_add hZp]
      congr 1
      rw [div_eq_mul_inv, Real.rpow_mul hZp.le,
        Real.rpow_logb hZp hZ.ne' hn]
      norm_num

end SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionCapacity

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceDeletionCapacity -/

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceDeletionClipped; sha256 64b2763eddd095b0e5a6d8da7e25a5596f0ac3813e28e0b7e3e1b3bb9664e8ad -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceDeletionClipped.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                               

                                    

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily Cycle25CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceDeletionClipped -/

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceLowBranchGeometry; sha256 08b2701d6d2ac12224f669ae906eccfc5d693f2e42a5f0127ab1be08e23ff569 -/
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
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:7/10≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤5*M/96 ∧ (6*kappa-1)*ell≤M/6:=by
  have hkell:16/5*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:7/10≤kappa)(he:ell≤5*M/96)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤37*M/48+xi ∧
      reflected+short+6*kappa*z≤15*M/16+xi:=by
  have haz:0<along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤5*M/96:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:7/10≤kappa)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤M) ∨
    (0<Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
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
    have hY:1≤comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
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
    (hxi:xi≤M/16)(ht:reflected+short+z≤37*M/48+xi)
    (hc:reflected+short+6*kappa*z≤15*M/16+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  constructor <;> linarith

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceLowBranchGeometry -/
