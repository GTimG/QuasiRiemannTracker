/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B004
import Submissions.local44_20261013.Bundles.B008
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B010
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceReflection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceDeletionCapacity ; sha256 b93455388cf46c59dc4c8c64136dfff9ad629cbad536d6ebd8c0631815835d65 -/
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

local notation "O"=> HeckeFamily.O

lemma deleted_short_length (Z M:ℝ)(hZ:1< Z)(hM:0≤ M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤ comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤ comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

theorem deleted_reflection_excess {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤ w i)
    (Z M X₁ X₂ κ xi reflected:ℝ)(hZ:1< Z)(hM:0≤ M)
    (hX₁:0< X₁)(hX₂:0< X₂)(hκ:7/10≤κ)(hxi:0≤ xi)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    excess J w (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ≤
      xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=by
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hn₂p:0<((∏I∈D₂,I).absNorm:ℝ):=zero_lt_one.trans_le hn₂
  have hlog:0≤ Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=Real.logb_nonneg hZ hn₂
  have hell:0≤∑i∈F,w i:=Finset.sum_nonneg hw
  have hY₂:0< comparisonSecond Z M X₁ X₂:=by
    unfold comparisonSecond
    exact div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  rw [Real.logb_div hY₂.ne' hn₂p.ne'] at href
  have hb:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂)+
      (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)):=by linarith
  have hh:=(balanced_reflection_margins Z M X₁ X₂ (∑i∈F,w i) κ
    (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)) reflected hZ hM hX₁ hX₂ hell hκ hlarge hcap hb).2
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hsum:(∑i∈J,w i)≤∑i∈F,w i:=
    Finset.sum_le_sum_of_subset_of_nonneg hJF (fun i hi _=> hw i hi)
  have hks:=mul_le_mul_of_nonneg_left hsum (by linarith:0≤6*κ)
  unfold excess
  apply max_le _ (add_nonneg hxi hlog)
  nlinarith

theorem deleted_reflection_removal {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤ w i)
    (Z M X₁ X₂ κ xi reflected mesh:ℝ)(hZ:1< Z)(hM:0≤ M)
    (hX₁:0< X₁)(hX₂:0< X₂)(hκ:7/10≤κ)(hxi:0≤ xi)(hm:0≤ mesh)(hwm:∀i∈J,w i≤ mesh)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    ∃removed:Finset α,removed⊆J ∧
      (removed=J ∨ length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+reflected+
        6*κ*(∑i∈J\removed,w i)≤ M) ∧
      κ*(∑i∈removed,w i)≤ xi/6+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)/6+κ*mesh:=by
  obtain ⟨removed,hr,hcapacity,hcost⟩:=removal_excess_cost J w
    (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ mesh
    (by linarith) hm (fun i hi=> hw i (hJF hi)) hwm
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
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceDeletionCapacity -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceDivisors ; sha256 92aa526bae2378a1391371dff4458b74fa78382f1b5dd33e5ddd833be134bd92 -/
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
local notation "O"=> HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤ Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1< Z)(hY:0< Y)(hN:0< N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L Y:ℝ)(hwidth:s.width≤ L)(hY:1≤ Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤ a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:7/10≤κ)
    (hlarge:5*s.width/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤ short ∧ -Bmask≤ long ∧ s.width≤(L+Bmask)+long ∧
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
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceDivisors -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.FullWFiniteError ; sha256 389dd51824b86240e2fc640fa840a924038d7e304727898a3b7aa675e8563585 -/
section




/-! Summable physical row/tuple errors for the full-w transport at the new
lengths, with arbitrary power savings chosen after the height exponent. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma fullW_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^lx)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^ly)^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num [lx,ly] at *; nlinarith)

lemma fullW_prime_product_bound {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^ell := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma fullW_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*ell) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show h+ζ≤1 by norm_num [h] at *;linarith))
  have hp := fullW_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(ell*(3:ℕ))=Z^(6+3*ell) := by rw [←Real.rpow_add hZ0];congr 1;push_cast;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


lemma fullW_prime_tuple_count {K : ℕ} (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^ell := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


theorem original_row_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(h+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=ell →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^lx) (Z^ly) Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 (Z^lx) (Z^ly) Z a e H (1/2)‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*ell)+saving)/τ)
  have hN' : (8+3*ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^lx) (Z^ly) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := fullW_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := fullW_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*ell)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*ell)/height H^N) := by
      have hh : Z^(6+3*ell)*Z^(2:ℝ)=Z^(8+3*ell) := by rw [←Real.rpow_add hZ0];congr 1;push_cast;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


def finiteCentralFullWRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralFullWIntegral S hS hmax (fun i=>(P i).val) (fun i=> hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u) (1/2)

theorem finite_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(h+ζ)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^lx) (Z^ly) Z-
        finiteCentralFullWRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^lx) (Z^ly) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_fullW_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(h+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show h+ζ≤1 by norm_num [h] at *;linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (fullW_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show ell≤1 by norm_num [ell])) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^lx) (Z^ly) Z u-
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^lx) (Z^ly) Z (a u) e (H u) (1/2)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=> hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=> hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) (fun j _=> hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralFullWRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^lx) (Z^ly) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^lx) (Z^ly) Z (a u) e (H u) (1/2)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]


end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.FullWFiniteError -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorRamifiedMass ; sha256 d1d111256fa463d844ddc5abbb886703296f9e8b614410064e7442705bc7f530 -/
section



/-! Actual coefficient bounds for ramified local errors.  The certified original
regular-error estimate is uniform on a vertical line.  Exact finite-degree
extraction turns that estimate into the coefficient bound needed before the
physical numerator is reconstructed. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

structure QuadraticCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ

def QuadraticCoefficients.eval (c : QuadraticCoefficients) (T : ℂ) : ℂ :=
  quadratic c.a c.b c.c T
def QuadraticCoefficients.mass (c : QuadraticCoefficients) (r : ℝ) : ℝ :=
  quadraticMass c.a c.b c.c r

def ramifiedRegularCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let X := Q ^ (-x)
  let B := star eta * Q ^ x
  let P₀ := rowClosedMarked p hp hg eta a X 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a X 1 V rho j - P₀
  let S := B * (1 - V) *
    (rowMarkedTerm p hp hg eta a X 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a X V))
  ⟨B * (1 - V) * P₀,
    B * (1 - V) * P₁ - 1 - (1 - V) * P₀ - S,
    -(1 - V) * P₁⟩

theorem ramified_regular_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j -
      ramifiedStrictSelected p hp hg eta a rho x w z j =
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).eval
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hP := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  have hT := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedSelected ramifiedStrictSelected ramifiedClosed
  rw [hP, hT]
  simp only [pow_one]
  unfold QuadraticCoefficients.eval ramifiedRegularCoefficients quadratic
  ring

/-- No analytic estimate is assumed here: this coefficient mass follows from the
original regular-error theorem, applied on the complete old vertical line. -/
theorem ramified_regular_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (alpha eps sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) (j : ℕ) (hj : j < 6) :
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤
      1155 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) := by
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) (1 - alpha - 6 * eps) sigma
    (385 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ))
    c.a c.b c.c (by linarith) hsigma (by
      intro w hw
      have hh := ramifiedSelected_central_regular p hp hg hc eta a rho x w z
        alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j hj
      rw [ramified_regular_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

def ramifiedStrictCoefficient (eta a rho x z : ℂ) (j : ℕ) : ℂ :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  star eta * Q ^ x * (1 - V) *
    (rowMarkedTerm p hp hg eta a (Q ^ (-x)) 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a (Q ^ (-x)) V))

theorem ramified_strict_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedStrictSelected p hp hg eta a rho x w z j =
      ramifiedStrictCoefficient p hp hg eta a rho x z j *
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w) := by
  have ht := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedStrictSelected ramifiedStrictCoefficient
  rw [ht]
  simp only [pow_one]
  ring

/-- The only large coefficient is the original strict ramified coefficient. -/
theorem ramified_strict_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j < 6) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 - sigma) := by
  have hh := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

theorem ramified_boundary_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j ≤ 1) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) := by
  have hh := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

def ramifiedCorrectionCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let P₀ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 1 V rho j - P₀
  ⟨1 + (1 - V) * P₀, (1 - V) * P₁, 0⟩

theorem ramified_correction_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedClosed p hp hg eta a rho x w z j =
      (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hh := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  unfold ramifiedClosed
  rw [hh]
  unfold ramifiedCorrectionCoefficients QuadraticCoefficients.eval quadratic
  ring

theorem ramified_correction_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma)
    (j : ℕ) (hj : j < 6) :
    (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤ 579 := by
  let c := ramifiedCorrectionCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) sigma sigma 193 c.a c.b c.c
    (by linarith) le_rfl (by
      intro w hw
      have hh := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z
        hQ heta ha hρ hx (by rw [hw]; exact hsigma) hz (by rw [hw]; exact hxw) j hj
      rw [ramified_correction_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  norm_num only [show (3 : ℝ) * 193 = 579 by norm_num] at hb
  exact hb

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorRamifiedMass -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorReflectionData ; sha256 719141f1c86207748efa35949eb854274052264308ef34b44f0aa06ac63bd4b0 -/
section





/-! A fixed reflection presentation for each actual physical row. The same
combined conductor is used both in coefficient damping and in reflection. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

structure PhysicalReflectionData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) where
  presentation : Character
  primitive : Character
  phase : ℂ
  element_eq : ∀n:O,elementCoeff (rowCharacter S hS u) n=elementCoeff presentation n
  inverse_eq : ∀J:Ideal O,idealCoeff (rowCharacter S hS u).inverse J=idealCoeff presentation.inverse J
  phase_norm : ‖phase‖=1
  conductor_bound : primitive.modulus.absNorm*(redundantIdeal presentation.modulus primitive.modulus).absNorm≤
    fixedConductorConstant S*(Ideal.span {u.val}:Ideal O).radical.absNorm
  split : ∀(G:𝓢(ℝ,ℂ))(X R:ℝ),0< X→
    HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0=
      phase*(retainedSchwartz presentation primitive G X R+discardedSchwartz presentation primitive G X R)

theorem physical_reflection_data_exists (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue≠1) : Nonempty (PhysicalReflectionData S hS u) := by
  obtain ⟨τ,ψ,g,he,hi,hnτ,hp,hnp,hg,hτ,hcap,hdef,hsplit⟩ := RowConductor.row_original_split S hS u hn
  exact ⟨⟨τ,ψ,g,he,hi,hg,hcap.trans hτ,hsplit⟩⟩

namespace PhysicalReflectionData
variable {S : Finset (Ideal O)} {hS : ∀P∈S,Prime P} {u : FreeRow}

def combinedConductor (D : PhysicalReflectionData S hS u) : ℝ :=
  (D.primitive.modulus.absNorm:ℝ)*(redundantIdeal D.presentation.modulus D.primitive.modulus).absNorm

theorem combined_pos (D : PhysicalReflectionData S hS u) : 0< D.combinedConductor :=
  RowConductor.reflected_scale_pos D.presentation D.primitive

theorem combined_le_radical (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).radical.absNorm := by
  unfold combinedConductor
  exact_mod_cast D.conductor_bound

theorem radical_le_row (u : FreeRow) :
    (Ideal.span {u.val}:Ideal O).radical.absNorm≤(Ideal.span {u.val}:Ideal O).absNorm := by
  letI : Finite (O ⧸ (Ideal.span {u.val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
  exact FiniteConductor.absNorm_le_of_le (show (Ideal.span {u.val}:Ideal O)≤(Ideal.span {u.val}:Ideal O).radical from Ideal.le_radical)

theorem combined_le_row (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*rowNorm u := by
  exact D.combined_le_radical.trans (mul_le_mul_of_nonneg_left
    (by unfold rowNorm;exact_mod_cast radical_le_row u) (Nat.cast_nonneg _))

theorem redundant_le_combined (D : PhysicalReflectionData S hS u) :
    (Ideal.absNorm (∏P∈sourcePrimes D.presentation D.primitive,P):ℝ)≤ D.combinedConductor := by
  have hp : (1:ℝ)≤ D.primitive.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr D.primitive.modulus_ne_bot)
  exact le_mul_of_one_le_left (by positivity) hp

end PhysicalReflectionData

/-- A coefficient dilation bound gives the exact reflected length without
charging the redundant primes or repeated-prime conductor deficit twice. -/
theorem combined_scale_of_dilation (Cu Ccond Nu N Y U y v : ℝ)
    (hC : 0< Ccond) (hNu : 0< Nu) (hN : 0< N) (hU : 0< U)
    (hNuU : Nu≤ U) (hY : Y=U^y)
    (hdilation : max 1 (Cu*N/(Ccond*Nu))≤ U^v) :
    Cu≤ Ccond*U^(1-y+v)*(Y/N) := by
  have hd := (le_max_right 1 (Cu*N/(Ccond*Nu))).trans hdilation
  have hm : Cu*N≤ U^v*(Ccond*Nu) := (div_le_iff₀ (mul_pos hC hNu)).mp hd
  have hmul : Cu*N≤ Ccond*U^(1+v) := by
    calc
      _ ≤ U^v*(Ccond*Nu) := hm
      _ ≤ U^v*(Ccond*U) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNuU hC.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one];ring
  rw [hY,←mul_div_assoc,le_div_iff₀ hN]
  apply hmul.trans_eq
  rw [mul_assoc,←Real.rpow_add hU]
  congr 2
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorReflectionData -/

/- BEGIN ORIGINAL MODULE Global.Transport.SourceAmplitudeClasses ; sha256 14e27e3ad2ab19799ee76a7825f366f0d3271ab35d71b39eaa9c2198155ea65d -/
section




/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := Cycle25WeightedHighRowFamily.actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.SourceAmplitudeClasses -/
