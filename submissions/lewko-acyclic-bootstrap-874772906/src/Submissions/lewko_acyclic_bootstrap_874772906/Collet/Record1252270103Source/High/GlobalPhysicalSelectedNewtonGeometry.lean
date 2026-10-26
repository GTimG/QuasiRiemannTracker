/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The same actual selected allocations supply every finite Newton geometry
field. The first common ideal is kept in the puncture, not the correction. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedAllocatedNormCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Pool.FixedCell
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst
open Cycle61InitialMass Cycle61Moment OAI.SevenEighths.Record1252270103Source Record1252270103Second
open Admission.SelectedHighCofactorFamily Admission.SelectedLowDictionary Pool
local notation "O"=>HeckeFamily.O
local instance selectedNewtonGeometryDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem actual_selected_newton_geometry {α:Type}[Fintype α]
    (s:Input α)(reflected second:Bool)(l:FirstSourceLabel)(C₂ D₂ R:Ideal O)
    (sel:Selection s reflected second l C₂ D₂ R)
    (W₁ W₂:𝓢(ℝ,ℂ))(b Z Bfirst Bsecond BL Bplain amp ell mesh loss Bsource:ℝ)
    (depth:ℕ)(P:Finset (Ideal O))(L:Ideal O)
    (hR:R≠0)(hL:Squarefree L)(hCf:sel.Cf∣L^2)
    (hfirst:((if reflected then l.1.2 else l.1.1).absNorm:ℝ)≤Z^Bfirst)
    (hsecond:((if second then D₂ else C₂).absNorm:ℝ)≤Z^Bsecond)
    (hLcap:(L.absNorm:ℝ)≤Z^BL)
    (hW₁:s.W₁=(W₁:ℝ→ℂ))(hW₂:s.W₂=(W₂:ℝ→ℂ))
    (hb₁:s.b₁≤b)(hb₂:s.b₂≤b)(hb:0≤b)(hell:0<ell)
    (hpool:FixedCellPoolData P Z amp ell mesh loss (Bsecond+2*BL) Bsource depth)
    (havoid:∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (hdepth:Bplain/ell≤depth)(hplain:b^2*(s.X₁*s.X₂)≤Z^Bplain):
    CorrectedSourceGeometry sel.finalInput W₁ W₂ b Z (Bfirst+Bsecond+2*BL) amp depth
      (Selection.frozenLeft sel) (Selection.frozenRight sel) (Selection.correction sel)
      (Selection.marked sel) (Selection.puncture sel) P := by
  let C₁:=if reflected then l.1.2 else l.1.1
  let C:=if second then D₂ else C₂
  have hZ:1<Z:=hpool.scale_gt_one
  have hz:=zero_lt_one.trans hZ
  have hC₁:C₁≠0:=allocation_ne s C₁ sel.B₁
  have hC:C≠0:=allocation_ne sel.firstInput C sel.B₂
  have hCfn:sel.Cf≠0:=allocation_ne _ _ sel.Bf
  have hCfCap:(sel.Cf.absNorm:ℝ)≤Z^(2*BL):=by
    apply (corrected_norm_mono_of_dvd sel.Cf (L^2) (pow_ne_zero 2 hL.ne_zero) hCf).trans
    rw [map_pow,Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hLcap 2).trans_eq
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  have hp₁:sel.B₁.val (Sum.inr 0)*sel.B₁.val (Sum.inr 1)∣C₁:=by
    simpa only [allocation_product s C₁ sel.B₁] using plain_product_dvd_tuple sel.B₁.val
  have hp₂:sel.B₂.val (Sum.inr 0)*sel.B₂.val (Sum.inr 1)∣C:=by
    simpa only [allocation_product sel.firstInput C sel.B₂] using plain_product_dvd_tuple sel.B₂.val
  have hpf:sel.Bf.val (Sum.inr 0)*sel.Bf.val (Sum.inr 1)∣sel.Cf:=by
    simpa only [allocation_product _ _ sel.Bf] using plain_product_dvd_tuple sel.Bf.val
  have hprod:Selection.frozenLeft sel*Selection.frozenRight sel∣(C₁*C)*sel.Cf:=by
    have he:Selection.frozenLeft sel*Selection.frozenRight sel=
        ((sel.B₁.val (Sum.inr 0)*sel.B₁.val (Sum.inr 1))*
          (sel.B₂.val (Sum.inr 0)*sel.B₂.val (Sum.inr 1)))*
          (sel.Bf.val (Sum.inr 0)*sel.Bf.val (Sum.inr 1)):=by
      dsimp only [Selection.frozenLeft,Selection.frozenRight]
      ring
    rw [he]
    exact mul_dvd_mul (mul_dvd_mul hp₁ hp₂) hpf
  have hnorm:((Selection.frozenLeft sel*Selection.frozenRight sel).absNorm:ℝ)≤
      Z^(Bfirst+Bsecond+2*BL):=
    (corrected_norm_mono_of_dvd _ _ (mul_ne_zero (mul_ne_zero hC₁ hC) hCfn) hprod).trans
      (corrected_norm_mul_cap _ _ Z (Bfirst+Bsecond) (2*BL) hz
        (corrected_norm_mul_cap _ _ Z Bfirst Bsecond hz hfirst hsecond) hCfCap)
  have hcorrection:Selection.correction sel∣Selection.puncture sel:=by
    refine ⟨R*C₁,?_⟩
    dsimp only [Selection.correction,Selection.puncture,C,C₁]
    ring
  have hDcap:((Selection.correction sel).absNorm:ℝ)≤Z^(Bsecond+2*BL):=by
    simpa only [Selection.correction,one_mul] using
      corrected_norm_mul_cap C sel.Cf Z Bsecond (2*BL) hz hsecond hCfCap
  have hg:=actual_frozen_ideal_gates sel hR
  have hraw:=sel.raw_caps s.X₁ s.X₂ s.Y₁ s.Y₂ le_rfl le_rfl le_rfl le_rfl
  have hplain':b^2*(sel.finalInput.X₁*sel.finalInput.X₂)≤Z^Bplain:=
    (mul_le_mul_of_nonneg_left (mul_le_mul hraw.1 hraw.2.1 sel.finalInput.X₂_pos.le s.X₁_pos.le)
      (sq_nonneg b)).trans hplain
  apply corrected_source_geometry_of_caps sel.finalInput W₁ W₂ b Z (Bfirst+Bsecond+2*BL)
    amp Bplain (Bsecond+2*BL) ell depth _ _ _ _ _ P
    hW₁ hW₂ hb₁ hb₂ hb hZ hell hg.2.2.1 hg.1 hg.2.1 hcorrection hnorm hDcap
    (Finset.card_pos.mpr hpool.nonempty) hpool.prime _ hpool.norm_lower hpool.norm_upper _
    hpool.card_newton hdepth hplain'
  · intro p hp
    exact_mod_cast hpool.norm_ge_sixteen p hp
  · intro p hp i I hI
    exact havoid p hp i.val.val.val I hI

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_selected_newton_geometry
