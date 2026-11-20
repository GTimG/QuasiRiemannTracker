/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentTerm_f0f64eca2558203e_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

open CenteredMomentSourceLiveColumn CenteredMomentCommonRawCost

open CenteredMomentDivisorAllocation MixedCommonCoefficient

def fixedMarkCost (r:Source ι a b) : ℝ :=
  (∏i:ι,2*(r.M i)^2)^2*(∏i:ι,(256*r.M i)^2)

lemma fixedMarkCost_nonneg (r:Source ι a b) : 0≤fixedMarkCost r:=by
  unfold fixedMarkCost
  exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun _ _=>sq_nonneg _))

/-- Actual native B/E/aL summand under the original full normalization. -/
theorem native_term_square (ha:0<a) (hb:0≤b) (ω₁ ω₂:Character)
    (ε Bcap:ℝ) (hε:0<ε) (hB:0≤Bcap) :
    ∃ J:ℕ,∃ S:Finset (ℕ×ℕ),∃ hS:(0,0)∈S,
    ∀ Q:Id,∃ C:ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
    ∀ (r:Source ι a b) (D:FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ)≤U^Bcap →
    ∀ (G L:Id),G≠0 → Squarefree L → ∀ (B:commonAlloc r G) (E:fullPrimaryAlloc r G B L),
      (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
        (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ)≤U^Bcap →
    ∀ (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2))) (v:ℝ),
    ‖nativePhysicalTerm r ha hb D ω₁ ω₂ G L B aL E v‖^2 ≤
      fixedMarkCost r*(C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*
        (1+‖r.t₁+v‖+‖r.t₂+v‖)^J)^2*(r.T*(∏i:ι,r.P i))*
        ((((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm)*max 1 r.L)⁻¹:=by
  obtain ⟨J,S,hS,h⟩:=primary_physical_square (ι:=ι) ha hb ω₁ ω₂ ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩:=h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with U hu
  intro r D hQ hcond G L hG hL B E hbudget aL v
  by_cases hactive:allocationTerm L Finset.univ E.val aL=0
  · unfold nativePhysicalTerm TwistedRawSource.primaryCanonicalScalar
    simp only [hactive,mul_zero,zero_mul,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (fixedMarkCost_nonneg r) (sq_nonneg _))
        (mul_nonneg r.total_pos.le (Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hP i)))))
      (by positivity)
  · exact (native_term_norm_le_original r ha hb D ω₁ ω₂ G L B aL E v).trans
      (original_primary_payment r G L hG hL B E aL hactive v _ _
        (hu r D hQ hcond G L hG hL.ne_zero B E hbudget v))

/-- Five ordinary numerical caps produce the literal native label budget. -/
theorem physical_input_budget (r:Source ι a b) (G L:Id) (B:commonAlloc r G)
    (E:fullPrimaryAlloc r G B L) (U bcap:ℝ) (hU:0<U)
    (hF:(r.Fhole.absNorm:ℝ)≤U^bcap)
    (hP:(∏i:liveIndices E.val,2*r.P i.val.val)≤U^bcap)
    (hR:(r.R.absNorm:ℝ)≤U^bcap) (hG:(G.absNorm:ℝ)≤U^bcap)
    (hL:(L.absNorm:ℝ)≤U^bcap) :
    (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
      (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ)≤U^(5*bcap):=by
  have hp0:0≤∏i:liveIndices E.val,2*r.P i.val.val:=Finset.prod_nonneg
    (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (r.hP i.val.val)))
  calc
    _ ≤ U^bcap*U^bcap*U^bcap*U^bcap*U^bcap:=by gcongr
    _ = U^(bcap+bcap+bcap+bcap+bcap):=by
      rw [Real.rpow_add hU,Real.rpow_add hU,Real.rpow_add hU,Real.rpow_add hU]
    _ = _:=by congr 1;ring

#print axioms native_term_square
#print axioms physical_input_budget
end
end QRH.Cycle092.FixedCubeGauss
