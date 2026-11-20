/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentLabels

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
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentH8_5edf64e31cb9bfaa_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

/-- Absolute summation charges only the actual frozen scalar mass. -/
theorem weighted_square_sum {κ : Type*} [Fintype κ] (w f : κ→ℂ) (K : ℝ)
    (hK : 0≤K) (hf : ∀i,‖f i‖^2 ≤ K) :
    ‖∑i,w i*f i‖^2 ≤ (∑i,‖w i‖)^2*K := by
  have h (i:κ) : ‖f i‖ ≤ Real.sqrt K:=by
    have hh:=hf i
    nlinarith [Real.sq_sqrt hK,Real.sqrt_nonneg K,norm_nonneg (f i)]
  have hn : ‖∑i,w i*f i‖ ≤ (∑i,‖w i‖)*Real.sqrt K:=by
    calc
      _ ≤ ∑i,‖w i*f i‖:=norm_sum_le _ _
      _ ≤ ∑i,‖w i‖*Real.sqrt K:=Finset.sum_le_sum (fun i _=>by
        rw [norm_mul];exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
      _ = _:= (Finset.sum_mul ..).symm
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by
    rw [mul_pow,Real.sq_sqrt hK])

/-- The genuine physical signed source has its two exterior phases removed
separately, at the true ordinary rectangle T/qOrd. -/
theorem physical_pair_square (ha : 0<a) (hb : 0≤b) (ω₁ ω₂ : Character)
    (ε Bcap : ℝ) (hε : 0<ε) (hB : 0≤Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
    ∀ (r:Source ι a b) (D:FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) ≤ U^Bcap →
    ∀ (M K : Id),
      ((∏P∈residualSuppliers M∪residualHoles K,P.val).absNorm:ℝ) ≤ U^Bcap →
    ∀ (d:Id×Id),d.1≠0 → d.2≠0 → ∀v:ℝ,
    let qOrd:ℝ:=(d.1.absNorm:ℝ)*d.2.absNorm
    let labels:=residualSuppliers M∪residualHoles K
    let allowed:=supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row
      (residualSuppliers M) (residualHoles K) (residualHoles K)
    ‖(Real.sqrt r.T:ℂ)⁻¹*(
      fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂)
        (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
        (fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) labels) allowed
        (r.X₁/(d.1.absNorm:ℝ)) (r.X₂/(d.2.absNorm:ℝ))-
      fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂)
        (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
        (fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) labels) allowed
        (r.Y₁/(d.1.absNorm:ℝ)) (r.Y₂/(d.2.absNorm:ℝ)))‖^2 ≤
      (C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*
        (1+‖r.t₁+v‖+‖r.t₂+v‖)^J)^2*r.T*(qOrd*max 1 r.L)⁻¹ := by
  obtain ⟨J,S,hS,h⟩:=FixedAllocationWeight.fixed_independent_profiles_square
    a b ha hb ω₁ ω₂ ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩:=h Q Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with U hu
  intro r D hQ hcond M K hlabels d hd₁ hd₂ v
  let p:Profiles a b:=⟨fun j=>if j=0 then r.W₁ else r.W₂,fun j=>by
    split_ifs <;> first | exact r.hs₁ | exact r.hs₂⟩
  have hn (I:Id) (hI:I≠0) : 1≤(I.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hn₁:=hn d.1 hd₁
  have hn₂:=hn d.2 hd₂
  have hn₁p:=zero_lt_one.trans_le hn₁
  have hn₂p:=zero_lt_one.trans_le hn₂
  have hq : 1≤(d.1.absNorm:ℝ)*d.2.absNorm:=one_le_mul_of_one_le_of_one_le hn₁ hn₂
  have hlen₁ : r.L/((d.1.absNorm:ℝ)*d.2.absNorm) ≤ r.L/(d.1.absNorm:ℝ):=
    div_le_div_of_nonneg_left r.hL.le hn₁p (le_mul_of_one_le_right hn₁p.le hn₂)
  have hlen₂ : r.L/((d.1.absNorm:ℝ)*d.2.absNorm) ≤ r.L/(d.2.absNorm:ℝ):=
    div_le_div_of_nonneg_left r.hL.le hn₂p (le_mul_of_one_le_left hn₂p.le hn₁)
  have hh:=hu p D D hQ hQ (residualSuppliers M∪residualHoles K)
    (residualSuppliers M) (residualHoles K) (residualHoles K)
    (supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row
      (residualSuppliers M) (residualHoles K) (residualHoles K))
    (by intro P hP; simpa only [Finset.mem_union,or_assoc,or_self] using hP)
    (fun _ _=>Finset.Subset.refl _) hcond hcond hlabels
    (r.t₁+v) (r.t₂+v) (r.X₁/(d.1.absNorm:ℝ)) (r.X₂/(d.2.absNorm:ℝ))
    (r.Y₁/(d.1.absNorm:ℝ)) (r.Y₂/(d.2.absNorm:ℝ)) r.T r.L
    ((d.1.absNorm:ℝ)*d.2.absNorm) ((d.1.absNorm:ℝ)*d.2.absNorm) r.total_pos r.hL hq le_rfl
    (hlen₁.trans (div_le_div_of_nonneg_right r.hX₁ hn₁p.le))
    (hlen₂.trans (div_le_div_of_nonneg_right r.hX₂ hn₂p.le))
    (hlen₁.trans (div_le_div_of_nonneg_right r.hY₁ hn₁p.le))
    (hlen₂.trans (div_le_div_of_nonneg_right r.hY₂ hn₂p.le))
    (physical_shortened_products r d).1 (physical_shortened_products r d).2
  dsimp only at hh ⊢
  rw [fixedCubeRawSource_signed_normalized _ _ _ _ _ _ _ _ _ _
    (div_pos (r.hL.trans_le r.hX₁) hn₁p) (div_pos (r.hL.trans_le r.hX₂) hn₂p)
    (div_pos (r.hL.trans_le r.hY₁) hn₁p) (div_pos (r.hL.trans_le r.hY₂) hn₂p)] at hh
  simpa only [p,Profiles.control,ite_true,show (1:Fin 2)≠0 from by decide,ite_false, fixedCubePhysicalSource, actualProfile₁, actualProfile₂, actualOrdinaryProfile,
    h8Profile, OrdinaryProfile.atHeight, OrdinaryProfile.normalized] using hh

#print axioms physical_pair_square
#print axioms weighted_square_sum
end
end QRH.Cycle092.FixedCubeGauss
