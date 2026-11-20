/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedLiveMarkMass
import Candidate.C092.transport.FixedCubeGaussPhysicalScales
import Candidate.C092.transport.FixedMarkedPay
import Candidate.C092.transport.H8ProfileUniform

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
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentLabels_eede368ef17e9d96_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

/-- The seed puncture uses the original intersection S∩H and divides the
actual source hole ideal, regardless of the size of the full seed set S. -/
theorem puncture_dvd_hole (r : Source ι a b) : punctureProduct r.S r.H ∣ r.Fhole := by
  unfold punctureProduct
  apply Finset.prod_dvd_of_coprime
  · intro P _ Q _ hPQ
    exact ProbePhysical.primeIdeal_coprime P Q hPQ
  · intro P hP
    exact r.hH P (Finset.mem_filter.mp hP).2

theorem puncture_ne (r : Source ι a b) : punctureProduct r.S r.H≠0:=
  Finset.prod_ne_zero_iff.mpr (fun P _=>P.property.ne_zero)

/-- The literal supplier/holes union has radical product dividing the actual
puncture. Suppliers are already divisors of its surviving marked product. -/
theorem residual_label_product_dvd (M K : Id) (hM : M≠0) (hK : K≠0) (hMK : M∣K) :
    (∏P∈residualSuppliers M∪residualHoles K,P.val) ∣ K := by
  have hs : residualSuppliers M ⊆ residualHoles K:=by
    intro P hP
    exact prime_dvd_mem_support K hK P
      (((prime_dvd_iff_positive M hM P).mpr
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP))).trans hMK)
  rw [Finset.union_eq_right.mpr hs]
  exact primeSupport_product_dvd K hK

/-- Native polynomial label budget: no cap on the full original seed product
is assumed. Only Fhole, surviving mark annuli, R,G,L enter. -/
theorem actual_label_norm_cap (r : Source ι a b) (G L M : Id)
    (hG : G≠0) (hL : L≠0) (hM : M≠0) :
    ((∏P∈residualSuppliers M∪residualHoles ((punctureProduct r.S r.H*M)*((r.R*G)*L)),P.val).absNorm:ℝ) ≤
      (r.Fhole.absNorm:ℝ)*(M.absNorm:ℝ)*(r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ) := by
  let K:Id:=(punctureProduct r.S r.H*M)*((r.R*G)*L)
  have hK : K≠0:=mul_ne_zero (mul_ne_zero (puncture_ne r) hM) (mul_ne_zero (mul_ne_zero r.hR hG) hL)
  have hd:=residual_label_product_dvd M K hM hK ⟨punctureProduct r.S r.H*((r.R*G)*L),by ring⟩
  have hd':K∣r.Fhole*M*((r.R*G)*L):=mul_dvd_mul_right
    (mul_dvd_mul_right (puncture_dvd_hole r) M) _
  have hn:=Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (mul_ne_zero (mul_ne_zero r.hFhole hM) (mul_ne_zero (mul_ne_zero r.hR hG) hL))))
    (map_dvd Ideal.absNorm (hd.trans hd'))
  have hr : ((∏P∈residualSuppliers M∪residualHoles K,P.val).absNorm:ℝ) ≤
      ((r.Fhole*M*((r.R*G)*L)).absNorm:ℝ):=by exact_mod_cast hn
  simpa only [K,map_mul,Nat.cast_mul,mul_assoc] using hr

/-- The surviving genuine pool assignments obey the original annulus product
cap; there is no new supplier-norm premise. -/
theorem remaining_mark_norm_cap (r : Source ι a b) (G L : Id) (B : commonAlloc r G)
    (E : fullPrimaryAlloc r G B L)
    (p : (i : ↥(liveIndices E.val)) → ↥(r.pool i.val.val)) :
    ((∏i:liveIndices E.val,(p i).val).absNorm:ℝ) ≤ ∏i:liveIndices E.val,2*r.P i.val.val := by
  simp only [map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>Nat.cast_nonneg _)
    (fun i _=>(r.hpn _ _ (p i).property).2)

#print axioms actual_label_norm_cap
#print axioms remaining_mark_norm_cap
end
end QRH.Cycle092.FixedCubeGauss
