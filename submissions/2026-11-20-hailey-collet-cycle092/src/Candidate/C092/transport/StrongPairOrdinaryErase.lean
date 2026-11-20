/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Weighted whole-slot erasure keeps the actual row-dependent P4 short test. -/
import Candidate.C092.transport.StrongPairOrdinaryPrice
import Candidate.C092.transport.WitnessP4Apply

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open QRH.Cycle092.WholeSlot
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual

/-- No profile or row is replaced: the two ordinary values may depend on
all of the row's supported witness data. Only whole original marks are erased. -/
theorem weighted_mark_erasure {Row Slot : Type*} [Fintype Row] [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F ⊆ T) (weight : Row→ℝ) (A B : Row→ℂ)
    (mark : Slot→Row→ℂ) (cap : Slot→ℝ) (hw : ∀ u,0 ≤ weight u)
    (hmark : ∀ u,∀ k∈T\F,‖mark k u‖^2 ≤ cap k) :
    (∑ u,weight u*‖A u*B u*(∏ k∈T,mark k u)‖^2) ≤
      (∏ k∈T\F,cap k)*(∑ u,weight u*‖A u*B u*(∏ k∈F,mark k u)‖^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have hwu := hw u
  simp only [norm_mul,norm_prod,mul_pow,←Finset.prod_pow]
  have hp := Finset.prod_le_prod₀ (fun k _=>sq_nonneg ‖mark k u‖) (fun k hk=>hmark u k hk)
  have he := Finset.prod_sdiff (f:=fun k=>‖mark k u‖^2) hFT
  rw [←he]
  have hh := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ weight u*‖A u‖^2*‖B u‖^2*∏ k∈F,‖mark k u‖^2 by positivity)
  convert hh using 1 <;> ring

/-- The exact response payment, with its true erased slot count and width. -/
theorem weighted_low_erasure {Row Slot : Type*} [Fintype Row] [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) (weight : Row→ℝ) (A B : Row→ℂ) (mark : Slot→Row→ℂ)
    (w : Slot→ℝ) {U e pay L d quota rounding : ℝ}
    (hU : 1 ≤ U) (he : 0 ≤ e) (hpay : 0 ≤ pay) (hw : ∀ u,0 ≤ weight u)
    (hwidth : (∑ k,w k) ≤ L)
    (hdelete : (∑ k∈Finset.univ\F,w k) ≤ max 0 ((∑ k,w k)-d*quota+rounding))
    (hmark : ∀ u,∀ k∈Finset.univ\F,‖mark k u‖^2 ≤ pay*U^(e*w k)) :
    (∑ u,weight u*‖A u*B u*(∏ k,mark k u)‖^2) ≤
      (pay^(Finset.univ\F).card*U^(e*max 0 (L-d*quota+rounding)))*
        (∑ u,weight u*‖A u*B u*(∏ k∈F,mark k u)‖^2) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have h := weighted_mark_erasure Finset.univ F (Finset.subset_univ _) weight A B mark
    (fun k=>pay*U^(e*w k)) hw hmark
  simp only [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUp,←Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_right (p3_payment F w hU he hpay hwidth hdelete) (Finset.sum_nonneg (fun u _=>mul_nonneg (hw u) (sq_nonneg _))))

/-- The actual retained P4 estimate, its true complement response and a
paid exponent produce the original full product on exactly the same rows. -/
theorem weighted_ordinary_paid {Row Slot : Type*} [Fintype Row] [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) (weight : Row→ℝ) (A B : Row→ℂ) (mark : Slot→Row→ℂ)
    (w : Slot→ℝ) {U e Cslot buffer n y ν d m cap decrement rounding ε extra target K : ℝ}
    (hU : 1 ≤ U) (he : 0 ≤ e) (hCslot : 0 ≤ Cslot) (hK : 0 ≤ K)
    (hw : ∀ u,0 ≤ weight u) (hwidth : (∑ k,w k) ≤ sourceWidth n y-(u:ℝ))
    (hdelete : (∑ k∈Finset.univ\F,w k) ≤
      max 0 ((∑ k,w k)-d*(frozenCapacity n cap-decrement)+rounding))
    (hmark : ∀ u,∀ k∈Finset.univ\F,‖mark k u‖^2 ≤ (Cslot*U^buffer)*U^(e*w k))
    (hp4 : (∑ u,weight u*‖A u*B u*(∏ k∈F,mark k u)‖^2) ≤
      K*U^(d+ν*(y-d*m)+3*d*ε+extra-buffer*((Finset.univ\F).card:ℝ)))
    (hpaid : ordinaryEscapeExponent n y e ν d m cap decrement rounding ε extra ≤ target) :
    (∑ u,weight u*‖A u*B u*(∏ k,mark k u)‖^2) ≤
      (Cslot^(Finset.univ\F).card*K)*U^target := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hErase := weighted_low_erasure F weight A B mark w hU he
    (show 0 ≤ Cslot*U^buffer by positivity) hw hwidth hdelete hmark
  have hbound := hErase.trans (mul_le_mul_of_nonneg_left hp4 (by positivity))
  have heq : ((Cslot*U^buffer)^(Finset.univ\F).card*
      U^(e*max 0 (sourceWidth n y-(u:ℝ)-
        d*(frozenCapacity n cap-decrement)+rounding)))*
      (K*U^(d+ν*(y-d*m)+3*d*ε+extra-buffer*((Finset.univ\F).card:ℝ))) =
      (Cslot^(Finset.univ\F).card*K)*
        U^(ordinaryEscapeExponent n y e ν d m cap decrement rounding ε extra) := by
    rw [mul_pow,←Real.rpow_mul_natCast hUp.le]
    unfold ordinaryEscapeExponent
    rw [show (Cslot^(Finset.univ\F).card*U^(buffer*((Finset.univ\F).card:ℝ))*
        U^(e*max 0 (sourceWidth n y-(u:ℝ)-
          d*(frozenCapacity n cap-decrement)+rounding)))*
        (K*U^(d+ν*(y-d*m)+3*d*ε+extra-buffer*((Finset.univ\F).card:ℝ))) =
        (Cslot^(Finset.univ\F).card*K)*
          (U^(buffer*((Finset.univ\F).card:ℝ))*
           U^(e*max 0 (sourceWidth n y-(u:ℝ)-
             d*(frozenCapacity n cap-decrement)+rounding))*
           U^(d+ν*(y-d*m)+3*d*ε+extra-buffer*((Finset.univ\F).card:ℝ))) by ring]
    rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
    congr 2
    ring
  rw [heq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU hpaid) (by positivity))

#print axioms weighted_mark_erasure
#print axioms weighted_ordinary_paid
end
end QRH.Cycle092.StrongPair
