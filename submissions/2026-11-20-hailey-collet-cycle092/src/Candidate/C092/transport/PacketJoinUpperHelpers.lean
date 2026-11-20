/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.PacketJoinE49PaddedFinalFee
import Candidate.C092.transport.PacketJoinFixedPaddedFinalFee
import Candidate.C092.transport.PacketJoinNativePaddedFinalFee
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage
open QRH.Cycle092.SelectedNonfloor
namespace QRH.Cycle092.PacketJoin

def routeTopAdmission (route : CountRoute) (δ p : ℝ) : Prop :=
  ∃ c : DirectCertificate,c∈directCertificates ∧ c.route=route ∧ c.edge=3 ∧ c.box.Contains (δ,p)
def upperSectorAdmission (δ p : ℝ) : Prop :=
  routeTopAdmission .old δ p ∨ routeTopAdmission .native δ p ∨
    fixedTopAdmission δ p ∨ pairedUpperAdmission δ p

lemma four_filter_sum {ι : Type*} (s : Finset ι) (A B C : ι→Prop) (f : ι→ℝ) :
    (∑ b∈s,f b)=
    (∑ b∈s.filter A,f b)+
    (∑ b∈(s.filter (fun b=>¬A b)).filter B,f b)+
    (∑ b∈((s.filter (fun b=>¬A b)).filter (fun b=>¬B b)).filter C,f b)+
    (∑ b∈((s.filter (fun b=>¬A b)).filter (fun b=>¬B b)).filter (fun b=>¬C b),f b) := by
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases ha:A b <;> by_cases hB:B b <;> by_cases hC:C b <;> simp [ha,hB,hC]

variable [Geometry.Parameters]
lemma upper_normalized_rhs_mono {Z d a τ fee target target' C C' : ℝ} {m m' i : ℕ}
    (hZ : 1 ≤ Z) (hd : 0<d) (hC : 0 ≤ C) (hCC : C ≤ C') (hm : m ≤ m') (ht : target ≤ target') :
    C*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee target)  ≤ 
    C'*(3+(3*i+1:ℕ)*Z^τ)^m'*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee target') := by
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hU : 1 ≤ Z^d := Real.one_le_rpow hZ hd.le
  have hT : 1 ≤ 3+(3*i+1:ℕ)*Z^τ := by
    have h : 0 ≤ (3*i+1:ℕ)*Z^τ := by positivity
    linarith
  have he : finalPower a d sourceCost fee target ≤ finalPower a d sourceCost fee target' := by
    unfold finalPower
    have h := div_le_div_of_nonneg_right (by linarith : target-rowPrice (2*a-1) 0 0 d sourceCost-fee ≤ target'-rowPrice (2*a-1) 0 0 d sourceCost-fee) hd.le
    linarith
  have hpow := pow_le_pow_right₀ hT hm
  have hrpow := Real.rpow_le_rpow_of_exponent_le hU he
  have hC' : 0 ≤ C' := hC.trans hCC
  gcongr
end QRH.Cycle092.PacketJoin
