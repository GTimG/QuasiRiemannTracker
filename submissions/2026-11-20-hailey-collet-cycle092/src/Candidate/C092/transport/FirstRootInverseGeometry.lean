/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The same two inverse divisors reduce the root volume and the safe minimum
scale. Their full price cancels in the fixed-row excess calculation. -/
import Candidate.C092.transport.FirstRootDivisorCaps
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O

theorem original_volume_divisors {ι:Type*} [Fintype ι] (S:Finset ι) (P:ι→ℝ)
    (hp:∀i,1≤P i) (X₁ X₂ a b:ℝ) (hx:0≤X₁) (hy:0≤X₂) (ha:0<a) (hb:0<b) :
    ((X₁/a)*(X₂/b)*(∏j∈S,P j))*(a*b) ≤ X₁*X₂*∏i,P i := by
  have hprod : (∏j∈S,P j) ≤ ∏i,P i :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ S)
      (fun i _ => zero_le_one.trans (hp i)) (fun i _ _=>hp i)
  calc
    _ = (X₁*X₂)*(∏j∈S,P j) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hx hy)

theorem minimum_divisors (X₁ X₂ Y₁ Y₂ p₁ p₂ q : ℝ) (hx:q ≤ X₁ ∧ q ≤ X₂ ∧ q ≤ Y₁ ∧ q ≤ Y₂)
    (hq:0<q) (hp₁:1≤p₁) (hp₂:1≤p₂) :
    q/(p₁*p₂) ≤ min (min (X₁/p₁) (X₂/p₂)) (min (Y₁/p₁) (Y₂/p₂)) := by
  have h0:=zero_lt_one.trans_le hp₁
  have h1:=zero_lt_one.trans_le hp₂
  have hmain (x d e:ℝ) (h:q≤x) (hd:0<d) (he:1≤e) :
      q/(d*e) ≤ x/d := by
    apply (div_le_div_iff₀ (mul_pos hd (zero_lt_one.trans_le he)) hd).mpr
    have hh:=le_mul_of_one_le_right (hq.le.trans h) he
    nlinarith only [mul_le_mul_of_nonneg_right (h.trans hh) hd.le]
  refine le_min (le_min (hmain _ _ _ hx.1 h0 hp₂) ?_) (le_min (hmain _ _ _ hx.2.2.1 h0 hp₂) ?_)
  · rw [mul_comm p₁ p₂];exact hmain _ _ _ hx.2.1 h1 hp₁
  · rw [mul_comm p₁ p₂];exact hmain _ _ _ hx.2.2.2 h1 hp₁

/-- One shared logarithmic debit for inverse restoration and the subsequent
first common ideal. It can be passed as c to fixed_filled_admissible. -/
theorem inverse_common_ledger (Z vol K Lf q p₁ p₂ ng firstSelected A₀ cFee b : ℝ)
    (hZ:1<Z) (hvol:0<vol) (hK:0<K) (hLf:0<Lf)
    (hp₁:0<p₁) (hp₂:0<p₂) (hg:0<ng)
    (hvolcap:vol*(p₁*p₂) ≤ Z^A₀)
    (hchild:K*Z^firstSelected*ng≤Z^cFee*vol)
    (hpaymin: q ≤ Lf*(p₁*p₂)*ng) (hq:Z^b ≤ q) :
    let c := Real.logb Z ((p₁*p₂)*ng)
    Real.logb Z K ≤ A₀-c-firstSelected+cFee ∧
    max 0 (b-c) ≤ Real.logb Z (max 1 Lf) := by
  let pp:=p₁*p₂
  have hp:0<pp:=mul_pos hp₁ hp₂
  have h0:=zero_lt_one.trans hZ
  have h1:=Real.logb_le_logb_of_le hZ (mul_pos hvol hp) hvolcap
  have h2:=Real.logb_le_logb_of_le hZ (mul_pos (mul_pos hK (Real.rpow_pos_of_pos h0 _)) hg) hchild
  have hm:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos h0 b) (hq.trans hpaymin)
  change Real.logb Z (vol*pp) ≤ _ at h1
  change Real.logb Z (Z^b) ≤ Real.logb Z (Lf*pp*ng) at hm
  change Real.logb Z K ≤ A₀-Real.logb Z (pp*ng)-firstSelected+cFee ∧
    max 0 (b-Real.logb Z (pp*ng)) ≤ Real.logb Z (max 1 Lf)
  rw [Real.logb_mul hp.ne' hg.ne']
  rw [Real.logb_mul hvol.ne' hp.ne',Real.logb_rpow h0 hZ.ne'] at h1
  rw [Real.logb_mul (mul_pos hK (Real.rpow_pos_of_pos h0 _)).ne' hg.ne',
    Real.logb_mul hK.ne' (Real.rpow_pos_of_pos h0 _).ne',
    Real.logb_mul (Real.rpow_pos_of_pos h0 _).ne' hvol.ne'] at h2
  simp only [Real.logb_rpow h0 hZ.ne'] at h2
  rw [Real.logb_rpow h0 hZ.ne',Real.logb_mul (mul_pos hLf hp).ne' hg.ne',Real.logb_mul hLf.ne' hp.ne'] at hm
  refine ⟨by linarith,max_le (Real.logb_nonneg hZ (le_max_left _ _)) ?_⟩
  linarith [Real.logb_le_logb_of_le hZ hLf (le_max_right 1 Lf)]

#print axioms original_volume_divisors
#print axioms minimum_divisors
#print axioms inverse_common_ledger
end QRH.Cycle092.FixedFramePacking
