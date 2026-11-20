/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Caps on the actual inverse divisors in the common supported rectangle.
They apply to both restored arms, even when one shortened arm is empty. -/
import Submissions.sil_density_split_20261026.CubeFree.FP.KernelRowPools
import Candidate.C092.transport.FixedFirstGeometry
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP KernelRowPools KernelRowProfiles KernelRowExpansion
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.Second.Provider
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O

theorem root_divisor_caps (S:Finset PrimeIdeal) (b M₁ M₂:ℝ) {d:IdealPair}
    (hd:d∈divisorPool (supportedRectangle S b M₁ M₂)) :
    1≤(d.1.absNorm:ℝ) ∧ 1≤(d.2.absNorm:ℝ) ∧
    (d.1.absNorm:ℝ)≤b*M₁ ∧ (d.2.absNorm:ℝ)≤b*M₂ := by
  have hnz:=divisor_supported hd
  obtain ⟨p,hp,hpd⟩:=Finset.mem_image.mp hd
  obtain ⟨n,hn,hpn⟩:=Finset.mem_biUnion.mp hp
  have he := expandedAt_reconstruct (supportedRectangle_nonzero hn) hpn
  have hi : d.1 ∣ n.1 := by rw [←he,←hpd]; exact dvd_mul_right _ _
  have hj : d.2 ∣ n.2 := by rw [←he,←hpd]; exact dvd_mul_right _ _
  obtain ⟨hi',hj'⟩:=Finset.mem_product.mp (Finset.mem_filter.mp hn).1
  have leN (A B:Id) (h:B ≠ 0) (hd:A∣B) : (A.absNorm:ℝ) ≤ B.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h)) (map_dvd Ideal.absNorm hd)
  exact ⟨nrm_one_le hnz.1,nrm_one_le hnz.2.1,
    (leN _ _ (supportedRectangle_nonzero hn).1 hi).trans ((mem_idealBall _ _).mp hi').2,
    (leN _ _ (supportedRectangle_nonzero hn).2 hj).trans ((mem_idealBall _ _).mp hj').2⟩

/-- For both-long parents the scale q=U^.115 eventually exceeds b=9/4.
Consequently every one of the four divided scales is at least U⁻¹. -/
theorem root_four_lengths_lower (S:Finset PrimeIdeal) (b M₁ M₂ U X₁ X₂ Y₁ Y₂:ℝ) {d:IdealPair}
    (hd:d∈divisorPool (supportedRectangle S b M₁ M₂))
    (hU:1<U) (hb:0≤b) (hM₁:M₁≤U) (hM₂:M₂≤U)
    (hx:b≤X₁ ∧ b≤X₂ ∧ b≤Y₁ ∧ b≤Y₂) :
    U⁻¹ ≤ min (min (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ)))
      (min (Y₁/(d.1.absNorm:ℝ)) (Y₂/(d.2.absNorm:ℝ))) := by
  have hc:=root_divisor_caps S b M₁ M₂ hd
  have h0:=zero_lt_one.trans hU
  have arm (X n m:ℝ) (hn:1≤n) (hc:n≤b*m) (hm:m≤U) (hx:b≤X) :
      U⁻¹ ≤ X/n := by
    apply (le_div_iff₀ (zero_lt_one.trans_le hn)).mpr
    calc
      U⁻¹*n ≤ U⁻¹*(b*U) := mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hm hb)) (inv_nonneg.mpr h0.le)
      _ = b := by field_simp
      _ ≤ _ := hx
  exact le_min (le_min (arm _ _ _ hc.1 hc.2.2.1 hM₁ hx.1) (arm _ _ _ hc.2.1 hc.2.2.2 hM₂ hx.2.1))
    (le_min (arm _ _ _ hc.1 hc.2.2.1 hM₁ hx.2.2.1) (arm _ _ _ hc.2.1 hc.2.2.2 hM₂ hx.2.2.2))

/-- Full root-volume lower guard used by the numeric zero/tail payments. -/
theorem divided_volume_reciprocal {X₁ X₂ slotProduct U:ℝ} (hU:1<U)
    (hx:U⁻¹≤X₁) (hy:U⁻¹≤X₂) (hslot:1 ≤ slotProduct) :
    (X₁*X₂*slotProduct)⁻¹ ≤ U^2 := by
  have hp:=inv_pos.mpr (zero_lt_one.trans hU)
  have hinner: U⁻¹*U⁻¹ ≤ X₁*X₂ := mul_le_mul hx hy hp.le (hp.le.trans hx)
  have hprod:U⁻¹*U⁻¹ ≤ X₁*X₂*slotProduct :=
    hinner.trans (le_mul_of_one_le_right (mul_nonneg (hp.le.trans hx) (hp.le.trans hy)) hslot)
  calc
    _ ≤ (U⁻¹*U⁻¹)⁻¹ := (inv_le_inv₀ ((mul_pos hp hp).trans_le hprod) (mul_pos hp hp)).mpr hprod
    _ = _ := by simp [pow_two]

#print axioms root_divisor_caps
#print axioms root_four_lengths_lower
#print axioms divided_volume_reciprocal
end QRH.Cycle092.FixedFramePacking
