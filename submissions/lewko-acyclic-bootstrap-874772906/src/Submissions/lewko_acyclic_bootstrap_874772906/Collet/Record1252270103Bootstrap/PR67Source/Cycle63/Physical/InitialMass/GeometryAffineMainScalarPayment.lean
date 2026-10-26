import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePrimePayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

variable [Cycle63.AffineLedger] in
/-- Only the scalar loss ledger is enlarged to the ambient slot count.
The physical source and its Fourier scales keep the actual subset count. -/
theorem geometry_affine_low_target_card_mono (g : GeometryAffineLowSchedule)
    (n N : ℕ) (hn : n≤N) (amp omega mesh : ℝ) :
    geometryAffineLowTarget g n amp omega mesh≤geometryAffineLowTarget g N amp omega mesh := by
  have hcast : (n:ℝ)≤N := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hcast g.δ_pos.le
  dsimp only [geometryAffineLowTarget]
  nlinarith only [hmul]

variable [Cycle63.AffineLedger] in
theorem geometry_affine_subset_low_target_ledger
    (g : GeometryAffineLowSchedule) (B L : ℝ) (n N : ℕ) (hn : n≤N)
    (amp omega mesh : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤g.μ/8) :
    geometryAffineLowTarget g n amp omega mesh+3*g.δ-amp≤
      -(Cycle63.AffineLedger.lowReserve:ℝ)+2*g.μ := by
  have hm := geometry_affine_low_target_card_mono g n N hn amp omega mesh
  have hb := geometry_affine_final_low_target_ledger g B L N amp omega mesh hB hL hδ hω hmesh
  linarith only [hm,hb]

/-- Physical selection and the finite ratio image each pay one common
rate; the single prime average pays the third. The branch targets include
the amplifier exponent, which cancels once. -/
theorem geometry_affine_main_selected_ratio_payment
    (Z n amp δ low high target coefficient cap Cb Ksel CL CH ratio : ℝ)
    (hZ : 1<Z) (hn : Z^(amp-δ)≤n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap)
    (hCb : 0≤Cb) (hKsel : 0≤Ksel) (hCL : 0≤CL) (hCH : 0≤CH)
    (hratio : ratio≤Cb*(Ksel*Z^δ*(CL*Z^low+CH*Z^high))*Z^δ)
    (hlow : low+3*δ-amp≤target) (hhigh : high+3*δ-amp≤target) :
    (56/n)*coefficient*ratio≤
      (56*cap*Cb*Ksel*(CL+CH))*Z^target := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hn0 : 0<n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
  have hsplit : Cb*(Ksel*Z^δ*(CL*Z^low+CH*Z^high))*Z^δ=
      (Cb*Ksel*CL)*Z^(low+δ+δ)+(Cb*Ksel*CH)*Z^(high+δ+δ) := by
    simp only [Real.rpow_add hZ0]
    ring
  have hlo := geometry_affine_prime_payment_of_bound Z n amp δ (low+δ+δ) target
    coefficient cap (Cb*Ksel*CL) ((Cb*Ksel*CL)*Z^(low+δ+δ))
    hZ hn hc hcap (by positivity) le_rfl (by linarith only [hlow])
  have hhi := geometry_affine_prime_payment_of_bound Z n amp δ (high+δ+δ) target
    coefficient cap (Cb*Ksel*CH) ((Cb*Ksel*CH)*Z^(high+δ+δ))
    hZ hn hc hcap (by positivity) le_rfl (by linarith only [hhigh])
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤56) hn0.le) hc)
  rw [hsplit] at hscaled
  calc
    _ ≤ (56/n)*coefficient*((Cb*Ksel*CL)*Z^(low+δ+δ)+
      (Cb*Ksel*CH)*Z^(high+δ+δ)) := hscaled
    _ = (56/n)*coefficient*((Cb*Ksel*CL)*Z^(low+δ+δ))+
      (56/n)*coefficient*((Cb*Ksel*CH)*Z^(high+δ+δ)) := by ring
    _ ≤ (56*cap*(Cb*Ksel*CL))*Z^target+
      (56*cap*(Cb*Ksel*CH))*Z^target := add_le_add hlo hhi
    _ = _ := by ring

/-- The HIGH part left as a given real: physical selection and the finite ratio image each pay one common rate, the
single prime average pays the third, and the HIGH constant enters linearly. The amplifier exponent cancels once. -/
theorem geometry_affine_main_selected_ratio_payment_linear
    (Z n amp δ low target coefficient cap Cb Ksel CL CH ratio : ℝ)
    (hZ : 1<Z) (hn : Z^(amp-δ)≤n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap)
    (hCb : 0≤Cb) (hKsel : 0≤Ksel) (hCL : 0≤CL) (hCH : 0≤CH)
    (hratio : ratio≤Cb*(Ksel*Z^δ*(CL*Z^low+CH))*Z^δ)
    (hlow : low+3*δ-amp≤target) :
    (56/n)*coefficient*ratio≤
      (56*cap*Cb*Ksel*CL)*Z^target+(56*cap*Cb*Ksel)*Z^(3*δ-amp)*CH := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hn0 : 0<n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
  have hsplit : Cb*(Ksel*Z^δ*(CL*Z^low+CH))*Z^δ=
      (Cb*Ksel*CL)*Z^(low+δ+δ)+(Cb*Ksel*CH)*Z^(δ+δ) := by
    simp only [Real.rpow_add hZ0]
    ring
  have hlo := geometry_affine_prime_payment_of_bound Z n amp δ (low+δ+δ) target
    coefficient cap (Cb*Ksel*CL) ((Cb*Ksel*CL)*Z^(low+δ+δ))
    hZ hn hc hcap (by positivity) le_rfl (by linarith only [hlow])
  have hhi := geometry_affine_prime_payment_of_bound Z n amp δ (δ+δ) (3*δ-amp)
    coefficient cap (Cb*Ksel*CH) ((Cb*Ksel*CH)*Z^(δ+δ))
    hZ hn hc hcap (by positivity) le_rfl (by linarith only [])
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤56) hn0.le) hc)
  rw [hsplit] at hscaled
  calc
    _ ≤ (56/n)*coefficient*((Cb*Ksel*CL)*Z^(low+δ+δ)+
      (Cb*Ksel*CH)*Z^(δ+δ)) := hscaled
    _ = (56/n)*coefficient*((Cb*Ksel*CL)*Z^(low+δ+δ))+
      (56/n)*coefficient*((Cb*Ksel*CH)*Z^(δ+δ)) := by ring
    _ ≤ (56*cap*(Cb*Ksel*CL))*Z^target+
      (56*cap*(Cb*Ksel*CH))*Z^(3*δ-amp) := add_le_add hlo hhi
    _ = _ := by ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
