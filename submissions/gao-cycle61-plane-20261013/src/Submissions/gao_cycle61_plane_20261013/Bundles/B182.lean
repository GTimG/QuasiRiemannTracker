/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B169
import Submissions.gao_cycle61_plane_20261013.Bundles.B171
import Submissions.gao_cycle61_plane_20261013.Bundles.B181

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePrimePayment; sha256 c77786250b74f075dac9353899d08ae19313a4f731edc6197c8e31bb2a8a9bff -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- The actual prime-cardinality lower bound cancels the amplifier exponent
once. All source, profile, and height factors can remain in the constant. -/
theorem geometry_affine_prime_power_payment
    (Z n amp loss target coefficient C : ℝ)
    (hZ : 0< Z) (hn : Z^(amp-loss)≤ n)
    (hc : 0≤ coefficient) (hC : 0≤ C) :
    (56/n)*coefficient*(C*Z^target)≤
      (56*coefficient*C)*Z^(target+loss-amp) := by
  have hp : 0< Z^(amp-loss) := Real.rpow_pos_of_pos hZ _
  have hnum : 0≤(56*coefficient*C)*Z^target := by positivity
  calc
    (56/n)*coefficient*(C*Z^target) = ((56*coefficient*C)*Z^target)/n := by ring
    _ ≤ ((56*coefficient*C)*Z^target)/Z^(amp-loss) :=
      div_le_div_of_nonneg_left hnum hp hn
    _ = (56*coefficient*C)*(Z^target/Z^(amp-loss)) := by ring
    _ = (56*coefficient*C)*Z^(target+loss-amp) := by
      rw [←Real.rpow_sub hZ]
      congr 2
      ring

/-- A retained ordinary bound is paid using its single prime average and
the existing amplifier-coefficient cap. The exponent premise includes the
selection, ratio, and prime losses before comparison with the final saving. -/
theorem geometry_affine_prime_payment_of_bound
    (Z n amp loss target exponent coefficient cap C value : ℝ)
    (hZ : 1< Z) (hn : Z^(amp-loss)≤ n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap) (hC : 0≤ C)
    (hvalue : value≤ C*Z^target) (hexponent : target+loss-amp≤ exponent) :
    (56/n)*coefficient*value≤(56*cap*C)*Z^exponent := by
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  have hn0 : 0< n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
  have hv := mul_le_mul_of_nonneg_left hvalue
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤56) hn0.le) hc)
  have hp := geometry_affine_prime_power_payment Z n amp loss target coefficient C hZ0 hn hc hC
  have hcoef : 56*coefficient*C≤56*cap*C := by gcongr
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hexponent
  have hcap0 : 0≤ cap := hc.trans hcap
  exact (hv.trans hp).trans (mul_le_mul hcoef hpow
    (Real.rpow_nonneg hZ0.le _) (by positivity))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_prime_power_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_prime_payment_of_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePrimePayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainScalarPayment; sha256 f9a8605075efd998e7727a6d59b34b043c29294e6f9bfed30da7b4e63cb3647e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                              
                                                               

set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- Only the scalar loss ledger is enlarged to the ambient slot count.
The physical source and its Fourier scales keep the actual subset count. -/
theorem geometry_affine_low_target_card_mono (g : GeometryAffineLowSchedule)
    (n N : ℕ) (hn : n≤ N) (amp omega mesh : ℝ) :
    geometryAffineLowTarget g n amp omega mesh≤ geometryAffineLowTarget g N amp omega mesh := by
  have hcast : (n:ℝ)≤ N := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hcast g.δ_pos.le
  dsimp only [geometryAffineLowTarget]
  nlinarith only [hmul]

theorem geometry_affine_subset_low_target_ledger
    (g : GeometryAffineLowSchedule) (B L : ℝ) (n N : ℕ) (hn : n≤ N)
    (amp omega mesh : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤ g.μ/8) :
    geometryAffineLowTarget g n amp omega mesh+3*g.δ-amp≤
      -(1/3750000:ℝ)+2*g.μ := by
  have hm := geometry_affine_low_target_card_mono g n N hn amp omega mesh
  have hb := geometry_affine_final_low_target_ledger g B L N amp omega mesh hB hL hδ hω hmesh
  linarith only [hm,hb]

/-- Physical selection and the finite ratio image each pay one common
rate; the single prime average pays the third. The branch targets include
the amplifier exponent, which cancels once. -/
theorem geometry_affine_main_selected_ratio_payment
    (Z n amp δ low high target coefficient cap Cb Ksel CL CH ratio : ℝ)
    (hZ : 1< Z) (hn : Z^(amp-δ)≤ n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap)
    (hCb : 0≤ Cb) (hKsel : 0≤ Ksel) (hCL : 0≤ CL) (hCH : 0≤ CH)
    (hratio : ratio≤ Cb*(Ksel*Z^δ*(CL*Z^low+CH*Z^high))*Z^δ)
    (hlow : low+3*δ-amp≤ target) (hhigh : high+3*δ-amp≤ target) :
    (56/n)*coefficient*ratio≤
      (56*cap*Cb*Ksel*(CL+CH))*Z^target := by
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  have hn0 : 0< n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
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

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_main_selected_ratio_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_low_target_card_mono
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_subset_low_target_ledger

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainScalarPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRetainedPayment; sha256 0e0de21b7366ac13bf90252077b714ab3c0b3480e304e09be59df2b2dfd03c6c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- Close the scalar part of the actual main contraction after putting both
selected branches under one profile and height control. The exceptional
payment is already averaged; the ordinary payment uses the prime factor once. -/
theorem geometry_affine_main_contracted_payment
    (Z n amp δ low high target coefficient cap Cb Ksel CL CH Ce Co control
      main exceptional ratio : ℝ)
    (hZ : 1< Z) (hn : Z^(amp-δ)≤ n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap)
    (hCb : 0≤ Cb) (hKsel : 0≤ Ksel) (hCL : 0≤ CL) (hCH : 0≤ CH)
    (hCo : 0≤ Co) (hcontrol : 0≤ control)
    (hcontract : (56/n)*coefficient*main≤ exceptional+Co*((56/n)*coefficient*ratio))
    (hexceptional : exceptional≤ Ce*control*Z^target)
    (hratio : ratio≤ Cb*(Ksel*Z^δ*((CL*control)*Z^low+(CH*control)*Z^high))*Z^δ)
    (hlow : low+3*δ-amp≤ target) (hhigh : high+3*δ-amp≤ target) :
    (56/n)*coefficient*main≤
      (Ce+Co*(56*cap*Cb*Ksel*(CL+CH)))*control*Z^target := by
  have hp := geometry_affine_main_selected_ratio_payment
    Z n amp δ low high target coefficient cap Cb Ksel (CL*control) (CH*control) ratio
    hZ hn hc hcap hCb hKsel (mul_nonneg hCL hcontrol) (mul_nonneg hCH hcontrol)
    hratio hlow hhigh
  apply hcontract.trans
  have hs := add_le_add hexceptional (mul_le_mul_of_nonneg_left hp hCo)
  convert hs using 1 <;> ring

/-- The error family already contains its single prime average in the joint
weight. Its contraction and finite ratio image therefore need no further
prime factor. The first error weight remains inside that family. -/
theorem geometry_affine_error_contracted_payment
    (Z εratio exponent target Cb C Ce Co control paidError exceptional ratio : ℝ)
    (hZ : 1< Z) (hCb : 0≤ Cb) (hC : 0≤ C) (hCo : 0≤ Co) (hcontrol : 0≤ control)
    (hcontract : paidError≤ exceptional+Co*ratio)
    (hexceptional : exceptional≤ Ce*control*Z^target)
    (hratio : ratio≤ Cb*(C*control*Z^exponent)*Z^εratio)
    (hexponent : exponent+εratio≤ target) :
    paidError≤(Ce+Co*Cb*C)*control*Z^target := by
  have hz := Real.rpow_le_rpow_of_exponent_le hZ.le hexponent
  have hp := mul_le_mul_of_nonneg_left hz
    (mul_nonneg (mul_nonneg hCb hC) hcontrol)
  have heq : Cb*(C*control*Z^exponent)*Z^εratio=
      (Cb*C*control)*Z^(exponent+εratio) := by
    rw [Real.rpow_add (zero_lt_one.trans hZ)]
    ring
  rw [heq] at hratio
  have hs := add_le_add hexceptional
    (mul_le_mul_of_nonneg_left (hratio.trans hp) hCo)
  apply hcontract.trans
  convert hs using 1 <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_main_contracted_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_error_contracted_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRetainedPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryFinalErrorLoss; sha256 0ec64e4eefc5d0c54ab9cb146a9bc2f8edbe828ce885f0e807c7747bd69a87cf -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- The extracted projector uses actual slot cardinality, while its scalar
loss is paid by a common ambient rate. This does not alter Fourier data. -/
theorem geometry_final_error_raw_loss
    (μ omega mesh : ℝ) (n N : ℕ) (hμ : 0<μ) (hn : n≤ N)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*n+
      (omega+μ/8)/6+(3/4)*mesh+δ≤μ := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hd : δ≤μ/128:=hb.2.2.1
  have he:=(geometry_final_error_dictionary_budget μ N hμ).2 n hn
  linarith only [hd,he,hω,hmesh,hμ]

/-- The physical error theorem has room for the actual projector error,
source-volume loss, four common losses, and its remaining error fee. -/
theorem geometry_final_error_physical_loss (μ error : ℝ)
    (hμ : 0<μ) (he : error≤μ) :
    error+μ/8+4*(μ/8)+μ/8≤64*μ := by
  linarith only [hμ,he]

/-- Projector, allocation, shell, and finite ratio losses are paid together.
The error joint weight already contains its single prime average. -/
theorem geometry_final_error_paid_ledger (μ : ℝ) (N : ℕ) (hμ : 0<μ) :
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    (δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))+δ≤
      -(7/60000000:ℝ)+μ := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hd : 0<δ:=hb.1
  have hp:=hb.2.2.2.2.2.1
  change 130*δ+3*(3*((N:ℝ)+2))*δ+δ+8*δ≤μ at hp
  linarith only [hd,hp]

/-- A strict saving remains after the complete scalar error ledger. -/
theorem geometry_final_error_exponent_saving (εaffine : ℝ) :
    -(7/60000000:ℝ)+geometryLossUnit 1 εaffine≤-(7/120000000:ℝ) := by
  have h:=(geometry_loss_unit_reserve 1 εaffine 1 le_rfl).2
  linarith only [h]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_error_raw_loss
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_error_physical_loss
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_error_paid_ledger
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_error_exponent_saving

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryFinalErrorLoss -/
