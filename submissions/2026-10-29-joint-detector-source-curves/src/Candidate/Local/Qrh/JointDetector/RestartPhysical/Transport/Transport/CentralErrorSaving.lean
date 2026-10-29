/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.CentralErrorSaving (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
set_option autoImplicit false
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN]
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.RestartDensitySplitReturn.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.y:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.x_add_y, Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.ly_coarse, Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell_pos, mul_nonneg (by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.ly_coarse] : 0 ≤ Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.y) ha, mul_nonneg (by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.ly_coarse] : 0 ≤ Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.y) he])

lemma central_prime_product_bound {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/10000000000)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ≤1 by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.h_interval]))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ)*(3:ℕ))=Z^(6+3*Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Arithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

end SevenEighths.RestartDensitySplitReturn.TransportHighRowFamily

end

end OAI
