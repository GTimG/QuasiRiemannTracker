/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.GeometricTail (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.Transport.LargeDyad
set_option autoImplicit false
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped BigOperators
namespace SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily
open ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0 < Z) (n : ℕ) :
    Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)*r)*(Z^((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    Summable (fun n : ℕ=>Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)*r)*(Z^((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    (∑'n : ℕ,Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)*r)*(Z^((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤r ∧ 8/5+δ < r ∧
      (1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily
end

end OAI
