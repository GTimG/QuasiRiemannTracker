/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 OpenAI. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.AdaptiveSupplier
import Candidate.Local.Qrh.JointDetector.PointwisePrice

/-! The nonlinear price consumes the same actual zero/slot count and the same
LOW/HIGH decomposition. The selected operator estimate remains explicit. -/
namespace Qrh.JointDetector.PointwiseSupplier
noncomputable section
set_option autoImplicit false
open Set QRH.SilDensitySplit.CubeFree OAI.SevenEighths

/-- Scalar payment at each literal cut; no derivative of the cut is used. -/
theorem high_law : AdaptiveSupplier.HighLaw PointwisePrice.q0 PointwisePrice.highSup where
  floor_ge := le_rfl
  zero := by
    intro q ν P s M hq hν hs
    exact PointwisePrice.zero_energy_le_highSup hq hν le_rfl hs
  joint := by
    intro q ν δ P s M hq hν hδ hM hs
    exact PointwisePrice.jointRate_energy hq hν hδ hM hs
  full := by
    intro q ν P s M hq hν hs
    have hνg : ν ∈ Icc PointwisePrice.q0 (3/4) := ⟨hq.1.trans hν.1,hν.2⟩
    have hκ := PointwisePrice.slope_bounds hνg
    have hk0 := (PointwisePrice.slope_pos hνg).le
    have hext : 0 ≤ (ν-PointwisePrice.slope ν)*max (s-M/10) 0 :=
      mul_nonneg (sub_nonneg.mpr hκ.2) (le_max_right _ _)
    have hslot := mul_le_mul_of_nonneg_right
      (show ν-PointwisePrice.slope ν ≤ 1 by linarith [hν.2]) hs
    have hb := PointwisePrice.le_highSup hq.1 hν.1 hν.2 P s M
    unfold PointwisePrice.g at hb
    change (1-PointwisePrice.k ν)*M+ν*(P+s) ≤ M+PointwisePrice.highSup q P s M+s
    nlinarith

/-- All-real packed source for the literal nonlinear price. Count meshes are
chosen before the finite dictionary, while height degrees precede live heights. -/
theorem priced_source_of_whole_count
    (hwhole : NaturalCount.WholeJointCountOn (57/100))
    (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (qfun : ℝ → ℝ) (hq : ∀ w, qfun w ∈ Icc PointwisePrice.q0 (3/4))
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hB : 0 < B₀) (hB1 : B₀ ≤ 1) (hc : 0 < c₀)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (PointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq) (9/10) 4 4 :=
  AdaptiveSupplier.priced_source_of_whole_count hwhole
    PointwisePrice.q0 PointwisePrice.highSup high_law
    B₀ L₀ c₀ (9/10) 4 4 hL hβ ⟨hB,hB1,hc⟩ (by norm_num) (by norm_num) hp
    qfun hq (PointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq)
    (fun _ _ _ _ => rfl)

/-- Both old adaptive chains and the new nonlinear chain now require only
one explicit analytic input, the actual selected all-source norm estimate. -/
theorem priced_source (hnorm : NaturalCount.ActualSelectedSlotNorm)
    (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (qfun : ℝ → ℝ) (hq : ∀ w, qfun w ∈ Icc PointwisePrice.q0 (3/4))
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hB : 0 < B₀) (hB1 : B₀ ≤ 1) (hc : 0 < c₀)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (PointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq) (9/10) 4 4 :=
  priced_source_of_whole_count
    (NaturalCount.wholeJointCountOn_of_actualSelectedSlotNorm hnorm (57/100) le_rfl)
    B₀ L₀ c₀ hL qfun hq hβ hB hB1 hc hp

end
end Qrh.JointDetector.PointwiseSupplier

#print axioms Qrh.JointDetector.PointwiseSupplier.priced_source
#print axioms Qrh.JointDetector.AdaptiveSupplier.policyPackedProvider
