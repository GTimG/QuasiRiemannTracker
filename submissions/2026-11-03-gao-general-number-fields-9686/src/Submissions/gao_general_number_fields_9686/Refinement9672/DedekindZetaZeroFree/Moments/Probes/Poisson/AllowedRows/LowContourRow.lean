/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/AllowedRows/LowContourRow.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowContourShifts

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RowLowContourRow

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.PoissonKernel
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowTriple (Fu : D.Row → ℂ → ℂ → ℂ → ℂ) (u : D.Row) (x y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral x (fun ξ =>
    comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => kernelWith D Fu u ξ w z Z)))

theorem row_initial_eq (u : D.Row) (hu : u.u ≠ 1) (U Z : ℝ) (hU : 2 ≤ U) (hZ : 2 ≤ Z)
    (hq : U ≤ D.q u ∧ D.q u < 2 * U) :
    rowTriple D (rowFactor D) u 4 4 2 Z =
      rowTriple D (fun u ξ w z =>
        D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ) u
        Scales.rightLine Scales.wLine Scales.zLine Z := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hf : (fun (u : D.Row) (ξ w z : ℂ) =>
      D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ) =
      PoissonKernel.rowFactor D := by
    funext u ξ w z
    unfold PoissonKernel.rowFactor
    ring
  rw [hf]
  unfold rowTriple
  exact LowRowContourShifts.triple_shift_K D u hu Z hZ0

theorem row_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row), u.u ≠ 1 → ∀ (U Z : ℝ), 2 ≤ U → 2 ≤ Z →
      U ≤ D.q u → D.q u < 2 * U →
      ‖rowTriple D (fun u ξ w z =>
        D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ) u
        Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε) := by
  obtain ⟨A_F, ρ, hA, hconv, -⟩ := DetectorHeight.detector_height_exists D
  obtain ⟨C, hC, hdec⟩ := RowKernelGrowth.wzIntegral_decay_right D A_F hconv ε hε 2 two_pos
  have hI : MeasureTheory.Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2:ℝ))) :=
    integrable_one_add_norm (μ := MeasureTheory.volume) (by norm_num)
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) :=
    MeasureTheory.integral_nonneg (fun t => by positivity)
  refine ⟨(2 * Real.pi)⁻¹ * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) * C + 1, ?_, ?_⟩
  · have : 0 ≤ (2 * Real.pi)⁻¹ * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) * C := by
      apply mul_nonneg (mul_nonneg (by positivity) hI0) hC.le
    linarith
  · intro u hu U Z hU hZ hUq hUq2
    have hZ0 : (0 : ℝ) < Z := by linarith
    have hf : (fun (u : D.Row) (ξ w z : ℂ) =>
        D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ) =
        PoissonKernel.rowFactor D := by
      funext u ξ w z
      unfold PoissonKernel.rowFactor
      ring
    rw [hf]
    have hent : RowKernelGrowth.EntireNumerator D u :=
      RowAnalyticContinuation.exists_entire_numerator D u hu
    have hdec' := hdec U hU u hu hent hUq hUq2
    have hE : (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1))
        = Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := rfl
    have hUe : (17 / 40 : ℝ) + ε - Scales.zLine = 1 / 40 + ε := by unfold Scales.zLine; ring
    have key : ∀ t : ℝ, ‖PoissonKernel.wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I)
        Scales.wLine Scales.zLine Z‖ ≤
        (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε)) *
          (1 + ‖t‖) ^ (-(2:ℝ)) := by
      intro t
      have h := hdec' t Z hZ0
      rw [hE, hUe] at h
      rw [Real.norm_eq_abs]
      calc _ ≤ _ := h
        _ = _ := by ring
    have hJ := MeasureTheory.norm_integral_le_of_norm_le
      (hI.const_mul (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε)))
      (Filter.Eventually.of_forall key)
    rw [MeasureTheory.integral_const_mul] at hJ
    have hc : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
      simp [norm_inv, norm_mul, Real.pi_pos.le]
    have hP : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε) := by
      positivity
    show ‖DedekindZetaZeroFree.comparisonVerticalIntegral Scales.rightLine (fun ξ =>
      PoissonKernel.wzIntegral D u ξ Scales.wLine Scales.zLine Z)‖ ≤ _
    unfold DedekindZetaZeroFree.comparisonVerticalIntegral
    rw [norm_mul, hc]
    have hJ' : ‖∫ t : ℝ, PoissonKernel.wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I)
        Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε) *
          (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) := hJ
    have h2 : (2 * Real.pi)⁻¹ * ‖∫ t : ℝ, PoissonKernel.wzIntegral D u
        ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        (2 * Real.pi)⁻¹ * (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε) *
          (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)))) :=
      mul_le_mul_of_nonneg_left hJ' (by positivity)
    have hfin : (2 * Real.pi)⁻¹ * (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
        U ^ (1 / 40 + ε) * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)))) =
        ((2 * Real.pi)⁻¹ * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) * C) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε)) := by ring
    have hlast : ((2 * Real.pi)⁻¹ * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) * C) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε)) ≤
        ((2 * Real.pi)⁻¹ * (∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) * C + 1) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 40 + ε)) := by
      apply mul_le_mul_of_nonneg_right (by linarith) hP
    exact le_trans h2 (le_trans (le_of_eq hfin) (le_trans hlast (le_of_eq (by ring))))

end

end DedekindZetaZeroFree.Quantitative.RowLowContourRow

end Refinement9672
