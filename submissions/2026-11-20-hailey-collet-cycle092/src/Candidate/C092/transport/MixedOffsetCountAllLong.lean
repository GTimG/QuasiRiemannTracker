/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine last amplified inverse pays the all-long bank class. -/
import Candidate.C092.transport.MixedOffsetCountBankFacts
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

/-- The final-offset count is obtained from the original inverse supplier,
not assumed. The saturated inverse may vary by row; native dyads/zero and
full source profiles remain those of the actual last bank fiber. -/
theorem actual_all_long_count (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D) :
    ∃Ki : ℝ,0 ≤ Ki ∧ ∃Ji : ℕ,∀η : Character,∃Ci : ℝ,0<Ci ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (d a t₀ γ T allowance height : ℝ) (i : ℕ),
      (1/200:ℝ) ≤ d → 1/2 ≤ a → 2*a-1 ≤ 3/4 → D.ε ≤ 1/10000000 →
      1 ≤ t₀-γ → t₀-γ ≤ 3/2 → 0 ≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T ≤ height →
    ∀ (P : Presented D S η Z d a (t₀-γ) T allowance i) (F : Slice P),
      1 ≤ F.fiber.r → ∀common : Finset FreeRow,common⊆F.fiber.rows →
    let U:=Z^d
    let v:=5/6-(2*a-1)
    let R:=1/6+v*t₀
    let C:=max 1 (12*(1+height)*((Ci*(1+height)^Ji)*Ki))
    let loss:=countLoss D.ε P.batch.mesh D.t
    (common.card:ℝ) ≤ C*U^(R-v*γ+loss) ∧
    ∀q₀ : ℝ,4*q₀/3 ≤ v*γ → (common.card:ℝ) ≤ C*U^(R-4*q₀/3+loss) := by
  obtain ⟨Ki,hKi,Ji,hsource⟩:=QRH.Cycle092.DirectCount.source_inverse_fiber_count D S
  refine ⟨Ki,hKi,Ji,?_⟩
  intro η
  obtain ⟨Ci,hCi,hsource⟩:=hsource η
  refine ⟨Ci,hCi,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d a t₀ γ T allowance height i hd ha hδhi hεhi ht ht' hh hf P F hlong common hsub
  dsimp only
  have hU : 1<Z^d:=Real.one_lt_rpow hZ.1 (by linarith)
  have hg:=F.fiber.lengths hU
  have hr2 : F.fiber.r ≤ 2:=by linarith [hg.2.1]
  have hc:=hZ.2 d hd a D.ε (t₀-γ) T allowance i P.batch P.data P.profile P.upper P.widths P.real
    F.bin F.label F.left F.right F.nonempty height hh ha hf (by linarith) hr2
  have hsubCard : (common.card:ℝ) ≤ (F.fiber.rows.card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
  have hv : 0 ≤ 5/6-(2*a-1):=by linarith only [hδhi]
  have hvhi : 5/6-(2*a-1) ≤ 1:=by linarith only [ha]
  have hupper:=mul_le_mul_of_nonneg_left hg.2.1 hv
  have hcollar:=mul_le_mul_of_nonneg_right hvhi D.epsilon_pos.le
  have hE : sourceExponent F.fiber.r-(2*a-1)*F.fiber.r+2*D.ε+D.t ≤
      (1/6+(5/6-(2*a-1))*t₀)-(5/6-(2*a-1))*γ+countLoss D.ε P.batch.mesh D.t := by
    unfold sourceExponent
    rw [max_eq_right (by linarith only [hlong] : (1:ℝ) ≤ (1+5*F.fiber.r)/6)]
    unfold countLoss
    nlinarith only [hupper,hcollar,D.epsilon_pos,D.t_pos,P.batch.mesh_nonneg]
  let C:=max 1 (12*(1+height)*((Ci*(1+height)^Ji)*Ki))
  have hC : 0 ≤ C:=zero_le_one.trans (le_max_left _ _)
  have hraw : 12*(1+height)*((Ci*(1+height)^Ji)*Ki) ≤ C:=le_max_right _ _
  have hp : (common.card:ℝ) ≤ C*(Z^d)^((1/6+(5/6-(2*a-1))*t₀)-
      (5/6-(2*a-1))*γ+countLoss D.ε P.batch.mesh D.t) :=
    (hsubCard.trans hc).trans
      ((mul_le_mul_of_nonneg_right hraw (Real.rpow_nonneg (zero_lt_one.trans hU).le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hE) hC))
  refine ⟨hp,?_⟩
  intro q₀ hq
  apply hp.trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le ?_) hC
  linarith only [hq]

#print axioms actual_all_long_count
end
end QRH.Cycle092.MixedOffsetCount
