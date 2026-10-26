/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Marked.GeometryRawBudget
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle153MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Cycle63MarkedPlain

/-- The same native root cutoff dominates through 2/3. The former top
was the crossing of a particular affine ledger, rather than a source
restriction on the marked detector. -/
theorem native_dominantRoot_anti :
    StrictAntiOn (fun d=>Cycle63.Optimization.dominantRoot d)
      (Set.Icc Cycle63.Optimization.firstJunction (2/3:ℝ)) ∧
    ContinuousOn (fun d=>Cycle63.Optimization.dominantRoot d)
      (Set.Icc Cycle63.Optimization.firstJunction (2/3:ℝ)) := by
  unfold_ledger_channels
  rat_mono [Cycle63.Optimization.junction_enclosure]

theorem native_ledger_dominance {δ : ℝ}
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤(2/3:ℝ)) :
    Cycle63.Optimization.capCoefficient δ*(1-6*Cycle63.Optimization.markedRootCutoff)≤
      Cycle63.Optimization.markedRootCutoff*
        (6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack) := by
  have hd : δ∈Set.Icc Cycle63.Optimization.firstJunction (2/3:ℝ) := hδ
  have hJ : Cycle63.Optimization.firstJunction∈Set.Icc Cycle63.Optimization.firstJunction (2/3:ℝ) := by
    refine ⟨le_rfl,?_⟩
    linarith [Cycle63.Optimization.junction_enclosure.2]
  have hr : Cycle63.Optimization.dominantRoot δ≤ Cycle63.Optimization.markedRootCutoff :=
    native_dominantRoot_anti.1.antitoneOn hJ hd hδ.1
  have hpos : 0<(6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack)+
      6*Cycle63.Optimization.capCoefficient δ := by
    unfold_ledger_channels
    rat_pos [hd,Cycle63.Optimization.junction_enclosure]
  unfold Cycle63.Optimization.dominantRoot at hr
  rw [div_le_iff₀ hpos] at hr
  linarith

theorem marked_tail_dominates (D ρ ordloss S δ : ℝ) (hD : 0≤ D)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤(2/3:ℝ))
    (hρ : Cycle63.Optimization.density δ≤ρ) (hord : 0≤ ordloss) :
    min (Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D))
      (D*markedRootCutoff*(6*(ρ+ordloss)-1-Cycle63.Optimization.tailSlack))=
      Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D) := by
  apply min_eq_left
  unfold markedRootCutoff
  have hd0 : 0≤δ := by linarith [Cycle63.Arithmetic.q0_bounds.1]
  have hd : δ≤(3/4:ℝ) := by linarith
  have hcap := Cycle63.Optimization.markedGain_le_capacity (S:=S)
    (F:=(1-6*Cycle63.Optimization.markedRootCutoff)*D) hd0 hd
  have hdom := mul_le_mul_of_nonneg_left (native_ledger_dominance hδ) hD
  have hk := Cycle63.Optimization.markedRootCutoff_bounds
  have htail := mul_le_mul_of_nonneg_left
    (show 6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack≤
      6*(ρ+ordloss)-1-Cycle63.Optimization.tailSlack by linarith)
    (mul_nonneg hD (by linarith [hk.1] : (0:ℝ)≤ Cycle63.Optimization.markedRootCutoff))
  calc
    _ ≤ Cycle63.Optimization.capCoefficient δ*((1-6*Cycle63.Optimization.markedRootCutoff)*D) := hcap
    _ = D*(Cycle63.Optimization.capCoefficient δ*(1-6*Cycle63.Optimization.markedRootCutoff)) := by ring
    _ ≤ D*(Cycle63.Optimization.markedRootCutoff*
        (6*Cycle63.Optimization.density δ-1-Cycle63.Optimization.tailSlack)) := hdom
    _ ≤ _ := by linarith [htail]

/-- Every raw analytic fee is paid at the actual supplied width cap.
No old ledger's slotTop or unmarked crossing enters this inequality. -/
theorem marked_raw_error_budget (D S Smax ρ mesh μ normfee heightfee : ℝ)
    (hD : D≤130) (hS : S≤ Smax) (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤ Cycle63.Optimization.geometryLossCap)
    (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*markedRate+2*markedBinWidth*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ+normfee+heightfee≤
      Cycle63.Optimization.markedLossAt Smax := by
  norm_num [markedRate,markedBinWidth,Cycle63.Optimization.markedBinWidth,markedPad,
    Cycle63.Optimization.markedRate,Cycle63.Optimization.markedPad,Cycle63.Optimization.markedLossAt,
    Cycle63.Optimization.geometryLossCap,Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.allowanceUnit,Cycle63.Optimization.planeQuadratic,
    Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound] at hmesh hμ ⊢
  linarith

theorem marked_raw_exponent_paid (D S Smax ρ δ mesh μ normfee heightfee : ℝ)
    (hD0 : 0≤ D) (hD : D≤130) (hS : S≤ Smax)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤(2/3:ℝ))
    (hρδ : Cycle63.Optimization.density δ≤ρ) (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤ Cycle63.Optimization.geometryLossCap)
    (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ-
      min (Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D))
        (D*markedRootCutoff*(6*(ρ+markedRate)-1-Cycle63.Optimization.tailSlack))+normfee+heightfee≤
      D*ρ+δ*S-Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D)+
        Cycle63.Optimization.markedLossAt Smax := by
  rw [marked_tail_dominates D ρ markedRate S δ hD0 hδ hρδ
    (by norm_num [markedRate,Cycle63.Optimization.markedRate,Cycle63.Optimization.geometryLossCap,
      Cycle63.Optimization.lowReserveWeight,Cycle63.Optimization.allowanceUnit,
      Cycle63.Optimization.planeQuadratic,Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound])]
  have h := marked_raw_error_budget D S Smax ρ mesh μ normfee heightfee hD hS hρ hmesh hμ hnorm hheight
  nlinarith

end
end OAI.SevenEighths.Cycle153MarkedPlain

#print axioms OAI.SevenEighths.Cycle153MarkedPlain.native_ledger_dominance
#print axioms OAI.SevenEighths.Cycle153MarkedPlain.marked_raw_exponent_paid
