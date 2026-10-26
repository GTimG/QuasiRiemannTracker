import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.TerminalLedger
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.LocalMoment.RestrictedIncumbent
import Mathlib
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily ConcreteTraceCRT CenteredMomentInductionEnergy

/-- Adding the literal radial support does not change the actual energy.
This permits conductor control without bounding all elements of `keep`. -/
theorem energy_support_restriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep low : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy χ m A t W₁ W₂ pool coeff P X₁ X₂ (fun z => keep z ∧ low z) Φ K =
    energy χ m A t W₁ W₂ pool coeff P X₁ X₂
      (fun z => keep z ∧ (Φ (‖eisEmbedding z‖^2/K) ≠ 0 ∧ low z)) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hp : Φ (‖eisEmbedding z‖^2/K) = 0
  · simp [hp]
  · by_cases hk : keep z <;> by_cases hl : low z <;> simp [hp,hk,hl]

variable [Cycle63.AffineLedger] in
/-- The second-transform nominal width is distinct from the original row
width which pays the amplifier and low reserve. Both are retained explicitly. -/
theorem paid_low_exponent_shifted [Cycle63.AffineLedger.DeletesIntoOldRegion]
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Cycle63.AffineLedger.g b+6*(M*Cycle63.AffineLedger.amp b)+padding) :
    width+εold+buffer+Cycle63.AffineLedger.lowRate*max (total-width) 0+
        Cycle63.AffineLedger.q*mesh ≤
      nominal+δ+M*Cycle63.AffineLedger.amp b-M*(Cycle63.AffineLedger.lowReserve)+εold+buffer+
        Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh := by
  have hbnd := Cycle63.Physical.low_paid_excess_bound hb hM hwidth hδ hpad htotal
  have hid : total-nominal-(width-nominal) = total-width := by ring
  rw [hid] at hbnd
  linarith

/-- Move the finite slot buffer out of the constant and into its exact source
exponent; the remaining factor is fixed before the live base. -/
theorem buffer_power_identity (C Z ε d : ℝ) (N : ℕ) (hZ : 0 < Z) :
    (C*Z^(2*ε*d))^N = C^N*Z^(2*ε*d*(N:ℝ)) := by
  rw [mul_pow, ← Real.rpow_natCast (Z^(2*ε*d)) N, ← Real.rpow_mul hZ.le]

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
