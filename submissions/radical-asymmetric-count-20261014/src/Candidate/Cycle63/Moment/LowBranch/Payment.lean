import Candidate.Cycle63.Moment.LowBranch.Main

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcreteTraceCRT CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

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

/-- The actual child width may be below the nominal width. The joint width
and deletion payment retains that deficit and leaves the exact low reserve. -/
theorem paid_low_exponent
    {b M width δ total padding εold buffer mesh : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-M ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-M ≤ M*Cycle63.Arithmetic.g b+6*(M*Cycle63.Arithmetic.amp b)+padding) :
    width+εold+buffer+(2*Cycle63.Arithmetic.q0/9)*max (total-width) 0+
        Cycle63.Arithmetic.q0*mesh ≤
      M+δ+M*Cycle63.Arithmetic.amp b-M*(7/30000000)+εold+buffer+
        (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh := by
  have hbnd := Cycle63.Physical.low_paid_excess_bound hb hM hwidth hδ hpad htotal
  have hid : total-M-(width-M) = total-width := by ring
  rw [hid] at hbnd
  linarith

/-- The second-transform nominal width is distinct from the original row
width which pays the amplifier and low reserve. Both are retained explicitly. -/
theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Cycle63.Arithmetic.g b+6*(M*Cycle63.Arithmetic.amp b)+padding) :
    width+εold+buffer+(2*Cycle63.Arithmetic.q0/9)*max (total-width) 0+
        Cycle63.Arithmetic.q0*mesh ≤
      nominal+δ+M*Cycle63.Arithmetic.amp b-M*(7/30000000)+εold+buffer+
        (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh := by
  have hbnd := Cycle63.Physical.low_paid_excess_bound hb hM hwidth hδ hpad htotal
  have hid : total-nominal-(width-nominal) = total-width := by ring
  rw [hid] at hbnd
  linarith

/-- The squared slot buffer can be made arbitrarily small after the finite
slot count is fixed. All three positive prime-estimate parameters are chosen
before live rows and heights. -/
theorem exists_buffer_parameters (N : ℕ) (d Rwidth error : ℝ)
    (hd : 0 < d) (hRw : 0 ≤ Rwidth) (he : 0 < error) :
    ∃ ε e κ : ℝ, 0 < ε ∧ 0 < e ∧ e < 1/1000 ∧ 0 < κ ∧
      8*e*Rwidth+κ ≤ ε ∧ 2*ε*d*(N:ℝ) ≤ error := by
  let ε := error/(4*d*((N:ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let e := min (ε/(32*(Rwidth+1))) (1/2000)
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hecap : e*(32*(Rwidth+1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hbudget : 8*e*Rwidth+ε/2 ≤ ε := by
    have hen : 0 ≤ e := he0.le
    nlinarith
  refine ⟨ε,e,ε/2,hε,he0,he1,by positivity,hbudget,?_⟩
  have hid : ε*(4*d*((N:ℝ)+1)) = error := div_mul_cancel₀ error (by positivity)
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- Move the finite slot buffer out of the constant and into its exact source
exponent; the remaining factor is fixed before the live base. -/
theorem buffer_power_identity (C Z ε d : ℝ) (N : ℕ) (hZ : 0 < Z) :
    (C*Z^(2*ε*d))^N = C^N*Z^(2*ε*d*(N:ℝ)) := by
  rw [mul_pow, ← Real.rpow_natCast (Z^(2*ε*d)) N, ← Real.rpow_mul hZ.le]

#print axioms energy_support_restriction
#print axioms paid_low_exponent
#print axioms exists_buffer_parameters
#print axioms buffer_power_identity
end
end OAI.SevenEighths.Cycle63Moment.LowBranch
