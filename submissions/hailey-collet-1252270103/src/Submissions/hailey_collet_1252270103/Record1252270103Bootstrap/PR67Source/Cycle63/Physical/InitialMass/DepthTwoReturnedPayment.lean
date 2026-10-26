import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoReturnedCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighClassPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The payment of the returned HIGH parts of many first-level rows: with every class paying the reserve of its
second-step parent and every row paying the first-level reserve, the weighted sum of the count forms is at most the
target times `Z` to minus the margin of the two-level ledger plus the losses. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle63.Physical Cycle63.Optimization LocalMoment
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The returned HIGH parts of the rows of a finite set, one per orientation of the second level and row, paid
against the target `Z^E₀`. Per row `r`: the weight is at most `Z^(E₀ + X0 r + price (target r + mesh))`; the
first-level coordinates `X0 X1 X2 X3` pay the first-level reserve at every bin `δ ∈ [secondJunction, 3/4]` with saving
`γ₁ r ≥ 0`; the missing radical `X1 r` lies in `[0, B]` and the rows over one ideal with `X1 ≤ m₁` number at most
`Apre Z^m₁`; the energy scale, length and amplifier of the second-step parent satisfy the scale identity, the volume
after the deletion and the amplifier bound of the two-level ledger in the parent's cell `cell r`; and the losses are
at most `Lmax`. Every record has at most `K` classes and pays the reserve of its parent. Then the weighted sum of the
count forms is at most `C (1+T)^J Apre K Z^(E₀ - highTwoMargin + Lmax + width (3 + 4B) + loss)`. The degree `J`
precedes the dictionary and the character, and the constants precede the rows and both heights. -/
theorem depth_two_returned_payment {Base : Type} [Fintype Base]
    (B loss width : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) (hwidth : 0 < width) :
    ∃ J : ℕ, ∀ (base : Base → Character) (η₀ : Character), ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (unit : Bool → P → FirstSourceLabel → O) (Z T : ℝ), 2 ≤ Z → 0 ≤ T →
      ∀ R : ∀ b p, SecondStepHighCount M H hH base η₀ Z B T b (v p) (unit b p),
      ∀ (rows : Finset P) (W : P → ℝ) (Apre K E₀ Lmax : ℝ)
        (cell scale length amp X0 X1 X2 X3 m₁ A₁ a₁ small₁ γ₁ deleted target : P → ℝ)
        (loss₂ κ mesh pad price ω : ℝ),
      (∀ r ∈ rows, 0 ≤ W r) → 0 ≤ Apre → 0 ≤ K →
      (∀ r ∈ rows, 0 ≤ X1 r ∧ X1 r ≤ B) →
      (∀ m : ℝ, ∀ D : Ideal O,
        (((rows.filter (fun r => X1 r ≤ m)).filter (fun r => Ideal.span {v r} = D)).card : ℝ) ≤ Apre*Z^m) →
      (∀ b, ∀ r ∈ rows, (Fintype.card (R b r).Class : ℝ) ≤ K) →
      (∀ b, ∀ r ∈ rows, (R b r).Pays secondJunction (scale r) (length r) (amp r) loss₂) →
      (∀ r ∈ rows, W r ≤ Z^(E₀ + X0 r + price*(target r + mesh))) →
      (∀ r ∈ rows, ∀ δ, secondJunction ≤ δ → δ ≤ 3/4 →
        X0 r + X1 r + density δ*X2 r + δ*X3 r ≤
          small₁ r - (m₁ r*(1 - density δ) - δ*A₁ r - a₁ r*amplifierCost δ) - γ₁ r) →
      (∀ r ∈ rows, 0 ≤ γ₁ r) →
      (∀ r ∈ rows, scale r + Real.logb Z ((Ideal.span {v r}).absNorm : ℝ) ≤ X2 r + κ) →
      (∀ r ∈ rows, length r ≤ X3 r - deleted r + pad) →
      (∀ r ∈ rows, fixedDeletion (cell r) ≤ target r ∧ target r ≤ deleted r) →
      (∀ r ∈ rows, firstCellTop ≤ cell r ∧ cell r ≤ slotTop) →
      (∀ r ∈ rows, 1 ≤ m₁ r ∧ A₁ r ≤ twoLevelTotalA (cell r) ∧ a₁ r ≤ firstAmp (cell r) ∧
        amp r ≤ secondAmp (cell r) + ω) →
      (∀ r ∈ rows, ∀ δ, secondJunction ≤ δ → δ ≤ 3/4 →
        small₁ r + loss₂ + density δ*κ + δ*pad + price*mesh + (price - firstJunction)*target r +
          amplifierCost δ*ω ≤ Lmax) →
        ∑ r ∈ rows, W r*∑ b, (R b r).value ≤
          C*(1+T)^J*Apre*K*Z^(E₀ - highTwoMargin + Lmax + width*(3 + 4*B) + loss) := by
  obtain ⟨J, hJ⟩ := depth_two_returned_sum (Base := Base) M H hH B loss width hB hloss hwidth
  refine ⟨J, fun base η₀ => ?_⟩
  obtain ⟨C, hC, hsum⟩ := hJ base η₀
  refine ⟨C, hC, ?_⟩
  intro P v unit Z T hZ hT R rows W Apre K E₀ Lmax cell scale length amp X0 X1 X2 X3 m₁ A₁ a₁ small₁ γ₁ deleted
    target loss₂ κ mesh pad price ω hW hApre hK hX1 hpre hcard hpays hweight h₁ hγ₁ hscale hvol hdel hcell hcaps
    hLmax
  have hZ0 : 0 < Z := by linarith
  have hq := secondJunction_mem
  have hzero : ∀ b, ∀ r ∈ rows, ∀ σ, 4/5 ≤ (R b r).zeroBin σ ∧ (R b r).zeroBin σ ≤ 7/8 := by
    intro b r hr σ
    have hp := hpays b r hr σ
    constructor <;> linarith [hp.1, hp.2.1]
  have hpay : ∀ b, ∀ r ∈ rows, ∀ σ, W r*Z^((R b r).exponent σ + (R b r).missExp σ +
      unmarkedDensity (2*(R b r).zeroBin σ - 1)*(R b r).rowExp σ + X1 r) ≤
        Z^(E₀ - highTwoMargin + Lmax) := by
    intro b r hr σ
    have hp := hpays b r hr σ
    have hδ : secondJunction ≤ 2*(R b r).zeroBin σ - 1 ∧ 2*(R b r).zeroBin σ - 1 ≤ 3/4 := ⟨hp.1, hp.2.1⟩
    have hpair := second_step_class_pair_bound M H hH (R b r) (hpays b r hr) le_rfl σ (hcell r hr)
      (h₁ r hr _ hδ.1 hδ.2) (hγ₁ r hr) (hscale r hr) (hvol r hr) (hdel r hr).1 (hdel r hr).2 (hcaps r hr).1
      (hcaps r hr).2.1 (hcaps r hr).2.2.1 (hcaps r hr).2.2.2 (mesh := mesh) (price := price)
    have hL := hLmax r hr _ hδ.1 hδ.2
    rw [density_eq_unmarkedDensity] at hpair
    calc W r*Z^((R b r).exponent σ + (R b r).missExp σ +
          unmarkedDensity (2*(R b r).zeroBin σ - 1)*(R b r).rowExp σ + X1 r)
        ≤ Z^(E₀ + X0 r + price*(target r + mesh))*Z^((R b r).exponent σ + (R b r).missExp σ +
          unmarkedDensity (2*(R b r).zeroBin σ - 1)*(R b r).rowExp σ + X1 r) :=
          mul_le_mul_of_nonneg_right (hweight r hr) (Real.rpow_nonneg hZ0.le _)
      _ = Z^(E₀ + (X0 r + X1 r + (R b r).exponent σ + (R b r).missExp σ +
          unmarkedDensity (2*(R b r).zeroBin σ - 1)*(R b r).rowExp σ + price*(target r + mesh))) := by
          rw [← Real.rpow_add hZ0]
          congr 1
          ring
      _ ≤ Z^(E₀ - highTwoMargin + Lmax) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          rw [density_eq_unmarkedDensity] at hL
          linarith only [hpair, hL]
  exact hsum v unit Z T hZ hT R rows W X1 Apre K (E₀ - highTwoMargin + Lmax) hW hX1 hApre hK hpre hcard hzero hpay

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
