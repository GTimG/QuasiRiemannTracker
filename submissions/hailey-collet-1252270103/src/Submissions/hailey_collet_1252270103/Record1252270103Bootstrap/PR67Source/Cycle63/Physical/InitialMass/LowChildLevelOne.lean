import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildTwoLevelRow5
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildFactsTwoLevel
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelRate
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificateValues
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoPresented
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Row 5 at the parameters of the first step of the two-level ledger: the selected low frequency columns of the final
daughters of the LOW children, at the unit one, the mask `28`, the plain scales `1/4` and `9/4` and the losses of the
schedule of the first step, from the second step as the only open input. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalNatural

/-- The predicate that presents the final daughters of the LOW children of the first step: a final daughter is
presented in the sense of `DepthTwoPresented` at the height `Z^τT`, and the puncture of its state has norm at most
`Z^8`. This is the predicate of `geometryLowChildrenPresented_depthTwo` at the cap `8` of the puncture. -/
def levelOnePresented (τT : ℝ) (Bmask : ℝ) (η : Character) (Z : ℝ) (s : NaturalState Z Bmask 2) (v : O) (T : ℝ) :
    Prop :=
  DepthTwoPresented τT η Z s v T ∧ (s.puncture.absNorm : ℝ) ≤ Z ^ (8 : ℝ)

/-- A state presented by `levelOnePresented` has the height of its zeros in `[0, Z^τT]`. -/
theorem levelOnePresented_range {τT Bmask : ℝ} {η : Character} {Z : ℝ} {s : NaturalState Z Bmask 2} {v : O}
    {T : ℝ} (h : levelOnePresented τT Bmask η Z s v T) : 0 ≤ T ∧ T ≤ Z ^ τT :=
  ⟨(Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) τT).trans h.1.1.1, h.1.1.2⟩

/-- The degree of the height of the returned parts at the first step is absorbed by the height exponent
`δ/(6 (J + 1))`: `J` times this exponent is at most `δ/6`. -/
theorem degree_mul_tau_le (J : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : (J : ℝ) * (δ / (6 * ((J : ℝ) + 1))) ≤ δ / 6 := by
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h : (J : ℝ) * (δ / (6 * ((J : ℝ) + 1))) = δ / 6 * ((J : ℝ) / ((J : ℝ) + 1)) := by
    field_simp
  rw [h]
  exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity))

/-- The geometry loss unit of the schedule is at most `1/(128·10⁸)`. -/
theorem geometryLossCap_le : Cycle63.Optimization.geometryLossCap ≤ 1 / (128 * 10 ^ 8) := by
  have h : 0 ≤ (1 / 2) / Cycle63.Optimization.slotPrice :=
    div_nonneg (by norm_num) Cycle63.Optimization.slotPrice_pos.le
  unfold Cycle63.Optimization.geometryLossCap Cycle63.Optimization.lowReserveWeight
    Cycle63.Optimization.allowanceUnit
  norm_num
  linarith

/-- The slacks of the grid and of the amplifier of `twoLevelCertificates_of_small` are not negative. -/
theorem twoLevel_slacks_nonneg {G : ℕ} {ωmax εpad : ℝ} (hG : 0 < G) (hω : 0 ≤ ωmax) (hpad : 0 ≤ εpad) :
    0 ≤ Cycle63.Optimization.secondSlope / G ∧
      0 ≤ Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1 Cycle63.Optimization.secondJunction *
          (2 * ωmax + εpad) +
        Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1 Cycle63.Optimization.secondJunction *
          (1 + 6 * Cycle63.Optimization.slotPrice) / G := by
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hslope := Cycle63.Optimization.secondSlope_bounds
  have hK := Cycle63.Optimization.secondAmplifierRatio_bounds
  have hprice := Cycle63.Optimization.slotPrice_mem
  have hK0 : 0 ≤ Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1
      Cycle63.Optimization.secondJunction := by linarith [hK.1]
  refine ⟨div_nonneg (by linarith [hslope.1]) hGr.le, ?_⟩
  have h1 := mul_nonneg hK0 (by linarith : 0 ≤ 2 * ωmax + εpad)
  have h2 : 0 ≤ Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1
      Cycle63.Optimization.secondJunction * (1 + 6 * Cycle63.Optimization.slotPrice) / G :=
    div_nonneg (mul_nonneg hK0 (by linarith [hprice.1])) hGr.le
  linarith


/-- The height exponent of the returned parts at the first step: `δ/(6 (J + 1))`, where `J` is the degree of the
payment of the returned parts for the label cap `Bret` of their records and the losses `δ/6`, `δ/(6 (3 + 4 Bret))`. -/
def levelOneTau (Base : Type) [Fintype Base] (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (Bret δ : ℝ) : ℝ :=
  δ / (6 * ((returnedHeightDegree Base M H hH Bret (δ / 6) (δ / (6 * (3 + 4 * Bret))) : ℝ) + 1))

/-- The degree of the payment of the returned parts times the height exponent `levelOneTau` is at most `δ/6`: the
hypothesis `hJτ` of row 5 at the first step. -/
theorem levelOneTau_spec (Base : Type) [Fintype Base] (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (Bret : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (returnedHeightDegree Base M H hH Bret (δ / 6) (δ / (6 * (3 + 4 * Bret))) : ℝ) * levelOneTau Base M H hH Bret δ ≤
      δ / 6 :=
  degree_mul_tau_le _ hδ

set_option linter.unusedVariables false in
/-- Row 5 at the parameters of the first step of the two-level ledger, for the modulus `M`, from the second step as the
only open input.

The schedule `g` has the geometry loss unit `g.μ` at most `geometryLossCap`. The width cap is `Mcap = 101/100`, the
grid of the second step has `G ≥ 10¹²` points, the frequency loss is at most `ωmax ≤ 10⁻¹⁰` and the loss floor of
the second step at most `10⁻⁹`. The presentation is `levelOnePresented τT`, with a height exponent `τT` such that the
degree `J` of the payment of the returned parts of the modulus satisfies `J τT ≤ δ/6` (`levelOneTau`). The second step
`stepTwo` is the contract `SecondStepReturnAt` at the class of the first step and at the slot bound `Lslot`, for every
slot type and smooth slot profile supported in `[1, 2]`, for the children whose multipliers have norm at most
`Z^(101/100 + 5·4 + δ + 1)`, with returned records of label cap `Bret ≥ 4`. The slot bound `Lslot` is at most the
common mesh `commonMesh (101/100) 28 1 (g.μ/8)` (`hLslot`).
Everything else is discharged: the certificates by `twoLevelCertificates_of_small`, the rate and the reflection loss by
`two_level_absorption`, and the facts of the first level by `lowReturnedFacts_two_level` with the numeric condition
`twoLevelReturnedBudget`. -/
theorem lowSelectedPaidAt_two_level [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {Base : Type} [Fintype Base] (base : Character → Base → Character)
    (g : GeometryAffineLowSchedule) (hμ : g.μ ≤ Cycle63.Optimization.geometryLossCap)
    (G : ℕ) (hG : 10 ^ 12 ≤ G) (ωmax lossFloor τT : ℝ) (hω0 : 0 ≤ ωmax) (hω1 : ωmax ≤ 1 / 10 ^ 10)
    (hloss : lossFloor ≤ 1 / 10 ^ 9) (Lslot : ℝ)
    (hLslot : Lslot ≤ Cycle25.Energy.commonMesh (101 / 100) 28 1 (g.μ / 8)) (Bret : ℝ) (hBret : 4 ≤ Bret)
    (hJτ : (returnedHeightDegree Base M H hH Bret (g.δ / 6) (g.δ / (6 * (3 + 4 * Bret))) : ℝ) * τT ≤ g.δ / 6)
    (stepTwo : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : ℝ → ℂ), ContDiff ℝ ∞ W →
      Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
      SecondStepReturnAt (α := α) M H hH base W 2 (1 / 4) (9 / 4) 2 28 1
        Lslot (33 / 50) (33 / 50) (101 / 100) (g.μ / 8) Bret
        (SecondApplicable G lossFloor (fun η Z s v T => levelOnePresented τT 28 η Z s v T ∧
          ((Ideal.span {v}).absNorm : ℝ) ≤ Z ^ (101 / 100 + 5 * 4 + g.δ + 1)))) :
    LowSelectedPaidAt M H hH g (101 / 100) Lslot (fun u om _ => u = 1 ∧ om ≤ ωmax) lowSideExponent
      (levelOnePresented τT) := by
  intro α _ _ W hWs hW hbeta Cs hCs
  have hμ0 := g.μ_pos
  have hδ0 := g.δ_pos
  have hδcap := g.δ_cap
  have hcap : g.μ ≤ 1 / (128 * 10 ^ 8) := hμ.trans geometryLossCap_le
  have hμ8 : g.μ / 8 ≤ 1 / 10 ^ 10 := by
    norm_num at hcap ⊢
    linarith
  have hδ10 : g.δ ≤ 1 / 10 ^ 10 := by
    norm_num at hcap ⊢
    linarith
  have hG6 : 1000000 ≤ G := le_trans (by norm_num) hG
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG6
  have hsmall : 2 * ωmax + g.μ / 8 ≤ 9 / 10000000 := by
    norm_num at hω1 hμ8 ⊢
    linarith
  have hcert0 := twoLevelCertificates_of_small (G := G) (εpad := g.μ / 8) (ωmax := ωmax) hG6 hω0 hsmall
  have e : (1 : ℝ) + 1 / 100 = 101 / 100 := by norm_num
  rw [e] at hcert0
  obtain ⟨hgrid0, hamp0⟩ := twoLevel_slacks_nonneg (G := G) (ωmax := ωmax) (εpad := g.μ / 8) hGpos hω0
    (by linarith)
  have habs := two_level_absorption (L := Cycle63.Arithmetic.firstLevelLedger) (εpad := g.μ / 8) (Mmin := 1)
    (by linarith) one_pos
  have hnum := twoLevelReturnedBudget (Led := Cycle63.Arithmetic.firstLevelLedger) (G := G) (ωmax := ωmax)
    (ε := g.δ) (lossFloor := lossFloor) (εpad := g.μ / 8) (εwidth := g.μ / 8) (εold := g.μ / 8) (εlabels := g.δ)
    hG hω0 hω1 hδ10 hloss (by linarith) hμ8 (by linarith) (by linarith) hδ0.le
  have hfacts := lowReturnedFacts_two_level (α := α) M H hH W 2 (1 / 4) (9 / 4) 28 1 Lslot (33 / 50) (33 / 50) (101 / 100)
    (g.μ / 8) 1 g.τ g.δ g.e g.vslot 31 (9 / 4) (g.μ / 8) (g.μ / 8) 1 g.δ (Fintype.card α) Cs 1 g.δ 4 g.δ ωmax
    (levelOnePresented τT 28) lossFloor _ _ hδ0 (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by linarith) one_pos (by linarith) hδ0.le hgrid0 hamp0 hnum
  exact lowSelectedStmt_two_level (α := α) M H hH W 1 2 (1 / 4) (9 / 4) 28 1 Lslot (33 / 50) (33 / 50) (101 / 100)
    (g.μ / 8) (by norm_num) hWs hW (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by linarith) hLslot hbeta 1 31 g.τ g.δ g.e g.κ g.vslot 1 31 (by norm_num) (by norm_num) g.τ_pos hδ0 g.e_pos g.e_cap
    g.κ_pos g.vslot_nonneg (by simpa only [mul_one] using g.budget) (by norm_num) (by norm_num) (by norm_num) le_rfl
    (9 / 4) (g.μ / 8) (g.μ / 8) 1 g.δ (by norm_num) (by linarith) (by linarith) (by norm_num) hδ0
    (Fintype.card α) G Cs 1 g.δ 4 g.δ ωmax (1 / 1000) (7 / 2500) (reflectionLoss (g.μ / 8) 1) lossFloor _ _ hCs
    (by norm_num) hδ0 (by norm_num) hδ0 (by norm_num) (by norm_num) habs.1 le_rfl hcert0 base
    (levelOnePresented τT 28) Bret hBret (stepTwo W hW hWs) τT (fun η Z st v Tz h => levelOnePresented_range h) hJτ habs.2.1 habs.2.2
    hfacts

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
