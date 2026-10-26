import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondStepReturnProof
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondStepMesh
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificateValues
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelCell
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The return of the second step at the parameters of the first level: the explicit losses, mesh and presentation of
the second step, from which the numeric hypotheses of the general theorem follow. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentEnergyState

/-- The dictionary rate of the schedule of the second step for `n` slots. -/
def secondStepDictionaryRate (n : ℕ) : ℝ :=
  geometryFinalDictionaryRate secondStepLossUnit 31 3 4 3 130 (3 * ((n : ℝ) + 2)) n

/-- The loss that the HIGH given of the second step needs: `(13/8)` of the loss unit and `9 n + 282` dictionary
rates. -/
def secondStepLossNeeded (n : ℕ) : ℝ := 13 / 8 * secondStepLossUnit + (9 * (n : ℝ) + 282) * secondStepDictionaryRate n

/-- The least loss of the second step: the width `101/100` times the loss needed and the loss of the old moment. -/
def secondStepLossFloor (εaffine : ℝ) (n : ℕ) : ℝ := 101 / 100 * (secondStepLossNeeded n + secondStepOldLoss εaffine)

/-- The presentation of the states of the second step at the first level: the states are presented by their child
multipliers at the height `Z ^ τT`, their punctures have norm at most `Z ^ 8` and their multipliers have norm at
most `Z ^ Bv`. -/
def secondStepPresented (τT Bv : ℝ) :
    Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop :=
  fun η Z s v T => (DepthTwoPresented τT η Z s v T ∧ (s.puncture.absNorm : ℝ) ≤ Z ^ (8 : ℝ)) ∧
    ((Ideal.span {v}).absNorm : ℝ) ≤ Z ^ Bv

/-- The dictionary rate of the second step is positive, at most `1/128` of the loss unit, and at most the loss unit
over `2048 (n + 1)`. -/
theorem secondStepDictionaryRate_bounds (n : ℕ) :
    0 < secondStepDictionaryRate n ∧ secondStepDictionaryRate n ≤ secondStepLossUnit / 128 ∧
      secondStepDictionaryRate n ≤ secondStepLossUnit / (2048 * ((n : ℝ) + 1)) := by
  obtain ⟨h1, -, h3, -⟩ := geometry_final_dictionary_budgets secondStepLossUnit 31 3 4 3 130
    (3 * ((n : ℝ) + 2)) n secondStepLossUnit_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  refine ⟨h1, h3, (min_le_right _ _).trans_eq ?_⟩
  norm_num

theorem secondStepLossNeeded_nonneg (n : ℕ) : 0 ≤ secondStepLossNeeded n := by
  have h1 := secondStepLossUnit_pos
  have h2 := (secondStepDictionaryRate_bounds n).1
  have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold secondStepLossNeeded
  positivity

/-- The loss needed by the HIGH given of the second step is at most twice its loss unit, for every number `n` of
slots: the `9 n + 282` dictionary rates are at most `282/2048` of the loss unit. -/
theorem secondStepLossNeeded_le (n : ℕ) : secondStepLossNeeded n ≤ 2 * secondStepLossUnit := by
  have hμ := secondStepLossUnit_pos
  have hr := (secondStepDictionaryRate_bounds n).2.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (9 * (n : ℝ) + 282) * secondStepDictionaryRate n ≤
      (9 * (n : ℝ) + 282) * (secondStepLossUnit / (2048 * ((n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have h2 : (9 * (n : ℝ) + 282) * (secondStepLossUnit / (2048 * ((n : ℝ) + 1))) ≤ 282 * secondStepLossUnit / 2048 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hμ.le hn]
  unfold secondStepLossNeeded
  linarith

/-- The loss of the old moment is at most `1/10^11` at the first step of the two-level ledger: the loss unit is at most
`1/128` of the LOW reserve of the first step, which is below `10⁻⁹`. -/
theorem secondStepOldLoss_le [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger] (εaffine : ℝ) :
    secondStepOldLoss εaffine ≤ 1 / 10 ^ 11 := by
  have h1 : geometryLossUnit 1 εaffine ≤ Cycle63.AffineLedger.lowReserve * 1 / 128 := by
    unfold geometryLossUnit
    exact (min_le_right _ _).trans (min_le_left _ _)
  have h2 := firstLowReserve_enclosure.2
  rw [lowReserve_eq] at h1
  unfold secondStepOldLoss
  rw [div_div, div_le_iff₀ (by norm_num)]
  norm_num at h2 ⊢
  linarith

/-- The least loss of the second step is at most `1/10^9`. -/
theorem secondStepLossFloor_le [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger] (εaffine : ℝ) (n : ℕ) :
    secondStepLossFloor εaffine n ≤ 1 / 10 ^ 9 := by
  have h1 := secondStepLossNeeded_le n
  have h2 := secondStepOldLoss_le εaffine
  have h3 := secondStepLossUnit_le
  have h4 : secondStepAffineLoss = 1 / 10 ^ 10 := rfl
  unfold secondStepLossFloor
  nlinarith [h1, h2]

/-- The second step's return at the parameters of the first level: the plain profiles of the class `(1/4, 9/4)`, the
mask `28`, the plain cap `1`, the window `[1, 2]`, the zeros of height `33/50`, the largest width `101/100`, and the loss
`εold = μ/8` of the old moment, for the loss unit `μ = geometryLossUnit 1 εaffine` of the first level. The slot bound
`Lslot` of the first level is at most `2/5` of the mesh `secondStepMesh` of the second step. The second step runs the
schedule of the affine loss `secondStepAffineLoss`, in the unit base of a state, whose mask `20` is `5/2` of the mask `8`
of the punctures of the presented states. The labels of the HIGH given have the cap `130 + 5/2 Bv`, so that the
multipliers of norm at most `Z ^ Bv` are presented, and `Bnorm` is at least `101/100` of it. The states have the
presentation `secondStepPresented τT Bv` and the least loss `secondStepLossFloor εaffine n`, which is at most `10^-9`.
The generic step `hcontract` and the producer `hproducer` of the HIGH given are the hypotheses of the general
theorem. -/
theorem second_step_return_first_level {α : Type} [Fintype α] [DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (εaffine τT Bv Bnorm Lslot : ℝ) (G : ℕ) (hεaffine : 0<εaffine) (hG : 0<G) (hτT : 0<τT) (hBv : 0≤Bv)
    (hBnorm : 101/100*(130+5/2*Bv)≤Bnorm) (hslot : 5/2*Lslot ≤ secondStepMesh εaffine)
    (hcontract : ∀ g : GeometryAffineLowSchedule,
      GeometryAffineAtStateStatement (α:=α) M H hH W hW hWs hβlo hβhi g secondStepAffineLoss
        (1/4) (9/4) 2 20 (secondStepMesh εaffine) (secondStepOldLoss εaffine))
    (hproducer : DepthTwoHighGivenStatement (α:=α) M H hH W hW hWs hβlo hβhi secondStepAffineLoss
      (1/4) (9/4) 2 20 (secondStepMesh εaffine) (τT/(101/100)) (130+5/2*Bv)
      (secondStepLossNeeded (Fintype.card α))) :
    SecondStepReturnAt (α:=α) M H hH fourFixedDictionary W 2 (1/4) (9/4) 2 28 1 Lslot (33/50) (33/50) (101/100)
      (geometryLossUnit 1 εaffine/8) Bnorm
      (SecondApplicable G (secondStepLossFloor εaffine (Fintype.card α)) (secondStepPresented τT Bv)) := by
  have hε₂ : 0 < secondStepAffineLoss := secondStepAffineLoss_pos
  have hεold : 101/100*secondStepOldLoss εaffine ≤ geometryLossUnit 1 εaffine/8 := by
    refine le_of_eq ?_
    unfold secondStepOldLoss
    field_simp
  have hfloor : ∀ i : Cycle63.SecondIndex G, secondStepMesh εaffine <
      @Cycle63.AffineLedger.amplifierFloor (Cycle63.secondFamily G i)/2 := by
    intro i
    have h1 := Cycle63.lowReserveWeight_le_secondFamily_amplifierFloor G i
    have h2 := secondStepMesh_le_reserveWeight εaffine
    have h3 := Cycle63.Optimization.lowReserveWeight_pos
    linarith
  have hres : ∀ i : Cycle63.SecondIndex G, 128*geometryLossUnit 1 secondStepAffineLoss ≤
      @Cycle63.AffineLedger.lowReserve (Cycle63.secondFamily G i) := by
    intro i
    have h1 := Cycle63.secondFamily_lowReserve_ge G i
    have h2 : geometryLossUnit 1 secondStepAffineLoss ≤ secondStepAffineLoss/128 :=
      min_le_left _ _
    have h3 : secondStepAffineLoss ≤ 1/10^10 := le_rfl
    linarith
  have h3δ : 3*geometryFinalDictionaryRate (geometryLossUnit 1 secondStepAffineLoss) 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α)≤Cycle63.Optimization.lowReserveWeight := by
    have h1 := (secondStepDictionaryRate_bounds (Fintype.card α)).2.1
    have h2 := secondStepLossUnit_le
    have h3 : secondStepAffineLoss = 1 / 10 ^ 10 := rfl
    have hlw : Cycle63.Optimization.lowReserveWeight = 1 / 10 ^ 8 := by
      norm_num [Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit]
    show 3 * secondStepDictionaryRate (Fintype.card α) ≤ _
    linarith
  exact second_step_return M H hH W hW hWs hβlo hβhi secondStepAffineLoss (1/4) (9/4) 2 28 20 8 Bv 1
    Lslot (33/50) (33/50) (101/100) (geometryLossUnit 1 εaffine/8) (secondStepOldLoss εaffine)
    (secondStepMesh εaffine) τT (secondStepLossFloor εaffine (Fintype.card α)) (130+5/2*Bv)
    (secondStepLossNeeded (Fintype.card α)) Bnorm G (secondStepPresented τT Bv) hG hε₂ (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) hBv (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (secondStepOldLoss_pos hεaffine) hεold (secondStepMesh_pos hεaffine).le hslot (by positivity)
    (by linarith) hBnorm (secondStepLossNeeded_nonneg _) le_rfl hfloor hres (secondStepMesh_le_dictionary _)
    (secondStepMesh_le_producer _) (secondStepMesh_le_oldMoment _) h3δ (fun _ _ _ _ _ h => ⟨h.1.1, h.1.2, h.2⟩)
    hcontract hproducer

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
