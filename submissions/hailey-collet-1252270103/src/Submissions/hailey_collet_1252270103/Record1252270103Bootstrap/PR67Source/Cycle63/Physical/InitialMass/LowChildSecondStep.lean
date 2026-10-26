import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildLevelOne
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondStepFirstLevel
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineAtStateProof
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedParameterSchedule
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Row 5 of the first step of the two-level ledger from the second step's return: the second step at the parameters
of the first level, with the moment at a natural state as its generic step. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion Cycle63MarkedPlain
open Cycle63Moment Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The norm cap of the multipliers of the children that the second step serves at the first level: `Mcap + 5 Bnorm +
ε + 1` at the width cap `101/100`, the label cap `4` and the shell slack `δ`. -/
def levelOneMultiplierCap (δ : ℝ) : ℝ := 101/100+5*4+δ+1

/-- The label cap of the records returned by the second step at the first level. -/
def levelOneReturnedCap : ℝ := 190

/-- The height exponent of the presented children of the first level, for the modulus `M` and the dictionary rate
`δ`: `levelOneTau` at the label cap `levelOneReturnedCap` of the returned records. -/
def levelOneHeight (δ : ℝ) : ℝ :=
  levelOneTau ((RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)) M H hH levelOneReturnedCap δ

theorem levelOneHeight_pos {δ : ℝ} (hδ : 0 < δ) : 0 < levelOneHeight M H hH δ := by
  unfold levelOneHeight levelOneTau
  have h : (0:ℝ) ≤ (returnedHeightDegree ((RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)) M H hH
    levelOneReturnedCap (δ / 6) (δ / (6 * (3 + 4 * levelOneReturnedCap))) : ℝ) := Nat.cast_nonneg _
  positivity

/-- Row 5 of the first step of the two-level ledger for the modulus `M`, with the second step as its input.

The schedule `g` has the loss unit `geometryLossUnit 1 εaffine`; the slot bound `Lslot` is at most the common mesh
`commonMesh (101/100) 28 1 (g.μ/8)` and `5/2` of it at most the mesh `secondStepMesh εaffine` of the second step. The
frequency losses are at most `ωmax = g.μ/4`, the presentation is `levelOnePresented` at the
height exponent `levelOneHeight`, and the second step runs on the grid of `10¹²` points with the loss floor `10⁻⁹`.
The generic step of the second step is `actual_geometry_affine_at_state`; the producer `hproducer` of its HIGH given is
the hypothesis. -/
theorem lowSelectedPaidAt_first_level [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger]
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (εaffine : ℝ) (hεaffine : 0<εaffine) (g : GeometryAffineLowSchedule) (hgμ : g.μ=geometryLossUnit 1 εaffine)
    (Lslot : ℝ) (hLslot : Lslot≤Cycle25.Energy.commonMesh (101/100) 28 1 (g.μ/8))
    (hslot : 5/2*Lslot ≤ secondStepMesh εaffine)
    (hproducer : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
      (hWs : Function.support W⊆Set.Icc (1:ℝ) 2),
      DepthTwoHighGivenStatement (α:=α) M H hH W hW hWs hβlo hβhi secondStepAffineLoss (1/4) (9/4) 2 20
        (secondStepMesh εaffine) (levelOneHeight M H hH g.δ/(101/100))
        (130+5/2*levelOneMultiplierCap g.δ) (secondStepLossNeeded (Fintype.card α))) :
    LowSelectedPaidAt M H hH g (101/100) Lslot (fun u om _ => u=1 ∧ om≤g.μ/4) lowSideExponent
      (levelOnePresented (levelOneHeight M H hH g.δ)) := by
  have hμ : g.μ≤Cycle63.Optimization.geometryLossCap := hgμ ▸ geometry_loss_below_marked_cap εaffine
  have hcap : g.μ≤1/(128*10^8) := hμ.trans geometryLossCap_le
  have hτ := levelOneHeight_pos M H hH g.δ_pos
  have hδ1 : g.δ≤1 := by linarith [g.δ_cap, g.μ_cap]
  have hBv : 0≤levelOneMultiplierCap g.δ := by
    unfold levelOneMultiplierCap
    linarith [g.δ_pos]
  have hBnorm : 101/100*(130+5/2*levelOneMultiplierCap g.δ)≤levelOneReturnedCap := by
    unfold levelOneMultiplierCap levelOneReturnedCap
    linarith
  refine lowSelectedPaidAt_two_level M H hH fourFixedDictionary g hμ (10^12) le_rfl (g.μ/4) (1/10^9)
    (levelOneHeight M H hH g.δ) (by linarith [g.μ_pos]) (by norm_num at hcap ⊢; linarith) le_rfl Lslot hLslot
    levelOneReturnedCap (by norm_num [levelOneReturnedCap]) (levelOneTau_spec _ M H hH _ g.δ_pos.le) ?_
  intro α _ _ W hW hWs
  have hstep := second_step_return_first_level (α:=α) M H hH W hW hWs hβlo hβhi εaffine (levelOneHeight M H hH g.δ)
    (levelOneMultiplierCap g.δ) levelOneReturnedCap Lslot (10^12) hεaffine (by norm_num) hτ hBv hBnorm hslot
    (fun g' => actual_geometry_affine_at_state (α:=α) M H hH W hW hWs hβlo hβhi g' secondStepAffineLoss 2 20
      (secondStepMesh εaffine) (secondStepOldLoss εaffine))
    (hproducer W hW hWs)
  rw [hgμ]
  exact SecondStepReturnAt.mono
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => SecondApplicable.mono (secondStepLossFloor_le _ _) (fun _ _ _ _ _ h' => h') h)
    hstep

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
