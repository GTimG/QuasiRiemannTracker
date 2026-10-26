/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed pre-slot loss and post-cardinality buffer instantiate the actual
HIGH source with one consistent set of numerical geometry budgets. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularHighParameters
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalAnalyticParametersHeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Admission
local notation "O"=>HeckeFamily.O

def regularParameters (W:ℝ→ℂ)(θ εslot:ℝ)(J:ℕ)(bound:ℕ→ℝ)
    (hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
    (hθ:0<θ)(hes:0<εslot)(hb:∀k,0≤bound k):HighSourceParameters:=
  actualPhysicalParameters W 1 1 εslot θ 2 40 20 1 100 (1/100) J bound
    hWs hW (by norm_num) (by norm_num) hes hθ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb

theorem regular_parameters_height (W:ℝ→ℂ)(θ εslot:ℝ)(J:ℕ)(bound:ℕ→ℝ)
    (hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
    (hθ:0<θ)(hes:0<εslot)(hb:∀k,0≤bound k):
    let P:=regularParameters W θ εslot J bound hWs hW hθ hes hb
    P.τ<(1/100:ℝ)/2 ∧ 4*P.τ<(1/100:ℝ)*(θ/16) ∧
      2*P.τ<(1/100:ℝ)*(εslot/4) ∧ 16*P.τ≤P.d*P.vplain ∧ 8*P.τ≤P.d*P.vslot ∧
      2*P.τ*(J+1)≤θ/16 ∧ 2*P.τ<100*(εslot/4):=by
  have h:=physical_height_spec J θ (1/100) 100 εslot hθ (by norm_num) (by norm_num) hes
  dsimp only [regularParameters,actualPhysicalParameters,highParameters]
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2,
    h.2.2.2.1.trans_le (by nlinarith only [hes])⟩

variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (reserve θ mesh amp:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hm:0≤mesh)(hmesh:100*mesh≤θ)(hamp:0<amp)
variable (R₀:Ideal O)(hR₀:R₀≠0)
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)

/-- The source degree is selected first; the same positive height exponent
and actual parameter record are then supplied to the HIGH and LOW branches. -/
def regular_some_control_supply (high:Source)
    (hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ) :=
  let hs:=regular_some_source (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh amp N wmin rmin εslot hf hc hm hmesh hamp R₀ hR₀ hβ hβhi high hB0 hB1 hlam hcap0 hcap1 hparent
  let bound:=Classical.choose hs
  let hb:= (Classical.choose_spec hs).1
  let hj:= (Classical.choose_spec hs).2
  let J:=Classical.choose hj
  let hJ:=Classical.choose_spec hj
  let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  let ht:=regular_parameters_height W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  hJ P.τ P.hτ ht.1 ht.2.1 ht.2.2.1 P rfl rfl rfl le_rfl le_rfl
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters]) rfl rfl
    ht.2.2.2.2.1 ht.2.2.2.1
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])

/-- The source degree is selected first; the same positive height exponent
and actual parameter record are then supplied to the HIGH and LOW branches. -/
def regular_natural_control_supply
    (hparent:100*mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) θ) :=
  let hs:=regular_natural_source (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh amp N wmin rmin εslot hf hc hm hmesh hamp R₀ hR₀ hβ hβhi hparent
  let bound:=Classical.choose hs
  let hb:= (Classical.choose_spec hs).1
  let hj:= (Classical.choose_spec hs).2
  let J:=Classical.choose hj
  let hJ:=Classical.choose_spec hj
  let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  let ht:=regular_parameters_height W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  hJ P.τ P.hτ ht.1 ht.2.1 ht.2.2.1 P rfl rfl rfl le_rfl le_rfl
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters]) rfl rfl
    ht.2.2.2.2.1 ht.2.2.2.1
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_parameters_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_some_control_supply
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_natural_control_supply
