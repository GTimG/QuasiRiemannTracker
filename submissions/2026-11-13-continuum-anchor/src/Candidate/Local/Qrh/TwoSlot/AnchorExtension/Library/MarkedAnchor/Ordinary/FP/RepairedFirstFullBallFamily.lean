/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform full-ball energy bounds over the finite root types from the
summed raw-side input First.SummedRetainedRawSides. Constants and eventual bounds are chosen
before the moving root index.
Modified by Sil (2026-10-26): the family premise is First.SummedRetainedRawSides (balanced summed Seam 0) instead of the replaced per-divisor RetainedRawSides; statement otherwise unchanged.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedFirstFullBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedFirstFullBallFamily
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open RepairedFirstFullBall
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqFullBallFamily {κ : Type*} : DecidableEq κ := Classical.decEq _

set_option maxHeartbeats 800000 in
theorem fullBallCost_of_raw_sides_family
    (Index : Type v) [Fintype Index] (Slot : Index → Type u) [∀k,Fintype (Slot k)]
    (N J : ℕ) (hcard : ∀k,Fintype.card (Slot k) ≤ N)
    (cRad Cp ξ κ εmass εout : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0 < Cp) (hξ : 0 < ξ) (hκ : 0 < κ)
    (hεmass : 0 < εmass) (hεout : 0 < εout) :
    ∀η : Character,∃Cfull : ℝ,0 < Cfull ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀k : Index,∀s : Source (Slot k) (1/4) (9/4),s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) → sourceVolume s ≤ Z^(8:ℝ) →
    ∀A loss : ℝ,0 ≤ A → (profileCap s)^2 ≤ Cp*A → loss+εmass ≤ εout →
      First.SummedRetainedRawSides s (by norm_num) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z)‖/sourceVolume s ≤ Cfull*A*Z^(1+εout) := by
  intro η
  choose constants hconstants hb using fun k : Index =>
    fullBallCost_of_raw_sides (ι:=Slot k) N J cRad Cp ξ κ εmass εout hcRad hCp hξ hκ hεmass hεout η
  let C := 1+∑k : Index,constants k
  have hC : 0 < C := by
    have hp := Finset.sum_nonneg (fun k (_ : k∈(Finset.univ : Finset Index)) => (hconstants k).le)
    dsimp only [C]
    linarith
  have hc (k : Index) : constants k ≤ C := by
    have hp := Finset.single_le_sum (s:=Finset.univ) (f:=constants)
      (fun k _ => (hconstants k).le) (Finset.mem_univ k)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb,eventually_gt_atTop (1:ℝ)] with Z hfamily hZ
  refine ⟨hZ,?_⟩
  intro k s hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol A loss hA hprofile hloss hsides
  have he := (hfamily k).2 s (hcard k) hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol
    A loss hA hprofile hloss hsides
  apply he.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc k) hA)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedFirstFullBallFamily
