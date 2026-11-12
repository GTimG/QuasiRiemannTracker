/- Copyright (c) 2026 Sil. Apache-2.0.
Finite outer-subset uniformity for the actual kept reference. Its
constants precede both T0 and every restoration subset inside T0.

Modified by Sil (2026-10-26): threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceFamily`; the reference lane
`hlane : ReferenceEnergyFine D` is threaded through, with `bΦ η η₀ Q0` (and the gates of `Q0`)
before the constants, `s.η₀ = η₀`, slot widths `≤ laneMesh`, slot frequencies `≤ V`,
`internalQ Q η₀ = Q0`, and `referenceCost … V`; the slot type lives in `Type`.
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootDispatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceFamily
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional
open MixedFirstReferenceEnergy MixedFirstProfileEnvelope
open RestoredRootEnergy RestoredInitialSource RecenteredRootSetup RecenteredRootRows
open RecenteredRootReferenceBound RecenteredRootDispatch
open Qrh.MarkedAnchor.Ordinary.Reference CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type} [Fintype α]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {D:Qrh.MarkedAnchor.Ordinary.StepData}(G:Qrh.MarkedAnchor.Ordinary.StepGates D)

private theorem cost_mono (s : Setup M H D α) (ε V : ℝ) (hV : 0 ≤ V) (Φ : 𝓢(ℝ,ℂ))
    (J0 J : ℕ) (hJ : J0 ≤ J) (S0 S : Finset (ℕ×ℕ)) (hS : S0 ⊆ S)
    (C0 C : ℝ) (hC0 : 0 ≤ C0) (hC : C0 ≤ C) :
    referenceCost M H G s ε J0 S0 C0 V Φ ≤ referenceCost M H G s ε J S C V Φ := by
  have hc (W : 𝓢(ℝ,ℂ)) : sourceControl S0 W ≤ sourceControl S W :=
    Seminorm.le_def.mp (Finset.sup_mono hS) W
  have hA0 : 0 ≤ sourceControl S0 (s.p.profile 0)*sourceControl S0 (s.p.profile 1) :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hA : sourceControl S0 (s.p.profile 0)*sourceControl S0 (s.p.profile 1) ≤
      sourceControl S (s.p.profile 0)*sourceControl S (s.p.profile 1) :=
    mul_le_mul (hc _) (hc _) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hA2 := pow_le_pow_left₀ hA0 hA 2
  have hHgt : 1 ≤ height 0 V s.t s.t := by
    unfold height
    simp only [abs_zero,add_zero]
    linarith [norm_nonneg s.t]
  have hHp := pow_le_pow_right₀ hHgt hJ
  have hCpos : 0 ≤ C := hC0.trans hC
  have hmain := mul_le_mul
    (mul_le_mul hC hA2 (sq_nonneg _) hCpos) hHp
    (pow_nonneg (zero_le_one.trans hHgt) _) (mul_nonneg hCpos (sq_nonneg _))
  unfold referenceCost
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (zero_lt_one.trans s.hZ).le _))
    (radial_control_nonneg Φ)

set_option maxHeartbeats 1000000 in
/-- This is the order required by the original initial-energy contract:
the finite ambient type is fixed, then one set of controls and constants,
then every original T0 and every restored root inside that T0. -/
theorem uniform_original_reference_family (hlane : ReferenceEnergyFine D)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (Lcap ε : ℝ) (hLcap : 8 ≤ Lcap) (hε : 0 < ε)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q0 : Id) [NeZero Q0]
    (hQt : Q0 ≠ ⊤) (hQ72 : Q0 ≤ Ideal.span {(72:O)}) (hQM : Q0 ≤ M) (hQη : Q0 ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H D T0, s.Z=Z → s.W=W → s.Lcap=Lcap → s.η₀=η₀ →
    (∀ i, s.w i ≤ laneMesh hlane (Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100)) → ∀ V : ℝ, 0 ≤ V → (∀ i, |s.v i| ≤ V) →
    ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
    D.s₀≤markedWidth M H s → Qrh.MarkedAnchor.Ordinary.RootParameters.NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s) →
    ∀ X Y : ℝ, 0 < X → 0 < Y → X*Y=s.Y₁*s.Y₂ →
      X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ →
      (X ≤ rootReference M H G s ε ∨ Y ≤ rootReference M H G s ε) →
    ∀ Q : Id, internalQ Q η₀ = Q0 →
    ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ → (∀ x, 0 ≤ (Φ x).re) → ∀ rows : Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤
      referenceCost M H G s ε J control C V Φ := by
  choose degrees controls constants hconstants hb using fun T0 : Finset α =>
    uniform_original_reference (α:=T0) M H hH G hlane W hW hWs Lcap ε hLcap hε
      bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  let J := ∑ T0 : Finset α, degrees T0
  let control := (Finset.univ : Finset (Finset α)).biUnion controls
  let C := 1+∑ T0 : Finset α, constants T0
  have hC : 0 < C := by
    have hp := Finset.sum_nonneg (fun T0 (_ : T0∈(Finset.univ : Finset (Finset α))) => (hconstants T0).le)
    dsimp only [C]
    linarith
  have hdegree (T0 : Finset α) : degrees T0 ≤ J :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ T0)
  have hcontrol (T0 : Finset α) : controls T0 ⊆ control :=
    Finset.subset_biUnion_of_mem controls (Finset.mem_univ T0)
  have hconstant (T0 : Finset α) : constants T0 ≤ C := by
    have hp := Finset.single_le_sum (s:=Finset.univ) (f:=constants)
      (fun T0 _ => (hconstants T0).le) (Finset.mem_univ T0)
    dsimp only [C]
    linarith
  refine ⟨J,control,C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb,eventually_gt_atTop (1:ℝ)] with Z hfamily hZ
  refine ⟨hZ,?_⟩
  intro T0 s hsZ hsW hsLc hsη hw V hV hv hn₁ hn₂ hs₀ hhigh X Y hX hY hXY hXU hYU hshort Q hQ Φ hΦs hΦ rows
  have he := (hfamily T0).2 s hsZ hsW hsLc hsη hw V hV hv hn₁ hn₂ hs₀ hhigh X Y hX hY hXY hXU hYU
    hshort Q hQ Φ hΦs hΦ rows
  subst Z
  exact he.trans (cost_mono M H G s ε V hV Φ (degrees T0) J (hdegree T0)
    (controls T0) control (hcontrol T0) (constants T0) C (hconstants T0).le (hconstant T0))

end
end Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceFamily
