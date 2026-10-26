/- Copyright (c) 2026 Sil. Apache-2.0.
Finite outer-subset uniformity for the actual kept reference. Its
constants precede both T0 and every restoration subset inside T0.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RecenteredRootDispatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootReferenceFamily
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
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

private theorem cost_mono (s : Setup M H α) (ε : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (J0 J : ℕ) (hJ : J0 ≤ J) (S0 S : Finset (ℕ×ℕ)) (hS : S0 ⊆ S)
    (C0 C : ℝ) (hC0 : 0 ≤ C0) (hC : C0 ≤ C) :
    referenceCost M H s ε J0 S0 C0 Φ ≤ referenceCost M H s ε J S C Φ := by
  have hc (W : 𝓢(ℝ,ℂ)) : sourceControl S0 W ≤ sourceControl S W :=
    Seminorm.le_def.mp (Finset.sup_mono hS) W
  have hA0 : 0 ≤ sourceControl S0 (s.p.profile 0)*sourceControl S0 (s.p.profile 1) :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hA : sourceControl S0 (s.p.profile 0)*sourceControl S0 (s.p.profile 1) ≤
      sourceControl S (s.p.profile 0)*sourceControl S (s.p.profile 1) :=
    mul_le_mul (hc _) (hc _) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hA2 := pow_le_pow_left₀ hA0 hA 2
  have hHgt : 1 ≤ height 0 0 s.t s.t := by
    unfold height
    simp only [abs_zero,zero_add,add_zero]
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
theorem uniform_original_reference_family
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (Lcap ε : ℝ) (hLcap : 8 ≤ Lcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (η : Character) (bΦ : ℝ), 2 ≤ bΦ → ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H T0, s.Z=Z → s.W=W → s.Lcap=Lcap →
    ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
    RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s) →
    ∀ X Y : ℝ, 0 < X → 0 < Y → X*Y=s.Y₁*s.Y₂ →
      X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ →
      (X ≤ rootReference M H s ε ∨ Y ≤ rootReference M H s ε) →
    ∀ Q : Id, ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ → (∀ x, 0 ≤ (Φ x).re) → ∀ rows : Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤
      referenceCost M H s ε J control C Φ := by
  choose degrees controls constants hconstants hb using fun T0 : Finset α =>
    uniform_original_reference (α:=T0) M H hH W hW hWs Lcap ε hLcap hε
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
  intro η bΦ hbΦ
  have hevents := fun T0 : Finset α => hb T0 η bΦ hbΦ
  filter_upwards [Filter.eventually_all.mpr hevents,eventually_gt_atTop (1:ℝ)] with Z hfamily hZ
  refine ⟨hZ,?_⟩
  intro T0 s hsZ hsW hsLc hn₁ hn₂ hhigh X Y hX hY hXY hXU hYU hshort Q Φ hΦs hΦ rows
  have he := (hfamily T0).2 s hsZ hsW hsLc hn₁ hn₂ hhigh X Y hX hY hXY hXU hYU hshort Q Φ hΦs hΦ rows
  subst Z
  exact he.trans (cost_mono M H s ε Φ (degrees T0) J (hdegree T0)
    (controls T0) control (hcontrol T0) (constants T0) C (hconstants T0).le (hconstant T0))

end
end Candidate.FourthPower.RecenteredRootReferenceFamily
