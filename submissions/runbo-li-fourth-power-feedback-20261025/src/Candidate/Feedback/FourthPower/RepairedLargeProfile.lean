/- Copyright (c) 2026 Sil. Apache-2.0.
Condense the explicitly paid large root budget to one homogeneous
ordinary-profile product and one independent-height degree. All constants
precede the root and first/supplier data.
-/
import Candidate.Feedback.FourthPower.RepairedLargeFirstCost
import Candidate.Feedback.FourthPower.RepairedSmallCommonProfile
import Candidate.Feedback.FourthPower.RepairedSmallSideAlgebra

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedLargeProfile
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass CenteredMomentSecondWindowBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice CenteredMomentFirstAmplificationChoice
open EisensteinSchwartzPoisson
open MixedPrincipalPair MixedOriginalTail MixedFirstProfileEnvelope
open RepairedRawContext RepairedSupplierProfiles RepairedRawReference
open RepairedLargeSupplierBudget RepairedPaidFirstBudget
open RepairedSmallCommonProfile RepairedSmallSideAlgebra
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def degree (U : RepairedLargeSupplierBudget.Controls) : ℕ := U.nonexceptionalDegree+2*U.exceptionalDegree
def control (U : RepairedLargeSupplierBudget.Controls) : Finset (ℕ×ℕ) :=
  ({(0,0)}∪U.nonexceptionalControl)∪U.exceptionalControl

theorem control_zero (U : RepairedLargeSupplierBudget.Controls) : (0,0) ∈ control U := by
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
theorem control_nonexceptional (U : RepairedLargeSupplierBudget.Controls) : U.nonexceptionalControl ⊆ control U := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
theorem control_exceptional (U : RepairedLargeSupplierBudget.Controls) : U.exceptionalControl ⊆ control U :=
  Finset.subset_union_right

variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem envelope_profile (s : Source ι a b) (N : ℕ) (Kslot : ℝ) (hKslot : 1 ≤ Kslot)
    (U : RepairedLargeSupplierBudget.Controls) (t₀ V tp : ℝ) (hV : 0 ≤ V) :
    (RepairedSupplierProfiles.profileEnvelope s N Kslot U.exceptionalDegree U.exceptionalControl 1 0)^2*
      heightBase tp^(2*U.exceptionalDegree) ≤
      (markedCap N Kslot)^2*commonProfile s (degree U) (control U) t₀ V tp := by
  have hh : 1+‖s.t₁‖+‖s.t₂‖ ≤ height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀]
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+‖s.t₁‖+‖s.t₂‖) hh (2*U.exceptionalDegree)
  have hp := profile_powers_le s (2*U.exceptionalDegree) (2*U.exceptionalDegree) (degree U)
    U.exceptionalControl (control U) t₀ V tp (control_exceptional U) (by unfold degree; omega)
    (by unfold degree; omega) hV
  have hprofile : (sourceControl U.exceptionalControl s.W₁*sourceControl U.exceptionalControl s.W₂)^2*
      (1+‖s.t₁‖+‖s.t₂‖)^(2*U.exceptionalDegree)*heightEnvelope tp^(2*U.exceptionalDegree) ≤
        commonProfile s (degree U) (control U) t₀ V tp := by
    apply le_trans _ hp
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) (pow_nonneg (heightEnvelope_pos tp).le _)
  have he := mul_le_mul_of_nonneg_left hprofile (sq_nonneg (markedCap N Kslot))
  have hjpow : ((1+‖s.t₁‖+‖s.t₂‖)^U.exceptionalDegree)^2 =
      (1+‖s.t₁‖+‖s.t₂‖)^(2*U.exceptionalDegree) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    _ = (markedCap N Kslot)^2*
        ((sourceControl U.exceptionalControl s.W₁*sourceControl U.exceptionalControl s.W₂)^2*
          (1+‖s.t₁‖+‖s.t₂‖)^(2*U.exceptionalDegree)*heightEnvelope tp^(2*U.exceptionalDegree)) := by
      unfold RepairedSupplierProfiles.profileEnvelope
      simp only [Real.one_rpow,mul_one,mul_pow,hjpow,show heightBase tp=heightEnvelope tp by rfl]
      ring
    _ ≤ _ := he

theorem core_profile (s : Source ι a b) (N : ℕ) (Kslot : ℝ) (hKslot : 1 ≤ Kslot)
    (U : RepairedLargeSupplierBudget.Controls) (t₀ V tp : ℝ) (hV : 0 ≤ V) :
    profileCore s Kslot N U.nonexceptionalDegree U.nonexceptionalControl t₀ tp V ≤
      (Kslot^(2*N)*(profileMoment U.nonexceptionalDegree)^2)*
        commonProfile s (degree U) (control U) t₀ V tp := by
  have hp := profile_powers_le s U.nonexceptionalDegree (2*U.nonexceptionalDegree) (degree U)
    U.nonexceptionalControl (control U) t₀ V tp (control_nonexceptional U)
    (by unfold degree; omega) (by unfold degree; omega) hV
  have he := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (pow_nonneg (zero_le_one.trans hKslot) (2*N))
      (sq_nonneg (profileMoment U.nonexceptionalDegree)))
  convert he using 1 <;> first | rfl | (dsimp only [profileCore]; ring)

variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}

theorem uniform_root_profile (N : ℕ) (Kslot : ℝ) (hKslot : 1 ≤ Kslot)
    (U : RepairedLargeSupplierBudget.Controls) (c : RepairedLargeSupplierBudget.Constants) :
    ∃ C : ℝ,1 ≤ C ∧
    ∀ (ι : Type u) [Fintype ι],Fintype.card ι ≤ N →
    ∀ (Wslot : ℝ → ℂ) (Holes : ℕ) (ε Z : ℝ) (η η₀ : Character),
    ∀ d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀,∀ tp : ℝ,
      rootBudget d U c tp ≤
      C*(sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U) := by
  let Cz := c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(4*(Kslot^N)^2)*
    (2:ℝ)^(2*N)*(9/4:ℝ)^2*Kslot^(2*N)
  let Cn := c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
    (Kslot^(2*N)*(profileMoment U.nonexceptionalDegree)^2)*Kslot^(2*N)
  let Ce := c.exceptional*selectedCap N Kslot*(markedCap N Kslot)^2*
    slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ)
  let Ct := c.tail*selectedCap N Kslot*(4*(Kslot^N)^2)*Kslot^(2*N)
  have hcz := c.zero_pos
  have hcn := c.nonexceptional_pos
  have hce := c.exceptional_pos
  have hct := c.tail_pos
  have hk : 0 ≤ Kslot := zero_le_one.trans hKslot
  have hselected : 0 ≤ selectedCap N Kslot := by unfold selectedCap; positivity
  have hCz : 0 ≤ Cz := by dsimp only [Cz,selectedCap]; positivity
  have hCn : 0 ≤ Cn := by dsimp only [Cn]; positivity
  have hCe : 0 ≤ Ce := by dsimp only [Ce,selectedCap,slotShapeCap,markedCap]; positivity
  have hCt : 0 ≤ Ct := by dsimp only [Ct,selectedCap]; positivity
  let C₀ := 256*(Cz+Cn+Ce+Ct)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  let C := 1+C₀*heightEnvelope 0^(2*degree U)
  have hC : 1 ≤ C := by
    have hh := mul_nonneg hC₀ (pow_nonneg (heightEnvelope_pos 0).le (2*degree U))
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro ι instι hcard Wslot Holes ε Z η η₀ d tp
  have hdV := d.hV
  let P := commonProfile d.root (degree U) (control U) d.t₀ d.V tp
  have hP : 0 ≤ P := common_profile_nonneg _ _ _ _ _ _ d.hV
  have hp := profile_cap_le d.root N (degree U) Kslot (control U) (control_zero U)
    d.t₀ d.V tp hcard hKslot d.hM d.hV
  have hn := core_profile d.root N Kslot hKslot U d.t₀ d.V tp d.hV
  have he := envelope_profile d.root N Kslot hKslot U d.t₀ d.V tp d.hV
  have hz : rootZero d c ≤ Cz*P := by
    unfold rootZero
    calc
      _ ≤ c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*((4*(Kslot^N)^2)*P)*
          (2:ℝ)^(2*N)*(9/4:ℝ)^2*Kslot^(2*N) := by gcongr
      _ = _ := by dsimp only [Cz]; ring
  have hnc : rootNonexceptional d U c tp ≤ Cn*P := by
    unfold rootNonexceptional
    calc
      _ ≤ c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
          ((Kslot^(2*N)*(profileMoment U.nonexceptionalDegree)^2)*P)*Kslot^(2*N) := by gcongr
      _ = _ := by dsimp only [Cn]; ring
  have hec : rootExceptional d U c tp ≤ Ce*P := by
    have hf : 0 ≤ c.exceptional*selectedCap N Kslot*slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ) := by
      unfold selectedCap slotShapeCap
      positivity
    have hh := mul_le_mul_of_nonneg_left he hf
    convert hh using 1 <;> dsimp only [rootExceptional,Ce] <;> ring
  have htc : rootTail d c ≤ Ct*P := by
    unfold rootTail
    calc
      _ ≤ c.tail*selectedCap N Kslot*((4*(Kslot^N)^2)*P)*Kslot^(2*N) := by gcongr
      _ = _ := by dsimp only [Ct]; ring
  have hall : rootBudget d U c tp ≤ C₀*P := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hz hnc) hec) htc)
      (by norm_num : (0:ℝ) ≤ 256)
    convert hh using 1 <;> dsimp only [rootBudget,C₀] <;> ring
  have hv := pow_le_pow_left₀ (heightEnvelope_pos tp).le (height_envelope_le_zero tp) (2*degree U)
  rw [mul_pow] at hv
  have hheight : 0 ≤ height d.t₀ d.V d.root.t₁ d.root.t₂ := by unfold height; positivity
  have hprofile : P ≤ heightEnvelope 0^(2*degree U)*
      ((sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U)) := by
    have hh := mul_le_mul_of_nonneg_left hv
      (mul_nonneg
        (sq_nonneg (sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂))
        (pow_nonneg hheight (degree U)))
    convert hh using 1 <;> first | rfl | ((try dsimp only [P,commonProfile]); ring)
  apply hall.trans
  have hbase : 0 ≤ (sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U) := by positivity
  calc
    _ ≤ C₀*(heightEnvelope 0^(2*degree U)*
        ((sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
          (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U))) :=
      mul_le_mul_of_nonneg_left hprofile hC₀
    _ ≤ C*((sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
          (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U)) := by
      have hc : C₀*heightEnvelope 0^(2*degree U) ≤ C := by dsimp only [C]; linarith
      convert mul_le_mul_of_nonneg_right hc hbase using 1 <;> ring
    _ = _ := by ring

end
end Candidate.Feedback.FourthPower.RepairedLargeProfile
