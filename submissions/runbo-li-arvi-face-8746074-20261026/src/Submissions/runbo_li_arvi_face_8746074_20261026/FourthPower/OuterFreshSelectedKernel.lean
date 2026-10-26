/- Copyright (c) 2026 Sil. Apache-2.0.
Original positive selected weights, their product fibers, and the common
angle envelope. All normalization and selected-dependent masks are explicit.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshWeightedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Candidate.FourthPower.OuterFreshSelectedKernel
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstPhysicalSource CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentSecondLiveBlock CenteredMomentSecondDyadicRowSupport
open CenteredMomentSecondEnergySplit CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondWindowBudget CenteredMomentLogDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedLiveNormalization
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierOuterActive MixedSupplierSource
open MixedSupplierOriginalFrequency
open MixedFirstProfileEnvelope MixedFirstChosenEnergy
open OuterFreshWindowPair OuterFreshConsumer OuterFreshBlock OuterFreshRows
open OuterFreshNonexceptionalFamily OuterFreshStructure OuterFreshSelectedWindow
open OuterFreshPairedAllocatedWindow OuterFreshAllocationMass OuterFreshArtificialSum
open OuterFreshFixedWindows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def rawAverage (q:Data ι)(x:Frozen q)(r:Source (RestIndex q) a b)
    (seed:Id)(τ:Character)(ξ χ₀ χ ρ:RayCharacter)(Q C E:Id)
    (hC:Supported C)(hE:Supported E)(U:Finset (CommonIndex C E))
    (t θ X Y R:ℝ)(n:Fin 4→ℤ) : ℝ :=
  ∑y∈activeSelected q,(selectedPositiveWeight q x y τ/MixedSelectedVolume.scale q)*
    rawKernelPair τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
      C E hC hE U χ ρ θ X Y
      (dyadicRows (liveRows C E U R (outerRows false q x y τ ξ χ₀ Q C E U R)) n)

/-- Exact original natural-zero weights are grouped first; only then
their nonnegative grouped weights are dominated by groupedWeight. -/
theorem selected_raw_pair_le (q:Data ι)(x:Frozen q)(hqP:∀i,0<q.P i)
    (r:Source (RestIndex q) a b)(ha:0<a)(hm:Matches q x r ha)
    (seed:Id)(τ:Character)(ξ χ₀ χ ρ:RayCharacter)(Q C E:Id)
    (hC:Supported C)(hE:Supported E)(U:Finset (CommonIndex C E))
    (ψ:RayCharacter→Character)
    (hψ:SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (t θ X Y R:ℝ)(n:Fin 4→ℤ) :
    rawAverage q x r seed τ ξ χ₀ χ ρ Q C E hC hE U t θ X Y R n≤
      ∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        pairedWindowMass q (dyadicRows (liveRows C E U R (sourceRows C E U R)) n)
          (actualKeep q x τ ξ χ₀ Q C E U R)
          (fun F z=>residualWindow false r ha C hC seed D F (ψ χ) t θ X z)
          (fun F z=>residualWindow true r ha E hE seed D F (ψ (ρ⁻¹)) t θ Y (-z)) := by
  let rows:=dyadicRows (liveRows C E U R (sourceRows C E U R)) n
  let keep:=actualKeep q x τ ξ χ₀ Q C E U R
  let Ds:=fixedDivisors q x r seed E hE
  let term:=fun (D F:Id)(z:O)=>if keep F z then
    ‖residualWindow false r ha C hC seed D F (ψ χ) t θ X z‖*
      ‖residualWindow true r ha E hE seed D F (ψ (ρ⁻¹)) t θ Y (-z)‖ else 0
  let B:=fun F:Id=>∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*∑z∈rows,term D F z
  have hB (F:Id):0≤B F:=Finset.sum_nonneg (fun D _=>
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun z _=>by
      dsimp only [term]
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact le_rfl)))
  have hscale:=MixedSelectedVolume.scale_pos q hqP
  have hpoint (y:Selected q):
      rawKernelPair τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        C E hC hE U χ ρ θ X Y
        (dyadicRows (liveRows C E U R (outerRows false q x y τ ξ χ₀ Q C E U R)) n)≤
      B (selectedProduct q y) :=
    fixed_raw_kernel_masked q x y r ha hm seed τ ξ χ₀ χ ρ Q C E hC hE U ψ hψ t θ X Y R n
  have hgroup:=selected_positive_grouping q x τ B
  have hcompleted (D:Id):
      pairedWindowMass q rows keep
        (fun F z=>residualWindow false r ha C hC seed D F (ψ χ) t θ X z)
        (fun F z=>residualWindow true r ha E hE seed D F (ψ (ρ⁻¹)) t θ Y (-z))=
      ∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*∑z∈rows,term D F z := by
    exact Finset.sum_coe_sort (selectedProducts q)
      (fun F : Id => (groupedWeight q F/MixedSelectedVolume.scale q)*
        ∑z∈rows,term D F z)
  calc
    _≤∑y∈activeSelected q,(selectedPositiveWeight q x y τ/MixedSelectedVolume.scale q)*B (selectedProduct q y) :=
      Finset.sum_le_sum (fun y hy=>mul_le_mul_of_nonneg_left (hpoint y)
        (div_nonneg (selected_positive_nonneg q x y τ) hscale.le))
    _=(∑y∈activeSelected q,selectedPositiveWeight q x y τ*B (selectedProduct q y))/MixedSelectedVolume.scale q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _=(∑F∈selectedProducts q,outerGroupedWeight q x τ F*B F)/MixedSelectedVolume.scale q := by rw [hgroup]
    _≤(∑F∈selectedProducts q,groupedWeight q F*B F)/MixedSelectedVolume.scale q :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun F hF=>
        mul_le_mul_of_nonneg_right (outer_grouped_le q x τ F) (hB F))) hscale.le
    _=∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        pairedWindowMass q rows keep
          (fun F z=>residualWindow false r ha C hC seed D F (ψ χ) t θ X z)
          (fun F z=>residualWindow true r ha E hE seed D F (ψ (ρ⁻¹)) t θ Y (-z)) := by
      simp_rw [hcompleted]
      simp only [B,Finset.mul_sum,Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro z hz
      ring

def profileBase (r:Source ι a b)(C Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ V Z Rdecl ε:ℝ) : ℝ :=
  C*Kslot^(2*N)*(sourceControl control r.W₁*sourceControl control r.W₂)^2*
    (height t₀ V r.t₁ r.t₂)^degree*
    (CenteredMomentSecondWindowBudget.profileMoment degree)^2*(Z^Rdecl/fixedPresentationCost)*Z^ε

def angleEnvelope (r:Source ι a b)(C Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ tp V Z Rdecl ε:ℝ) : ℝ :=
  profileBase r C Kslot N degree control t₀ V Z Rdecl ε*heightEnvelope tp^(2*degree)

theorem profileBase_nonneg (r:Source ι a b)(C Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ V Z Rdecl ε:ℝ)(hC:0≤C)(hK:0≤Kslot)(hV:0≤V)(hZ:0≤Z) :
    0≤profileBase r C Kslot N degree control t₀ V Z Rdecl ε := by
  have hheight:0≤height t₀ V r.t₁ r.t₂:=by unfold height;positivity
  have hfixed:=fixedPresentationCost_pos.le
  unfold profileBase
  positivity

theorem angleEnvelope_nonneg (r:Source ι a b)(C Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ tp V Z Rdecl ε:ℝ)(hC:0≤C)(hK:0≤Kslot)(hV:0≤V)(hZ:0≤Z) :
    0≤angleEnvelope r C Kslot N degree control t₀ tp V Z Rdecl ε :=
  mul_nonneg (profileBase_nonneg r C Kslot N degree control t₀ V Z Rdecl ε hC hK hV hZ)
    (pow_nonneg (heightEnvelope_pos tp).le _)

/-- Both original Fourier angles have one fixed polynomial height majorant.
No common divisor, prefix or Z-dependent scalar is hidden in this envelope. -/
theorem paired_envelope_polynomial (r:Source ι a b)(C Kslot:ℝ)(N degree:ℕ)
    (control:Finset (ℕ×ℕ))(t₀ tp V θ Z Rdecl ε:ℝ)
    (hC:0≤C)(hK:0≤Kslot)(hV:0≤V)(hZ:0≤Z) :
    Real.sqrt (
      windowEnvelope r C Kslot N degree control logAnnulus logAnnulus_compact logAnnulus_smooth
        t₀ tp V θ Z Rdecl ε*
      windowEnvelope r C Kslot N degree control logAnnulus logAnnulus_compact logAnnulus_smooth
        t₀ tp V (-θ) Z Rdecl ε)≤
      angleEnvelope r C Kslot N degree control t₀ tp V Z Rdecl ε*(1+‖θ‖)^(2*degree) := by
  have heq (angle:ℝ):
      windowEnvelope r C Kslot N degree control logAnnulus logAnnulus_compact logAnnulus_smooth
        t₀ tp V angle Z Rdecl ε=
      profileBase r C Kslot N degree control t₀ V Z Rdecl ε*heightCost tp angle^(2*degree) := by
    unfold windowEnvelope profileBase CenteredMomentSecondWindowBudget.profileMoment
    ring
  rw [heq,heq]
  have heven:heightCost tp (-θ)=heightCost tp θ:=by simp only [heightCost,norm_neg]
  rw [heven,←pow_two,Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg (profileBase_nonneg r C Kslot N degree control t₀ V Z Rdecl ε hC hK hV hZ)
      (pow_nonneg (heightCost_pos tp θ).le _))]
  have hp:=pow_le_pow_left₀ (heightCost_pos tp θ).le (heightCost_le_envelope tp θ) (2*degree)
  apply (mul_le_mul_of_nonneg_left hp
    (profileBase_nonneg r C Kslot N degree control t₀ V Z Rdecl ε hC hK hV hZ)).trans_eq
  rw [mul_pow]
  unfold angleEnvelope
  ring

end
end Candidate.FourthPower.OuterFreshSelectedKernel
