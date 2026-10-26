/- Copyright (c) 2026 Sil. Apache-2.0.
Actual SECOND tail at original Kchild. Arbitrary saving pays the selected
cardinality and restores the ORIGINAL Nu^-1 before any divisor summation.

-/
import Candidate.FourthPower.RepairedRemainderGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRawTail
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice CenteredMomentSupportedTailAggregate
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open OuterFreshSource OuterFreshSelected OuterFreshConsumer
open OuterFreshCutoffAllowance RepairedGroupedConsumer RepairedRemainderGeometry
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Scalar spending of an arbitrary tail exponent. W and Nu are kept
explicit until their polynomial caps have actually been used. -/
theorem spend_tail (W U Z BW BU saving : ℝ) (hW : 0 ≤ W) (hU : 0 < U) (hZ : 1 < Z)
    (hWcap : W ≤ Z^BW) (hUcap : U ≤ Z^BU) :
    W^2 * Z^(-(saving+2*BW+BU)) ≤ Z^(-saving) / U := by
  have hz := zero_lt_one.trans hZ
  have hprod : W^2 * U ≤ Z^(2*BW+BU) := by
    apply (mul_le_mul (pow_le_pow_left₀ hW hWcap 2) hUcap hU.le (sq_nonneg _)).trans_eq
    rw [pow_two, ← Real.rpow_add hz, ← Real.rpow_add hz]
    congr 1
    ring
  apply (le_div_iff₀ hU).mpr
  calc
    _ = (W^2 * U) * Z^(-(saving+2*BW+BU)) := by ring
    _ ≤ Z^(2*BW+BU) * Z^(-(saving+2*BW+BU)) :=
      mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring

/-- No Fourier-tail premise. The existing arbitrary-saving theorem is
invoked with saving+2BW+BU. The bound is already raw and includes actual
selected Cauchy; only frozen/supplier sums remain to be applied upstream.
K is allowed below one, and T is the caller's same actual second cutoff.
-/
theorem uniform_raw_tail_original_seed (N : ℕ) (B BW BU ζ saving : ℝ)
    (hB : 0 ≤ B) (hζ : 0 < ζ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (κ : Type u) [Fintype κ], ∀ a b : ℝ, ∀ s : Source κ a b,
    ∀ ha : 0 < a, 0 ≤ b → ∀ cover : OriginalEnclosure s, Fintype.card κ ≤ N →
    ∀ (u : Id) (L : Finset κ) (J : Finset {i // i ∉ Lᶜ}), u ≠ 0 → (u.absNorm : ℝ) ≤ Z^BU →
    let q := supplierData s ha u L J
    selectedVolume q ≤ Z^BW → ∀ x : Frozen q,
    let r := residualSource s ha cover u L J x
    ∀ (seed : Id) (ξ : RayCharacter) (τ : Character) (t K X T : ℝ),
      0 < K → 0 < X → poolCap r ≤ Z^B → sourceNormCap r.P b r.T r.d ≤ X →
      X ≤ Z^B → K ≤ Z^B → T ≤ Z^B → X^2/K ≤ T →
    ((activeSelected q).card : ℝ) *
      ‖selectedSum q x τ (fun y => secondDiscardedEnergy τ t (sourceColumns r)
        (outerColumn q x y seed ξ) ballProfile K T Z ζ)‖ ≤
      Ctail * (256 : ℝ)^N * selectedMass q s.M * (profileCap s)^2 * Z^(-saving) / (u.absNorm : ℝ) := by
  obtain ⟨control,C,hC,htail⟩ := uniform_average_tail B ζ (saving+2*BW+BU) hB hζ
  let seminorm := control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  have hsemi : 0 ≤ seminorm := apply_nonneg _ _
  let Ctail := 1+C*seminorm
  have hCt : 0 < Ctail := by dsimp only [Ctail]; positivity
  have hCC : C*seminorm ≤ Ctail := by dsimp only [Ctail]; linarith
  refine ⟨Ctail,hCt,htail.mono ?_⟩
  intro Z hZdata
  refine ⟨hZdata.1,?_⟩
  intro κ instκ a b s ha hb cover hcard u L J hu hUcap q hWcap x r seed ξ τ t K X T
    hK hX hpool hsupport hXcap hKcap hTcap hcutoff
  have hP : ∀ i, 0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hW := selectedVolume_pos q hP
  have hMass : 0 ≤ selectedMass q s.M := by unfold selectedMass; positivity
  have hProf := profileCap_nonneg s
  have hProfR := profileCap_nonneg r
  have hz := zero_lt_one.trans hZdata.1
  have he := hZdata.2 κ q x a b r ha hb (residual_matches s ha cover u L J x)
    s.M (fun i => zero_le_one.trans (s.hM i)) (fun i I _ => s.hν i I)
    s.hWnorm hP (fun i I hI => (s.hpn i I hI).2)
    seed ξ τ t K X T hK hX hpool hsupport hXcap hKcap hTcap hcutoff
  have hgroup := (grouped_norm_le_average q x τ hP
    (fun y => secondDiscardedEnergy τ t (sourceColumns r) (outerColumn q x y seed ξ) ballProfile K T Z ζ)).trans
      (mul_le_mul_of_nonneg_left he hW.le)
  have hprofSq : (profileCap r)^2 ≤ (profileCap s)^2 :=
    pow_le_pow_left₀ hProfR (residual_profileCap_le s ha cover u L J x) 2
  let Lead := selectedMass q s.M * Ctail * (profileCap s)^2
  have hLead : 0 ≤ Lead := by dsimp only [Lead]; positivity
  have hgroup' : ‖selectedSum q x τ
      (fun y => secondDiscardedEnergy τ t (sourceColumns r) (outerColumn q x y seed ξ) ballProfile K T Z ζ)‖ ≤
      selectedVolume q * Lead * Z^(-(saving+2*BW+BU)) := by
    apply hgroup.trans
    calc
      _ = selectedVolume q * selectedMass q s.M * (C*seminorm) *
          (profileCap r)^2 * Z^(-(saving+2*BW+BU)) := by dsimp only [seminorm]; ring
      _ ≤ selectedVolume q * selectedMass q s.M * Ctail *
          (profileCap s)^2 * Z^(-(saving+2*BW+BU)) := by gcongr
      _ = _ := by dsimp only [Lead]; ring
  have hj : Fintype.card q.J ≤ N := (MixedSelectedVolume.selected_card_le q).trans hcard
  have hcardSel : ((activeSelected q).card : ℝ) ≤ (256 : ℝ)^N * selectedVolume q :=
    (active_selected_annular_card q (fun i => (hP i).le) (fun i I hI => (s.hpn i I hI).2)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hW.le)
  have hpaid := spend_tail (selectedVolume q) (u.absNorm : ℝ) Z BW BU saving hW.le
    (zero_lt_one.trans_le (ideal_norm_one_le hu)) hZdata.1 hWcap hUcap
  calc
    _ ≤ ((activeSelected q).card : ℝ) * (selectedVolume q * Lead * Z^(-(saving+2*BW+BU))) :=
      mul_le_mul_of_nonneg_left hgroup' (Nat.cast_nonneg _)
    _ ≤ ((256 : ℝ)^N * selectedVolume q) * (selectedVolume q * Lead * Z^(-(saving+2*BW+BU))) :=
      mul_le_mul_of_nonneg_right hcardSel (by positivity)
    _ = ((256 : ℝ)^N * Lead) * ((selectedVolume q)^2 * Z^(-(saving+2*BW+BU))) := by ring
    _ ≤ ((256 : ℝ)^N * Lead) * (Z^(-saving) / (u.absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_left hpaid (by positivity)
    _ = _ := by dsimp only [Lead]; ring

end
end Candidate.FourthPower.RepairedRawTail
