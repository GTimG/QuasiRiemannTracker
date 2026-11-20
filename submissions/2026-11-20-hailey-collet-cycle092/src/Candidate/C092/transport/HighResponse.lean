/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.1 high response. Applies Joseph Bebel's selected-cell norm to the original
normalized slot mass and an arbitrary ordinary coefficient on actual ideals. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalUniformNear
import Submissions.arvi_selected_leaf.JointDetector.FineCanonicalFromNorm
import Submissions.arvi_selected_leaf.JointDetector.FineNaturalCount

namespace QRH.Cycle092.HighResponse
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_HighResponse_d525081d231555f8_001 (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)


theorem actual_H6 : FineNaturalCount.ActualSelectedSlotNorm :=
  FineCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm

/-- The exact P.1 slope, before losses from the mass of merged coefficients. -/
theorem saving {U V A X Y : ℝ} (hU : 1 ≤ U) (hV : 98/100 ≤ V)
    (hA : A ≤ 919/1000) (hX : X ≤ U^A) (hY : Y ≤ U^V)
    (hx : 0 ≤ X) (hy : 0 ≤ Y) :
    X + Y^(1-(5001/10000 : ℝ))*X^(5001/10000 : ℝ) ≤ 2*U^(V-305/10000) := by
  have hu := zero_lt_one.trans_le hU
  have h₁ := hX.trans (Real.rpow_le_rpow_of_exponent_le hU (show A ≤ V-305/10000 by linarith))
  have h₂ : Y^(1-(5001/10000 : ℝ))*X^(5001/10000 : ℝ) ≤
      (U^V)^(1-(5001/10000 : ℝ))*(U^A)^(5001/10000 : ℝ) := by
    exact mul_le_mul (Real.rpow_le_rpow hy hY (by norm_num)) (Real.rpow_le_rpow hx hX (by norm_num))
      (by positivity) (by positivity)
  rw [←Real.rpow_mul hu.le,←Real.rpow_mul hu.le,←Real.rpow_add hu] at h₂
  have h₃ := h₂.trans (Real.rpow_le_rpow_of_exponent_le hU
    (show V*(1-(5001/10000 : ℝ))+A*(5001/10000 : ℝ) ≤ V-305/10000 by linarith))
  linarith

/-- A single mesh precedes the later finite family and the chosen coefficient.
Both the natural root and the radial keep restriction are retained in the input;
no bound on the number of elements in the selected row set is assumed. -/
theorem original_high_response (Mmin Mcap smin loss : ℝ)
    (hm : 0 < Mmin) (hm' : Mmin ≤ Mcap) (hs : 0 < smin) (hl : 0 < loss) :
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (V A Y X : ℝ) (root : HeckeInverseAmplification.NonzeroIdeal) (cores : Finset FreeRow),
    98/100 ≤ V → A ≤ 919/1000 → Z^(Mmin/20) ≤ Y → Y ≤ bΦ*Z^st.rowWidth → Y ≤ Z^V →
    (∀ u ∈ cores, rowNorm u ≤ Y ∧
      ∃ hz : st.radial.keep (rowMap (u,root)),
        st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
        Z^((5001/10000:ℝ)*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) →
    1 ≤ X → X ≤ Z^A → ∀ (S : Finset (Ideal O)) (c : S → ℂ),
    (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      ∑ z : cores.image Subtype.val, ‖FineDetectorWords.ordinaryPolynomial S c z.val‖^2 ≤
        C*Z^(V-305/10000+loss)*∑ I, ‖c I‖^2 := by
  obtain ⟨m,hm₀,h⟩ := actual_H6 Mmin Mcap smin loss 1 hm hm' hs hl (by norm_num)
  refine ⟨m,hm₀,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hb
  obtain ⟨C,hC,hZ⟩ := h mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hb
  refine ⟨2*C,by positivity,hZ.mono ?_⟩
  rintro Z ⟨hZ,hst⟩; refine ⟨hZ,?_⟩
  intro j st hc hp hw hM T θ w σ v t height hw₀ hwm hlo hhi hh hv hsw V A Y X root cores hV hA hY₀ hY₁ hY₂ hc₀ hX₀ hX₁ S c hN
  have op := hst j st hc hp hw hM T θ w σ v t height hw₀ hwm hlo hhi hh hv hsw (5001/10000) Y root cores
    (by constructor <;> norm_num) hY₀ hY₁ hc₀
  have hu := zero_lt_one.trans hZ
  have hex : A ≤ FineDetectorWords.detectorAuxiliarySourceCap 1 (Mcap+1) := by
    unfold FineDetectorWords.detectorAuxiliarySourceCap; linarith [le_max_left (1:ℝ) (3*(Mcap+1))]
  have hupp := op.2 X S hX₀ (hX₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hex)) hN
  have hsav := saving hZ.le hV hA hX₁ hY₂ (zero_le_one.trans hX₀)
    ((Real.rpow_pos_of_pos hu _).le.trans hY₀)
  have hSN := hupp.trans (mul_le_mul_of_nonneg_left hsav (by positivity))
  have he := (FineDetectorWords.ordinaryPolynomial_energy (cores.image Subtype.val) S c).trans
    (mul_le_mul_of_nonneg_right hSN (by positivity))
  calc
    _ ≤ C * Z^loss * (2*Z^(V-305/10000)) * ∑ I, ‖c I‖^2 := he
    _ = _ := by rw [Real.rpow_add hu]; ring

#print axioms actual_H6
#print axioms original_high_response
end
end QRH.Cycle092.HighResponse
