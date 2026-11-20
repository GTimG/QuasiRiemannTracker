/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairSmallJoin

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.SmallCore

/-- A uniform genuine homogeneous fourth. The zero-quota alternative
has exactly no assigned slots and uses the independent unmarked source. -/
theorem mixed_small_fourth_source (hβ : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr),
    ∀ (W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2  ≤  bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η η₀ : Character) (Q : Ideal O),Q  ≤  rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀  ≤  Ideal.span {(72:O)} →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V a : ℝ,radiusMin  ≤  V → V  ≤  98/100 → (369/1000:ℝ)  ≤  a → a  ≤  1 →
    ∀ (F : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
      (t height : ℝ),
      (∀ i,0  ≤  w i) → (∀ i,w i  ≤  mesh) →
      (∀ i,(33/50:ℝ)  ≤  σ i) → (∀ i,σ i  ≤  (33/50:ℝ)) →
      0  ≤  height → (∀ i,|v i|  ≤  height) →
      2*(∑ i∈F,w i)  ≤  fourthQuota a V → (fourthQuota a V=0 → F=∅) →
    ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (X : ℝ),0 < X → length U X  ≤  a →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ u∈s,initialKeep η (internalQ Q η₀) u.val) → (∀ u∈s,rowNorm u  ≤  U^V) →
      (∀ u∈s,∀ i∈F,‖mark i u‖=
        ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀ θ W U w σ v i) t (U^(w i))‖) →
      (∑ u∈s,(‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^2*
        ∏ i∈F,‖mark i u‖^2)^2)  ≤ 
      C*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree*U^(V+1/10000) := by
  obtain ⟨m,hm,hnat⟩:=native_source hβ (1/10000) (by norm_num)
  let mesh : ℝ:=radiusMin*m
  have hrad : 0 < radiusMin:=by norm_num [radiusMin]
  refine ⟨mesh,mul_pos hrad hm,?_⟩
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η η₀ Q hQr hQ0 hQt hQ72
  obtain ⟨dn,Sn,Cn,hCn,hnat⟩:=hnat (Fin 2×Slot) rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQr hQ0 hQt hQ72
  obtain ⟨du,Su,Cu,hCu,hunmarked⟩:=independent_fourth_source hβ rayM Hr hHr bΦ
    (by linarith) hΦs η η₀ Q hQr hQ0 hQt hQ72
  refine ⟨max dn du,Sn∪Su,Cn+Cu+1,by positivity,?_⟩
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp hnat
  have hlarge:=(tendsto_rpow_atTop hrad).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,hunmarked,eventually_gt_atTop (1:ℝ)] with U hlarge hunmarked hU
  intro V a hV0 hV1 ha ha1 F θ w σ v t height hw hwm hσlo hσhi hh hv hquota hzero p j X hX hXa s mark hk hy hmark
  have hUp : 0 < U:=zero_lt_one.trans hU
  have hV : 0 < V:=hrad.trans_le hV0
  have hVone : V  ≤  1:=hV1.trans (by norm_num)
  have hXX : X  ≤  U := by
    have hlen : length U X  ≤  1:=hXa.trans ha1
    have hm' : max 1 X  ≤  U^((1:ℝ)) :=
      (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le (le_max_left _ _))).1 hlen
    simpa using (le_max_right (1:ℝ) X).trans hm'
  have hd:=QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1  ≤  1+|t|+height:=by linarith [abs_nonneg t]
  by_cases hq : fourthQuota a V=0
  · have he:=hzero hq
    subst F
    have hE:=hunmarked hU.le V hV.le hVone p j t height X hh hX hXX s hk hy
    simp only [Finset.prod_empty,mul_one,←pow_mul] at *
    have hc : Cu  ≤  Cn+Cu+1:=by linarith
    have hS:=control_mono Su (Sn∪Su) Finset.subset_union_right (p.profile j)
    have hs0:=sourceControl_nonneg Su (p.profile j)
    have hp:=pow_le_pow_right₀ hheight (le_max_right dn du)
    exact hE.trans (by gcongr)
  · have hq' : 0 < fourthQuota a V:=lt_of_le_of_ne (le_max_left _ _) (Ne.symm hq)
    have hsrc₀:=hZ₀ (U^V) (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hU.le hV0))
    have hsrc:=homogeneous_native_labelled rayM Hr hHr ha hV0 hV1 hq' hsrc₀
    have hrel (i : Slot) : w i/V  ≤  m:=mesh_rescale hrad hV0 hm.le le_rfl (hwm i)
    have hcap : length (U^V) X  ≤  a/V:=by
      rw [length_rpow_base U X V hUp]
      exact div_le_div_of_nonneg_right hXa hV.le
    have hE:=small_native_arm rayM Hr hHr hsrc F θ w σ v t height hw hrel hσlo hσhi hh hv
      hΦs p j X hX hU hV hcap hquota s mark hk hy hmark
    have hc : Cn  ≤  Cn+Cu+1:=by linarith
    have hS:=control_mono Sn (Sn∪Su) Finset.subset_union_left (p.profile j)
    have hs0:=sourceControl_nonneg Sn (p.profile j)
    have hp:=pow_le_pow_right₀ hheight (le_max_left dn du)
    have hr:=Real.rpow_le_rpow_of_exponent_le hU.le
      (show V*(1+(1/10000:ℝ))  ≤  V+1/10000 by linarith only [hVone])
    exact hE.trans (by gcongr)

#print axioms mixed_small_fourth_source
end
end QRH.Cycle092.StrongPair
