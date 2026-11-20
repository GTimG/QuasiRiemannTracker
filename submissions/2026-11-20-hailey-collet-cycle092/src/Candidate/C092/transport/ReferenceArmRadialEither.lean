/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early P.3 envelope for every retained original whole-slot subproduct. -/
import Candidate.C092.transport.ReferenceArmRadialSubsets
import Candidate.C092.transport.StrongPairCommon
import Candidate.C092.transport.ReferenceShortP3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

theorem actual_reference_either_arm (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character)
    (Q1 Q : Ideal O) (hQ1r : Q1≤ rayM)
    (hQ10 : internalQ Q1 ηshort₀≠0) (hQ1t : internalQ Q1 ηshort₀≠⊤)
    (hQ172 : internalQ Q1 ηshort₀≤ Ideal.span {(72:O)}) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ V : ℝ, 0≤ V → V≤2 →
    ∀ (T : Finset ι) (θ1 θ2 : ι → RayQuotient.Characters rayM Hr) (w σ v1 v2 : ι→ℝ),
    (∀ i∈T, (33/50:ℝ) ≤ σ i) → (∀ i∈T, σ i ≤ (33/50:ℝ)) → (∑ i∈T,w i) ≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → ((X₁ ≤ U^shortCap ∧ X₂ ≤ U) ∨ (X₂ ≤ U^shortCap ∧ X₁ ≤ U)) →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q1 ηshort₀) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^V) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ1 W U w σ v1 i) t₁ (U^(w i))‖) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ =
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηlong₀ θ2 W U w σ v2 i) t₂ (U^(w i))‖) →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₁|+|t₂|+|t₂|+height)^d*U^(terminalFramePrice V) := by
  obtain ⟨d1,S1,C1,hC1,h1⟩ := actual_reference_radial_subsets ι hβ rayM Hr hHr W hW hWs
    bΦ hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q1 Q hQ1r hQ10 hQ1t hQ172 hQr hQ0 hQt hQ72
  obtain ⟨d2,S2,C2,hC2,h2⟩ := actual_reference_radial_subsets ι hβ rayM Hr hHr W hW hWs
    bΦ hbΦ hΦs η₂ η₁ ηlong₀ ηshort₀ Q Q1 hQr hQ0 hQt hQ72 hQ1r hQ10 hQ1t hQ172
  refine ⟨d1+d2,S1∪S2,C1+C2,by positivity,?_⟩
  filter_upwards [h1,h2] with U h1 h2
  refine ⟨h1.1,?_⟩
  intro V hV hV2 T θ1 θ2 w σ v1 v2 hlo hhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hrect
    s mark hk1 hk2 hy hm1 hm2
  have hu : 0< U := zero_lt_one.trans h1.1
  have hb : 1≤1+|t₁|+|t₁|+|t₂|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  rcases hrect with hr|hr
  · have he := h1.2 V hV hV2 T θ1 w σ v1 hlo hhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂
      hr.1 hr.2 s mark hk1 hk2 hy hm1
    have hc := pair_control_mono p (show S1⊆S1∪S2 from Finset.subset_union_left)
    have hd := pow_le_pow_right₀ hb (Nat.le_add_right d1 d2)
    have hn := p.control_nonneg S1
    have hn' := p.control_nonneg (S1∪S2)
    exact he.trans (by gcongr <;> first | positivity | linarith)
  · let q : Profiles (1/4) (9/4) :=
      ⟨fun i=> if i=0 then p.profile 1 else p.profile 0,fun i=> by split_ifs <;> exact p.support _⟩
    have he := h2.2 V hV hV2 T θ2 w σ v2 hlo hhi hsum q t₂ t₁ height X₂ X₁ hh hX₂ hX₁
      hr.1 hr.2 s mark hk2 hk1 hy hm2
    have hqc : q.control S2=p.control S2 := by
      simp only [q,Profiles.control,ite_true,show (1:Fin 2)≠0 from by decide,ite_false]
      ring
    rw [hqc] at he
    simp only [q,ite_true,show (1:Fin 2)≠0 from by decide,ite_false] at he
    rw [finiteEnergyOn_swap] at he
    have hheight : 1+|t₂|+|t₂|+|t₁|+|t₁|+height=1+|t₁|+|t₁|+|t₂|+|t₂|+height := by ring
    rw [hheight] at he
    have hc := pair_control_mono p (show S2⊆S1∪S2 from Finset.subset_union_right)
    have hd := pow_le_pow_right₀ hb (Nat.le_add_left d2 d1)
    have hn := p.control_nonneg S2
    have hn' := p.control_nonneg (S1∪S2)
    exact he.trans (by gcongr <;> first | positivity | linarith)

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.actual_reference_either_arm
