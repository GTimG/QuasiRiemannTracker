/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual uncentered root from only the original signed centered estimate.
The reference bound is proved by P.3, never supplied as a hypothesis. -/
import Candidate.C092.transport.OrderedPairPhaseStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

theorem enlarge_profile_price {a b : ℝ} (p : Profiles a b)
    {S₀ S : Finset (ℕ×ℕ)} {C₀ C U e₀ e height₀ height : ℝ} {d₀ d : ℕ}
    (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (hS : S₀⊆S) (hU : 1 ≤ U) (he : e₀≤e)
    (hh₀ : 0 ≤ height₀) (hh : 1 ≤ height) (hhle : height₀≤height) (hd : d₀≤d) :
    C₀*(p.control S₀)^2*height₀^d₀*U^e₀ ≤ C*(p.control S)^2*height^d*U^e := by
  have hp := pair_control_mono p hS
  have hpn := p.control_nonneg S₀
  have hpn' := p.control_nonneg S
  have hpow := (pow_le_pow_left₀ hh₀ hhle d₀).trans (pow_le_pow_right₀ hh hd)
  have hup := Real.rpow_le_rpow_of_exponent_le hU he
  have hu₀ : 0 ≤ U^e₀ := Real.rpow_nonneg (zero_le_one.trans hU) _
  have hu' : 0 ≤ U^e := Real.rpow_nonneg (zero_le_one.trans hU) _
  have hCn : 0 ≤ C := hC₀.trans hC
  have hhn : 0 ≤ height := zero_le_one.trans hh
  gcongr

theorem actual_uncentered_root (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (H Wmax ε bΦ Ccenter : ℝ) (dcenter : ℕ) (Scenter : Finset (ℕ×ℕ))
    (hH : 0 < H) (hH1 : H ≤ 1)
    (hreserve : 4*(shortWidth+Wmax) < H) (hε : 0 < ε) (hεH : ε ≤ H) (hCc : 0 ≤ Ccenter)
    (hbΦ : 0 < bΦ) (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQr₁ : Q₁ ≤ rayM) (hQ0₁ : internalQ Q₁ η₀₁ ≠ 0) (hQt₁ : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ72₁ : internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)})
    (hQr₂ : Q₂ ≤ rayM) (hQ0₂ : internalQ Q₂ η₀₂ ≠ 0) (hQt₂ : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ72₂ : internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (T : Finset ι) (θ₁ θ₂ : ι → RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : ι→ℝ),
    (∀ i∈T, (33/50:ℝ) ≤ σ₁ i) → (∀ i∈T, σ₁ i ≤ (33/50:ℝ)) →
    (∀ i∈T, (33/50:ℝ) ≤ σ₂ i) → (∀ i∈T, σ₂ i ≤ (33/50:ℝ)) → (∑ i∈T,w i) ≤ Wmax →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U^H → X₂ ≤ U^H → X₁*X₂ ≤ U^(H+shortWidth) →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) → (∀ u∈s,rowNorm u ≤ U^H) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ = ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ = ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
    (U^shortWidth < X₁ → U^shortWidth < X₂ →
      alignedPairEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
        (U^shortWidth) (X₁*X₂/U^shortWidth) mark ≤
        Ccenter*(p.control Scenter)^2*(1+|t₁|+|t₂|+height)^dcenter*U^(1+ε)) →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^(1+ε) := by
  obtain ⟨d₁,S₁,C₁,hC₁,hfirst⟩ := actual_short_reference_subsets ι hβ rayM Hr hHr W hW hWs
    H Wmax ε bΦ hH hH1 hreserve hε hεH hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₂ hQr₂ hQ0₂ hQt₂ hQ72₂
  obtain ⟨d₂,S₂,C₂,hC₂,hsecond⟩ := actual_short_reference_subsets ι hβ rayM Hr hHr W hW hWs
    H Wmax ε bΦ hH hH1 hreserve hε hεH hbΦ hΦs η₂ η₁ η₀₂ η₀₁ Q₁ hQr₁ hQ0₁ hQt₁ hQ72₁
  obtain ⟨d₃,S₃,C₃,hC₃,hlarge⟩ := actual_centered_reference_step ι hβ rayM Hr hHr W hW hWs
    H Wmax ε bΦ (1+ε) Ccenter dcenter Scenter hH hH1 hreserve hε hεH
    (by linarith only [hH1]) hCc hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₂ hQr₂ hQ0₂ hQt₂ hQ72₂
  let D := max d₁ (max d₂ d₃)
  let controls := (S₁∪S₂)∪S₃
  let C := C₁+C₂+C₃
  have hC : 0 < C := by dsimp [C]; positivity
  have hS₁ : S₁⊆controls := Finset.subset_union_left.trans Finset.subset_union_left
  have hS₂ : S₂⊆controls := Finset.subset_union_right.trans Finset.subset_union_left
  have hS₃ : S₃⊆controls := Finset.subset_union_right
  have hd₁ : d₁≤D := le_max_left _ _
  have hd₂ : d₂≤D := (le_max_left _ _).trans (le_max_right _ _)
  have hd₃ : d₃≤D := (le_max_right _ _).trans (le_max_right _ _)
  have hc₁ : C₁≤C := by dsimp [C]; linarith
  have hc₂ : C₂≤C := by dsimp [C]; linarith
  have hc₃ : C₃≤C := by dsimp [C]; linarith
  refine ⟨D,controls,C,hC,?_⟩
  filter_upwards [hfirst,hsecond,hlarge] with U hf hs hl
  refine ⟨hf.1,?_⟩
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ hlo₁ hhi₁ hlo₂ hhi₂ hsum p t₁ t₂ height X₁ X₂
    hh hX₁ hX₂ hX₁K hX₂K hprod s mark hk₁ hk₂ hy hm₁ hm₂ hcenter
  have hhfull : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  rcases reference_dispatch U X₁ X₂ with hshort | hshort | hlong
  · have hb := hf.2 T θ₁ w σ₁ v₁ hlo₁ hhi₁ hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hX₂K s mark hk₂ hy hm₁
    exact hb.trans (enlarge_profile_price p hC₁.le hc₁ hS₁ hf.1.le (by linarith only [hH1])
      (by positivity) hhfull (by linarith [abs_nonneg t₁]) hd₁)
  · let p' : Profiles (1/4) (9/4) :=
      ⟨fun i => if i=0 then p.profile 1 else p.profile 0,fun i => by split_ifs <;> exact p.support _⟩
    have hp : p'.control S₂ = p.control S₂ := by
      simp only [p',Profiles.control,ite_true,show (1:Fin 2)≠0 from by decide,ite_false]
      ring
    have hb := hs.2 T θ₂ w σ₂ v₂ hlo₂ hhi₂ hsum p' t₂ t₁ height X₂ X₁ hh hX₂ hX₁ hshort hX₁K s mark hk₁ hy hm₂
    rw [hp] at hb
    simp only [p',ite_true,show (1:Fin 2)≠0 from by decide,ite_false] at hb
    have heq : finiteEnergyOn T s η₂ η₁ (p.profile 1) (p.profile 0) t₂ t₁ X₂ X₁ mark =
        finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark := by
      unfold finiteEnergyOn
      apply Finset.sum_congr rfl
      intro u hu
      ring
    rw [heq] at hb
    exact hb.trans (enlarge_profile_price p hC₂.le hc₂ hS₂ hf.1.le (by linarith only [hH1])
      (by positivity) hhfull (by linarith [abs_nonneg t₂]) hd₂)
  · have hb := hl.2 T θ₁ w σ₁ v₁ hlo₁ hhi₁ hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hprod
      s mark hk₂ hy hm₁ (hcenter hlong.1 hlong.2)
    exact hb.trans (enlarge_profile_price p hC₃.le hc₃ hS₃ hf.1.le le_rfl
      (by positivity) hhfull le_rfl hd₃)

#print axioms actual_uncentered_root
end
end QRH.Cycle092.OrderedPairPhase
