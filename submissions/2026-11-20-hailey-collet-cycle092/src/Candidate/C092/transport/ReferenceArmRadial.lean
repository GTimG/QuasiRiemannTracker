/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.3 on the literal original ray-prime pools and original annular marked
coefficients, with independent ordinary characters, profiles and pitches. -/
import Candidate.C092.transport.ReferenceShortP3Physical
import Candidate.C092.transport.ReferenceArmRadialPhysical
import Candidate.C092.transport.ReferenceArmRadialAbsolute
import Candidate.C092.transport.ReferenceShortP3Step
import Candidate.C092.transport.ExhaustedPairPriceAllRadii
import Candidate.C092.transport.TinyCoreSlots
import Candidate.C092.transport.ReferenceArmRadialFourthJoin
import Candidate.C092.transport.ReferenceArmRadialGates

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
open QRH.Cycle092.TinyCore QRH.Cycle092.ExhaustedPairPrice QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.SilDensitySplit.CubeFree.FP.MixedCanonicalSource (slotProfile)
local notation "O" => HeckeFamily.O

theorem actual_reference_radial (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 0 < bΦ)
    (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character)
    (Q1 Q : Ideal O) (hQ1r : Q1≤ rayM)
    (hQ10 : internalQ Q1 ηshort₀≠0) (hQ1t : internalQ Q1 ηshort₀≠⊤)
    (hQ172 : internalQ Q1 ηshort₀≤ Ideal.span {(72:O)}) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ V : ℝ, 0≤ V → V≤2 →
    ∀ (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) → (∑i,w i)≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U^shortCap → X₂ ≤ U →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q1 ηshort₀) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^V) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₁|+|t₂|+|t₂|+height)^d*U^(terminalFramePrice V) := by
  let ε : ℝ := (QRH.SourceCertificate.u:ℝ)/4
  have hε : 0<ε := by norm_num [ε,QRH.SourceCertificate.u]
  obtain ⟨ds,Ss,Cs,hCs,hs⟩ := actual_two_radius_reference ι hβ rayM Hr hHr W hW hWs
    ε bΦ hε hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q hQr hQ0 hQt hQ72
  obtain ⟨da,Sa,Ca,hCa,ha⟩ := actual_absolute_reference ι hβ rayM Hr hHr W hW hWs
    ε bΦ hε hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q1 Q hQ1r hQ10 hQ1t hQ172 hQr hQ0 hQt hQ72
  refine ⟨ds+da,Ss∪Sa,Cs+Ca,by positivity,?_⟩
  filter_upwards [hs,ha] with U hs ha
  refine ⟨hs.1,?_⟩
  intro V hV hV2 θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hlong s mark hk1 hk2 hy hm
  have hu : 0<U := zero_lt_one.trans hs.1
  have hpS := pair_control_mono p (show Ss⊆Ss∪Sa from Finset.subset_union_left)
  have hpA := pair_control_mono p (show Sa⊆Ss∪Sa from Finset.subset_union_right)
  have hbase : 1≤1+|t₁|+|t₁|+|t₂|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hprice : radialPrice V+ε≤ terminalFramePrice V :=
    (all_radius_price hV (by norm_num [ε,QRH.SourceCertificate.u])).le
  have hX1U : X₁≤U := hshort.trans (by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hs.1.le
      (by norm_num [shortCap] : shortCap≤(1:ℝ))))
  by_cases hv : V≤4/5
  · have he := ha.2 V hV hV2 θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂
      hX1U hlong s mark hk1 hk2 hy hm
    have hpow : U^(V+widthCap+ε)≤ U^(terminalFramePrice V) :=
      Real.rpow_le_rpow_of_exponent_le hs.1.le (by simpa only [radialPrice,if_pos hv] using hprice)
    have hdegree : (1+|t₁|+|t₂|+height)^da≤(1+|t₁|+|t₁|+|t₂|+|t₂|+height)^(ds+da) :=
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₁,abs_nonneg t₂]) da).trans
        (pow_le_pow_right₀ hbase (Nat.le_add_left da ds))
    have hpn := p.control_nonneg Sa
    have hcn := p.control_nonneg (Ss∪Sa)
    exact he.trans (by gcongr <;> first | positivity | linarith)
  · have he := hs.2 V hV hV2 θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂
      hshort hlong s mark hk2 hy hm
    have hpow : U^((max V markedRadius+V)/2+ε)≤ U^(terminalFramePrice V) :=
      Real.rpow_le_rpow_of_exponent_le hs.1.le (by simpa only [radialPrice,if_neg hv] using hprice)
    have hdegree : (1+|t₂|+|t₂|+height)^ds≤(1+|t₁|+|t₁|+|t₂|+|t₂|+height)^(ds+da) :=
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₁]) ds).trans
        (pow_le_pow_right₀ hbase (Nat.le_add_right ds da))
    have hpn := p.control_nonneg Ss
    have hcn := p.control_nonneg (Ss∪Sa)
    exact he.trans (by gcongr <;> first | positivity | linarith)

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.actual_reference_radial
