/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Literal independently colored StrongPair leaves on actual sixth-free fibers,
plus the genuine first-ideal-norm vanishing used to count dyadic classes.
-/
import Candidate.C092.transport.RegularColoredGroupedUniform
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight scale_pos)
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredGroupedLeaves_171076cfbe674ccc_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}


/-- The only analytic leaf of the grouped price. It is a literal finite
StrongPair energy on the actual sixth-free fiber, with two independently
shortened ordinary lengths and every surviving whole-slot subset. -/
def framePricedLeaves (θ : GData L) {mesh Z : ℝ} (η ω₁ ω₂ : Character)
    (r : GSrc θ mesh Z) (v M Hsource loss K Pbd : ℝ) (J : ℕ) : Prop :=
  ∀ (A : Finset (Fin θ.N)) (j : DictIdx) (Y₁ Y₂ : ℝ),0<Y₁ → 0<Y₂ →
    (∀e:Fin 2,length Z (scale e*Y₁)≤L+1 ∧ length Z (scale e*Y₂)≤L+1) →
    (∀e:Fin 2×Fin 2,length Z (scale e.1*Y₁)+length Z (scale e.2*Y₂)≤Pbd) →
    let mark := fun (i:A) y=>normalizedSlot (anchors η j) pmask 1 y
      (originalPools θ.rayM θ.Hray 2 Z (fun i:A=>r.w i.val) i)
      (originalCoefficients θ.rayM θ.Hray θ.hH θ.η₀ (fun i:A=>r.χ i.val) θ.W Z
        (fun i:A=>r.w i.val) (fun i:A=>r.σ i.val) (fun i:A=>r.freq i.val) i) (r.t+v) (Z^(r.w i.val))
    ∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (R:Finset NonzeroFrequency),
      (∀z∈R,initialKeep (anchors η j) (internalQ θ.Q θ.η₀) z.val ∧ rawFrequencyNorm z≤Z^M) →
      ∀ B : HeckeInverseAmplification.NonzeroIdeal,(sixthFreeFiber R B).Nonempty →
      ∀ D₁∈IdealMobiusDivisorSum.idealDivisors B.val,
      ∀ D₂∈IdealMobiusDivisorSum.idealDivisors B.val,∀ T : Finset A,
        StrongPair.finiteEnergyOn T (sixthFreeFiber R B) ((anchors η j).product ω₁) ((anchors η j).product ω₂)
          ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
          (2*Real.pi*(r.t₁+v/(2*Real.pi))) (2*Real.pi*(r.t₂+v/(2*Real.pi)))
          ((scale e.1*Y₁)/(D₁.absNorm:ℝ)) ((scale e.2*Y₂)/(D₂.absNorm:ℝ))
          (fun i u=>mark i u.val) ≤ K*pairWeight J τ*
            Z^(coreWidth Z M B+loss+(5/6)*max 0 (Hsource-coreWidth Z M B))

theorem frameChildE_eq_zero_small (ω₁ ω₂ η : Character) {θ : GData L} {mesh Z : ℝ}
    (r : GSrc θ mesh Z) (v : ℝ) (j : DictIdx) (A : Finset (Fin θ.N))
    (X₁ X₂ : ℝ) (V : O) (K : ℝ)
    (hs : (0<X₁ ∧ θ.b*X₁<1) ∨ (0<X₂ ∧ θ.b*X₂<1)) :
    frameChildE ω₁ ω₂ η r v j A X₁ X₂ V K=0 := by
  unfold frameChildE GroupedPair.pairEnergy GroupedPair.row
  have hzero (z : O) :
      CenteredMomentHeckeHeight.rowTwistedSum ((anchors η j).product ω₁) pmask 1 z r.W₁
        (2*Real.pi*(r.t₁+v/(2*Real.pi))) X₁=0 ∨
      CenteredMomentHeckeHeight.rowTwistedSum ((anchors η j).product ω₂) pmask 1 z r.W₂
        (2*Real.pi*(r.t₂+v/(2*Real.pi))) X₂=0 := by
    rcases hs with ⟨hp,hs⟩|⟨hp,hs⟩
    · exact Or.inl (rowTwistedSum_eq_zero_of_small _ _ _ _ _ θ.a θ.b θ.ha0 r.hs₁ _ _ hp hs)
    · exact Or.inr (rowTwistedSum_eq_zero_of_small _ _ _ _ _ θ.a θ.b θ.ha0 r.hs₂ _ _ hp hs)
  have hmul (z : O) :
      CenteredMomentHeckeHeight.rowTwistedSum ((anchors η j).product ω₁) pmask 1 z r.W₁
        (2*Real.pi*(r.t₁+v/(2*Real.pi))) X₁ *
      CenteredMomentHeckeHeight.rowTwistedSum ((anchors η j).product ω₂) pmask 1 z r.W₂
        (2*Real.pi*(r.t₂+v/(2*Real.pi))) X₂=0 := by
    rcases hzero z with h|h <;> simp [h]
  simp only [hmul,mul_zero,zero_mul,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),ite_self,tsum_zero]

#print axioms frameChildE_eq_zero_small
end
end QRH.Cycle092.RegularColoredForward
