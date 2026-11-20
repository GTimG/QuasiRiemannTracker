/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairSource
import Candidate.C092.transport.SmallCoreNative

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

/-- Absolute duplicated-fourth quota. A saturated ordinary cap receives
no marks and is handled by its authentic unmarked fourth. -/
def fourthQuota (a V : ℝ) : ℝ:=max 0 (V/2-a-1/1000)

theorem fourth_quota_total (n y V : ℝ) :
    SmallCore.quota n y V  ≤  (fourthQuota n V+fourthQuota y V)/2 := by
  have hn:=le_max_right (0:ℝ) (V/2-n-1/1000)
  have hy:=le_max_right (0:ℝ) (V/2-y-1/1000)
  dsimp [fourthQuota,SmallCore.quota] at *
  linarith

/-- The same fixed native positive face supplies every nonsaturated
homogeneous fourth, with its actual ordinary length cap and quota. -/
theorem homogeneous_native_admissible {a V x z s : ℝ}
    (ha : (369/1000:ℝ) ≤ a) (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100)
    (hq : 0<fourthQuota a V)
    (hb : Box (a/V) (a/V) (fourthQuota a V/V) x z s) :
    (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face nativeCost).Admissible x z s 1 := by
  have hV : 0<V := (by norm_num [radiusMin] : (0:ℝ)<radiusMin).trans_le hV0
  have heq : fourthQuota a V=V/2-a-1/1000 := by
    dsimp [fourthQuota] at *
    rcases lt_max_iff.mp hq with h|h
    · linarith
    · exact max_eq_right h.le
  have hq' : 0<V/2-a-1/1000 := by rwa [heq] at hq
  obtain ⟨hx,hz,hpair,hs,hsl⟩:=hb
  have hxcap : x ≤ a/V := by rcases hpair with h|h <;> exact h.1
  have hzcap : z ≤ a/V := by rcases hpair with h|h <;> exact h.2
  have hacap : a/V ≤ 1/2 := (div_le_iff₀ hV).mpr (by linarith)
  have hsnum : s*V ≤ fourthQuota a V := (le_div_iff₀ hV).mp hsl
  have hqcap : fourthQuota a V/V ≤ 1/8 := by
    apply (div_le_iff₀ hV).mpr
    rw [heq]
    linarith
  have hnum : 2*a+(2+10*nativeCost)*fourthQuota a V ≤ V*(1-nativeCost) := by
    rw [heq]
    norm_num [nativeCost] at *
    nlinarith
  have hbudget : a/V+a/V+(2+10*nativeCost)*(fourthQuota a V/V) ≤ 1-nativeCost := by
    rw [show a/V+a/V+(2+10*nativeCost)*(fourthQuota a V/V)=
      (2*a+(2+10*nativeCost)*fourthQuota a V)/V by ring]
    exact (div_le_iff₀ hV).mpr (by nlinarith [hnum])
  have hsl':=mul_le_mul_of_nonneg_left hsl
    (show 0 ≤ 2+10*nativeCost by norm_num [nativeCost])
  dsimp [SourceFace.Admissible,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face]
  simp only [mul_one]
  refine ⟨hx,hxcap.trans hacap,hz,hzcap.trans hacap,hs,?_,?_⟩
  · norm_num [nativeCost] at *
    linarith
  · linarith [hsl.trans hqcap]

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem homogeneous_native_labelled {a V bslot lo hi bΦ mesh σlo σhi ε U C : ℝ}
    {W : ℝ→ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (ha : (369/1000:ℝ) ≤ a) (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100)
    (hq : 0<fourthQuota a V)
    (hsrc : InitialAffineAt (α:=Slot) rayM Hr hHr
      (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face nativeCost)
      W bslot lo hi bΦ mesh σlo σhi 1 1 ε U η η₀ Q degree controls C) :
    LabelledAt (α:=Slot) rayM Hr hHr (a/V) (a/V) (fourthQuota a V/V)
      W bslot lo hi bΦ mesh σlo σhi 1 1 ε U η η₀ Q degree controls C := by
  intro T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hb
  have he : M=1:=le_antisymm hM' hM
  subst M
  exact hsrc T θ w σ v t height hw hwm hlo hhi hh hv 1 le_rfl le_rfl Φ hΦs hΦ p X₁ X₂
    hX₁ hX₂ (homogeneous_native_admissible ha hV0 hV1 hq hb)

#print axioms fourth_quota_total
#print axioms homogeneous_native_admissible
#print axioms homogeneous_native_labelled
end
end QRH.Cycle092.StrongPair
