/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One true source-cap horizon serves every original restoration tuple and
inverse divisor. The reference companion uses only individual length caps. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamilyGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentEnergyBands
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open RestoredRootDictionary RestoredInitialSource
open QRH.Cycle090 QRH.Cycle092.NativeStrip QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- This is geometric source intake, uniform before any live marks,
characters, heights, first label, allocation or selected native class. -/
theorem earlier_divided_caps (N:ℕ) :
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
    ∀ (ι:Type) [Fintype ι] (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
      (hHr:RayOrthogonality.globalUnits M ≤ Hr)
      (r:RestoredRootSource.Data M Hr ι), r.Z=Z → Fintype.card ι ≤ N →
    ∀ (n y l X₁ X₂ t₁ t₂:ℝ),sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      l ≤ sourceWidth n y → (∑i,r.w i) ≤ l →
      0<X₁ → 0<X₂ → length Z X₁ ≤ n → length Z X₂ ≤ y →
      Z^shortWidth<X₁ → Z^shortWidth<X₂ →
    ∀d∈divisorPool (KernelRowPools.supportedRectangle (primeEnclosure Z) (9/4)
      (max X₁ (Z^shortWidth)) (max X₂ (X₁*X₂/Z^shortWidth))),
    ∀g:DividedLengths r.Z X₁ X₂ (Z^shortWidth) (X₁*X₂/Z^shortWidth) d,
      BallCaps (dividedCanonicalSource M Hr hHr r X₁ X₂ (Z^shortWidth)
        (X₁*X₂/Z^shortWidth) t₁ t₂ d g) Z n y r.w := by
  filter_upwards [restored_caps N] with Z hcaps
  refine ⟨hcaps.1,?_⟩
  intro ι inst M instM Hr hHr r hEq hN n y l X₁ X₂ t₁ t₂ hy0 hy1 hn hl hwr
    hX₁ hX₂ hxn hxy hlong₁ hlong₂ d hd g
  subst Z
  let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ (r.Z^shortWidth)
    (X₁*X₂/r.Z^shortWidth) t₁ t₂ d g
  have hp:∀i,s.P i=r.Z^(r.w i):=fun _=>rfl
  have href:=earlier_reference_bounds r.Z n y X₁ X₂ hcaps.1 hy1 hn hX₁ hX₂ hxn hxy hlong₁ hlong₂
  dsimp only at href
  exact hcaps.2 ι s (primeEnclosure r.Z) d X₁ X₂ (r.Z^shortWidth) (X₁*X₂/r.Z^shortWidth)
    (max X₁ (r.Z^shortWidth)) (max X₂ (X₁*X₂/r.Z^shortWidth)) n y l r.w
    hN r.hw hp hy0 hy1 hn hxn hxy hwr hl
    (by convert hlong₁.le using 1 <;> norm_num [shortWidth])
    (by convert hlong₂.le using 1 <;> norm_num [shortWidth])
    (by norm_num [shortWidth])
    (by convert href.2.2.2.2.2.2.1 using 1 <;> norm_num [shortWidth])
    (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
    href.2.2.2.2.2.2.2.2.1 href.2.2.2.2.2.2.2.2.2 hd rfl rfl rfl rfl rfl

#print axioms earlier_divided_caps
end
end QRH.Cycle092.ActualStageFrameBudget
