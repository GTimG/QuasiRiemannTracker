import Submissions.hailey_collet_1252270103.Cycle25.Energy.Endpoint
import Submissions.hailey_collet_1252270103.Cycle61.Assembly.Baseline

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Both incumbent endpoints are genuine original analytic inputs, with a
single degree and profile control. No affine or improved endpoint is used. -/
theorem original_incumbent
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S C₀ ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε (3/4)
          Z η₀ Q degree S C₁ := by
  have hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) := by
    linarith [Cycle61.Assembly.baseline_beta]
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap (3/4) ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap (by norm_num) hε hbeta hκ
  exact certified_terminal (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap
    (3/4) ε hmask hMcap.le (by norm_num) hε hcert

#print axioms original_incumbent
end
end OAI.SevenEighths.Cycle61Moment.LowBranch
