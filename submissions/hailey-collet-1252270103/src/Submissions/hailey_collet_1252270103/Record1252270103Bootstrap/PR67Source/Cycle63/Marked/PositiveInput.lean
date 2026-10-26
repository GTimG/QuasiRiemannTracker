import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.AnnularHeight
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open Cycle63MarkedHeight
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance positiveInputFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The full incumbent analytic induction supplies the actual marked input for
an arbitrary fixed common profile and arbitrary fixed relative anchor. All
row characters, masks, slot rays and heights remain quantified after scale. -/
theorem fixed_positive_input
    (W : ℝ→ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0<aslot) (hs : Function.support W⊆Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (ha : 0<a)
    (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0< radial) (hmask : 0≤Bmask)
    (hMcap : 0<Mcap) (hκ : (3/4:ℝ)≤κ) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃ degree : ℕ, ∃ seminorms : Finset (ℕ×ℕ), ∀ η₀ : Character,
      ∀ Q : Ideal O, Q≤M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
        internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃ C : ℝ, 0<C ∧ ∀ᶠ U : ℝ in atTop, 1<U ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ U η₀ Q degree seminorms C := by
  have hc := CenteredMomentEnergyCertifiedExistence.terminal_certificate (α:=α)
    M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε haslot hs hW hbslot
    ha haUpper hb hrad hmask hMcap hκ hε hβ hκβ
  obtain ⟨degree,seminorms,h⟩ := certified_terminal (α:=α) M H hH W bslot a b
    radial Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith) hε hc
  refine ⟨degree,seminorms,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C,hC₀,hC,hb⟩ := h η₀ Q hQM hQ0 hQt hQ72
  exact ⟨C,hC,hb.mono (fun U hU=>⟨hU.1,hU.2.2⟩)⟩

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
