import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
import OAI.NumberTheory.DirichletL.Energy.WidthRanges

namespace QRHBoundsPR9
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (683505193 / 781250000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

theorem zeta {s : ℂ} (hs : (683505193 / 781250000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  sorry

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (683505193 / 781250000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  sorry

theorem exactAllDirichlet (ell : ℝ) (hlo : (1:ℝ)/6 ≤ ell) (hhi : ell ≤ (1:ℝ)/5)
    (hpoly : 927*ell^4 - 3135*ell^3 + 2433*ell^2 + 275*ell - 100 = 0)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 11/12 - ell/4 < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

theorem exactZeta (ell : ℝ) (hlo : (1:ℝ)/6 ≤ ell) (hhi : ell ≤ (1:ℝ)/5)
    (hpoly : 927*ell^4 - 3135*ell^3 + 2433*ell^2 + 275*ell - 100 = 0)
    {s : ℂ} (hs : 11/12 - ell/4 < s.re) : riemannZeta s ≠ 0 := by
  sorry

theorem exactAllHecke (ell : ℝ) (hlo : (1:ℝ)/6 ≤ ell) (hhi : ell ≤ (1:ℝ)/5)
    (hpoly : 927*ell^4 - 3135*ell^3 + 2433*ell^2 + 275*ell - 100 = 0)
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : 11/12 - ell/4 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  sorry

theorem quarticRootExistsUnique : ∃! ell : ℝ,
    (1:ℝ)/6 ≤ ell ∧ ell ≤ (1:ℝ)/5 ∧
      927*ell^4 - 3135*ell^3 + 2433*ell^2 + 275*ell - 100 = 0 := by
  sorry
end QRHBoundsPR9

namespace QRHBoundsPR9
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (3/4) ε
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
theorem plainMoment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) (hε : 0 < ε)
    (hbeta : 51 / 100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (commonMesh Mcap Bmask L ε) lo hi Mcap ε κ Z η₀ Q J S C := by
  sorry
end
end QRHBoundsPR9
