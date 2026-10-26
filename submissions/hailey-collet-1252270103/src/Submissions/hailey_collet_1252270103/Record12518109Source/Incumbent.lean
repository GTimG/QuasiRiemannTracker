/- Adapted by Hailey Collet from the PR63 natural-terminal assembly of
Zhongpai Gao, retaining OpenAI, Hailey Collet, DaysSky and predecessor
attribution. Apache-2.0. The previously proved beta cap is explicit. -/
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Endpoint

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109SourceLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Original natural/zero moments at any established compact incumbent.
The degree and profile control precede the base character and moving data. -/
theorem incumbent_at
    (κI : ℝ) (hκlo : 7/10 ≤ κI) (hκhi : κI ≤ 3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κI)
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
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε κI
          Z η₀ Q degree S C₁ := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κI ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκlo hε hbeta hκbeta
  obtain ⟨degree,S,hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap κI ε hmask hMcap.le (by linarith) hε hcert
  have hmesh := Cycle25.Energy.compact_mesh_le Mcap Bmask L κI ε
    hMcap.le hmask hε hκlo hκhi
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hev⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C₀,C₁,hC₀,hC₁,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,hZ.2.1,?_⟩
  intro T θ w σ v t height hw hwL hσlo hσhi hh hv s hQ hs p
    X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  exact hZ.2.2 T θ w σ v t height hw (fun i => (hwL i).trans hmesh)
    hσlo hσhi hh hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity

end
end OAI.SevenEighths.Record12518109SourceLow
#print axioms OAI.SevenEighths.Record12518109SourceLow.incumbent_at
