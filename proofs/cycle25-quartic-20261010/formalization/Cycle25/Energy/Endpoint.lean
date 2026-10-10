import Cycle25.Energy.CertifiedExistence
import Cycle25.Energy.KappaGeometry

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace Cycle25.Energy

open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges

local notation "O" => HeckeFamily.O

/-- Independent of the arithmetic family, slot count, profiles and target height. -/
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (3 / 4) ε

theorem commonMesh_pos (Mcap Bmask L ε : ℝ) (hM : 0 ≤ Mcap)
    (hB : 0 ≤ Bmask) (hε : 0 < ε) : 0 < commonMesh Mcap Bmask L ε := by
  exact (bounds Mcap (finalSourceCap Mcap Bmask L ε) (3 / 4) ε hM
    (sourceCap_nonneg Mcap Bmask L hM hB _) (by norm_num) hε).2.2.2.2.1

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The original canonical ray-prime family with one common smooth slot profile.
The zero-slot input is supplied by the completed unconditional endpoint. -/
theorem terminal_positive_at
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
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκlo hε hbeta hκbeta
  obtain ⟨J, S, hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith) hε hcert
  have hmesh := compact_mesh_le Mcap Bmask L κ ε hMcap.le hmask hε hκlo hκhi
  refine ⟨J, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz, Cp, _, hCp, hz⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cp, hCp, ?_⟩
  filter_upwards [hz] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p
    X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity
  exact hZ.2.2 T θ w σ v t height hw (fun i => (hwL i).trans hmesh)
    hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity

end Cycle25.Energy
