import QRH.Energy.CertifiedExistence
import QRH.Energy.UniformMesh

/-! Actual masked moment bounds obtained from the extended analytic width induction.
The κ-independent mesh has no finite-slot-type parameter. All energy objects are
upstream originals. The original lower bound on the zero supremum remains explicit. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.QRHPlainMoment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyWidthRanges
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCertifiedExistence QRHUniformMesh
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_uniform_moment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot) (ha : 0 < a)
    (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    0 < fineMesh Mcap Bmask L 1 ε ∧
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        ∀ κ : ℝ, (13/18 : ℝ) ≤ κ → 2*HeckeZeroSupremum.beta-1 ≤ κ →
          PositiveAt (α := α) M H hH W bslot a b radial Bmask L
            (fineMesh Mcap Bmask L 1 ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive := by
  let κ₀ : ℝ := max (13/18) (2*HeckeZeroSupremum.beta-1)
  have hklo : (13/18 : ℝ) ≤ κ₀ := le_max_left _ _
  have hkb : 2*HeckeZeroSupremum.beta-1 ≤ κ₀ := le_max_right _ _
  have hk0 : 0 ≤ κ₀ := by linarith
  have hk1 : κ₀ ≤ 1 := max_le (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one])
  have hm := fineMesh_uniform_lower Mcap Bmask L κ₀ ε hMcap.le hmask hk0 hk1 hε
  have hc := terminal_certificate_extended (α := α) M H hH W aslot bslot
    a b radial Bmask L lo hi Mcap κ₀ ε haslot hWs hW hbslot ha haUpper hb hrad
    hmask hMcap hklo hε hbeta hkb
  obtain ⟨degree, S, hbound⟩ := certified_terminal M H hH W bslot a b radial Bmask L
    lo hi Mcap κ₀ ε hmask hMcap.le hk0 hε hc
  refine ⟨hm.1, degree, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, hCzero, hCpositive, hbound⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero, Cpositive, hCzero, hCpositive, ?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1, hZ.2.1, ?_⟩
  intro κ hklo' hkb'
  exact positiveAt_kappa_mesh_mono M H hH W bslot a b radial Bmask L
    (fineMesh Mcap Bmask L κ₀ ε) (fineMesh Mcap Bmask L 1 ε) lo hi Mcap ε κ₀ κ Z
    η₀ Q degree S Cpositive (max_le hklo' hkb') hm.2 hZ.2.2

end SevenEighths.QRHPlainMoment
end
end OAI
