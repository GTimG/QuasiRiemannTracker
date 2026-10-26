import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Prior
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance incumbentFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [Fintype α] [DecidableEq α] in
/-- A moment bound for slots up to a length holds for the slots up to any smaller length. -/
theorem positiveAt_of_le {W : ℝ → ℂ} {bslot a b radial Bmask L L₁ L₂ lo hi Mcap ε κ Z : ℝ}
    {η₀ : Character} {Q : Ideal O} {degree : ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ}
    (h : PositiveAt (α := α) M H hH W bslot a b radial Bmask L L₁ lo hi Mcap ε κ Z η₀ Q degree S C)
    (hL : L₂ ≤ L₁) :
    PositiveAt (α := α) M H hH W bslot a b radial Bmask L L₂ lo hi Mcap ε κ Z η₀ Q degree S C :=
  fun T θ w σ v t height hw hwL => h T θ w σ v t height hw (fun i => (hwL i).trans hL)

/-- The common slot-length cap is the fine mesh at the baseline price `3/4`; the fine mesh
`reserve/(κ + 1)` is larger at every price `κ ≤ 3/4`. -/
theorem commonMesh_le_fineMesh {Mcap Bmask L ε κ : ℝ} (hMcap : 0 ≤ Mcap) (hBmask : 0 ≤ Bmask)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hκ' : κ ≤ 3/4) :
    Cycle25.Energy.commonMesh Mcap Bmask L ε ≤ CenteredMomentEnergyWidthRanges.fineMesh Mcap Bmask L κ ε := by
  have hr := (CenteredMomentEnergyWidthSchedule.bounds Mcap
    (CenteredMomentEnergyWidthRanges.finalSourceCap Mcap Bmask L ε) κ ε hMcap
    (CenteredMomentEnergyWidthRanges.sourceCap_nonneg Mcap Bmask L hMcap hBmask _) hκ hε).2.2.2.1
  unfold Cycle25.Energy.commonMesh CenteredMomentEnergyWidthRanges.fineMesh
    CenteredMomentEnergyWidthSchedule.mesh
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

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
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε Cycle63.Optimization.slotPrice
          Z η₀ Q degree S C₁ := by
  have hκ := Cycle63.Assembly.slotPrice_admissible
  have hκ0 : (7/10 : ℝ) ≤ Cycle63.Optimization.slotPrice := by
    linarith [Cycle63.Optimization.slotPrice_mem.1]
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap Cycle63.Optimization.slotPrice ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
  obtain ⟨degree, S, h⟩ := certified_terminal (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap
    Cycle63.Optimization.slotPrice ε hmask hMcap.le Cycle63.Optimization.slotPrice_pos.le hε hcert
  have hmesh := commonMesh_le_fineMesh (L := L) hMcap.le hmask hε Cycle63.Optimization.slotPrice_pos.le
    Cycle63.Optimization.slotPrice_mem.2
  refine ⟨degree, S, fun η₀ Q hQ h0 h1 h72 => ?_⟩
  obtain ⟨C₀, C₁, hC₀, hC₁, hZ⟩ := h η₀ Q hQ h0 h1 h72
  exact ⟨C₀, C₁, hC₀, hC₁, hZ.mono fun Z hZ => ⟨hZ.1, hZ.2.1, positiveAt_of_le M H hH hZ.2.2 hmesh⟩⟩

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
