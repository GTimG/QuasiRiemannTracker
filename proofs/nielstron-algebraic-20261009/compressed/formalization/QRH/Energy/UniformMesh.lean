import OAI.NumberTheory.DirichletL.Energy.WidthRanges
import OAI.NumberTheory.DirichletL.Energy.Bands

/-! A κ-independent mesh and monotonicity of the actual masked energy predicate.
The mesh is independent of the finite slot type; no moment bound is assumed here. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.QRHUniformMesh
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyWidthSchedule
open HeckeFamily CenteredMomentEnergyBands

lemma fineMesh_uniform_lower (M B L κ ε : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    0 < fineMesh M B L 1 ε ∧ fineMesh M B L 1 ε ≤ fineMesh M B L κ ε := by
  have hp := fineMesh_pos M B L 1 ε hM hB (by norm_num) hε
  refine ⟨hp, ?_⟩
  have hr : 0 ≤ reserve M (finalSourceCap M B L ε) ε :=
    (bounds M (finalSourceCap M B L ε) κ ε hM
      (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.1.le
  unfold fineMesh mesh
  exact div_le_div_of_nonneg_left hr (by linarith) (by linarith)

local notation "O" => HeckeFamily.O
variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Raising κ shrinks the admitted capacities, and shrinking the slot mesh admits
fewer weights. The actual energy, mask and coefficient expressions stay identical. -/
theorem positiveAt_kappa_mesh_mono (W : ℝ → ℂ)
    (bslot a b radial Bmask L meshOld meshNew lo hi Mcap ε κOld κNew Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (hκ : κOld ≤ κNew) (hmesh : meshNew ≤ meshOld)
    (h : PositiveAt (α := α) M H hH W bslot a b radial Bmask L meshOld
      lo hi Mcap ε κOld Z η₀ Q degree S C) :
    PositiveAt (α := α) M H hH W bslot a b radial Bmask L meshNew
      lo hi Mcap ε κNew Z η₀ Q degree S C := by
  intro T θ w σ v t height hw hwmesh hσlo hσhi hheight hv
    s hQ hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hkc : 6 * κOld * (∑ i, w i) ≤ 6 * κNew * (∑ i, w i) :=
    mul_le_mul_of_nonneg_right (by linarith) hsum
  exact h T θ w σ v t height hw (fun i => (hwmesh i).trans hmesh)
    hσlo hσhi hheight hv s hQ hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ (by linarith)

end SevenEighths.QRHUniformMesh
end
end OAI
