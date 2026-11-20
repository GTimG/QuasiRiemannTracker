/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A single measured marked factor selects the core. The positive width cutoff
and the finite slot dictionary may be chosen after the mesh. -/
import Candidate.C092.transport.HighResponse
import Candidate.C092.transport.ActualColumn
namespace QRH.Cycle092.SelectedMark
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

def one {N : ℕ} (d : SelectedSlotData N) (j : Fin N) (δ : ℝ) : SelectedSlotData 1 :=
  ⟨fun _ => d.width j,fun _ => δ*d.width j,fun _ => d.sources j,fun _ => d.coefficient j⟩

theorem operator (amax loss : ℝ) (ha : 1 ≤ amax) (hl : 0 < loss) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ B wmin : ℝ, 0 ≤ B → 0 < wmin →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (N : ℕ) (d : SelectedSlotData N) (j : Fin N) (cores : Finset FreeRow)
        (mesh V Y X : ℝ), 0 ≤ mesh → mesh ≤ μ → d.Bounded Z mesh B → wmin ≤ d.width j →
        (∀ u ∈ cores, Z^((5001/10000:ℝ)*d.width j) ≤ ‖d.polynomial j u.val‖^2) →
        98/100 ≤ V → 1 ≤ Y → Y ≤ Z^amax → Y ≤ Z^V → (∀ u ∈ cores, rowNorm u ≤ Y) →
        1 ≤ X → X ≤ Z^(919/1000:ℝ) → ∀ (S : Finset (Ideal O)) (c : S → ℂ),
        (∀ I ∈ S, (I.absNorm : ℝ) ≤ X) →
          (∑ z : cores.image Subtype.val, ‖FineDetectorWords.ordinaryPolynomial S c z.val‖^2) ≤
            C*Z^(V-305/10000+loss)*∑ I, ‖c I‖^2 := by
  obtain ⟨μ,hμ,hmesh⟩ := NaturalSelectedNorm.natural_selected_cell_norm amax (3*amax+1) (1/10000) loss (by linarith) le_rfl (by norm_num) (by norm_num) hl
  refine ⟨μ,hμ,?_⟩; intro B wmin hB hw
  obtain ⟨C,Z₀,hC,hZ₀⟩ := hmesh 1 B wmin hB hw
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hZ₀' hZ
  refine ⟨hZ,?_⟩; intro N d j cores mesh V Y X hm hm' hd hwidth hsel hV hY hY' hYV hcore hX hX' S c hS
  let p := one d j (5001/10000)
  have hbd : p.Bounded Z mesh B := ⟨fun _ => hd.width_nonneg j,fun _ => hd.width_le_mesh j,fun _ => hd.source_nonzero j,fun _ => hd.source_norm j,fun _ => hd.coefficient_mass j⟩
  have hselect : p.Selects Z (cores.image Subtype.val) := by
    intro z hz i; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz; exact hsel u hu
  have hslope : p.HasSlope (5001/10000) := by simp [SelectedSlotData.HasSlope,p,one]
  have hw' : wmin ≤ ∑ i, p.width i := by simpa [p,one] using hwidth
  have hbound := hZ₀ Z mesh (5001/10000) hZ₀' hm hm' (by norm_num) (by norm_num)
    p cores S Y X hbd hselect hslope hw' hY hY' hcore hX
    (hX'.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))) hS
  have hs := HighResponse.saving hZ.le hV le_rfl hX' hYV (by linarith) (by linarith)
  have he := (FineDetectorWords.ordinaryPolynomial_energy (cores.image Subtype.val) S c).trans (mul_le_mul_of_nonneg_right
    (hbound.trans (mul_le_mul_of_nonneg_left hs (by positivity))) (by positivity))
  calc
    _ ≤ C*Z^loss*(2*Z^(V-305/10000))*∑ I, ‖c I‖^2 := he
    _ = _ := by rw [Real.rpow_add (zero_lt_one.trans hZ)]; ring

#print axioms operator
end
end QRH.Cycle092.SelectedMark
