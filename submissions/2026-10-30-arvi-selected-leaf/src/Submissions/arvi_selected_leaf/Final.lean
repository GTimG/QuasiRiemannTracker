/-
The final bound from the selected-leaf line, without the density chain.

The return (`Return/`, certified by `Tuning/`, three count windows) reads one global source, the end face
`G(99999/100000, 401/200, 13399/100000)` of the selected-leaf line (`Curve.e5_end`), for the count windows and for the
capped physical windows alike. The line starts at the end of the native line `G(99999/100000, 5143/2000, 1/10)`
(PR 76's fourth-power source `face0_source` and Sil's native cube-free step, `NativeStart.native_end`) and descends by
the selected-leaf step (`e5_step`) given the selected root energy at the cut `K = 501/1000` (R1, `selectedRootEnergy`).
No face of the 129-step density chain, no `arvi_density/Density/*`, no `Source/Hybrid*` and no `ChainK15` is used.
-/
import Submissions.arvi_selected_leaf.Notices
import Submissions.arvi_selected_leaf.Curve
import Submissions.arvi_selected_leaf.R1.Cap
import Submissions.arvi_selected_leaf.Tuning.Endpoint

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- R1 at the cut `K = 501/1000` of the selected-leaf line. -/
theorem selectedRootEnergy_sK : SelectedRootEnergy sK :=
  selectedRootEnergy sK (by unfold sK; norm_num) (by unfold sK; norm_num)

/-- The end face of the line with its cap as the literal `13399/100000`. -/
theorem e5_end_cap (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (401/200) (13399/100000) := by
  have e : (1/10 + 3/50 * (5143/2000 - 401/200) : ℝ) = 13399/100000 := by norm_num
  have h := e5_end hR1 hβ
  rwa [e] at h

/-- **The endpoint bound of the return from the selected-leaf line**, given the selected root energy. -/
theorem beta_le_theta_of_R1 (hR1 : SelectedRootEnergy sK) :
    HeckeZeroSupremum.beta ≤ (43670599/50000000 : ℝ) :=
  QRH.ArviDensity.Return.Tuning.beta_le_theta_of_sources (fun hβ => e5_end_cap hR1 hβ)
    (fun hβ => e5_end_cap hR1 hβ)

/-- **The endpoint bound of the return**: `β ≤ θ = 43670599/50000000 = 0.87341198`. -/
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (43670599/50000000 : ℝ) :=
  beta_le_theta_of_R1 selectedRootEnergy_sK

/-- **All-moduli Dirichlet nonvanishing** for `Re s > 43670599/50000000 = 0.87341198`. -/
theorem dirichlet_nonvanishing_e5 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43670599 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.Return.Tuning.dirichlet_of_sources (fun hβ => e5_end_cap selectedRootEnergy_sK hβ)
    (fun hβ => e5_end_cap selectedRootEnergy_sK hβ) χ hs hpole

end
end QRH.ArviSelectedLeaf

#print axioms QRH.ArviSelectedLeaf.beta_le_theta
#print axioms QRH.ArviSelectedLeaf.dirichlet_nonvanishing_e5
