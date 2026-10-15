import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometryGeneric

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal_generic {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) :=
  lowUnselectedProduct_norm_upper_nominal ell b Z hZ slots hslots J p

lemma eventually_low_selected_caps_generic {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
        Z^(lowSelectedLength ell J+ε/2) :=
  eventually_low_selected_caps ell hell b ε hε

end SevenEighths.ProbePhysical
end
end OAI
