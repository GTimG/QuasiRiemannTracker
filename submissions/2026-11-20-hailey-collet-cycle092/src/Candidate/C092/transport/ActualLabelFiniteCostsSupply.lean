/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   The two finite combinatorial inputs to the original fixed/regular split. -/
import Candidate.C092.transport.ActualLabelFiniteCostsBox
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
namespace QRH.Cycle092.ActualLabelFiniteCosts
local notation "Id" => Ideal HeckeFamily.O

/-- C is fixed before Z, colors, sources, phases and real windows.
The original box cardinal and original common-label multiplicity are both
retained, and their product costs only C Z^δ. -/
theorem finite_costs (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,2≤Z ∧
      ∀ {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Character),
      (∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) →
      ∀ (Kc R H : ℝ),1≤Kc → Kc≤Z^(40:ℝ) → 4*R≤Z^(40:ℝ) → H≤Z^(40:ℝ) →
      ∃ (Mm : ℕ) (M : ℤ),
        (Mm:ℝ)≤C*Z^(δ/2) ∧ 0≤M ∧ (M:ℝ)≤57*Real.logb 2 Z+2 ∧
        ((box M).card:ℝ)≤Z^(δ/2) ∧ ((box M).card:ℝ)*(Mm:ℝ)≤C*Z^δ ∧
        (∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
          IsColumn _ g → ∀G A,((Finset.univ : Finset (Lab
            (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
              (fun l=>g l=G ∧ lA _ l=A)).card≤Mm) ∧
        ∀l n,inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc R H l n → n∈box M := by
  obtain ⟨C,hC,hmult⟩ := actual_multiplicity (δ/2) (by positivity)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_box (δ/2) (by positivity)] with Z hbox
  refine ⟨hbox.1,?_⟩
  intro ι inst a b s ha ω₁ ω₂ hX Kc R H hK1 hK hR hH
  obtain ⟨Mm,hMm,hm⟩ := hmult Z (by linarith [hbox.1]) s ha ω₁ ω₂ hX
  obtain ⟨M,hM,hsize,hcard,hb⟩ := hbox.2 _ Kc R H hX hK1 hK hR hH
  have hZ0 : 0<Z := by linarith [hbox.1]
  refine ⟨Mm,M,hMm,hM,hsize,hcard,?_,hm,hb⟩
  calc
    _≤Z^(δ/2)*(C*Z^(δ/2)) := mul_le_mul hcard hMm (Nat.cast_nonneg _) (by positivity)
    _=C*(Z^(δ/2)*Z^(δ/2)) := by ring
    _=C*Z^(δ/2+δ/2) := by rw [Real.rpow_add hZ0]
    _=C*Z^δ := by congr 2; ring

/-- Ready for the actual second window Kc=16 K W^4 and
R=frequencyRadius Tsec Z ξ. The numerical gates are the genuine coarse
producer bounds; the label and dyadic costs are derived, never assumed. -/
theorem actual_window_finite_costs (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,2≤Z ∧
      ∀ {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Character),
      (∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) →
      ∀ (Kc Tsec ξ H : ℝ),8≤Kc → Kc≤Z^(2:ℝ) → 0≤Tsec → Tsec≤Z^(2:ℝ) → ξ≤1 → H≤Z^(8:ℝ) →
      ∃ (Mm : ℕ) (M : ℤ),
        (Mm:ℝ)≤C*Z^(δ/2) ∧ 0≤M ∧ (M:ℝ)≤57*Real.logb 2 Z+2 ∧
        ((box M).card:ℝ)≤Z^(δ/2) ∧ ((box M).card:ℝ)*(Mm:ℝ)≤C*Z^δ ∧
        (∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
          IsColumn _ g → ∀G A,((Finset.univ : Finset (Lab
            (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
              (fun l=>g l=G ∧ lA _ l=A)).card≤Mm) ∧
        ∀l n,inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc
          (frequencyRadius Tsec Z ξ) H l n → n∈box M := by
  obtain ⟨C,hC,hcost⟩ := finite_costs δ hδ
  refine ⟨C,hC,hcost.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst a b s ha ω₁ ω₂ hX Kc Tsec ξ H hK8 hK hT0 hT hξ hH
  have hZ1 : 1≤Z := by linarith [hz.1]
  have hK40 : Kc≤Z^(40:ℝ) := hK.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num))
  have hT36 : Tsec≤Z^(36:ℝ) := hT.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num))
  have hH40 : H≤Z^(40:ℝ) := hH.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num))
  exact hz.2 s ha ω₁ ω₂ hX Kc (frequencyRadius Tsec Z ξ) H (by linarith) hK40
    (frequency_radius_power40 Tsec Z ξ hz.1 hT0 hT36 hξ) hH40

#print axioms finite_costs
#print axioms actual_window_finite_costs
end QRH.Cycle092.ActualLabelFiniteCosts
