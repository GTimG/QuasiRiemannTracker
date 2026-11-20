/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Actual dyadic windows at Kc up to Z^40, with a real logarithmic box. -/
import Candidate.C092.transport.ActualLabelFiniteCostsMultiplicity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
namespace QRH.Cycle092.ActualLabelFiniteCosts
local notation "Id" => Ideal HeckeFamily.O

/-- Rescale only the bounding parameter in Sil's genuine box construction.
All actual Kc/R/H and all four original dyadic indices stay unchanged. -/
theorem box_of_power40 (S : Finset Id) (Kc R H Z : ℝ) (hZ : 2≤Z)
    (hX : ∀I∈S,(I.absNorm:ℝ)≤Z^(8:ℝ)) (hK1 : 1≤Kc) (hK : Kc≤Z^(40:ℝ))
    (hR : 4*R≤Z^(40:ℝ)) (hH : H≤Z^(40:ℝ)) :
    ∃ M : ℤ,0≤M ∧ (M:ℝ)≤57*Real.logb 2 Z+2 ∧
      ∀l n,inRange S Kc R H l n → n∈box M := by
  have hZ1 : 1<Z := by linarith
  have hZ0 : 0<Z := zero_lt_one.trans hZ1
  have hcube : 2≤Z^(3:ℝ) := hZ.trans (by
    calc Z=Z^(1:ℝ) := (Real.rpow_one Z).symm
         _≤Z^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num))
  have hpow18 : Z^(40:ℝ)≤(Z^(3:ℝ))^(18:ℝ) := by
    rw [←Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
  have hpow8 : Z^(8:ℝ)≤(Z^(3:ℝ))^(8:ℝ) := by
    rw [←Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
  obtain ⟨M,⟨hM,hsize⟩,hbox⟩ := box_exists S Kc R H (Z^(3:ℝ)) 19 hcube (by norm_num)
    (fun I hI=>(hX I hI).trans hpow8) hK1 (hK.trans hpow18) (hR.trans hpow18) (hH.trans hpow18)
  refine ⟨M,hM,?_,hbox⟩
  rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0] at hsize
  nlinarith

/-- The original frequency radius has a generous common polynomial cap. -/
theorem frequency_radius_power40 (Tsec Z ξ : ℝ) (hZ : 2≤Z) (hT0 : 0≤Tsec)
    (hT : Tsec≤Z^(36:ℝ)) (hξ : ξ≤1) : 4*frequencyRadius Tsec Z ξ≤Z^(40:ℝ) := by
  have hZ1 : 1<Z := by linarith
  have hZ0 : 0<Z := zero_lt_one.trans hZ1
  have h4 : (4:ℝ)≤Z^(2:ℝ) := by rw [Real.rpow_two]; nlinarith
  have hf : Z^(ξ/2)≤Z^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  unfold frequencyRadius
  calc
    _≤Z^(2:ℝ)*(Z^(36:ℝ)*Z^(1/2:ℝ)) := by gcongr
    _=Z^(77/2:ℝ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0];congr 1;ring
    _≤_ := Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)

/-- One threshold before every actual source and its real windows. -/
theorem eventually_box (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ Z : ℝ in atTop,2≤Z ∧ ∀ (S : Finset Id) (Kc R H : ℝ),
      (∀I∈S,(I.absNorm:ℝ)≤Z^(8:ℝ)) → 1≤Kc → Kc≤Z^(40:ℝ) →
      4*R≤Z^(40:ℝ) → H≤Z^(40:ℝ) → ∃ M : ℤ,0≤M ∧
      (M:ℝ)≤57*Real.logb 2 Z+2 ∧ ((box M).card:ℝ)≤Z^δ ∧
      ∀l n,inRange S Kc R H l n → n∈box M := by
  filter_upwards [box_card_subpower 57 δ (by norm_num) hδ,eventually_ge_atTop (2:ℝ)] with Z hb hZ
  refine ⟨hZ,?_⟩
  intro S Kc R H hX hK1 hK hR hH
  obtain ⟨M,hM,hsize,hbox⟩ := box_of_power40 S Kc R H Z hZ hX hK1 hK hR hH
  exact ⟨M,hM,hsize,hb M hM hsize,hbox⟩

#print axioms box_of_power40
#print axioms frequency_radius_power40
#print axioms eventually_box
end QRH.Cycle092.ActualLabelFiniteCosts
