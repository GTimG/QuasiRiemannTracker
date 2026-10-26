import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryWidth
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentCommonRadialData
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentFirstSourceConductorCaps Cycle63Moment Cycle63InitialMass
open CenteredMomentEnergyState CenteredMomentOriginalCommonHarmonic

/-- The first geometric character retains the polynomial conductor bound
of its literal fixed pair. No bound on the second character is substituted
for the first modulus. -/
theorem geometry_column_modulus_cap {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (hK : 0 < K) (bin : ℤ × (Fin 5 → ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let src := geometryFirstSource s R seed K Z ξ hK bin j.1
    ((geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus.absNorm : ℝ) ≤
      fixedPresentationCost * (s.η.modulus.absNorm : ℝ) * (src.C.absNorm : ℝ)^2 := by
  intro src
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  have hh := fixed_pair_caps s.η src.C src.D src.hC src.inactive
    j.2.2.1 j.2.2.2⁻¹ F
  cases reflected
  · exact hh.1
  · exact hh.2

/-- The hole ideal in the actual two-stage dictionary has polynomial
norm. Its first factor is controlled by the actual first source; its
second factor is exactly the retained state's puncture. -/
theorem eventually_geometry_holes_cap (η₀ : Character) (Bfirst Bmask : ℝ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
        (reflected second : Bool) (s : Input ι), s.η = η₀ →
      ∀ (R seed : Ideal O) (K ξ : ℝ) (hK : 0 < K) (bin : ℤ × (Fin 5 → ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (d : SecondInputDatum α) {bΦ : ℝ} (st : NaturalState Z Bmask bΦ),
      d.input.η = geometryColumnCharacter reflected s R seed K Z ξ hK bin j →
      st.puncture = d.R * (if second then d.D else d.C) →
      ((geometryFirstSource s R seed K Z ξ hK bin j.1).C.absNorm : ℝ) ≤ Z^Bfirst →
      let holes := d.input.η.modulus * (d.R * (if second then d.D else d.C))
      holes ≠ 0 ∧ (holes.absNorm : ℝ) ≤ Z^(2*Bfirst+Bmask+1) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (fixedPresentationCost * (η₀.modulus.absNorm : ℝ))]
    with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro ι α _ _ _ reflected second s hη R seed K ξ hK bin j d bΦ st hparent hpuncture hfirst holes
  have hholes : holes = d.input.η.modulus * st.puncture := by
    dsimp [holes]
    rw [hpuncture]
  rw [hholes]
  refine ⟨mul_ne_zero d.input.η.modulus_ne_bot st.puncture_ne_zero,?_⟩
  have hcap := geometry_column_modulus_cap reflected s R seed K Z ξ hK bin j
  rw [←hparent,hη] at hcap
  have hZp : 0 < Z := zero_lt_one.trans hZ
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ (fixedPresentationCost * (η₀.modulus.absNorm : ℝ) *
        ((geometryFirstSource s R seed K Z ξ hK bin j.1).C.absNorm : ℝ)^2) *
        Z^Bmask := mul_le_mul hcap st.puncture_bound (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)) (sq_nonneg _))
    _ ≤ (Z * (Z^Bfirst)^2) * Z^Bmask := by gcongr
    _ = Z^(1:ℝ) * (Z^Bfirst)^2 * Z^Bmask := by rw [Real.rpow_one]
    _ = Z^(2*Bfirst+Bmask+1) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le,
        ←Real.rpow_add hZp,←Real.rpow_add hZp]
      congr 1
      norm_num
      ring

/-- An additional sixth-power row mask is represented by its root ideal.
Its polynomial cost is additive, without charging the sixth power. -/
theorem holes_with_root_norm (R A : Ideal O) (U b a : ℝ) (hU : 0 < U)
    (hR : (R.absNorm : ℝ) ≤ U^b) (hA : (A.absNorm : ℝ) ≤ U^a) :
    ((R*A).absNorm : ℝ) ≤ U^(b+a) := by
  simp only [map_mul,Nat.cast_mul]
  rw [Real.rpow_add hU]
  exact mul_le_mul hR hA (Nat.cast_nonneg _) (Real.rpow_nonneg hU.le _)

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
