import Submissions.hailey_collet_1252270103.Record12518109Gain.Selection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness

namespace OAI.SevenEighths.Record12518109GainActual
noncomputable section
open HeckeFamily HeckeDetectorSupportedWitness
open Record12518109Gain

theorem actual_homogeneous_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀S : ℝ,0≤S →31/50≤2*a-1 →2*a-1≤3/4 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε (cutoff (2*a-1) S)
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSupportedWitness.actual_supported_witness_family
    dmin dmax τ ε e κ η I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label inst χ hχ a i hi ha ha' hnext hcurrent hQ S hS hν0 hν1
  have hs := selection_bounds hν0 hν1 hS
  exact hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha' hnext hcurrent hQ _ hs.2.2.1
    (hs.2.2.2.1.trans (by norm_num))

end
end OAI.SevenEighths.Record12518109GainActual
