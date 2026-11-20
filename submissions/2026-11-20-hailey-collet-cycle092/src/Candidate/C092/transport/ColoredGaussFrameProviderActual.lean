/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Literal finite colored classes and their genuine native frame label images. -/
import Candidate.C092.transport.ColoredGaussFrameProviderColumns
import Candidate.C092.transport.ColoredGaussFrameProviderRenormFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The native class set is filtered only after forming the actual colored
    coefficient. No zero of the uncolored aggregate is used. -/
def actualClass (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Character)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ) (n : Fin 4→ℤ) :=
  (Finset.univ : Finset (Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
    (fun l=>inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc R H l n ∧
      classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) ψ χ₀ Q m t Kc R l n≠0)

theorem grouped_regular_le_classes (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ ψ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc Tsec Z ξ H : ℝ) (hKc : 0<Kc) (M : ℤ)
    (hbox : ∀l n,inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc
      (frequencyRadius Tsec Z ξ) H l n→n∈box M) :
    RootColoredSeed.groupedPartTerms false s ha (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t Kc Tsec Z ξ H ≤
    ∑n∈box M,∑l∈actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc
      (frequencyRadius Tsec Z ξ) H n,
      classWeight (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc l n *
      ‖classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) ψ χ₀ Q m t Kc
        (frequencyRadius Tsec Z ξ) l n‖ :=
  splitLabel_le_classes _ _ ψ χ₀ Q m t Kc _ H hKc M hbox

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

def actualFrameLabels (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (n : Fin 4→ℤ) (χ : RayCharacter) : Finset (GLabel θ mesh Z) :=
  ((actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n).sigma
    (labelPool (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).image
      (fun k=>(frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)

/-- Fits is proved for every actual image label from the genuine coefficient
    carrier, cube-free constraints, source norm cap, and original hole data. -/
theorem actualFrameLabels_fits (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayCharacter)
    (hholes : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap))
    (hR₀ : ∀i,∀P∈s.H,P.val∈rs.R₀ i) (X : ℝ)
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤X)
    (hbudget : (s.R.absNorm:ℝ)*X^2*((∏I∈holes s.H,I).absNorm:ℝ)≤Z^θ.Bmask) :
    ∀x∈actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ,Fits η rs x := by
  intro x hx
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
  exact toLabel_fits η rs _ (frame_good ω₁ ω₂ s ha rs j₀ ξ g hg n χ k
    (Finset.mem_sigma.mp hk).2 hholes hR₀ X hX hbudget)

/-- Native Bmask≥24 fits every actual label under the existing Z^8
    root/selected column caps. Original holes are empty, as proved by the producer. -/
theorem actualFrameLabels_fits_caps (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayCharacter) (hH : s.H=∅) (hB : (24:ℝ)≤θ.Bmask)
    (hR : (s.R.absNorm:ℝ)≤Z^(8:ℝ))
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) :
    ∀x∈actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ,Fits η rs x := by
  apply actualFrameLabels_fits η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g hg n χ
  · rw [hH];exact Finset.empty_subset _
  · intro i P hP;rw [hH] at hP;exact False.elim (Finset.notMem_empty _ hP)
  · exact hX
  · have hz : 0<Z := zero_lt_one.trans rs.hZ
    have hh : (s.R.absNorm:ℝ)*(Z^(8:ℝ))^2 ≤ Z^(24:ℝ) := by
      calc
        _ ≤ Z^(8:ℝ)*(Z^(8:ℝ))^2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
        _ = Z^(24:ℝ) := by
          rw [show (24:ℝ)=8+8*2 by norm_num,Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_two]
    have hh' := hh.trans (Real.rpow_le_rpow_of_exponent_le rs.hZ.le hB)
    simpa [hH,MixedCompletedRows.holes] using hh'

/-- The second divisor stays in the native inverse-norm weight. -/
theorem actual_frame_weight (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (n : Fin 4→ℤ) (χ : RayCharacter)
    (k : Σ _ : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),Id) :
    gWeight ((frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η) =
      rho (g k.1)/(k.2.absNorm:ℝ) := by
  simp only [gWeight,frameData,LabelData.toLabel,norm_one,mul_one]

#print axioms grouped_regular_le_classes
#print axioms actualFrameLabels_fits
#print axioms actualFrameLabels_fits_caps
#print axioms actual_frame_weight
end
end QRH.Cycle092.ColoredGaussFrameProvider
