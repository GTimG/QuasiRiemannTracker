/- Copyright (c) 2026 Sil. Apache-2.0.
Complete the positive fourth-power image by the fixed smooth ball, then
apply the literal second Poisson identity. The original 1/W density stays
outside throughout; the physical prefactor is exactly 16 K W^3.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedPhysicalTransfer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

set_option autoImplicit false
namespace Candidate.FourthPower.MixedPoissonCompletion
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss CenteredMomentGaussEnergy
open CenteredMomentFirstAmplificationChoice ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem image_energy_le_smooth {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ)
    (Ds : Finset Id) (Ks : Finset O) (W K : ℝ) (hW : 0<W) (hK : 0<K)
    (hDs : ∀D∈Ds,Supported D) (hDN : ∀D∈Ds,(Ideal.absNorm D:ℝ)≤2*W)
    (hkN : ∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) :
    (∑r∈(Ds×ˢKs).image PositiveFamily.frequency,‖gaussPolynomial S a ha b r‖^2) ≤
      (gaussEnergy S a ha b ballProfile (16*K*W^4)).re := by
  apply finite_energy_le_gaussEnergy S a ha b ballProfile (16*K*W^4) (by positivity)
    ((Ds×ˢKs).image PositiveFamily.frequency) (fun z=>ballProfile_nonneg _)
  intro r hr
  apply ballProfile_majorizes (16*K*W^4) (by positivity)
  obtain ⟨⟨D,k⟩,hz,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hD,hk⟩ := Finset.mem_product.mp hz
  have hh := PositiveFamily.frequency_norm_bound D (hDs D hD) k W K hW.le (hDN D hD) (hkN k hk)
  exact hh

/-- The exact physical Poisson expression after the 1/W average. All
correlations, natural zeros and Fourier arguments remain those of baseline. -/
def secondPoissonDensity {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ) (K W : ℝ) : ℂ :=
  ∑i∈S,∑j∈S,(b i*star (b j))*
    (((16*K*W^3:ℝ):ℂ)/
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}):ℝ):ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}):ℝ):ℂ)))*
    ∑'h : O,actualCorrelation (a i) (a j) (ha i) (ha j) (-h)*
      paperRadialFourier ballProfile
        (16*K*W^4*‖eisEmbedding h‖^2/‖eisEmbedding (a i*a j)‖^2)

theorem density_normalized_poisson {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ)
    (K W : ℝ) (hK : 0<K) (hW : 0<W) :
    gaussEnergy S a ha b ballProfile (16*K*W^4)/(W:ℂ)=
      secondPoissonDensity S a ha b K W := by
  rw [gaussEnergy_poisson S a ha b ballProfile (16*K*W^4) (by positivity)]
  unfold secondPoissonDensity
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hWc : (W:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hW.ne'
  push_cast
  field_simp

theorem smoothed_weighted_average (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(Ds : Finset Id)(Ks : Finset O),
    (∀D∈Ds,Supported D) → (∀k∈Ks,k≠0) →
    ∀(w : Id→ℝ)(ρ : Id→O→ℝ)(W K L : ℝ),0<W → 0<K → 0≤L →
    (∀D∈Ds,0≤w D ∧ w D≤L) → (∀D∈Ds,∀k∈Ks,0≤ρ D k ∧ ρ D k≤1) →
    (∀D∈Ds,(Ideal.absNorm D:ℝ)≤2*W) →
    (∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) →
    ∀{ι : Type*}(S : Finset ι)(a : ι→O)(ha : ∀i,Supported (Ideal.span {a i}))(b : ι→ℂ),
    (∀i∈S,b i≠0→GaussTransfer.FifthFree (a i)) →
    (∑D∈Ds,w D*∑k∈Ks,ρ D k*
      ‖∑i∈S,b i*(idealRowHom (primaryGenerator D) (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k‖^2)/W ≤
      (L*C*(16*K*W^4)^ε/W)*(gaussEnergy S a ha b ballProfile (16*K*W^4)).re := by
  obtain ⟨C,hC,hbound⟩ := MixedPhysicalTransfer.sparse_weighted_average ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks hDs hk w ρ W K L hW hK hL hw hρ hDN hkN ι S a ha b hf
  apply (hbound Ds Ks hDs hk w ρ W K L hW hL hw hρ hDN hkN S a ha b hf).trans
  exact mul_le_mul_of_nonneg_left
    (image_energy_le_smooth S a ha b Ds Ks W K hW hK hDs hDN hkN) (by positivity)

/-- One unconditional passage from the weighted cubic twist on a positive
Gauss side to the exact second-Poisson family. No moment input is assumed. -/
theorem weighted_second_poisson (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(Ds : Finset Id)(Ks : Finset O),
    (∀D∈Ds,Supported D) → (∀k∈Ks,k≠0) →
    ∀(w : Id→ℝ)(ρ : Id→O→ℝ)(W K L : ℝ),0<W → 0<K → 0≤L →
    (∀D∈Ds,0≤w D ∧ w D≤L) → (∀D∈Ds,∀k∈Ks,0≤ρ D k ∧ ρ D k≤1) →
    (∀D∈Ds,(Ideal.absNorm D:ℝ)≤2*W) →
    (∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) →
    ∀{ι : Type*}(S : Finset ι)(a : ι→O)(ha : ∀i,Supported (Ideal.span {a i}))(b : ι→ℂ),
    (∀i∈S,b i≠0→GaussTransfer.FifthFree (a i)) →
    (∑D∈Ds,w D*∑k∈Ks,ρ D k*
      ‖∑i∈S,b i*(idealRowHom (primaryGenerator D) (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k‖^2)/W ≤
      L*C*(16*K*W^4)^ε*(secondPoissonDensity S a ha b K W).re := by
  obtain ⟨C,hC,hbound⟩ := smoothed_weighted_average ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks hDs hk w ρ W K L hW hK hL hw hρ hDN hkN ι S a ha b hf
  have he := hbound Ds Ks hDs hk w ρ W K L hW hK hL hw hρ hDN hkN S a ha b hf
  have hid := congrArg Complex.re (density_normalized_poisson S a ha b K W hK hW)
  simp only [Complex.div_ofReal_re] at hid
  apply he.trans_eq
  rw [←hid]
  ring

end
end Candidate.FourthPower.MixedPoissonCompletion
