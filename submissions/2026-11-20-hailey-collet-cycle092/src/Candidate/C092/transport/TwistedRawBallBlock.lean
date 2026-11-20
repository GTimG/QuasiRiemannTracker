/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The literal colored physical first block consumes summed colored raw sides. -/
import Candidate.C092.transport.TwistedRawBallPhysical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentFirstRetainedActive CenteredMomentFirstSectorLocalization
open CenteredMomentFirstColumns CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentLogDyadic
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstCommonSum
open MixedInnerExceptionalBlock CenteredMomentHeckeExpansion
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem selected_one_on_supported (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ)
    (seed I : Id) (hI : Supported I) :
    selectedCoefficient s ha ω₁ ω₂ seed 1 I = sourceColumn s ha ω₁ ω₂ seed I := by
  simp only [selectedCoefficient,selectedTwist,primaryGenerator_one,
    CanonicalRowCompletion.idealRowHom_one_supported I hI,one_pow,mul_one]

theorem retained_selected_one (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ) (η : Character)
    (m A : O) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedEnergy η m A t (sourceColumns s) (selectedCoefficient s ha ω₁ ω₂ 1 1) Φ K X Z ξ=
      retainedEnergy η m A t (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1) Φ K X Z ξ := by
  rw [retained_energy_sum,retained_energy_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [selected_one_on_supported s ha ω₁ ω₂ 1 I (Finset.mem_filter.mp hI).2,
    selected_one_on_supported s ha ω₁ ω₂ 1 J (Finset.mem_filter.mp hJ).2]

theorem block_selected_one (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ) (η : Character) (m A : O) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (sourceColumns s) (selectedCoefficient s ha ω₁ ω₂ 1 1) C D hC hD E rows Φ V K K₀ H₀ A₀ B₀=
      block η m A t (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1) C D hC hD E rows Φ V K K₀ H₀ A₀ B₀ := by
  have hl (I : columns C C hC.1 (sourceColumns s)) :
      coefficient η m A t (selectedCoefficient s ha ω₁ ω₂ 1 1) C I=
        coefficient η m A t (sourceColumn s ha ω₁ ω₂ 1) C I := by
    have hI : Supported I.val := by simpa only [element_span] using element_supported C C hC.1 (sourceColumns s) I
    unfold coefficient
    rw [selected_one_on_supported s ha ω₁ ω₂ 1 (C*I.val) ((supported_mul_iff _ _).mpr ⟨hC,hI⟩)]
  have hr (I : columns C D hD.1 (sourceColumns s)) :
      coefficient η m A t (selectedCoefficient s ha ω₁ ω₂ 1 1) D I=
        coefficient η m A t (sourceColumn s ha ω₁ ω₂ 1) D I := by
    have hI : Supported I.val := by simpa only [element_span] using element_supported C D hD.1 (sourceColumns s) I
    unfold coefficient
    rw [selected_one_on_supported s ha ω₁ ω₂ 1 (D*I.val) ((supported_mul_iff _ _).mpr ⟨hD,hI⟩)]
  simp only [block,hl,hr]

def blockTerm (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (η : Character) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  commonHeight s η t C D*block η (fixedBadMask*idealGenerator s.R) 1 t
    (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1) C D hC hD E rows Φ (fun _=>logAnnulus) K K₀ H₀ A₀ B₀

theorem actual_block_expansion (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ)
    (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (hrows : ∀z∈rows,z≠0) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0<K) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    blockTerm s ha ω₁ ω₂ η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀ =
      commonHeight s η t C D*scalar C D hC E K A₀ B₀*
        ∑u∈artificialDivisors s C D hD.1, (UniqueFactorizationMonoid.moebius u:ℂ)*
          activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)*
          ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            rawMatrix s ha ω₁ ω₂ C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
              (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀ := by
  have he := selected_physical_average s ha ω₁ ω₂ 1 η t C D hC hD hCD E rows hrows
    ({1}:Finset Id) (fun _=>1) 1 (by norm_num) (fun _ _=>by norm_num)
    Φ (fun _=>logAnnulus) K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  simpa only [Finset.sum_singleton,Finset.sum_product,one_div,inv_one,Complex.ofReal_one,
    one_mul,block_selected_one,blockTerm,rawMatrix] using he

/-- The ray projector is paid after the full first divisor sum. Raw side
    budgets are height-uniform sums of actual colored allocated energies. -/
theorem physical_block_of_raw (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃Ckernel : ℝ, 0≤Ckernel ∧ ∀s : Source ι a b, ∀ha : 0<a, ∀ω₁ ω₂ : Id→ℂ,
    ∀η : Character, ∀t : ℝ, ∀C D : Id, ∀hC : Supported C, ∀hD : Supported D,
    primeSupport C=primeSupport D → ∀E : Finset (CommonIndex C D),
    ∀rows : Finset O, (∀z∈rows,z≠0) → ∀K K₀ H₀ A₀ B₀ KL KR EL ER : ℝ,
    0<K → 0<K₀ → 0<H₀ → 0<A₀ → 0<B₀ → 0<KL → 0<KR → 0≤EL → 0≤ER →
    (∀z∈rows,‖eisEmbedding z‖^2≤KL) → (∀z∈rows,‖eisEmbedding z‖^2≤KR) →
    (∀χ ξ : RayCharacter, ∀v : ℝ,
      ∑u∈artificialDivisors s C D hD.1,
        rawEnergy s ha ω₁ ω₂ D C hC u (fixedPair η C D hC E χ (ξ⁻¹)).left v KL
          ≤EL*(1+‖v‖)^(2*J)) →
    (∀χ ξ : RayCharacter, ∀v : ℝ,
      ∑u∈artificialDivisors s C D hD.1,
        rawEnergy s ha ω₁ ω₂ C D hD u (fixedPair η C D hC E χ (ξ⁻¹)).right v KR
          ≤ER*(1+‖v‖)^(2*J)) →
    ‖blockTerm s ha ω₁ ω₂ η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀‖/sourceVolume s ≤
      (256*Ckernel*‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
        (windowBudget J t EL*windowBudget J t ER) := by
  obtain ⟨Ck,hCk,hkernel⟩ := summed_kernel_from_raw (ι:=ι) (a:=a) (b:=b) Φ J
  refine ⟨Ck,hCk,?_⟩
  intro s ha ω₁ ω₂ η t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ KL KR EL ER
    hK hK₀ hH₀ hA₀ hB₀ hKL hKR hEL hER hrowsL hrowsR hl hr
  let Us := artificialDivisors s C D hD.1
  let mat := fun χ ξ : RayCharacter => summedMatrix s ha ω₁ ω₂ C D hC hD E Us
    (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
    t rows Φ K K₀ H₀ A₀ B₀
  have hb : ∀χ ξ, ‖mat χ ξ‖≤Ck*(windowBudget J t EL*windowBudget J t ER) := by
    intro χ ξ
    exact hkernel s ha ω₁ ω₂ C D hC hD E Us _ _ t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR
      rows hrowsL hrowsR EL ER hEL hER (hl χ ξ) (hr χ ξ)
  have hp := QRH.SilDensitySplit.CubeFree.First.summed_ray_projector 1
    (Ck*(windowBudget J t EL*windowBudget J t ER)) zero_le_one mat (by simpa using hb)
  simp only [one_mul] at hp
  have hh : ‖commonHeight s η t C D‖≤1 := by
    rw [commonHeight,norm_mul,norm_star]
    exact (mul_le_mul (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
      (fixedBadMask*idealGenerator s.R) 1 1 t C hC.1)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
      (fixedBadMask*idealGenerator s.R) 1 1 t D hD.1) (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hphase : ‖activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)‖≤1 :=
    QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _
  rw [actual_block_expansion s ha ω₁ ω₂ η t C D hC hD hCD E rows hrows Φ K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀,
    QRH.SilDensitySplit.CubeFree.First.summed_projector_regroup]
  change ‖commonHeight s η t C D*scalar C D hC E K A₀ B₀*
    (activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)*
      ∑χ,∑ξ,pairCoeff firstPhaseTable χ ξ*mat χ ξ)‖/sourceVolume s≤_
  rw [norm_mul,norm_mul,norm_mul]
  have hs := mul_le_mul_of_nonneg_right hh (norm_nonneg (scalar C D hC E K A₀ B₀))
  have ha' := mul_le_mul_of_nonneg_left hphase (norm_nonneg (scalar C D hC E K A₀ B₀))
  calc
    _ ≤ (‖scalar C D hC E K A₀ B₀‖*‖∑χ,∑ξ,pairCoeff firstPhaseTable χ ξ*mat χ ξ‖)/sourceVolume s := by
      apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
      calc
        _ ≤ ‖scalar C D hC E K A₀ B₀‖*(‖activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)‖*
            ‖∑χ,∑ξ,pairCoeff firstPhaseTable χ ξ*mat χ ξ‖) :=
          mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hs) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hphase) (norm_nonneg _)
    _ ≤ (‖scalar C D hC E K A₀ B₀‖*(256*(Ck*(windowBudget J t EL*windowBudget J t ER))))/sourceVolume s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (sourceVolume_pos s).le
    _ = _ := by ring

#print axioms actual_block_expansion
#print axioms physical_block_of_raw
end
end QRH.Cycle092.TwistedRawBall
