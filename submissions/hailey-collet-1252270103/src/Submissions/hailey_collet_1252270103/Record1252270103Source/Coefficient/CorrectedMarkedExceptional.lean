/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine forcing-ideal count pays the corrected marked source on the original
finite rows, keep predicate, and positive radial weight. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedMarkedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondExceptionalCount CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedDetectorAmplitude
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O

theorem corrected_marked_exceptional_energy
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →Q≠⊤ →Q≤Ideal.span {(72:O)} →∃C₀ : ℝ,0<C₀ ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ι : Type*,∀inst : Fintype ι,∀s : Input ι,
      s.W₁=(W₁:ℝ→ℂ) →s.W₂=(W₂:ℝ→ℂ) →s.b₁≤b →s.b₂≤b →
      ∀Z : ℝ,1<Z →∀η : Character,∀χ : RayFourExpansion.RayCharacter,
      ∀C D : Ideal O,∀hC : Supported C,∀U : Finset (CommonIndex C D),
      IsCoprime Q C →idealCoeff η C≠0 →
      ∀R : Ideal O,R≠0 →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows : Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,FixedInducingRow (childCharacter η χ) Q (fixedBadMask*idealGenerator R) A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ)
        (fixedBadMask*idealGenerator R) 1 (A*z):ℝ)≤Z^Bχ) →
      ∀Cr Mrow : ℝ,0≤Cr →(∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^Mrow) →
      ∀A₁ A₂ Df K : Ideal O,A₁≠0 →A₂≠0 →Df∣R →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →(∀p∈P,∀i I,I∈s.slots i→¬p∣I) →
      2*((idealDividingPool P Df).card+depth+1:ℝ)≤P.card →
      ∀t L : ℝ,0<L →L≤s.X₁ →L≤s.X₂ →L≤s.Y₁ →L≤s.Y₂ →
      (∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
          (idealDividingPool P (n.1*n.2)).card≤depth) →
      ∀keep : O→Prop,∀Φ : 𝓢(ℝ,ℂ),(∀x,0≤(Φ x).re) →∀H : ℝ,
      (∑z∈rows,if keep z then
        (‖modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P))
          R 1 (childCharacter η χ) t (A*z)‖^2/volume s)*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          (max 1 L)^(-α)*slotControl s.toData)^2*volume s*
            SchwartzMap.seminorm ℝ 0 0 Φ := by
  obtain ⟨J,S,hS,hsource⟩ := corrected_marked_fixed_inducing_source
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hsource⟩ := hsource Q hQ0
  refine ⟨C₀,hC₀,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι inst s hsW₁ hsW₂ hb₁ hb₂ Z hZ η χ C D hC U hQC hη R hR
    A rows hrows hex hcond Cr Mrow hCr hNrow A₁ A₂ Df K hA₁ hA₂ hDR hnormA
    P hP hp hN hpool havoid hbudget t L hL hX₁ hX₂ hY₁ hY₂ hcount keep Φ hΦ H
  have hA : A≠0 := mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hm : fixedBadMask*idealGenerator R≠0 := mul_ne_zero fixedBadMask_ne_zero
    (idealGenerator_ne_zero R hR)
  have hml : goodLambda∣fixedBadMask*idealGenerator R :=
    (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣fixedBadMask*idealGenerator R :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hrowsCount := actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη
    (fixedBadMask*idealGenerator R) hm hml hm2 rows hrows hex Z Cr Mrow hZ hCr hNrow
  let E := C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
    (max 1 L)^(-α)*slotControl s.toData
  have hE : 0≤E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀.le
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)))
      (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)) (by positivity))
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) (slotControl_nonneg s.toData)
  have hV := volume_pos s
  have hpoint (z : O) (hz : z∈rows) :
      ‖modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P))
        R 1 (childCharacter η χ) t (A*z)‖^2/volume s≤E^2*volume s := by
    have hr := hsource W₁ W₂ hs₁ hs₂ ι inst s hsW₁ hsW₂ hb₁ hb₂ Z hZ.le
      (childCharacter η χ) R hR A z hA (hrows z hz) (hcond z hz) (hex z hz)
      A₁ A₂ Df K hA₁ hA₂ hDR hnormA P hP hp hN hpool havoid hbudget
      t L hL hX₁ hX₂ hY₁ hY₂ hcount
    apply (div_le_iff₀ hV).mpr
    calc
      _≤(E*volume s)^2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
      _=_ := by ring
  have hΦ0 : 0≤SchwartzMap.seminorm ℝ 0 0 Φ := apply_nonneg _ _
  calc
    _≤∑z∈rows,E^2*volume s*SchwartzMap.seminorm ℝ 0 0 Φ := by
      apply Finset.sum_le_sum
      intro z hz
      split_ifs with hk
      · exact mul_le_mul (hpoint z hz)
          ((Complex.re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ Φ _))
          (hΦ _) (mul_nonneg (sq_nonneg _) hV.le)
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) hV.le) hΦ0
    _=(rows.card:ℝ)*(E^2*volume s*SchwartzMap.seminorm ℝ 0 0 Φ) := by simp
    _≤_ := (mul_le_mul_of_nonneg_right hrowsCount
      (mul_nonneg (mul_nonneg (sq_nonneg _) hV.le) hΦ0)).trans_eq (by dsimp only [E];ring)

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_marked_exceptional_energy
