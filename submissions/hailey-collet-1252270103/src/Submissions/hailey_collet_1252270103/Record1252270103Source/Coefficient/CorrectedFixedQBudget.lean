/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed-Q adaptation of CorrectedExceptionalBudget; inherited source notices remain required.
One fixed cardinality cap controls the genuine forced-divisor constant
before every moving common allocation and surviving marked subtype. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalBudget
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedFixedQUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open ConcretePrimeRowBridge CompletedGauss CanonicalRowCompletion
open CenteredExceptionalProfile CenteredMomentRestrictedSource
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
local instance correctedFixedQExceptionalBudgetTupleDecidableEq (ι : Type*) : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem corrected_fixedQ_exceptional_energy_from_caps
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hεL : 0<εL)
    (hBχ : 0≤Bη+BR+Bfreq+BH+1) (hBA : 0≤BA) (hBpool : 0≤Bpool)
    (hell : 0<ell) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃C₀ : ℝ,0<C₀ ∧
      ∀N : ℕ,∃K₀ : ℝ,0<K₀ ∧
      ∀ι : Type*,∀inst : Fintype ι,Fintype.card ι≤N→
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
      ∀s : Input ι,(∀i,1≤s.P i)→
      ∀Z : ℝ,1<Z→∀η τ : Character,∀χ : RayFourExpansion.RayCharacter,
      ∀C D : Ideal O,∀hC : Supported C,∀U : Finset (CommonIndex C D),
      idealCoeff η C≠0→
      ∀A₁ A₂ Df K R seed : Ideal O,Squarefree seed→∀P : Finset (Ideal O),
      CorrectedForcedCaps s W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K R seed P→
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀Cm : Ideal O,Cm∣R→
      (∀I : Ideal O,Supported I→IsCoprime Cm I→∀t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          RayFourExpansion.rayCharacter χ (primaryGenerator I))→
      ∀m : O,m≠0→goodLambda∣m→(2:O)∣m→
      ∀Φ : 𝓢(ℝ,ℂ),(∀x,0≤(Φ x).re)→∀H brad : ℝ,0<H→0≤brad→
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic brad→
      (η.modulus.absNorm:ℝ)≤Z^Bη→((Ideal.span {A}).absNorm:ℝ)≤Z^Bfreq→
      H≤Z^BH→(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*brad≤Z→
      ∀t L : ℝ,0<L→L≤s.X₁→L≤s.X₂→L≤s.Y₁→L≤s.Y₂→
      sourceRestrictedEnergy
        (fun z=>z≠0 ∧ FixedInducingRow (childCharacter η χ) Q m A z)
        (finiteColumns (Fintype.piFinset s.pools))
        (QRH.Record1252270103Source.High.CoupledFirst.coefficient s
          (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R seed)
        (heightCoeff τ t) Φ H≤
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α L brad (Real.logb Z H) C₀ K₀*
        (1+‖t‖)^(2*J) := by
  obtain ⟨J,S,hS,hsource⟩:=corrected_fixedQ_forced_exceptional_energy_uniform
    a b ε εL (Bη+BR+Bfreq+BH+1) BA Bpool α depth ha hb hε hεL hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hsource⟩:=hsource Q hQ0 hQ hQ72
  refine ⟨C₀,hC₀,?_⟩
  intro N
  obtain ⟨K₀,hK₀,hsource⟩:=hsource N
  refine ⟨K₀,hK₀,?_⟩
  intro ι inst hcardι W₁ W₂ hs₁ hs₂ s hscales Z hZ η τ χ C D hC U hη
    A₁ A₂ Df K R seed hseed P hcap A Cm hCm hτ m hm hmLam hm2 Φ hΦ
    H brad hH hbrad hsupport hηcap hAcap hHcap hfixed t L hL hX₁ hX₂ hY₁ hY₂
  have hh:=hsource ι inst hcardι W₁ W₂ hs₁ hs₂ s hscales Z hZ η τ χ C D hC U hη
    A₁ A₂ Df K R seed hseed P Cm hCm hτ
    (fun z=>z≠0 ∧ FixedInducingRow (childCharacter η χ) Q m A z) Φ hΦ
    H brad (Real.logb Z H) hH hbrad t L hL hX₁ hX₂ hY₁ hY₂
    (forced_selector_geometries_of_caps s W₁ W₂ b Z BA Bpool Bplain BD BR ell depth
      A₁ A₂ Df K R seed P hcap Q η χ C D hC U m hm hmLam hm2
      brad H Bη Bfreq BH hZ hbrad hH Φ hsupport hηcap hAcap hHcap hfixed)
    (forced_source_geometries_of_caps s W₁ W₂ b Z BA Bpool Bplain BD BR ell depth
      A₁ A₂ Df K R seed P hb hZ hell hcap τ t)
  have hraw:=(div_le_iff₀ (volume_pos s)).mp hh
  apply hraw.trans_eq
  have hpow : (1+‖t‖)^(2*J)=((1+‖t‖)^J)^2 := by rw [Nat.mul_comm,pow_mul]
  rw [hpow]
  unfold correctedExceptionalBudget
  ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.correctedExceptionalBudget_nonneg
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_fixedQ_exceptional_energy_from_caps
