/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine corrected exceptional child estimate pays the physical block.
Only finite polynomial caps and the original character-family identity enter;
the full allocation count, frozen weights, divisor seed and row selector remain. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.ExceptionalWindow.ActualDivisors
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.ExceptionalWindow.Cardinality
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open Filter ExceptionalWindow
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second Record1252270103GlobalSelected
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSecondNonexceptional
open CenteredMomentSecondWholeKernel CenteredMomentSecondSectorRetained CenteredMomentSecondWindowBudget
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentMobiusRegroup RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile CenteredMomentSourceProfileMass
open ConcretePrimeRowBridge CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance selectedExceptionalPhysicalDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Seed-one payment after the full artificial-divisor sum. Both original
allocation cardinalities and the sharp common-norm power remain visible. -/
def pairedPayment (s:Input ι)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))
    (Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ)(J:ℕ)(t:ℝ):ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
    ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1)*(CenteredMomentCommonExceptionalCost.frozenProfile s)^2*
    correctedExceptionalBudget s T W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀*
    (heightEnvelope t^J*profileMoment J)^2

theorem exceptional_physical_paid
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α B δ : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hεL : 0<εL)
    (hBχ : 0≤Bη+BR+Bfreq+BH+1) (hBA : 0≤BA) (hBpool : 0≤Bpool)
    (hell : 0<ell) (hα0 : 0≤α) (hα : α<1/2) (hB : 0≤B) (hδ : 0<δ) :
    ∃J : ℕ,∃T : Finset (ℕ×ℕ),(0,0)∈T ∧
      ∀Q : Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃C₀ : ℝ,0<C₀ ∧
      ∃K₀ Cphys Hmass : ℝ,0<K₀ ∧ 0≤Cphys ∧ 0<Hmass ∧
      ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
      ∀s : Input ι,s.W₁=(W₁:ℝ→ℂ)→s.W₂=(W₂:ℝ→ℂ)→(∀i,1≤s.P i)→
      ∀(η : Character) (τ : RayCharacter→Character) (t : ℝ),
      ∀A₁ A₂ Df K R0 seed : Ideal O,∀P : Finset (Ideal O),
      let modifier:=Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s modifier R0 seed
      ∀(C D : Ideal O) (hC : Supported C) (hD : Supported D),
      seed∣C→seed∣D→primeSupport C=primeSupport D→IsCoprime Q C→idealCoeff η C≠0→
      ∀U : Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ : RayCharacter,∀I : Ideal O,Supported I→(IsCoprime C I∨IsCoprime D I)→
        ∀v : ℝ,heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I))→
      ∀(radius : ℝ) (rows : Finset O) (m : O) (χ₀ : RayCharacter),
      m≠0→goodLambda∣m→(2:O)∣m→(∀z∈rows,z≠0)→
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z)→
      ∀(Φ : 𝓢(ℝ,ℂ)) (H brad : ℝ),0<H→0≤brad→
      (∀x,0≤(Φ x).re)→Function.support (Φ:ℝ→ℂ)⊆Set.Iic brad→
      (∀z∈rows,1≤(Φ (normValue z/H)).re)→
      (η.modulus.absNorm:ℝ)≤Z^Bη→((Ideal.span {A}).absNorm:ℝ)≤Z^Bfreq→
      H≤Z^BH→(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*brad≤Z→
      ∀Lraw : ℝ,0<Lraw→Lraw≤s.X₁→Lraw≤s.X₂→Lraw≤s.Y₁→Lraw≤s.Y₂→
      (∀X : Ideal O,X=C∨X=D→
        ∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L→
        ∀B : actualAllocations s.pools X,frozenCoefficient B X R0 s.ν s.W s.P≠0→
          CorrectedAllocatedCaps s X R0 B W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K L P)→
      (∀I : sectorPool D hD.1 S,((I:Ideal O).absNorm:ℝ)≤Z^B)→
      ∀Hkernel : ℝ,0<Hkernel→∀n : Fin 4→ℤ,
      ‖physicalBlock η t S β C D hC hD U radius rows W Hkernel n‖≤
        Cphys*(outerScalar C D Hkernel n*normalizer C D U)*
          (Hmass*Z^(δ+B*εL)*pairedPayment s T W₁ W₂ Φ Q C D U
            Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀ J t)/
          (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨Hmass,hHmass,hmass⟩:=corrected_paired_actual_divisor_sum B δ hB hδ
  obtain ⟨J,T,hT,hsource⟩:=corrected_exceptional_physical_from_caps (ι:=ι)
    W decay a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α depth
    ha hb hε hεL hBχ hBA hBpool hell hα0 hα
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,K₀,Cphys,hK₀,hCphys,hsource⟩:=hsource Q hQ0 hQ hQ72
  refine ⟨C₀,hC₀,K₀,Cphys,Hmass,hK₀,hCphys,hHmass,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro W₁ W₂ hs₁ hs₂ s hW₁ hW₂ hscales η τ t A₁ A₂ Df K R0 seed P
    modifier S β C D hC hD hsC hsD hCD hQC hηC U A hτ radius rows m χ₀ hm hmLam hm2
    hrows hex Φ H brad hH hbrad hΦ hsupport hmajor hηcap hAcap hHcap hfixed
    Lraw hLraw hX₁ hX₂ hY₁ hY₂ hcaps hresidual Hkernel hHkernel n
  have hp:=hsource W₁ W₂ hs₁ hs₂ s hW₁ hW₂ hscales Z hZ.1 η τ t
    A₁ A₂ Df K R0 seed P C D hC hD hsC hsD hCD hQC hηC U hτ radius rows m χ₀
    hm hmLam hm2 hrows hex Φ H brad hH hbrad hΦ hsupport hmajor hηcap hAcap hHcap hfixed
    Lraw hLraw hX₁ hX₂ hY₁ hY₂ hcaps Hkernel hHkernel n
  have hm:=hZ.2 s C D R0 R0 hC.1 hD.1 T W₁ W₂ Φ Q U
    ε εL α Lraw brad (Real.logb Z H) C₀ K₀ J t hεL.le hα0 hbrad hK₀.le
    Finset.univ (fun I : sectorPool D hD.1 S=>(I:Ideal O))
    (fun I _=>(sectorPool_supported D hD.1 S I).1) (fun I _=>hresidual I)
  have ho:0≤Cphys*(outerScalar C D Hkernel n*normalizer C D U) := by
    have hnorm:0≤normalizer C D U := (normalizer_pos C D hC U).le
    have houter:0≤outerScalar C D Hkernel n := by unfold outerScalar; positivity
    positivity
  have hden:0≤(1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
    exact pow_nonneg (add_nonneg zero_le_one
      (div_nonneg (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le)
        (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le))) _
  apply hp.trans
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_left _ ho
  convert hm using 1 <;> dsimp only [pairedWindow,pairedPayment] <;> ring
/-- A single threshold serves all subsets of a fixed finite original slot type. -/
theorem exceptional_finite_subset_paid {κ:Type*} [Fintype κ]
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α B δ : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hεL : 0<εL)
    (hBχ : 0≤Bη+BR+Bfreq+BH+1) (hBA : 0≤BA) (hBpool : 0≤Bpool)
    (hell : 0<ell) (hα0 : 0≤α) (hα : α<1/2) (hB : 0≤B) (hδ : 0<δ) :
    ∃degree:Finset κ→ℕ,∃control:Finset κ→Finset (ℕ×ℕ),(∀A,(0,0)∈control A) ∧
      ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
      ∃csource ckernel cphysical cmass:Finset κ→ℝ,
      (∀A,0<csource A ∧ 0<ckernel A ∧ 0≤cphysical A ∧ 0<cmass A) ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀A:Finset κ,
      let J:=degree A
      let T:=control A
      let C₀:=csource A
      let K₀:=ckernel A
      let Cphys:=cphysical A
      let Hmass:=cmass A
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
      ∀s : Input A,s.W₁=(W₁:ℝ→ℂ)→s.W₂=(W₂:ℝ→ℂ)→(∀i,1≤s.P i)→
      ∀(η : Character) (τ : RayCharacter→Character) (t : ℝ),
      ∀A₁ A₂ Df K R0 seed : Ideal O,∀P : Finset (Ideal O),
      let modifier:=Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s modifier R0 seed
      ∀(C D : Ideal O) (hC : Supported C) (hD : Supported D),
      seed∣C→seed∣D→primeSupport C=primeSupport D→IsCoprime Q C→idealCoeff η C≠0→
      ∀U : Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ : RayCharacter,∀I : Ideal O,Supported I→(IsCoprime C I∨IsCoprime D I)→
        ∀v : ℝ,heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I))→
      ∀(radius : ℝ) (rows : Finset O) (m : O) (χ₀ : RayCharacter),
      m≠0→goodLambda∣m→(2:O)∣m→(∀z∈rows,z≠0)→
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z)→
      ∀(Φ : 𝓢(ℝ,ℂ)) (H brad : ℝ),0<H→0≤brad→
      (∀x,0≤(Φ x).re)→Function.support (Φ:ℝ→ℂ)⊆Set.Iic brad→
      (∀z∈rows,1≤(Φ (normValue z/H)).re)→
      (η.modulus.absNorm:ℝ)≤Z^Bη→((Ideal.span {A}).absNorm:ℝ)≤Z^Bfreq→
      H≤Z^BH→(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*brad≤Z→
      ∀Lraw : ℝ,0<Lraw→Lraw≤s.X₁→Lraw≤s.X₂→Lraw≤s.Y₁→Lraw≤s.Y₂→
      (∀X : Ideal O,X=C∨X=D→
        ∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L→
        ∀B : actualAllocations s.pools X,frozenCoefficient B X R0 s.ν s.W s.P≠0→
          CorrectedAllocatedCaps s X R0 B W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K L P)→
      (∀I : sectorPool D hD.1 S,((I:Ideal O).absNorm:ℝ)≤Z^B)→
      ∀Hkernel : ℝ,0<Hkernel→∀n : Fin 4→ℤ,
      ‖physicalBlock η t S β C D hC hD U radius rows W Hkernel n‖≤
        Cphys*(outerScalar C D Hkernel n*normalizer C D U)*
          (Hmass*Z^(δ+B*εL)*pairedPayment s T W₁ W₂ Φ Q C D U
            Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀ J t)/
          (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  have hp (A:Finset κ):=exceptional_physical_paid (ι:=A) W decay
    a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α B δ depth
    ha hb hε hεL hBχ hBA hBpool hell hα0 hα hB hδ
  choose J T hT hp using hp
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  choose C₀ hC₀ K₀ Cphys Hmass hK₀ hCphys hHmass hp using fun A=>hp A Q hQ0 hQ hQ72
  refine ⟨C₀,K₀,Cphys,Hmass,fun A=>⟨hC₀ A,hK₀ A,hCphys A,hHmass A⟩,?_⟩
  have hevent:∀ᶠ Z:ℝ in atTop,∀A:Finset κ,_:=Filter.eventually_all.mpr hp
  filter_upwards [hevent] with Z hZ
  exact ⟨(hZ ∅).1,fun A=>(hZ A).2⟩

end
end QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_physical_paid

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_finite_subset_paid
