/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine corrected exceptional child estimate pays the physical block.
Only finite polynomial caps and the original character-family identity enter;
the full allocation count, frozen weights, divisor seed and row selector remain. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalBudget
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalExceptionalChildren
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
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
local instance correctedExceptionalPhysicalDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def correctedAllocatedBudget (s : Input ι) (X R : Ideal O) (B : actualAllocations s.pools X)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ) : ℝ :=
  correctedExceptionalBudget (child s X R B s.η 0) S W₁ W₂ Φ Q C D seed U
    Z ε εL α (Lraw/ordinaryNorm B.val) Cr Mrow C₀ K₀

abbrev CorrectedAllocatedCaps (s : Input ι) (X R : Ideal O) (B : actualAllocations s.pools X)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b Z BA Bpool Bplain BD BR ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K seed : Ideal O) (P : Finset (Ideal O)) : Prop :=
  CorrectedForcedCaps (child s X R B s.η 0) W₁ W₂ b Z BA Bpool Bplain BD BR ell depth
    (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*X)
    (K*Collision.markedProduct B.val) (R*X) seed P

lemma correctedAllocatedCaps_transport (s : Input ι) (X R : Ideal O) (B : actualAllocations s.pools X)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b Z BA Bpool Bplain BD BR ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K seed : Ideal O) (P : Finset (Ideal O)) (τ : Character) (t : ℝ)
    (h : CorrectedAllocatedCaps s X R B W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K seed P) :
    CorrectedForcedCaps (child s X R B τ t) W₁ W₂ b Z BA Bpool Bplain BD BR ell depth
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*X)
      (K*Collision.markedProduct B.val) (R*X) seed P := by
  cases h
  constructor <;> assumption

theorem corrected_exceptional_physical_from_caps
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hεL : 0<εL)
    (hBχ : 0≤Bη+BR+Bfreq+BH+1) (hBA : 0≤BA) (hBpool : 0≤Bpool)
    (hell : 0<ell) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃T : Finset (ℕ×ℕ),(0,0)∈T ∧
      ∀Q : Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃C₀ : ℝ,0<C₀ ∧
      ∃K₀ Cphys : ℝ,0<K₀ ∧ 0≤Cphys ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
      ∀s : Input ι,s.W₁=(W₁:ℝ→ℂ)→s.W₂=(W₂:ℝ→ℂ)→(∀i,1≤s.P i)→
      ∀Z : ℝ,1<Z→∀(η : Character) (τ : RayCharacter→Character) (t : ℝ),
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
      ∀Hkernel : ℝ,0<Hkernel→∀n : Fin 4→ℤ,
      ‖physicalBlock η t S β C D hC hD U radius rows W Hkernel n‖≤
        Cphys*(outerScalar C D Hkernel n*normalizer C D U)*
          (∑L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
            ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
              (windowBudget J t (allocationBudget s C R0 (fun B=>
                correctedAllocatedBudget s C R0 B T W₁ W₂ Φ Q C D L U
                  Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀))*
               windowBudget J t (allocationBudget s D R0 (fun B=>
                correctedAllocatedBudget s D R0 B T W₁ W₂ Φ Q C D L U
                  Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀))))/
          (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨J,T,hT,hsource⟩:=corrected_exceptional_energy_from_caps
    a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell α depth
    ha hb hε hεL hBχ hBA hBpool hell hα0 hα
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hsource⟩:=hsource Q hQ0 hQ hQ72
  obtain ⟨K₀,hK₀,hsource⟩:=hsource (Fintype.card ι)
  obtain ⟨Cphys,hCphys,hphysical⟩:=actual_exceptional_physical_from_children (ι:=ι) W decay J J
  refine ⟨C₀,hC₀,K₀,Cphys,hK₀,hCphys,?_⟩
  intro W₁ W₂ hs₁ hs₂ s hW₁ hW₂ hscales Z hZ η τ t A₁ A₂ Df K R0 seed P
    modifier S β C D hC hD hsC hsD hCD hQC hηC U A hτ radius rows m χ₀ hm hmLam hm2
    hrows hex Φ H brad hH hbrad hΦ hsupport hmajor hηcap hAcap hHcap hfixed
    Lraw hLraw hX₁ hX₂ hY₁ hY₂ hcaps Hkernel hHkernel n
  have hz₁ : s.W₁ 0=0 := by
    rw [hW₁]
    by_contra hn
    have hh:=(hs₁ hn).1
    linarith
  have hz₂ : s.W₂ 0=0 := by
    rw [hW₂]
    by_contra hn
    have hh:=(hs₂ hn).1
    linarith
  have hchild (X : Ideal O) (hX : X=C∨X=D)
      (L : Ideal O) (hL : L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)))
      (hLsf : Squarefree L) (χ : RayCharacter) (v : ℝ) (B : actualAllocations s.pools X)
      (hB : frozenCoefficient B X R0 s.ν s.W s.P≠0) :
      childDivisorEnergy s modifier X R0 L B (τ χ) v
        (fun z=>z≠0 ∧ FixedInducingRow (childCharacter η χ) Q m A z) Φ H≤
        correctedAllocatedBudget s X R0 B T W₁ W₂ Φ Q C D L U Z ε εL α Lraw brad
          (Real.logb Z H) C₀ K₀*(1+‖v‖)^(2*J) := by
    have hcard : Fintype.card (liveIndices B.val)≤Fintype.card ι := by
      rw [Fintype.card_coe]
      exact Finset.card_le_univ _
    have hτX : ∀I : Ideal O,Supported I→IsCoprime X I→∀v : ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
      intro I hI hXI v
      apply hτ χ I hI _ v
      rcases hX with rfl|rfl
      · exact Or.inl hXI
      · exact Or.inr hXI
    have hlower:=child_raw_lower_bound s X R0 B (τ χ) v Lraw hLraw hX₁ hX₂ hY₁ hY₂
    have hpos : 0<Lraw/ordinaryNorm B.val :=
      div_pos hLraw (zero_lt_one.trans_le (ordinaryNorm_ge_one s X B))
    have hcap:=correctedAllocatedCaps_transport s X R0 B W₁ W₂ b Z BA Bpool Bplain BD BR ell depth
      A₁ A₂ Df K L P (τ χ) v (hcaps X hX L hL hLsf B hB)
    have hh:=hsource (liveIndices B.val) inferInstance hcard W₁ W₂ hs₁ hs₂
      (child s X R0 B (τ χ) v) (fun i=>hscales i.val) Z hZ η (τ χ) χ C D hC U hQC hηC
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*X)
      (K*Collision.markedProduct B.val) (R0*X) L hLsf P hcap X (dvd_mul_left X R0) hτX
      m hm hmLam hm2 Φ hΦ H brad hH hbrad hsupport hηcap hAcap hHcap hfixed
      v (Lraw/ordinaryNorm B.val) hpos hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
    have hprod : finiteTupleProduct B.val=X := (Finset.mem_filter.mp B.property).2
    have hmod:=funext (Collision.markedSourceModifier_common_allocation A₁ A₂ Df K X
      (poolCorrection P) B.val hprod)
    unfold childDivisorEnergy
    dsimp only [modifier]
    rw [hmod]
    exact hh
  apply hphysical Hkernel hHkernel n η τ t s modifier R0 seed hz₁ hz₂ C D hC hD hsC hsD hCD
    U hτ radius rows Q m χ₀ hQ72 hmLam hm2 hrows hex Φ H hH (fun z=>hΦ _) hmajor
    (fun L B=>correctedAllocatedBudget s C R0 B T W₁ W₂ Φ Q C D L U
      Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀)
    (fun L B=>correctedAllocatedBudget s D R0 B T W₁ W₂ Φ Q C D L U
      Z ε εL α Lraw brad (Real.logb Z H) C₀ K₀)
  · intro L B
    exact correctedExceptionalBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (zero_lt_one.trans hZ).le hbrad hK₀.le
  · intro L B
    exact correctedExceptionalBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (zero_lt_one.trans hZ).le hbrad hK₀.le
  · exact hchild C (Or.inl rfl)
  · exact hchild D (Or.inr rfl)
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_exceptional_physical_from_caps
