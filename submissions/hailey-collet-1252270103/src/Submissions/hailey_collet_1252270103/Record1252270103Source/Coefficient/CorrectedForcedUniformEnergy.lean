/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One fixed cardinality cap controls the genuine forced-divisor constant
before every moving common allocation and surviving marked subtype. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedForcedUniformMass
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
local instance correctedForcedUniformEnergyTupleDecidableEq (ι : Type*) : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem corrected_forced_exceptional_energy_uniform
    (a b ε εL Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hεL : 0<εL) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
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
      IsCoprime Q C→idealCoeff η C≠0→
      ∀A₁ A₂ Df K R seed : Ideal O,Squarefree seed→∀P : Finset (Ideal O),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀Cm : Ideal O,Cm∣R→
      (∀I : Ideal O,Supported I→IsCoprime Cm I→∀t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          RayFourExpansion.rayCharacter χ (primaryGenerator I))→
      ∀keep : O→Prop,∀Φ : 𝓢(ℝ,ℂ),(∀x,0≤(Φ x).re)→∀H Cr Mrow : ℝ,0<H→0≤Cr→
      ∀t L : ℝ,0<L→L≤s.X₁→L≤s.X₂→L≤s.Y₁→L≤s.Y₂→
      (∀Cf : forcedLabels seed (forcedSource s
          (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R seed),
        CorrectedRowGeometry Q η χ C D U (R*Cf) Z Bχ Cr Mrow keep Φ H)→
      (∀Cf : forcedLabels seed (forcedSource s
          (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R seed),
        ∀B : actualAllocations s.pools (Cf:Ideal O),
        CorrectedSourceGeometry (child s Cf R B τ t) W₁ W₂ b Z BA Bpool depth
          (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*Cf)
          (K*Collision.markedProduct B.val) (R*Cf) P)→
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (QRH.Record1252270103Source.High.CoupledFirst.coefficient s
          (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R seed)
        (heightCoeff τ t) Φ H/volume s≤
      K₀*(seed.absNorm:ℝ)^εL*(forcedProfileCost s*
        (exceptionalRowCost Q C D U Z Cr Mrow*
          (C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
            (max 1 L)^(-α)*slotControl s.toData)^2*volume s*SchwartzMap.seminorm ℝ 0 0 Φ))/
        (seed.absNorm:ℝ) := by
  obtain ⟨J,S,hS,hsource⟩:=corrected_source_energy_from_geometry
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hsource⟩:=hsource Q hQ0 hQ hQ72
  refine ⟨C₀,hC₀,?_⟩
  intro N
  obtain ⟨K₀,hK₀,hforced⟩:=marked_corrected_forced_source_uniform N εL hεL
  refine ⟨K₀,hK₀,?_⟩
  intro ι inst hcardι W₁ W₂ hs₁ hs₂ s hscales Z hZ η τ χ C D hC U hQC hη
    A₁ A₂ Df K R seed hseed P A Cm hCm hτ keep Φ hΦ H Cr Mrow hH hCr
    t L hL hX₁ hX₂ hY₁ hY₂ hrows hchildren
  let B₀:=C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J
  let E:=exceptionalRowCost Q C D U Z Cr Mrow*
    (B₀*(max 1 L)^(-α)*slotControl s.toData)^2*volume s*SchwartzMap.seminorm ℝ 0 0 Φ
  have hcost : 0≤exceptionalRowCost Q C D U Z Cr Mrow :=
    exceptionalRowCost_nonneg Q C D U Z Cr Mrow (zero_lt_one.trans hZ).le hCr
  have hseminorm : 0≤SchwartzMap.seminorm ℝ 0 0 Φ := apply_nonneg _ _
  have hE : 0≤E := mul_nonneg
    (mul_nonneg (mul_nonneg hcost (sq_nonneg _)) (volume_pos s).le) hseminorm
  apply hforced hcardι s A₁ A₂ Df K R seed (poolCorrection P) hseed τ t keep Φ H E hH hE
    (fun z=>hΦ _)
  intro Cf B
  have hB : finiteTupleProduct B.val=(Cf:Ideal O) := (Finset.mem_filter.mp B.property).2
  have hm:=funext (Collision.markedSourceModifier_common_allocation
    A₁ A₂ Df K (Cf:Ideal O) (poolCorrection P) B.val hB)
  unfold childDivisorEnergy
  rw [hm]
  have hg:=hchildren Cf B
  have hlower:=child_raw_lower_bound s Cf R B τ t L hL hX₁ hX₂ hY₁ hY₂
  have hLd : 0<L/ordinaryNorm B.val := div_pos hL
    (zero_lt_one.trans_le (ordinaryNorm_ge_one s Cf B))
  have hh:=hsource W₁ W₂ hs₁ hs₂ _ inferInstance (child s Cf R B τ t) Z hZ
    η τ χ C D hC U hQC hη
    (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*Cf)
    (K*Collision.markedProduct B.val) (R*Cf) P hg Cm
    (dvd_trans hCm (dvd_mul_right R (Cf:Ideal O))) hτ keep Φ hΦ H Cr Mrow hCr (hrows Cf)
    t (L/ordinaryNorm B.val) hLd hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
  apply hh.trans
  have hf:=child_centered_energy_factor s Cf R B τ t L α B₀ hscales hα0 hα
  have hhf:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hcost) hseminorm
  dsimp only [B₀,E] at hhf ⊢
  convert hhf using 1 <;> ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_forced_exceptional_energy_uniform
