import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryBudgetJoin
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentAllocatedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

private theorem main_paid_join (average coefficient norm exceptional ordinary C payment : ℝ)
    (ha : 0 ≤ average) (hc : 0 ≤ coefficient)
    (hn : norm ≤ exceptional + C*ordinary)
    (he : average*coefficient*exceptional ≤ payment) :
    average*coefficient*norm ≤ payment+C*average*coefficient*ordinary := by
  have h := mul_le_mul_of_nonneg_left hn (mul_nonneg ha hc)
  nlinarith only [h, he]

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The ordinary contraction constant is collected before the original subset,
while each source keeps its own actual Fourier cardinality. -/
theorem uniform_actual_geometry_main_ordinary_contraction (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ, 0<C ∧ ∀(T : Finset α){Label : Type}[Fintype Label]
      (d : Label→SecondInputDatum T)(w : Label→ℂ)(χ : Label→RayCharacter)
      (Q : Ideal O)(m : O)(E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  have data (T : Finset α) := main_original_from_normalized.{0,0} (α:=T)
    ballProfile A degree windowDegree hc hs
  choose C hC bound using data
  let total := 1+∑T : Finset α,C T
  have hnonneg : ∀T : Finset α,0≤C T := hC
  have htotal : 0<total := by
    have hsum := Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T≤total := by
    have hsum := Finset.single_le_sum (fun T _=>hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total,htotal,?_⟩
  intro T Label _ d w χ Q m E H hrows hE hH hnorm
  apply (bound T d w χ Q m E H hrows hE hH hnorm).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right (hle T)
  exact Finset.sum_nonneg (fun r hr=>div_nonneg (hE r hr)
    (pow_nonneg (by linarith [dyadicScale_pos r]) _))

variable (rayM : Ideal O) [NeZero rayM]
local instance affineMainContractionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- The exact prime average and amplifier coefficient are paid once. The
ordinary input remains the full joint normalized bound, after the original
full-zero filter and before any ratio-fiber contraction. -/
theorem actual_affine_main_retained_contraction
    (A ordinaryDegree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃Ce : ℝ,0<Ce ∧ ∃Sp : Finset (ℕ×ℕ),∃exceptionalDegree : ℕ,
    ∃Co : ℝ,0<Co ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=η)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      let s := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      let beta := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))
      let amp := Cycle63.AffineLedger.amp beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let μ := geometryLossUnit 1 εaffine
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
      let phase := fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
      let selected := geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
        (Fintype.card T) hZ key (affine_profile_zero p 0) (affine_profile_zero p 1)
      let datum := fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key j.val.1 (affine_profile_zero p 0)
          (affine_profile_zero p 1) j.val.2
      let coeff := fun j : selected=>geometryMainSecondWeight reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s)) phase j.val
      ∀(χ : selected→RayCharacter)(E Hratio : ℤ→ℝ),
      (∀r∈secondRatioBins (fun j=>(datum j).block),0≤E r) →
      (∀r∈secondRatioBins (fun j=>(datum j).block),0<Hratio r) →
      SecondNormalizedBound ballProfile ordinaryDegree windowDegree
        (fun j=>ordinarySecondDatum (datum j) (χ j) Qfix m) coeff E Hratio →
      (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
        ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight hZ key
          1 (Real.logb Z (volume s)) phase‖ ≤
        Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
          (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ))+
        Co*(56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
          (∑r∈secondRatioBins (fun j=>(datum j).block),E r/(1+dyadicScale r)^A) := by
  obtain ⟨Co,hCo,hordinary⟩ := uniform_actual_geometry_main_ordinary_contraction (α:=α)
    A ordinaryDegree windowDegree hc hs
  obtain ⟨Ce,hCe,Sp,exceptionalDegree,hexceptional⟩ := actual_affine_main_exceptional_payment (α:=α)
    rayM H hH Sbad hbad W hW hWs η εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2
  refine ⟨Ce,hCe,Sp,exceptionalDegree,Co,hCo,?_⟩
  filter_upwards [hexceptional] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hwin s beta amp P μ Ψ reflected key firstHeight
    phase selected datum coeff χ E Hratio hE hHratio hnorm
  have hrows : ∀j : selected,(datum j).rows=sourceRows (datum j).C (datum j).D
      (datum j).inactive (datum j).radius := by
    intro j
    unfold datum geometryLowSecondDatum actualSecondBlockDatum actualSecondInputDatum
    rfl
  have ho := hordinary T datum coeff χ Qfix m E Hratio hrows hE hHratio hnorm
  have hretained := actual_main_retained_nonzero_sum reflected s 1 1 Z 1 amp (μ/64) (μ/8)
    (9/4) firstHeight hZ key (affine_profile_zero p 0) (affine_profile_zero p 1)
    1 (Real.logb Z (volume s)) phase
  rw [←hretained] at ho
  have he := hz.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hwin Ψ reflected key firstHeight χ
  have hcell := Cycle63.AffineLedger.originalCell_mem ⟨hwin.slots_ge,hwin.slots_le⟩
  have hb := Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hcoef := (geometry_affine_main_amplifier_bound beta hb).1
  have havg : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  simp only [geometryAffineMainExceptionalNorm] at he
  exact main_paid_join _ _ _ _ _ _ _ havg hcoef ho he

variable [Cycle63.AffineLedger] in
/-- The exact prime average and amplifier coefficient are paid once at a parent with puncture `R`, seed `seed` and radial scale
`Z^Mrow`. The ordinary input remains the full joint normalized bound, after the original full-zero filter and before any
ratio-fiber contraction. -/
theorem actual_affine_main_parent_retained_contraction
    (A ordinaryDegree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Cs : ℝ) :
    ∃Ce : ℝ,0<Ce ∧ ∃Sp : Finset (ℕ×ℕ),∃exceptionalDegree : ℕ,
    ∃Co : ℝ,0<Co ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
      (η₀ : Character)(θ : T→RayQuotient.Characters rayM H)(w σ freq : T→ℝ),
      Matches rayM H hH s η₀ θ w σ freq W 2 Z →
    ∀(R seed : Ideal O)(Mrow : ℝ),R≠0 → Squarefree seed → (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤ Mrow →
      Mrow≤1 → Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16 →
      (∀j,w j≤ mesh) →
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B →
    ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
      let amp := Cycle63.AffineLedger.amp beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let μ := geometryLossUnit 1 εaffine
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
      let phase := fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q)
      let selected := geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) firstHeight
        (Fintype.card T) hZ key caps.zero₁ caps.zero₂
      let datum := fun j : selected=>geometryLowSecondDatum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key j.val.1 caps.zero₁ caps.zero₂ j.val.2
      let coeff := fun j : selected=>geometryMainSecondWeight reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key Mrow (Real.logb Z (volume s)) phase j.val
      ∀(χ : selected→RayCharacter)(E Hratio : ℤ→ℝ),
      (∀r∈secondRatioBins (fun j=>(datum j).block),0≤E r) →
      (∀r∈secondRatioBins (fun j=>(datum j).block),0<Hratio r) →
      SecondNormalizedBound ballProfile ordinaryDegree windowDegree
        (fun j=>ordinarySecondDatum (datum j) (χ j) Qfix m) coeff E Hratio →
      (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
        ‖geometryMainRetainedSum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) firstHeight hZ key
          Mrow (Real.logb Z (volume s)) phase‖ ≤
        Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
          (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)+
        Co*(56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
          (∑r∈secondRatioBins (fun j=>(datum j).block),E r/(1+dyadicScale r)^A) := by
  obtain ⟨Co,hCo,hordinary⟩ := uniform_actual_geometry_main_ordinary_contraction (α:=α)
    A ordinaryDegree windowDegree hc hs
  obtain ⟨Ce,hCe,Sp,exceptionalDegree,hexceptional⟩ := actual_affine_main_exceptional_parent_payment (α:=α)
    rayM H hH Sbad hbad W εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  refine ⟨Ce,hCe,Sp,exceptionalDegree,Co,hCo,?_⟩
  filter_upwards [hexceptional] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot haff beta hbeta
    amp P μ Ψ reflected key firstHeight phase selected datum coeff χ E Hratio hE hHratio hnorm
  have hrows : ∀j : selected,(datum j).rows=sourceRows (datum j).C (datum j).D
      (datum j).inactive (datum j).radius := by
    intro j
    unfold datum geometryLowSecondDatum actualSecondBlockDatum actualSecondInputDatum
    rfl
  have ho := hordinary T datum coeff χ Qfix m E Hratio hrows hE hHratio hnorm
  have hretained := actual_main_retained_nonzero_sum reflected s R seed Z Mrow amp (μ/64) (μ/8)
    (9/4) firstHeight hZ key caps.zero₁ caps.zero₂ Mrow (Real.logb Z (volume s)) phase
  rw [←hretained] at ho
  have he := hz.2 T hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot haff beta hbeta Ψ reflected key firstHeight χ
  have hcell := Cycle63.AffineLedger.originalCell_mem ⟨hzslot.1,hzslot.2⟩
  have hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hcoef := (geometry_affine_main_amplifier_bound beta hb).1
  have havg : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  simp only [geometryAffineMainExceptionalNorm] at he
  exact main_paid_join _ _ _ _ _ _ _ havg hcoef ho he

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
