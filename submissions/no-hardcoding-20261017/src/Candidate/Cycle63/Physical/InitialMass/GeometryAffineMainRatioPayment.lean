/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainRatioPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentExceptionalAmplitudePair RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

private theorem affine_ratio_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh := (p.support i h).1
  norm_num at hh

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineMainRatioPaymentFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- Actual affine source receipts pay the shared ratio image uniformly over
original subsets. The ratio loss is independent of the positive physical
localization rates, and every Fourier scale keeps the actual subset count. -/
theorem uniform_actual_affine_main_ratio_payment
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εaffine εratio : ℝ)(hεaffine : 0<εaffine)(hεratio : 0<εratio) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → Cycle63.CountAffine.windowBottom≤length Z X₁ → Cycle63.CountAffine.windowBottom≤length Z X₂ →
      length Z X₁≤Cycle63.CountAffine.plainLengthTop → length Z X₂≤Cycle63.CountAffine.plainLengthTop →
      Cycle63.Optimization.slotFloor≤∑i,w i → (∑i,w i)≤Cycle63.Optimization.slotTop →
      let s := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
      let amp := Cycle63.Arithmetic.amp beta
      let μ := geometryLossUnit 1 εaffine
      0<μ/64 ∧ 0<μ/8 ∧
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
      let selected := geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
        (Fintype.card T) hZ key (affine_ratio_plain_zero p 0) (affine_ratio_plain_zero p 1)
      let datum := fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key j.val.1 (affine_ratio_plain_zero p 0)
          (affine_ratio_plain_zero p 1) j.val.2
      ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤Cb*Z^εratio ∧
      (∀(E : ℝ),0≤E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^εratio) ∧
      ∀(χ : selected→RayCharacter)(Q : selected→Ideal O)(m : selected→O)(E : ℝ),0≤E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
          E/(1+dyadicScale r)^A)≤Cb*E*Z^εratio := by
  let μ := geometryLossUnit 1 εaffine
  have hμ : 0<μ := geometry_loss_unit_pos 1 εaffine (by norm_num) hεaffine
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((Cycle63.Arithmetic.lowReserve)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have data (T : Finset α) := eventual_actual_geometry_main_ratio_payment (α:=T)
    3 (μ/8) (9/4) (9/4) (μ/64) εratio (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by positivity) (by linarith) hεratio
  choose C hC hpaid using data
  let total := 1+∑T : Finset α,C T
  have hnonneg : ∀T : Finset α,0≤C T := fun T=>(hC T).le
  have htotal : 0<total := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T≤total := by
    have hh := Finset.single_le_sum (fun T _=>hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  obtain ⟨Cs,hCs,hsources⟩ := eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  refine ⟨total,htotal,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpaid,hsources,eventual_geometry_small_frequency μ hμ]
    with Z hp hs hf
  refine ⟨hs.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi s beta amp μ'
  refine ⟨by positivity,by positivity,?_⟩
  intro reflected key firstHeight selected datum
  have caps := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hcell := Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  have hb := Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0<amp := Cycle63.Arithmetic.amp_pos hb
  have hamp : |amp|≤3 := by
    rw [abs_of_pos hamp0]
    exact (Cycle63.Arithmetic.amp_bounds hb).2.trans (by linarith only [Cycle63.Optimization.amplifierCap_bounds.2])
  have hω : |frequencyLoss Z 32 (μ/64)+μ/8|≤3 := by
    rw [abs_of_nonneg hf.2.1]
    exact hf.2.2.trans (by linarith)
  have main := (hp T).2 reflected s 1 1 1 amp (μ/8) firstHeight hZ key caps.endpoints squarefree_one
    (affine_ratio_plain_zero p 0) (affine_ratio_plain_zero p 1) caps.sourceCap caps.volumeLog
    (by norm_num) hamp hω hamp0.le (by positivity)
  have hZε : 0≤Z^εratio := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  refine ⟨main.2.1.trans (mul_le_mul_of_nonneg_right (hle T) hZε),?_,?_⟩
  · intro E hE A
    apply (main.2.2.1 E hE A).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle T) hE) hZε
  · intro χ Q m E hE A
    apply (main.2.2.2 χ Q m E hE A).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle T) hE) hZε

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.uniform_actual_affine_main_ratio_payment
