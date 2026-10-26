import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseChild
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighColumn
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondWeightedCommon
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryZeroPartition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonProfile CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource Cycle63Moment FourierBridge
local instance geometryHighWindowDecidableSum {ι : Type} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Genuine all-height source bound. Constants precede moving characters,
heights and both allocations; the first child is never replaced by a datum
with only a matching character. -/
theorem actual_child_weighted_coarse_columns {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window cap scalarCap : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤ cap) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (m control T Cscalar : ℝ),0≤ control → 1≤T → 0≤Cscalar →
      ∀(key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀rows : Finset κ,
      (∀label∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤Z^B) →
      (∀label∈rows,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈rows,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈rows,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈rows,((key label).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈rows,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^m) →
      ∀s : Input α,(∀j,s.M j≤Cs) → s.upper≤b → s.b₁≤bs → s.b₂≤bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      (∀j,s.P j≤Z^cap) →
      ∀(C₁ R₁ : κ→ Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ seed : κ→ Ideal O)(hC₂ : ∀k,Supported (C₂ k))
        (χ₂ : κ→ Character)(t₂ : κ→ℝ)(z : κ→O)
        (scalar : κ→ℂ)(Ds : κ→Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤B₁ → 0≤B₂ → (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) →
      (B₁*B₂)^2≤ control → (∀k∈rows,seed k∣C₂ k) →
      (∀k∈rows,‖scalar k‖^2*(∏j,(first k).M j)^2*((C₂ k).absNorm:ℝ)^(ε-1)≤Cscalar*Z^scalarCap) →
      (∀k∈rows,∀D∈Ds k,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∑k∈rows,∑L∈Ds k,‖scalar k*normalizedColumn
        (withHeight (first k) (χ₂ k) (t₂ k))
        (C₂ k) (hC₂ k) (R₂ k) (seed k) L (z k)‖^2)≤
        K*(Cscalar*control)*(2*T)^(3*ε)*
          Z^(m+scalarCap+B+loss+((N:ℝ)+2)*cap+pad) := by
  obtain ⟨Ccoarse,hCcoarse,hcoarse⟩ := actual_child_selected_coarse_shell N hα
    B loss ε pad Cs b bs window cap hB hloss hε hpad hCs hb hbs hwindow hcap
  obtain ⟨Kcommon,hKcommon,hcommon⟩ := actual_second_weighted_common_selection (α:=α) b ε hε
  obtain ⟨Kcolumn,hKcolumn,hcolumn⟩ := actual_uniform_second_column_extraction (α:=α) ε hε
  refine ⟨Kcolumn*Kcommon*Ccoarse,by positivity,?_⟩
  filter_upwards [hcoarse] with Z hz
  refine ⟨hz.1,?_⟩
  intro κ left u₀ unit m control T Cscalar hcontrol hT hCscalar key hinj rows
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ seed hC₂ χ₂ t₂ z scalar Ds B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB hseed hscalar hDs
  have hzpos : 0<Z := by linarith [hz.1]
  have ht : 0<2*T := by linarith
  let extra := scalarCap+(B+loss+((N:ℝ)+2)*cap+pad)
  let E := Cscalar*Ccoarse*control*(2*T)^(2*ε)*Z^(m+extra)
  let shifted := fun k=>withHeight (first k) (χ₂ k) (t₂ k)
  have hjoint := hcommon rows (fun k=>liveIndices (A₁ k).val) shifted C₂ R₂ Ds z scalar E
    (fun _ _=>hupper) (fun k _=>(hC₂ k).1) ?_
  · calc
      _≤Kcolumn*(2*T)^ε*(∑k∈rows,‖scalar k‖^2*∑L∈Ds k,
          commonRetainedCost (shifted k) (C₂ k) (R₂ k) L (z k)) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun L hL => ?_
        rw [norm_mul,mul_pow]
        have he := hcolumn (liveIndices (A₁ k).val) (shifted k) (C₂ k) (hC₂ k)
          (R₂ k) (seed k) L (hseed k hk) (hDs k hk L hL).1 (z k)
        calc
          _≤‖scalar k‖^2*(Kcolumn*(L.absNorm:ℝ)^ε*
              commonRetainedCost (shifted k) (C₂ k) (R₂ k) L (z k)) :=
            mul_le_mul_of_nonneg_left he (sq_nonneg _)
          _≤‖scalar k‖^2*(Kcolumn*(2*T)^ε*
              commonRetainedCost (shifted k) (C₂ k) (R₂ k) L (z k)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (common_retained_cost_nonneg ..)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg _) (hDs k hk L hL).2.2.le hε.le) hKcolumn.le
          _=_ := by ring
      _≤Kcolumn*(2*T)^ε*(Kcommon*E) :=
        mul_le_mul_of_nonneg_left hjoint (by positivity)
      _=_ := by
        dsimp only [E,extra]
        rw [show 3*ε=ε+2*ε by ring,Real.rpow_add ht]
        simp only [Real.rpow_add hzpos]
        ring
  · intro S pick hne
    have hj := hz.2 left u₀ unit m control T hcontrol hT
      (fun k : S=>key k.val.val)
      (fun k l he=>Subtype.ext (Subtype.ext (hinj he))) Finset.univ
      (fun k _=>hrow k.val.val k.val.property)
      (fun k _=>hsupported k.val.val k.val.property)
      (fun k _=>heq k.val.val k.val.property)
      (fun k _=>hsupport k.val.val k.val.property)
      (fun k _=>hnorm k.val.val k.val.property)
      (fun k _=>hmissing k.val.val k.val.property)
      s hM hupper hb₁ hb₂ hwin hscales hP
      (fun k=>C₁ k.val.val) (fun k=>R₁ k.val.val) (fun k=>A₁ k.val.val)
      (fun k=>χ₁ k.val.val) (fun k=>t₁ k.val.val)
      (fun k=>C₂ k.val.val) (fun k=>R₂ k.val.val) pick
      (fun k=>χ₂ k.val.val) (fun k=>t₂ k.val.val)
      (fun k=>z k.val.val) (fun k=>Ds k.val.val) B₁ B₂ hB₁ hB₂ hW₁ hW₂ hcontrolB
      (fun k _=>hDs k.val.val k.val.property)
    let daughter := fun k : S=>commonData (withHeight (first k.val.val) (χ₂ k.val.val)
      (t₂ k.val.val)) (C₂ k.val.val) (R₂ k.val.val) (pick k)
    let shell := fun k : S=>∑L∈Ds k.val.val,∑a∈(daughter k).toSource.active L,
      retainedAllocationCost (daughter k) L a (z k.val.val)
    have hshell (k : S) : 0≤ shell k := Finset.sum_nonneg (fun _ _=>
      Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
    change (∑k : S,(‖scalar k.val.val‖^2*(∏j,(first k.val.val).M j)^2*
      ((C₂ k.val.val).absNorm:ℝ)^(ε-1))*shell k)≤_
    calc
      _≤∑k : S,(Cscalar*Z^scalarCap)*shell k := Finset.sum_le_sum
        (fun k _=>mul_le_mul_of_nonneg_right (hscalar k.val.val k.val.property) (hshell k))
      _=(Cscalar*Z^scalarCap)*(∑k : S,shell k) := (Finset.mul_sum ..).symm
      _≤(Cscalar*Z^scalarCap)*(Ccoarse*control*(2*T)^(2*ε)*
          Z^(m+B+loss+((N:ℝ)+2)*cap+pad)) :=
        mul_le_mul_of_nonneg_left hj (mul_nonneg hCscalar (Real.rpow_nonneg hzpos.le _))
      _=_ := by
        dsimp only [E,extra]
        simp only [Real.rpow_add hzpos]
        ring

/-- The Mellin shift is paid from the original outer-height budget. This
supplies the two literal small-height gates in every buffered zero bin. -/
theorem geometry_shifted_small_outer_height (T t height θ u : ℝ) (i : ℕ) (freq : ℝ)
    (hT : 0≤T) (hheight : 0≤height)
    (hsmall : |t|+height+2*Real.pi*(|u|+|θ|)≤T) (hfreq : |freq|≤height) :
    |t+2*Real.pi*(u-θ)+freq|+T/2≤(3*i+2:ℕ)*T ∧
      |t+2*Real.pi*(u-θ)|+T/2≤(3*i+2:ℕ)*T := by
  apply geometry_small_outer_height T (t+2*Real.pi*(u-θ)) height i freq hT hheight _ hfreq
  have ht:=abs_add_le t (2*Real.pi*(u-θ))
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)] at ht
  have hu : |u-θ|≤|u|+|θ| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le u (-θ)
  nlinarith [Real.pi_pos]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
