/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B152
import Candidate.Bundles.B174

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseJoint; sha256 03850fdfbf4aa59b9c44b71156fcc01df9c0ab6fc46d6376f834ce67a5bde05b -/
section
                                                     
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61Moment
local notation "O" => HeckeFamily.O

/-- Full residual-projector coarse energy for one injective joint selection.
The finite menu of slot types is fixed before the moving labels. -/
theorem actual_selected_coarse_shell {Index : Type}[Fintype Index]
    (Slots : Index→ Type)[∀i,Fintype (Slots i)][∀i,DecidableEq (Slots i)]
    (N : ℕ)(hN : ∀i,Fintype.card (Slots i)≤ N)
    (B loss ε : ℝ)(hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
      (Z m e allowance control T : ℝ),2≤ Z → 0≤ control → 1≤ T →
      ∀(key : κ→ NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤ Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤ Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^m) →
      ∀(index : κ→ Index)(s : ∀l,Data (Slots (index l)))(z : κ→ O)
        (Ds : κ→ Finset (Ideal O))(B₁ B₂ : κ→ℝ),
      (∀l∈labels,0≤ B₁ l ∧ 0≤ B₂ l) →
      (∀l∈labels,∀x,‖(s l).W₁ x‖≤ B₁ l ∧ ‖(s l).W₂ x‖≤ B₂ l) →
      (∀l∈labels,coarseAllocationControl (s l) (B₁ l) (B₂ l)≤ control*Z^e) →
      (∀l∈labels,(s l).toSource.allowance Z≤ allowance) →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∑l∈labels,∑D∈Ds l,∑a∈(s l).toSource.active D,
        retainedAllocationCost (s l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+e+allowance) := by
  choose K hK hbound using fun i=>actual_second_coarse_shell N (hN i) ε hε
  let Kall := 1+∑i,K i
  have hKall : 0< Kall := by
    dsimp [Kall]
    have hh : 0≤∑i,K i := Finset.sum_nonneg (fun i _=>(hK i).le)
    linarith
  have hKle (i : Index) : K i≤ Kall := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ)=>(hK j).le) (Finset.mem_univ i)
    dsimp [Kall]
    linarith
  obtain ⟨C,hC,hcount⟩ := actual_joint_coarse_row_count B loss hB hloss
  refine ⟨C*Kall,mul_pos hC hKall,?_⟩
  intro κ left u₀ unit Z m e allowance control T hZ hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index s z Ds B₁ B₂ hBs hWs hcost hallow hDs
  have hZ0 : 0< Z := by linarith
  have hc := hcount left u₀ unit Z hZ m (labels.image key)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hrow r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupported r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact heq r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupport r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hnorm r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hmissing r hr)
  rw [Finset.card_image_of_injective _ hinj] at hc
  let W := Kall*control*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0≤ W := by dsimp [W]; positivity
  have hpoint (l : κ)(hl : l∈labels) :
      (∑D∈Ds l,∑a∈(s l).toSource.active D,retainedAllocationCost (s l) D a (z l))≤ W := by
    have hh := hbound (index l) (s l) (Ds l) (fun D hD=>(hDs l hl D hD).1)
      T Z hT (by linarith) (fun D hD=>(hDs l hl D hD).2.1)
      (fun D hD=>(hDs l hl D hD).2.2) (fun _ _=>z l)
      (B₁ l) (B₂ l) (hBs l hl).1 (hBs l hl).2
      (fun x=>(hWs l hl x).1) (fun x=>(hWs l hl x).2)
    apply hh.trans
    calc
      _≤(control*Z^e)*Kall*(2*T)^(2*ε)*Z^allowance := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (hcost l hl) (hKle (index l)) (hK _).le (by positivity)
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (hallow l hl)
        · positivity
        · positivity
      _=W := by
        dsimp [W]
        rw [Real.rpow_add hZ0]
        ring
  calc
    _≤∑_l∈labels,W := Finset.sum_le_sum hpoint
    _=(labels.card:ℝ)*W := by simp
    _≤(C*Z^(m+B+loss))*W := mul_le_mul_of_nonneg_right hc hW
    _=(C*Kall)*control*(2*T)^(2*ε)*Z^(m+B+loss+e+allowance) := by
      dsimp [W]
      rw [show m+B+loss+e+allowance=(m+B+loss)+(e+allowance) by ring,Real.rpow_add hZ0 (m+B+loss) (e+allowance)]
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_coarse_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseJoint -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseChild; sha256 ebf7a601c70a22f7bdbb34c01e118670986841a617ef4fa367a34eeada6af51d -/
section
                                                     

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open Cycle61Moment
local notation "O" => HeckeFamily.O

/-- An all-height joint shell estimate from the original source's fixed
support, coefficient and scale bounds. The two common allocations and their
new heights are quantified after the constant and asymptotic threshold. -/
theorem actual_child_selected_coarse_shell {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window cap : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ cap) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (m control T : ℝ),0≤ control → 1≤ T →
      ∀(key : κ→ NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤ Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤ Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^m) →
      ∀s : Input α,(∀j,s.M j≤ Cs) → s.upper≤ b → s.b₁≤ bs → s.b₂≤ bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      (∀j,s.P j≤ Z^cap) →
      ∀(C₁ R₁ : κ→ Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ : κ→ Ideal O)(A₂ : ∀l,actualAllocations (first l).pools (C₂ l))
        (χ₂ : κ→ Character)(t₂ : κ→ℝ)(z : κ→ O)
        (Ds : κ→ Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤ B₁ → 0≤ B₂ → (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) →
      (B₁*B₂)^2≤ control →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (χ₂ l) (t₂ l)) (C₂ l) (R₂ l) (A₂ l)
      (∑l∈labels,∑D∈Ds l,∑a∈(src l).toSource.active D,
        retainedAllocationCost (src l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+((N:ℝ)+2)*cap+pad) := by
  let Index := (S : Finset α) × Finset S
  let Slots := fun i : Index=>↥i.2
  have hN (i : Index) : Fintype.card (Slots i)≤ N := by
    exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans hα)
  obtain ⟨C,hC,hshell⟩ := actual_selected_coarse_shell Slots N hN B loss ε hB hloss hε
  have hfixed := coarse_fixed_control_pos N Cs b bs hCs hb hbs
  refine ⟨C*coarseFixedControl N Cs b bs,mul_pos hC hfixed,?_⟩
  filter_upwards [eventual_two_common_allowance N window bs pad hwindow hbs hpad,
    eventually_ge_atTop (2:ℝ)] with Z hallow hZ
  refine ⟨hZ,?_⟩
  intro κ left u₀ unit m control T hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ A₂ χ₂ t₂ z Ds B₁ B₂ hB₁ hB₂ hW₁ hW₂ hcontrolB hDs src
  let index := fun l=> (⟨CenteredMomentCommonProfile.liveIndices (A₁ l).val,
    CenteredMomentCommonProfile.liveIndices (A₂ l).val⟩ : Index)
  have hh := hshell left u₀ unit Z m (((N:ℝ)+2)*cap) pad
    (coarseFixedControl N Cs b bs*control) T hZ (mul_nonneg hfixed.le hcontrol) hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index src z Ds (fun _=>B₁) (fun _=>B₂)
    (fun _ _=>⟨hB₁,hB₂⟩) (fun _ _ x=>⟨hW₁ x,hW₂ x⟩) ?_ ?_ hDs
  · convert hh using 1 <;> ring
  · intro l hl
    exact (actual_two_common_coarse_control N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap
      (by linarith) hB₁ hB₂ s hα hM hupper hb₁ hb₂ hscales hP
      (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l) (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrolB hfixed.le) (by positivity))
  · intro l hl
    have hh := hallow.2 s hα hwin hb₁ hb₂ (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)
    have hp : 0≤ Cycle61.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂] := by
      unfold Cycle61.Physical.plainClipAllowance
      exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hallow.1 (le_max_left _ _))
    linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_selected_coarse_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseChild -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondWeightedShellWindows; sha256 814883a5e52651a9223f1b9961825f3dc4fecb6cf2fda09a02da56a1bdd80331 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
local instance secondWeightedShellDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Transfer weighted joint shell energy through the actual Mellin windows.
The source-dependent scalar remains in the joint sum, so its cancellation
with the source exponents survives common-allocation selection. -/
theorem actual_second_weighted_shell_windows {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R seed : κ→ Ideal O)
      (hC : ∀k,Supported (C k)) (Ds : κ→ Finset (Ideal O))
      (η : κ→ Character) (t θ X : κ→ℝ) (hX : ∀k,0< X k)
      (z : κ→ O) (scalar : κ→ℂ)
      (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
      (J : ℕ) (E T : ℝ),0≤ E → 1≤ T →
      (∀k∈rows,seed k∣C k) → (∀k∈rows,(s k).upper≤ b) →
      (∀k∈rows,C k≠0) →
      (∀k∈rows,∀L∈Ds k,Squarefree L ∧ (L.absNorm:ℝ)≤2*T) →
      (∀u : ℝ,∀S : Finset rows,
        ∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,frozenCoefficient (pick k).val (C k.val.val) (R k.val.val)
          (s k.val.val).ν (s k.val.val).W (s k.val.val).P≠0) →
        (∑k : S,(‖scalar k.val.val‖^2*(∏j,(s k.val.val).M j)^2*((C k.val.val).absNorm:ℝ)^(ε-1))*
          (∑L∈Ds k.val.val,
          ∑a∈(commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)).toSource.active L,
            retainedAllocationCost (commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)) L a (z k.val.val)))≤ E*(1+‖u‖)^(2*J)) →
      (∑k∈rows,∑L∈Ds k,‖scalar k*windowColumn (s k) (C k) (hC k)
        (R k) (seed k) L (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
        (K*E*(2*T)^ε)*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  obtain ⟨K₁,hK₁,hwindow⟩ := actual_second_allocation_window_energy (α:=α) ε hε
  obtain ⟨K₂,hK₂,hcommon⟩ := actual_second_weighted_common_selection (α:=α) b ε hε
  refine ⟨K₁*K₂,mul_pos hK₁ hK₂,?_⟩
  intro κ rows slots s C R seed hC Ds η t θ X hX z scalar V hc hs J E T
    hE hT hseed hupper hCne hDs hjoint
  let pairs := rows.sigma Ds
  have hbudget (u : ℝ) :
      (∑q∈pairs,‖scalar q.1‖^2*((q.2.absNorm:ℝ)^ε)*
        commonRetainedCost (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
          (C q.1) (R q.1) q.2 (z q.1))≤
        (K₂*E*(2*T)^ε)*(1+‖u‖)^(2*J) := by
    have hh := hcommon rows slots
      (fun k=>withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      C R Ds z scalar (E*(1+‖u‖)^(2*J)) hupper hCne
      (fun S pick hne=>hjoint u S pick (fun k=>right_ne_zero_of_mul (hne k)))
    calc
      _≤∑q∈pairs,‖scalar q.1‖^2*(2*T)^ε*
          commonRetainedCost (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
            (C q.1) (R q.1) q.2 (z q.1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hmem := Finset.mem_sigma.mp hq
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (hDs q.1 hmem.1 q.2 hmem.2).2 hε.le)
            (sq_nonneg _)) (common_retained_cost_nonneg _ _ _ _ _)
      _=(2*T)^ε*(∑k∈rows,‖scalar k‖^2*∑L∈Ds k,
          commonRetainedCost (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
            (C k) (R k) L (z k)) := by
        simp only [pairs,Finset.sum_sigma,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro L hL
        ring
      _≤(2*T)^ε*(K₂*(E*(1+‖u‖)^(2*J))) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by linarith) _)
      _=_ := by ring
  have hw := hwindow pairs (fun q=>slots q.1) (fun q=>s q.1)
    (fun q=>C q.1) (fun q=>R q.1) (fun q=>seed q.1) (fun q=>q.2)
    (fun q=>hC q.1) (fun q=>η q.1) (fun q=>t q.1) (fun q=>θ q.1)
    (fun q=>X q.1) (fun q=>hX q.1) (fun q=>z q.1) (fun q=>scalar q.1)
    V hc hs J (K₂*E*(2*T)^ε) (by positivity)
    (fun q hq=>hseed q.1 (Finset.mem_sigma.mp hq).1)
    (fun q hq=>(hDs q.1 (Finset.mem_sigma.mp hq).1 q.2 (Finset.mem_sigma.mp hq).2).1)
    hbudget
  simp only [pairs,Finset.sum_sigma] at hw
  convert hw using 1 <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_weighted_shell_windows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondWeightedShellWindows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighWindow; sha256 40498f8772045c745e81bd55a4c4b2ec85a002d271f24b875100b69e500926ee -/
section
                                                     
                                                      
                                                              
                                                         

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonProfile CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource Cycle61Moment FourierBridge
local notation "O" => HeckeFamily.O
local instance geometryHighWindowDecidableSum {ι : Type} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Genuine all-height source bound. Constants precede moving characters,
heights and both allocations; the first child is never replaced by a datum
with only a matching character. -/
theorem actual_child_weighted_coarse_columns {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window cap scalarCap : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ cap) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (m control T Cscalar : ℝ),0≤ control → 1≤ T → 0≤ Cscalar →
      ∀(key : κ→ NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀rows : Finset κ,
      (∀label∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤ Z^B) →
      (∀label∈rows,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈rows,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈rows,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^B) →
      (∀label∈rows,((key label).val.1.1.1.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤ Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤ Z^B) →
      (∀label∈rows,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^m) →
      ∀s : Input α,(∀j,s.M j≤ Cs) → s.upper≤ b → s.b₁≤ bs → s.b₂≤ bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      (∀j,s.P j≤ Z^cap) →
      ∀(C₁ R₁ : κ→ Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ seed : κ→ Ideal O)(hC₂ : ∀k,Supported (C₂ k))
        (χ₂ : κ→ Character)(t₂ θ : κ→ℝ)(z : κ→ O)
        (scalar : κ→ℂ)(Ds : κ→ Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤ B₁ → 0≤ B₂ → (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) →
      (B₁*B₂)^2≤ control → (∀k∈rows,seed k∣C₂ k) →
      (∀k∈rows,‖scalar k‖^2*(∏j,(first k).M j)^2*((C₂ k).absNorm:ℝ)^(ε-1)≤ Cscalar*Z^scalarCap) →
      (∀k∈rows,∀D∈Ds k,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀u : ℝ,
      (∑k∈rows,∑L∈Ds k,‖scalar k*normalizedColumn
        (withHeight (first k) (χ₂ k) (t₂ k+2*Real.pi*(u-θ k)))
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
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ seed hC₂ χ₂ t₂ θ z scalar Ds B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB hseed hscalar hDs u
  have hzpos : 0< Z := by linarith [hz.1]
  have ht : 0<2*T := by linarith
  let extra := scalarCap+(B+loss+((N:ℝ)+2)*cap+pad)
  let E := Cscalar*Ccoarse*control*(2*T)^(2*ε)*Z^(m+extra)
  let shifted := fun k=>withHeight (first k) (χ₂ k) (t₂ k+2*Real.pi*(u-θ k))
  have hjoint := hcommon rows (fun k=>liveIndices (A₁ k).val) shifted C₂ R₂ Ds z scalar E
    (fun _ _=>hupper) (fun k _=>(hC₂ k).1) ?_
  · calc
      _≤ Kcolumn*(2*T)^ε*(∑k∈rows,‖scalar k‖^2*∑L∈Ds k,
          commonRetainedCost (shifted k) (C₂ k) (R₂ k) L (z k)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro L hL
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
      _≤ Kcolumn*(2*T)^ε*(Kcommon*E) :=
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
      (fun k=>χ₂ k.val.val) (fun k=>t₂ k.val.val+2*Real.pi*(u-θ k.val.val))
      (fun k=>z k.val.val) (fun k=>Ds k.val.val) B₁ B₂ hB₁ hB₂ hW₁ hW₂ hcontrolB
      (fun k _=>hDs k.val.val k.val.property)
    let daughter := fun k : S=>commonData (withHeight (first k.val.val) (χ₂ k.val.val)
      (t₂ k.val.val+2*Real.pi*(u-θ k.val.val))) (C₂ k.val.val) (R₂ k.val.val) (pick k)
    let shell := fun k : S=>∑L∈Ds k.val.val,∑a∈(daughter k).toSource.active L,
      retainedAllocationCost (daughter k) L a (z k.val.val)
    have hshell (k : S) : 0≤ shell k := Finset.sum_nonneg (fun _ _=>
      Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
    change (∑k : S,(‖scalar k.val.val‖^2*(∏j,(first k.val.val).M j)^2*
      ((C₂ k.val.val).absNorm:ℝ)^(ε-1))*shell k)≤ _
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


/-- A fixed Schwartz moment pays any polynomial loss on the complementary
Mellin heights. There is no bound on the moving shifted source heights. -/
theorem finite_weighted_mellin_tail_energy {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (H : ℝ) (hH : 0< H) (n : ℕ)
    (E : ℝ) (hE : 0≤ E)
    (hb : Integrable (fun u : ℝ=>(1+‖u‖)^n*‖b u‖))
    (hφ : ∀k,Integrable (fun u=>b u*φ k u))
    (hbound : ∀u : ℝ,(∑k,‖φ k u‖^2)≤ E) :
    H^(2*n)*(∑k,‖∫u : ℝ in {u : ℝ | H<1+‖u‖},b u*φ k u‖^2)≤
      E*(∫u : ℝ,(1+‖u‖)^n*‖b u‖)^2 := by
  let A := {u : ℝ | H<1+‖u‖}
  have hA : MeasurableSet A := isOpen_lt continuous_const (continuous_const.add continuous_norm) |>.measurableSet
  let ψ := fun k=>A.indicator (φ k)
  have hi (k : κ) : Integrable (fun u=>b u*ψ k u) := by
    convert (hφ k).indicator hA using 1
    funext u
    by_cases hu : u∈A <;> simp [ψ,hu]
  have hw (u : ℝ) : 0<(1+‖u‖)^n/H^n := by positivity
  have he (u : ℝ) : (∑k,‖ψ k u‖^2)≤ E*((1+‖u‖)^n/H^n)^2 := by
    by_cases hu : u∈A
    · have hpow : H^n≤(1+‖u‖)^n := pow_le_pow_left₀ hH.le hu.le n
      have hratio : 1≤(1+‖u‖)^n/H^n := (le_div_iff₀ (pow_pos hH n)).mpr (by simpa using hpow)
      have hsq : 1≤((1+‖u‖)^n/H^n)^2 := by nlinarith
      simpa only [ψ,Set.indicator_of_mem hu] using
        (hbound u).trans (by nlinarith)
    · simp only [ψ,Set.indicator_of_notMem hu,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
      positivity
  have hh := CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b ψ
    (fun u=>(1+‖u‖)^n/H^n) hw E hE (by
      convert hb.div_const (H^n) using 1
      funext u
      ring) hi he
  have hint (k : κ) : (∫u : ℝ,b u*ψ k u)=∫u : ℝ in A,b u*φ k u := by
    rw [←integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u∈A <;> simp [ψ,hu]
  simp only [hint] at hh
  have hr : (∫u : ℝ,((1+‖u‖)^n/H^n)*‖b u‖)=
      (∫u : ℝ,(1+‖u‖)^n*‖b u‖)/H^n := by
    calc
      _=(∫u : ℝ,(H^n)⁻¹*((1+‖u‖)^n*‖b u‖)) := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [div_eq_mul_inv]
        ring
      _=_ := by rw [integral_const_mul]; simp only [div_eq_mul_inv]; ring
  rw [hr] at hh
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hH.le (2*n))
  convert hm using 1
  rw [show 2*n=n*2 by omega,pow_mul]
  field_simp [(pow_pos hH n).ne']

/-- Literal joint complementary Mellin energy. The source bound consumed
here is supplied, at every height, by `actual_child_weighted_coarse_columns`.
Increasing n uses only the fixed window's Schwartz moments. -/
theorem actual_high_column_mellin_tail {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→ Finset α) (s : (k : κ)→ Input (slots k))
    (C R seed : κ→ Ideal O) (hC : ∀k,Supported (C k)) (Ds : κ→ Finset (Ideal O))
    (η : κ→ Character) (t θ X : κ→ℝ) (hX : ∀k,0< X k)
    (z : κ→ O) (scalar : κ→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (cutoff E : ℝ) (hcutoff : 0< cutoff) (hE : 0≤ E) (n : ℕ)
    (henergy : ∀u : ℝ,
      (∑k∈rows,∑L∈Ds k,‖scalar k*normalizedColumn
        (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
        (C k) (hC k) (R k) (seed k) L (z k)‖^2)≤ E) :
    cutoff^(2*n)*(∑k∈rows,∑L∈Ds k,
      ‖scalar k*(∫u : ℝ in {u : ℝ | cutoff<1+‖u‖},
        columnDensity V hc hs u*logPhase (θ k-u) (Real.log (X k))*
        normalizedColumn (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
          (C k) (hC k) (R k) (seed k) L (z k))‖^2)≤
      E*(∫u : ℝ,(1+‖u‖)^n*‖columnDensity V hc hs u‖)^2 := by
  let pairs:=rows.sigma Ds
  let φ (q : (_ : κ)×Ideal O) (u : ℝ):=logPhase (θ q.1-u) (Real.log (X q.1))*
    (scalar q.1*normalizedColumn (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
      (C q.1) (hC q.1) (R q.1) (seed q.1) q.2 (z q.1))
  have hi (q : (_ : κ)×Ideal O) : Integrable (fun u=>columnDensity V hc hs u*φ q u) := by
    have hh := (actual_window_column_integrable (s q.1) (C q.1) (hC q.1) (R q.1)
      (seed q.1) q.2 (η q.1) (t q.1) (θ q.1) (X q.1) (hX q.1) V hc hs (z q.1)).const_mul (scalar q.1)
    convert hh using 1
    funext u
    dsimp only [φ]
    ring
  have hb (u : ℝ) : (∑q : pairs,‖φ q.val u‖^2)≤ E := by
    rw [Finset.sum_coe_sort pairs (fun q=>‖φ q u‖^2)]
    simpa only [pairs,Finset.sum_sigma,φ,norm_mul,logPhase_norm,one_mul] using henergy u
  have ht:=finite_weighted_mellin_tail_energy (columnDensity V hc hs)
    (fun q : pairs=>φ q.val) cutoff hcutoff n E hE
    (columnDensity_moments V hc hs n) (fun q=>hi q.val) hb
  have he (q : (_ : κ)×Ideal O) :
      (∫u : ℝ in {u : ℝ | cutoff<1+‖u‖},columnDensity V hc hs u*φ q u)=
      scalar q.1*(∫u : ℝ in {u : ℝ | cutoff<1+‖u‖},
        columnDensity V hc hs u*logPhase (θ q.1-u) (Real.log (X q.1))*
        normalizedColumn (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
          (C q.1) (hC q.1) (R q.1) (seed q.1) q.2 (z q.1)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [φ]
    ring
  rw [Finset.sum_coe_sort pairs (fun q=>‖∫u : ℝ in {u : ℝ | cutoff<1+‖u‖},
    columnDensity V hc hs u*φ q u‖^2)] at ht
  simpa only [he,pairs,Finset.sum_sigma] using ht

/-- The Mellin shift is paid from the original outer-height budget. This
supplies the two literal small-height gates in every buffered zero bin. -/
theorem geometry_shifted_small_outer_height (T t height θ u : ℝ) (i : ℕ) (freq : ℝ)
    (hT : 0≤ T) (hheight : 0≤ height)
    (hsmall : |t|+height+2*Real.pi*(|u|+|θ|)≤ T) (hfreq : |freq|≤ height) :
    |t+2*Real.pi*(u-θ)+freq|+T/2≤(3*i+2:ℕ)*T ∧
      |t+2*Real.pi*(u-θ)|+T/2≤(3*i+2:ℕ)*T := by
  apply geometry_small_outer_height T (t+2*Real.pi*(u-θ)) height i freq hT hheight _ hfreq
  have ht:=abs_add_le t (2*Real.pi*(u-θ))
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)] at ht
  have hu : |u-θ|≤|u|+|θ| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le u (-θ)
  nlinarith [Real.pi_pos]

/-- A smaller inner Mellin exponent fits the original outer shell at a
threshold independent of every height, source, row and buffered index. -/
theorem eventually_geometry_inner_shift_admission (outer inner : ℝ) (hgap : inner< outer) :
    ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀t height θ u : ℝ,∀i : ℕ,∀freq : ℝ,
      0≤ height → |t|+height+2*Real.pi*|θ|≤ Z^outer/2 →
      1+‖u‖≤ Z^inner → |freq|≤ height →
      |t+2*Real.pi*(u-θ)+freq|+Z^outer/2≤(3*i+2:ℕ)*Z^outer ∧
        |t+2*Real.pi*(u-θ)|+Z^outer/2≤(3*i+2:ℕ)*Z^outer := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually
    (eventually_ge_atTop (4*Real.pi)),eventually_ge_atTop (1:ℝ)] with Z hpower hZ
  refine ⟨hZ,?_⟩
  intro t height θ u i freq hh hbase hu hf
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hp : 0≤ Z^inner := Real.rpow_nonneg hz.le _
  have hid : Z^outer=Z^inner*Z^(outer-inner) := by
    rw [←Real.rpow_add hz]
    congr 1
    ring
  have hinner : 2*Real.pi*|u|≤ Z^outer/2 := by
    rw [Real.norm_eq_abs] at hu
    have hmul:=mul_le_mul_of_nonneg_left hpower hp
    rw [hid]
    nlinarith [Real.pi_pos]
  apply geometry_shifted_small_outer_height (Z^outer) t height θ u i freq
    (Real.rpow_nonneg hz.le _) hh _ hf
  nlinarith

/-- Full coarse windows and arbitrary complementary-tail gain from the
literal two-allocation source. Neither conclusion has an energy premise. -/
theorem actual_child_weighted_coarse_windows {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window cap scalarCap : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ cap) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (m control T Cscalar : ℝ),0≤ control → 1≤ T → 0≤ Cscalar →
      ∀(key : κ→ NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀rows : Finset κ,
      (∀label∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤ Z^B) →
      (∀label∈rows,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈rows,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈rows,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^B) →
      (∀label∈rows,((key label).val.1.1.1.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤ Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤ Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤ Z^B) →
      (∀label∈rows,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤ Z^m) →
      ∀s : Input α,(∀j,s.M j≤ Cs) → s.upper≤ b → s.b₁≤ bs → s.b₂≤ bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      (∀j,s.P j≤ Z^cap) →
      ∀(C₁ R₁ : κ→ Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ seed : κ→ Ideal O)(hC₂ : ∀k,Supported (C₂ k))
        (χ₂ : κ→ Character)(t₂ θ X : κ→ℝ)(_hX : ∀k,0< X k)(z : κ→ O)
        (scalar : κ→ℂ)(Ds : κ→ Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤ B₁ → 0≤ B₂ → (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) →
      (B₁*B₂)^2≤ control → (∀k∈rows,seed k∣C₂ k) →
      (∀k∈rows,‖scalar k‖^2*(∏j,(first k).M j)^2*((C₂ k).absNorm:ℝ)^(ε-1)≤ Cscalar*Z^scalarCap) →
      (∀k∈rows,∀D∈Ds k,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀(V : ℝ→ℂ)(hc : HasCompactSupport V)(hs : ContDiff ℝ ∞ V),
      let E:=K*(Cscalar*control)*(2*T)^(3*ε)*
        Z^(m+scalarCap+B+loss+((N:ℝ)+2)*cap+pad)
      (∑k∈rows,∑L∈Ds k,‖scalar k*windowColumn (first k) (C₂ k) (hC₂ k)
        (R₂ k) (seed k) L (χ₂ k) (t₂ k) (θ k) (X k) V (z k)‖^2)≤
          E*(∫u : ℝ,‖columnDensity V hc hs u‖)^2 ∧
      ∀cutoff : ℝ,0< cutoff → ∀n : ℕ,
      cutoff^(2*n)*(∑k∈rows,∑L∈Ds k,
        ‖scalar k*(∫u : ℝ in {u : ℝ | cutoff<1+‖u‖},
          columnDensity V hc hs u*logPhase (θ k-u) (Real.log (X k))*
          normalizedColumn (withHeight (first k) (χ₂ k) (t₂ k+2*Real.pi*(u-θ k)))
            (C₂ k) (hC₂ k) (R₂ k) (seed k) L (z k))‖^2)≤
          E*(∫u : ℝ,(1+‖u‖)^n*‖columnDensity V hc hs u‖)^2 := by
  obtain ⟨K,hK,hcoarse⟩:=actual_child_weighted_coarse_columns N hα
    B loss ε pad Cs b bs window cap scalarCap hB hloss hε hpad hCs hb hbs hwindow hcap
  refine ⟨K,hK,?_⟩
  filter_upwards [hcoarse] with Z hz
  refine ⟨hz.1,?_⟩
  intro κ left u₀ unit m control T Cscalar hcontrol hT hCscalar key hinj rows
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ seed hC₂ χ₂ t₂ θ X hX z scalar Ds B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB hseed hscalar hDs V hc hs E
  have henergy:=hz.2 left u₀ unit m control T Cscalar hcontrol hT hCscalar key hinj rows
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ C₂ R₂ seed hC₂ χ₂ t₂ θ z scalar Ds B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB hseed hscalar hDs
  have hZ : 0≤ Z := by linarith [hz.1]
  have ht : 0≤2*T := by linarith
  have hE : 0≤ E := by dsimp only [E]; positivity
  constructor
  · have hw:=actual_heterogeneous_joint_window_energy (rows.sigma Ds)
      (fun q=>liveIndices (A₁ q.1).val) (fun q=>first q.1)
      (fun q=>C₂ q.1) (fun q=>R₂ q.1) (fun q=>seed q.1) (fun q=>q.2)
      (fun q=>hC₂ q.1) (fun q=>χ₂ q.1) (fun q=>t₂ q.1) (fun q=>θ q.1)
      (fun q=>X q.1) (fun q=>hX q.1) (fun q=>z q.1) (fun q=>scalar q.1)
      V hc hs 0 E hE (by
        intro u
        simpa only [Finset.sum_sigma,Nat.mul_zero,pow_zero,mul_one,E] using henergy u)
    simpa only [Finset.sum_sigma,pow_zero,one_mul] using hw
  · intro cutoff hcutoff n
    exact actual_high_column_mellin_tail rows (fun k=>liveIndices (A₁ k).val) first
      C₂ R₂ seed hC₂ Ds χ₂ t₂ θ X hX z scalar V hc hs cutoff E hcutoff hE n henergy

/-- Choose the tail moment degree before the scale. Its polynomial gain
absorbs the fixed coarse scale loss down to any prescribed target power. -/
theorem geometry_coarse_tail_degree (coarse target τ : ℝ) (hτ : 0<τ) :
    ∃n : ℕ,∀Z : ℝ,1≤ Z → Z^coarse≤ Z^target*(Z^τ)^(2*n) := by
  obtain ⟨n,hn⟩:=exists_nat_gt ((coarse-target)/(2*τ))
  refine ⟨n,?_⟩
  intro Z hZ
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have he : coarse≤ target+τ*(2*n:ℕ) := by
    have hh:=(div_lt_iff₀ (by positivity : 0<2*τ)).mp hn
    push_cast
    linarith
  calc
    Z^coarse≤ Z^(target+τ*(2*n:ℕ)) := Real.rpow_le_rpow_of_exponent_le hZ he
    _=Z^target*(Z^τ)^(2*n) := by
      rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_natCast]

/-- Exact complementary domain used by the original Mellin split. -/
theorem geometry_mellin_complement (cutoff : ℝ) :
    {u : ℝ | 1+‖u‖≤ cutoff}ᶜ={u : ℝ | cutoff<1+‖u‖} := by
  ext u
  simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_le]

/-- The actual second block keeps the original first child as its input,
including every profile and coefficient field, before Mellin height shifts. -/
theorem actual_high_second_block_input {α : Type*} [Fintype α] [DecidableEq α]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).input=s := rfl


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_weighted_coarse_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.finite_weighted_mellin_tail_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_second_block_input

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_column_mellin_tail
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_shifted_small_outer_height

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_weighted_coarse_windows

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_mellin_complement

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_geometry_inner_shift_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_coarse_tail_degree

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighWindow -/
