import Candidate.Cycle62.Physical.InitialMass.SecondCoarseCount
import Candidate.Cycle62.Physical.InitialMass.SecondCoarseControl

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle62Moment
local notation "O" => HeckeFamily.O

/-- Full residual-projector coarse energy for one injective joint selection.
The finite menu of slot types is fixed before the moving labels. -/
theorem actual_selected_coarse_shell {Index : Type}[Fintype Index]
    (Slots : Index→Type)[∀i,Fintype (Slots i)][∀i,DecidableEq (Slots i)]
    (N : ℕ)(hN : ∀i,Fintype.card (Slots i)≤N)
    (B loss ε : ℝ)(hB : 0≤B)(hloss : 0<loss)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
      (Z m e allowance control T : ℝ),2≤Z → 0≤control → 1≤T →
      ∀(key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^m) →
      ∀(index : κ→Index)(s : ∀l,Data (Slots (index l)))(z : κ→O)
        (Ds : κ→Finset (Ideal O))(B₁ B₂ : κ→ℝ),
      (∀l∈labels,0≤B₁ l ∧ 0≤B₂ l) →
      (∀l∈labels,∀x,‖(s l).W₁ x‖≤B₁ l ∧ ‖(s l).W₂ x‖≤B₂ l) →
      (∀l∈labels,coarseAllocationControl (s l) (B₁ l) (B₂ l)≤control*Z^e) →
      (∀l∈labels,(s l).toSource.allowance Z≤allowance) →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∑l∈labels,∑D∈Ds l,∑a∈(s l).toSource.active D,
        retainedAllocationCost (s l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+e+allowance) := by
  choose K hK hbound using fun i=>actual_second_coarse_shell N (hN i) ε hε
  let Kall := 1+∑i,K i
  have hKall : 0<Kall := by
    dsimp [Kall]
    have hh : 0≤∑i,K i := Finset.sum_nonneg (fun i _=>(hK i).le)
    linarith
  have hKle (i : Index) : K i≤Kall := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ)=>(hK j).le) (Finset.mem_univ i)
    dsimp [Kall]
    linarith
  obtain ⟨C,hC,hcount⟩ := actual_joint_coarse_row_count B loss hB hloss
  refine ⟨C*Kall,mul_pos hC hKall,?_⟩
  intro κ left u₀ unit Z m e allowance control T hZ hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index s z Ds B₁ B₂ hBs hWs hcost hallow hDs
  have hZ0 : 0<Z := by linarith
  have hc := hcount left u₀ unit Z hZ m (labels.image key)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hrow r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupported r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact heq r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupport r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hnorm r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hmissing r hr)
  rw [Finset.card_image_of_injective _ hinj] at hc
  let W := Kall*control*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0≤W := by dsimp [W]; positivity
  have hpoint (l : κ)(hl : l∈labels) :
      (∑D∈Ds l,∑a∈(s l).toSource.active D,retainedAllocationCost (s l) D a (z l))≤W := by
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
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_selected_coarse_shell
