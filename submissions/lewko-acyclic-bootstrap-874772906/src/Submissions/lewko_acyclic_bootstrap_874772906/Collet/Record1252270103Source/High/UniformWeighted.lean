/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.ActualWeighted
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.Record1252270103Source.High
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer Record12518109GainActual
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ordinary_weighted_uniform
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (capacity lam cap sourceMesh : ℝ)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ εm binWidth ζ η : ℝ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      1/2≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤sourceMesh → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff capacity lam cap B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          gain (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := ordinary_actual_weighted_row_sum (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 capacity lam cap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm ζ hsource hWs hW hbΦ hrad hζ hεm hβ
  obtain ⟨K,hK,hdyadic⟩ := fixed_label_dyadic_cost (Label:=Label) η hη
  let A : ℝ := (HeckeDetectorClassBudget.alphabetBound binWidth : ℝ)^Fintype.card Slot
  let C' := (1+A)*(1+K)*C
  have hA : 0≤A := by dsimp [A]; positivity
  have hC' : 0<C' := by dsimp [C']; positivity
  refine ⟨J,C',hC',?_⟩
  filter_upwards [hfield,hdyadic] with U hfield hdyadic
  refine ⟨hfield.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    witness hQ
  have he := hfield.2 B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax'
    hbin hbin' hwm hL hh hf hv hchoice witness hQ
  have hcard : (Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)≤A := by
    have hb := HeckeDetectorClassBudget.bin_card_le B.slots ((2*a-1)/2) binWidth (by linarith) hbin
    have hp : (HeckeDetectorClassBudget.alphabetBound binWidth)^B.slots.card≤
        (HeckeDetectorClassBudget.alphabetBound binWidth)^Fintype.card Slot := by
      apply Nat.pow_le_pow_right
      · unfold HeckeDetectorClassBudget.alphabetBound
        omega
      · exact Finset.card_le_univ B.slots
    dsimp only [A]
    exact_mod_cast hb.trans hp
  let E := rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
    gain (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
    155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)
  have hUp : 0<U := zero_lt_one.trans hfield.1
  have hcost : ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
      (dyadicLength U:ℝ)^2*C)≤(A*K*C)*U^η := by
    have hp := mul_le_mul hcard hdyadic (by positivity) hA
    have hpc := mul_le_mul_of_nonneg_right hp hC.le
    convert hpc using 1 <;> ring
  have hconst : A*K*C≤C' := by
    apply mul_le_mul_of_nonneg_right _ hC.le
    exact mul_le_mul (by linarith : A≤1+A) (by linarith : K≤1+K) hK (by positivity)
  apply he.trans
  change _≤C'*(1+height)^J*U^(E+η)
  calc
    _≤((A*K*C)*U^η)*(1+height)^J*U^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost (by positivity))
        (Real.rpow_nonneg hUp.le _)
    _≤(C'*U^η)*(1+height)^J*U^E := by
      gcongr
    _=C'*(1+height)^J*U^(E+η) := by rw [Real.rpow_add hUp E η]; ring

end QRH.Record1252270103Source.High
end
#print axioms QRH.Record1252270103Source.High.ordinary_weighted_uniform
