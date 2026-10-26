/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/ActualWeighted.lean. Original formulas and source attribution retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualSourceFields
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualUnmarkedGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.NaturalLowDensity.WeightedRows
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.Record1252270103Source.NaturalLowDensity.Actual
open OAI OAI.SevenEighths
open OAI.SevenEighths.Record12518109GainActual
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer
open QRH.Record1252270103Source.NaturalLowDensity.Assembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance actualWeightedFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_weighted_row_sum_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm ζ : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      1/2≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm → 0<binWidth → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(Record12518109Gain.rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          Record12518109Gain.gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Ju,Cu,hCu,hU⟩ := Record12518109GainActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  obtain ⟨Jm,Cm,hCm,hM⟩ := actual_marked_source_fields_fixedmesh (Slot:=Slot) M H hH base anchor bad
    hbadM hbad0 hbadTop hbad72 W lo hi bΦ (3/4) εm hWs hW hbΦ hrad
    (by linarith) hεm hβ hκβ
  let C := Cu+Cm
  let J := Ju+Jm
  refine ⟨J+1,192*C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hU,hM] with U hU hM
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hbin hbin'
    hwm hL hh hf hv hchoice witness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow,C]; positivity
  have hCu' : Cu*(1+height)^Ju≤Cnow := by
    apply mul_le_mul (show Cu≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCm' : Cm*(1+height)^Jm≤Cnow := by
    apply mul_le_mul (show Cm≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hcut (bin : BinLabel B.slots ((2*a-1)/2) binWidth) :=
    binCutoff_bounds B.slots B.widths a binWidth ha0 ha hbin hbin'
      (fun s hs=>(B.widthsPositive s hs).le) hL bin
  have hmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : RawFiberMoments
      (adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
        witness bin label left right) B.slots B.family B.Q B.widths U a ε
      (binCutoff B.slots B.widths a binWidth bin) (3/4) εm Cnow height label left right := by
    let F := adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
      witness bin label left right
    have hfields (u : FreeRow) (hu : u∈F) := adaptiveFiber_fields B.rows B.slots B.widths B.Q B.family
      U a ε T allowance binWidth i hbin witness bin label left right u hu
    have hsub : F⊆B.rows := fun u hu=>(hfields u hu).1
    by_cases hne : F.Nonempty
    · let ub : UnmarkedBatch Label U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i := {
        rows := F
        family := B.family
        witness := witness bin
        row_norm := fun u hu=>B.rowNorm u (hsub hu)
        data := D.data
        reverse := fun _=>false
        row_coeff := fun u hu j I=>by
          simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
            FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u (hsub hu) j I }
      have huf : ub.fiberRows label left right=F := by
        apply Finset.filter_eq_self.mpr
        intro u hu
        exact ⟨(hfields u hu).2.1,(hfields u hu).2.2.1,(hfields u hu).2.2.2.1⟩
      have hune : (ub.fiberRows label left right).Nonempty := huf.symm ▸ hne
      have hu := hU.2 a ε (binCutoff B.slots B.widths a binWidth bin) T allowance height i
        (by linarith) hε hεsmall (hcut bin).1 (hcut bin).2 hh hf ub rfl label left right hune
      dsimp only [UnmarkedBatch.fiber,UnmarkedFiber.r,UnmarkedFiber.m] at hu
      rw [huf] at hu
      have hgeom := fiber_lengths F hne B.family U a ε (binCutoff B.slots B.widths a binWidth bin)
        T allowance i hU.1 (witness bin) left right (fun u hu=>(hfields u hu).2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.1)
      dsimp only at hgeom
      have hr0 : 0≤Real.logb U ((2:ℝ)^left.val) := by linarith [hgeom.2.2.2.1,(hcut bin).1]
      have hm0 : 0≤Real.logb U ((2:ℝ)^right.val) := hgeom.2.2.2.2
      have hm1 : Real.logb U ((2:ℝ)^right.val)≤1 := by linarith [hgeom.2.2.1]
      refine ⟨?_,?_,?_,?_⟩
      · exact hu.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCu' (by positivity))
          (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro j k hjk σ hσ freq hfreq
        exact (hu.2 j k hjk σ hσ freq hfreq).trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).1 _ hr0 hcap1 hcap2
          (binCutoff B.slots B.widths a binWidth bin) n hn σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).2 _ hm0 hm1 hcap j k hjk σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change RawFiberMoments F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [he]
      constructor
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity
      · intro j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
  have he := weighted_row_sum B.rows B.slots B.family B.Q B.widths U a ε T allowance mesh binWidth ζ
    εm Cnow height i hU.1 ha0 ha hε (by linarith) hmesh hbin hζ hCnow hh hf B.widthsPositive hwm hL witness hQ hmom
  convert he using 1
  dsimp only [Cnow]
  rw [pow_succ]
  ring


theorem actual_weighted_row_sum_uniform_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth ζ η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      1/2≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        U^(Record12518109Gain.rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          Record12518109Gain.gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm ζ hWs hW hbΦ hrad hζ hεm hβ hκβ
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
  let E := Record12518109Gain.rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
    Record12518109Gain.gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
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

end QRH.Record1252270103Source.NaturalLowDensity.Actual
end
