/- Repeated marks: the complete actual weighted same-zero row count from the earlier ordinary
source, with repeated marks and per-class cutoffs. Fork of Collet's
`ordinary_actual_weighted_row_sum` (High/ActualWeighted.lean, Apache-2.0). The unmarked gates and
the ordinary marked fields are Collet's; the replicated inverse field is
`replicated_inverse_source_field`. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.WeightedK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.SourceFieldsK
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.ActualWeighted
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.RepeatedMarks.Source
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
open QRH.Record1252270103Source.High
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem ordinary_actual_weighted_row_sum_K (copies : ℕ) (hcopies : 1 ≤ copies)
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (capacity lam cap sourceMesh : ℝ)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ εm ζ : ℝ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      1/2≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤sourceMesh → 0<binWidth → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε
          (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          gainRep copies (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Ju,Cu,hCu,hU⟩ := Record12518109GainActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  obtain ⟨Jm,Cm,hCm,hM⟩ := ordinary_marked_source_fields_fixedmesh (Slot:=Slot) M H hH base anchor bad
    hbadM hbad0 hbadTop hbad72 capacity lam cap sourceMesh (by linarith) W bΦ εm hsource hWs hW hbΦ hrad hεm
  obtain ⟨Jr,Cr,hCr,hR⟩ := replicated_inverse_source_field (Slot:=Slot) M H hH copies base anchor bad
    W εm hWs hW hεm
  let C := Cu+Cm+Cr
  let J := Ju+Jm+Jr
  refine ⟨J+1,192*C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hU,hM,hR] with U hU hM hR
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hbin hbin'
    hwm hL hh hf hv hchoice witness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow,C]; positivity
  have hpowJ (k : ℕ) (hk : k ≤ J) : (1+height)^k ≤ (1+height)^J :=
    pow_le_pow_right₀ (by linarith : 1≤1+height) hk
  have hCu' : Cu*(1+height)^Ju≤Cnow := by
    apply mul_le_mul (show Cu≤C by dsimp [C]; linarith) (hpowJ Ju (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCm' : Cm*(1+height)^Jm≤Cnow := by
    apply mul_le_mul (show Cm≤C by dsimp [C]; linarith) (hpowJ Jm (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCr' : Cr*(1+height)^Jr≤Cnow := by
    apply mul_le_mul (show Cr≤C by dsimp [C]; linarith) (hpowJ Jr (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hcut (bin : BinLabel B.slots ((2*a-1)/2) binWidth) :
      1≤binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin ∧
      binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin≤3/2 := by
    have hh := classCutoff_bounds B.slots B.widths (binValue B.slots ((2*a-1)/2) binWidth bin)
      copies ha0 ha hB0 hlam hh0 hh1.le hL
    exact ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : FiberMomentsK
      (adaptiveFiberK copies capacity lam cap B.rows B.slots B.widths B.Q B.family U a ε T allowance
        binWidth i hbin witness bin label left right) B.slots copies B.family B.Q B.widths U a ε
      (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin) capacity lam cap εm Cnow
        height label left right := by
    let F := adaptiveFiberK copies capacity lam cap B.rows B.slots B.widths B.Q B.family U a ε T
      allowance binWidth i hbin witness bin label left right
    have hfields (u : FreeRow) (hu : u∈F) := adaptiveFiberK_fields copies capacity lam cap B.rows
      B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin witness bin label left right u hu
    have hsub : F⊆B.rows := fun u hu=>(hfields u hu).1
    by_cases hne : F.Nonempty
    · let ub : UnmarkedBatch Label U a ε (binCutoffK copies capacity lam cap B.slots B.widths a
          binWidth bin) T allowance i := {
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
      have hu := hU.2 a ε (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin) T
        allowance height i (by linarith) hε hεsmall (hcut bin).1 (hcut bin).2 hh hf ub rfl label
        left right hune
      dsimp only [UnmarkedBatch.fiber,UnmarkedFiber.r,UnmarkedFiber.m] at hu
      rw [huf] at hu
      have hgeom := fiber_lengths F hne B.family U a ε
        (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin)
        T allowance i hU.1 (witness bin) left right (fun u hu=>(hfields u hu).2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.1)
      dsimp only at hgeom
      have hr0 : 0≤Real.logb U ((2:ℝ)^left.val) := by linarith [hgeom.2.2.2.1,(hcut bin).1]
      have hm0 : 0≤Real.logb U ((2:ℝ)^right.val) := hgeom.2.2.2.2
      have hm1 : Real.logb U ((2:ℝ)^right.val)≤1 := by linarith [hgeom.2.2.1]
      refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
      · exact hu.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCu' (by positivity))
          (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro j k hjk σ hσ freq hfreq
        exact (hu.2 j k hjk σ hσ freq hfreq).trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).1 _ hr0 hcap1 hcap2
          (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin) n hn σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hwidth hcap j k hjk σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).2 _ hm0 hm1 hwidth hcap j k hjk σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        have he := hR.2 B height hh hv hchoice F hsub label selected hselected _ hr0 hcap1 hcap2
          (binCutoffK copies capacity lam cap B.slots B.widths a binWidth bin) n hn σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCr' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change FiberMomentsK F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [he]
      refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity
      · intro j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hwidth hcap j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
  have he := weighted_row_sum_K copies capacity lam cap hcopies hB0 hB1 hlam hh0 hh1 B.rows B.slots
    B.family B.Q B.widths U a ε T allowance mesh binWidth ζ
    εm Cnow height i hU.1 ha0 ha hε (by linarith) hmesh hbin hζ hCnow hh hf B.widthsPositive hwm
    hL witness hQ hmom
  convert he using 1
  dsimp only [Cnow]
  rw [pow_succ]
  ring

end QRH.RepeatedMarks.Source
end
