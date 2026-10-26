/- Repeated marks: fork of Record1252270103Source.High.MaxWeighted (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.MaxWeighted
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainC
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.CountWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainPaymentK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.PaymentWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.WitnessWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Finite.SourceValid2
import Submissions.runbo_li_arvi_face_8746074_20261026.Fork.Record1252270103Source.High.UniformWeighted
import Submissions.runbo_li_arvi_face_8746074_20261026.Fork.Record1252270103Source.High.MaxProducts
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
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
theorem ordinary_max_row_sum_uniform_rm
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
    ∃J : ℕ,∃C : ℝ,0<C ∧∀ᶠU : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      1/2≤2*a-1 →2*a-1≤3/4 →0≤ε →ε≤1/1000 →
      0≤mesh →mesh≤sourceMesh →binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤mesh) →0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) →(∀u∈B.rows,|B.commonHeight u|≤height) →
      (∀t : ℝ,1≤t → t≤3/2 →
        Nonempty (∀u,SupportedWitness (B.family u) U a ε t T allowance i)) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,∏s∈B.slots,max 1 (‖B.Q u s‖^2))≤C*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-QRH.RepeatedMarks.Source.gainC (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := ordinary_weighted_uniform_rm (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 capacity lam cap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η hsource hWs hW hbΦ hrad hbin hη hζ hεm hβ
  refine ⟨J,(2^Fintype.card Slot:ℝ)*C,by positivity,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax hbin' hwm
    hh hf hv ht hwitness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let L := 155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η
  have hsub (selected : Finset Slot) (hs : selected⊆B.slots) :
      (∑u∈B.rows,∏s∈selected,‖B.Q u s‖^2)≤C*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈selected,B.widths s)-QRH.RepeatedMarks.Source.gainC (2*a-1) capacity lam cap (∑s∈selected,B.widths s) 1+L) := by
    let B' := B.restrictSlots M H hH selected hs
    have hsel0 : 0≤∑s∈selected,B.widths s :=
      Finset.sum_nonneg (fun s hsel=>(B.widthsPositive s (hs hsel)).le)
    have witness : ∀bin : BinLabel B'.slots ((2*a-1)/2) binWidth,∀u,
        SupportedWitness (B'.family u) U a ε
          (binCutoff_rm capacity lam cap B'.slots B'.widths a binWidth bin) T allowance i := fun bin=>
      (hwitness _ (binCutoff_rm_bounds B'.slots B'.widths bin ha0 ha hB0 hlam hh0 hh1.le hsel0).1
        (binCutoff_rm_bounds B'.slots B'.widths bin ha0 ha hB0 hlam hh0 hh1.le hsel0).2).some
    have he := hU.2 B' a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax hbin'
      (fun s hsel=>hwm s (hs hsel))
      (Finset.sum_nonneg (fun s hsel=>(B.widthsPositive s (hs hsel)).le)) hh hf
      (fun s hsel=>hv s (hs hsel)) ht witness (fun u hu s hsel=>hQ u hu s (hs hsel))
    have hwidth : (∑s∈selected,B.widths s)≤∑s∈B.slots,B.widths s :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hmem _=>(B.widthsPositive s hmem).le)
    have hbinmul := mul_le_mul_of_nonneg_left hwidth (show 0≤2*binWidth by positivity)
    have hnorm (u : FreeRow) : ‖∏s∈selected,B.Q u s‖^2=∏s∈selected,‖B.Q u s‖^2 := by
      rw [norm_prod,←Finset.prod_pow]
    dsimp only [B',NaturalBatch.restrictSlots] at he
    simp only [hnorm] at he
    exact he.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU.1.le (by dsimp [L,B',NaturalBatch.restrictSlots] at *; linarith))
      (by positivity))
  have he := max_product_of_subproducts_rm B.rows B.slots B.widths (fun u s=>‖B.Q u s‖^2)
    (2*a-1) 1 U (C*(1+height)^J) L capacity lam cap hlam ha0 ha hU.1.le (by positivity)
    (fun s hs=>(B.widthsPositive s hs).le) (fun u hu s hs=>sq_nonneg _) hsub
  have hp : (2^B.slots.card:ℝ)≤2^Fintype.card Slot := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤2) (Finset.card_le_univ B.slots)
  apply he.trans
  convert mul_le_mul_of_nonneg_right hp
    (show 0≤C*(1+height)^J*U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
      QRH.RepeatedMarks.Source.gainC (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+L) by positivity) using 1 <;> dsimp [L] <;> ring

end QRH.Record1252270103Source.High
end
