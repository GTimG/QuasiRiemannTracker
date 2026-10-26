/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/ActualMaxWeighted.lean. Original formulas and source attribution retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.NaturalLowDensity.ActualWeighted
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.NaturalLowDensity.MaxRescale

set_option autoImplicit false
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
open Record12518109GainAssembly Record12518109Gain
open QRH.Record1252270103Source.NaturalLowDensity.Assembly
open QRH.Record1252270103Source.NaturalLowDensity
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance actualMaxWeightedFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def NaturalBatch.restrictSlots {base anchor : Label→Character} {bad : Label→Ideal O}
    {W : ℝ→ℂ} {lo hi U : ℝ} (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (selected : Finset Slot) (hsub : selected⊆B.slots) :
    NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U :=
  { B with
    slots := selected
    widthsPositive := fun s hs=>B.widthsPositive s (hsub hs)
    sigmaLower := fun s hs=>B.sigmaLower s (hsub hs)
    sigmaUpper := fun s hs=>B.sigmaUpper s (hsub hs)
    inversePrime := fun s hs=>B.inversePrime s (hsub hs)
    inverseRatios := fun s hs=>B.inverseRatios s (hsub hs)
    inverseLarge := fun s hs=>B.inverseLarge s (hsub hs)
    inverseIdentity := fun u hu s hs=>B.inverseIdentity u hu s (hsub hs)
    plainIdentity := fun u hu j s hs=>B.plainIdentity u hu j s (hsub hs) }

/-- Every whole-slot subset, including the empty one, is counted by the
actual natural supplier before expanding the product of maxima. -/
theorem actual_max_row_sum_uniform_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth ζ η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀ᶠU : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      1/2≤2*a-1 →2*a-1≤3/4 →0≤ε →ε≤1/1000 →
      0≤mesh →mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm →binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤mesh) →0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) →(∀u∈B.rows,|B.commonHeight u|≤height) →
      (∀selected : Finset Slot,selected⊆B.slots →
        Nonempty (∀u,SupportedWitness (B.family u) U a ε
          (cutoff (2*a-1) (∑s∈selected,B.widths s)) T allowance i)) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,∏s∈B.slots,max 1 (‖B.Q u s‖^2))≤C*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_uniform_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ζ η
    hWs hW hbΦ hrad hbin hη hζ hεm hβ hκβ
  refine ⟨J,(2^Fintype.card Slot:ℝ)*C,by positivity,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax hbin' hwm
    hh hf hv ht hwitness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let L := 155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η
  have hsub (selected : Finset Slot) (hs : selected⊆B.slots) :
      (∑u∈B.rows,∏s∈selected,‖B.Q u s‖^2)≤C*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈selected,B.widths s)-gain (2*a-1) (∑s∈selected,B.widths s) 1+L) := by
    let B' := NaturalBatch.restrictSlots M H hH B selected hs
    obtain ⟨witness⟩ := hwitness selected hs
    have he := hU.2 B' a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax hbin'
      (fun s hsel=>hwm s (hs hsel))
      (Finset.sum_nonneg (fun s hsel=>(B.widthsPositive s (hs hsel)).le)) hh hf
      (fun s hsel=>hv s (hs hsel)) ht (fun _=>witness) (fun u hu s hsel=>hQ u hu s (hs hsel))
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
  have he := max_product_of_subproducts B.rows B.slots B.widths (fun u s=>‖B.Q u s‖^2)
    (2*a-1) 1 U (C*(1+height)^J) L ha0 ha hU.1.le (by positivity)
    (fun s hs=>(B.widthsPositive s hs).le) (fun u hu s hs=>sq_nonneg _) hsub
  have hp : (2^B.slots.card:ℝ)≤2^Fintype.card Slot := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤2) (Finset.card_le_univ B.slots)
  apply he.trans
  convert mul_le_mul_of_nonneg_right hp
    (show 0≤C*(1+height)^J*U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
      gain (2*a-1) (∑s∈B.slots,B.widths s) 1+L) by positivity) using 1 <;> dsimp [L] <;> ring

end QRH.Record1252270103Source.NaturalLowDensity.Actual
end
