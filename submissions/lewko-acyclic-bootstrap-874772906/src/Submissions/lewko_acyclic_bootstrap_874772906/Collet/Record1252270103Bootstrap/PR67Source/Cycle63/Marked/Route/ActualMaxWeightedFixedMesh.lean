import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualWitnessesFixedMesh
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualUnmarkedUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualWitnesses
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionMaxAmplitude
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Cycle63MarkedAssembly
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource ProbeHighRowFamily
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_max_weighted_from_buffered_maxima_fixedmesh
    (base anchor : Label→ Character) (bad : Label→ Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (_hdmin : 0<dmin) (_hdmax : dmin≤dmax) (_hτ : 0<τ)
    (_hτzero : τ<dmin/2) (_hτheight : 4*τ<dmin*ηw)
    (_hε : 0<ε) (_hεsmall : ε≤1/1000) (_he : 0<e) (_he' : e<1/1000)
    (_hκw : 0<κw) (_hκw' : κw≤1) (_hηw : 0≤ηw)
    (_hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop →
      0≤ mesh → mesh≤Cycle63MarkedPlain.markedPlainMesh (Cycle63.Optimization.plainCapacityCost) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,(∏s∈B.slots,max 1 ‖B.Q u s‖)^2)≤
        C*(1+height)^J*
        (Z^d)^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          Cycle63.Optimization.markedGain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          156*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨Jm,hmarked⟩ := actual_weighted_from_buffered_maxima_fixedmesh
    (Slot:=Slot) base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth η
    hWs hW hbΦ hrad hbin hη hεm hβ hκβ
  obtain ⟨Ju,hunmarked⟩ := actual_unmarked_from_buffered_maxima_uniform (Slot:=Slot) M H hH base setup
    εm η hεm hη hβ
  refine ⟨Ju+Jm,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cm,hCm,hmarked⟩ := hmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cu,hCu,hunmarked⟩ := hunmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  let J := Ju+Jm
  let C := Cu+Cm
  have hC : 0<C := by dsimp [C]; linarith
  refine ⟨(2:ℝ)^Fintype.card Slot*C,by positivity,?_⟩
  filter_upwards [hmarked,hunmarked] with Z hmarked hunmarked
  refine ⟨hmarked.1,?_⟩
  intro d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax' hbin' hwm hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  let U := Z^d
  have hU : 1<U := Real.one_lt_rpow hmarked.1 (hdmin.trans_le hd)
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow]; positivity
  have hCu' : Cu*(1+height)^Ju≤Cnow := by
    apply mul_le_mul (show Cu≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  have hCm' : Cm*(1+height)^Jm≤Cnow := by
    apply mul_le_mul (show Cm≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  let loss := 156*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η
  have hS : 0≤∑s∈B.slots,B.widths s := Finset.sum_nonneg (fun s hs=>(B.widthsPositive s hs).le)
  have hcount : (B.rows.card:ℝ)≤Cnow*U^(VariableSupply.density (2*a-1)+loss) := by
    have he := hunmarked.2 d hd hd' B a height i hiI ha0 ha hh hf hχ hnext hcurrent hmod
    apply he.trans
    apply mul_le_mul hCu' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    dsimp [loss]
    nlinarith [mul_nonneg hbin.le hS]
  have hsub (selected : Finset Slot) (hs : selected⊆B.slots) (hne : selected.Nonempty) :
      (∑u∈B.rows,‖∏s∈selected,B.Q u s‖^2)≤Cnow*
        U^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈selected,B.widths s)-
          Cycle63.Optimization.markedGain (2*a-1) (∑s∈selected,B.widths s) 1+loss) := by
    let Bs := B.restrictSlots M H hH selected hs
    have hL : 0<∑s∈selected,B.widths s := Finset.sum_pos (fun s h=>B.widthsPositive s (hs h)) hne
    have he := hmarked.2 d hd hd' Bs a mesh height i hiI ha0 ha hmesh hmeshmax' hbin'
      (fun s h=>hwm s (hs h)) hL hh hf (fun s h=>hv s (hs h)) hchoice hχ hnext hcurrent hmod
      (fun u hu s h=>hQ u hu s (hs h))
    apply he.trans
    apply mul_le_mul hCm' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    have hsum : (∑s∈selected,B.widths s)≤∑s∈B.slots,B.widths s :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hs _=>(B.widthsPositive s hs).le)
    change _≤_
    have hchosen := VariableSupply.markedGain_one (2*a-1) (∑s∈selected,B.widths s)
    dsimp only [loss,Bs,NaturalBatch.restrictSlots]
    nlinarith [mul_le_mul_of_nonneg_left hsum (show 0≤2*binWidth by positivity)]
  have he := Deletion26.max_weighted_row_sum_of_nonempty B.rows B.slots B.Q B.widths U Cnow
    (VariableSupply.density (2*a-1)) (2*a-1) loss (fun x => Cycle63.Optimization.markedGain (2*a-1) x 1)
    (fun s hs=>(B.widthsPositive s hs).le) hU.le hCnow.le
    (fun _ _ hxy => Cycle63.Optimization.markedGain_deficit_mono (d := 2*a-1) (by linarith [ha0, Cycle63.Arithmetic.q0_bounds.1]) (by linarith [ha, Cycle63.Optimization.markedBinTop_bounds.2]) hxy)
    (Cycle63.Optimization.markedGain_zero (d := 2*a-1) (by linarith [ha, Cycle63.Optimization.markedBinTop_bounds.2])) hcount hsub
  have hN : (2:ℝ)^B.slots.card≤(2:ℝ)^Fintype.card Slot :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ B.slots)
  apply he.trans
  calc
    _≤(2:ℝ)^Fintype.card Slot*Cnow*U^(VariableSupply.density (2*a-1)+(2*a-1)*
        (∑s∈B.slots,B.widths s)-Cycle63.Optimization.markedGain (2*a-1) (∑s∈B.slots,B.widths s) 1+loss) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hCnow.le)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    _=_ := by
      dsimp only [Cnow,U,loss]
      congr 1
      · ring
      · ring_nf

end OAI.SevenEighths.Cycle63ActualWeighted

end
end Record1252270103Bootstrap.PR67
