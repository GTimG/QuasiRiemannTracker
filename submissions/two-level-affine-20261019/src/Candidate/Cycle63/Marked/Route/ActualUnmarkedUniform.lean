import Candidate.Cycle63.Marked.Route.ActualWitnesses
import Candidate.Cycle63.Marked.DeletionMaxAmplitude
import Candidate.Cycle63.Arithmetic.Constants

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

omit [Nonempty Label] [Fintype Slot] [DecidableEq Slot] in
theorem actual_unmarked_from_buffered_maxima_uniform
    (base : Label→ Character) (setup : DensityCountingSetup)
    (εm η : ℝ) (hεm : 0<εm) (hη : 0<η)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (_hdmin : 0<dmin) (_hdmax : dmin≤dmax) (_hτ : 0<τ)
    (_hτzero : τ<dmin/2) (_hτheight : 4*τ<dmin*ηw)
    (_hε : 0<ε) (_hεsmall : ε≤1/1000) (_he : 0<e) (_he' : e<1/1000)
    (_hκw : 0<κw) (_hκw' : κw≤1) (_hηw : 0≤ηw)
    (_hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0≤C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀{anchor : Label→ Character}{bad : Label→ Ideal O}{W : ℝ→ℂ}{lo hi : ℝ},
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a height : ℝ,∀i : ℕ,i≤I → Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (B.rows.card:ℝ)≤C*(1+height)^J*(Z^d)^(VariableSupply.density (2*a-1)+156*ε+εm+η) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨J,hJ⟩ := setup.actual_batch_count (Label := Label) εm η hεm hη hβ
  obtain ⟨C,hC,hcount⟩ := hJ D
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Z₀,hw⟩ := unmarked_batch_from_actual_maxima dmin dmax τ ε e κw ηw I
    hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hcount
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀≤Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' anchor bad W lo hi B a height i hiI ha0 ha hh hf hχ hnext hcurrent hmod
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hthreshold : U₀≤Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hc := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · have hcut := unmarkedCutoff_bounds (show 0≤2*a-1 by linarith) (show 2*a-1≤5/6 by linarith)
    have hcoeff : ∀u : B.rows,∀j I,idealCoeff (B.family u.val j) I=
        if (fun _:Label=>false) j then starRingEnd ℂ
          (idealCoeff ((D.data j).character ⟨u.val.val,u.val.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val.val,u.val.property.1⟩) I := by
      intro u j I
      simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
        FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u.val u.property j I
    obtain ⟨batch,hrows,hdata,hrev,hfamily⟩ := hw Z hZ₀ d hd hd' B.rows hne
      (fun u=>B.family u.val) (fun u=>hχ u.val u.property) D.data (fun _=>false) B.rowNorm hcoeff
      a i hiI (by linarith) (by linarith) hnext hcurrent (fun u=>hmod u.val u.property)
      (unmarkedCutoff (2*a-1)) hcut.1 hcut.2
    rw [←hrows]
    exact hc.2 a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) height i (by linarith) (by linarith)
      hε.le hεsmall hh hf batch hdata
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (zero_lt_one.trans hc.1).le _)

end OAI.SevenEighths.Cycle63ActualWeighted
