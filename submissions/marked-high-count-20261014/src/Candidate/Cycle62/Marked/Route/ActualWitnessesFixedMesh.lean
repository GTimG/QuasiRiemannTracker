import Candidate.Cycle62.Marked.Route.ActualWeightedFixedMesh
import Candidate.Cycle62.Marked.Route.ActualWitnesses
import Candidate.Cycle62.Marked.Route.ActualWeightedCount

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle62ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Cycle62MarkedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

theorem actual_weighted_from_buffered_maxima_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤Cycle62MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        (Z^d)^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          (7/45)*VariableSupply.chosenWidth (∑s∈B.slots,B.widths s)+
          155*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_uniform_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth η hWs hW hbΦ hrad
    hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Z₀,hwitness⟩ := actual_adaptive_supported_witnesses (Label:=Label) (Slot:=Slot)
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hfield
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀≤Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' B a mesh height i hi ha0 ha hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  have hthreshold : U₀≤Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hfield := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    obtain ⟨w⟩ := hwitness Z hZ₀ d hd hd' (fun u:B.rows=>B.family u.val)
      (fun u=>hχ u.val u.property) a binWidth i hi ha0 ha hbin hbin' hnext hcurrent
      (fun u=>hmod u.val u.property) B.slots B.widths
      (fun s hs=>(B.widthsPositive s hs).le) hL
    let urow : B.rows := ⟨u₀,hu₀⟩
    exact hfield.2 (B.retracted urow) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh height i
      ha0 ha hε.le hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
      (B.retracted_witnesses urow w) hQ
  · have hempty : B.rows=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty,Finset.sum_empty]
    have hUp : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    positivity

end OAI.SevenEighths.Cycle62ActualWeighted
#print axioms OAI.SevenEighths.Cycle62ActualWeighted.actual_weighted_from_buffered_maxima_fixedmesh
