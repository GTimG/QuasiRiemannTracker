/- Uniform tau quantifiers: the actual weighted and ordinary height degrees
are selected before tau; only the eventual scale threshold depends on tau.
Stage05 predecessor retained as a frozen compatibility receipt. -/
import Submissions.hailey_collet_1252270103.Record12518109Gain.ActualBinSourceTau
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRegularSetup

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState HeckePrimeRay HeckeDetectorZeros
open Cycle61Moment Record12518109Natural Record12518109GainActual Record12518109Gain
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_whole_max_row_sum_from_zero_bins_uniform_tau
    (ηchar η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤M) (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀τ : ℝ,0<τ →τ<dmin/2 →4*τ<dmin*ηw →∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d →d≤dmax →2≤Z^d →2<Z^τ →
      ∀B : NaturalBatch (Slot:=Slot) M H hH (cleanWholeBase M H hH ηchar η₀) (wholeSourceAnchor M H hH η₀) bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →31/50≤2*a-1 →2*a-1≤3/4 →
      0≤mesh →mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm →binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤mesh) →0≤height →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) →(∀u∈B.rows,|B.commonHeight u|≤height) →
      (∀(u : FreeRow)(hu : u∈B.rows),HeckeDetectorZeros.zeroMaximum (B.family u) (B.retained_nonprincipal M H hH u hu)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀(u : FreeRow)(hu : u∈B.rows),a≤HeckeDetectorZeros.zeroMaximum (B.family u) (B.retained_nonprincipal M H hH u hu)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      ∀θ : Slot→RayQuotient.Characters M H,
      (∀u∈B.rows,∀j,B.family u j=
        (naturalRow (cleanWholeBase M H hH ηchar η₀ j) u.val u.property.1).character) →
      (∀u∈B.rows,∀s∈B.slots,B.Q u s=naturalSlot
        (naturalRow (excluded ηchar (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
        (CenteredMomentPrimeSlot.primePool M H 2 ((Z^d)^(B.widths s)))
        (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
          HeckePrimeAnnular.annularWeight W ((Z^d)^(B.widths s)) (B.sigma s)
            (B.commonHeight u+B.relativeHeight s) K) ((Z^d)^(B.widths s))) →
      (∀u∈B.rows,∀s∈B.slots,∀θ',
        (twistedFamily M H hH (relativeRayBase M H hH
          (excluded ηchar (wholeAnchorMask M H hH η₀)) η₀ u.val u.property.1 (θ s)) θ').modulus.absNorm≤Z^d) →
      (∀s∈B.slots,rmin≤B.widths s ∧ B.widths s≤Rwidth) →
      (∀u∈B.rows,∀s∈B.slots,|B.commonHeight u+B.relativeHeight s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^ηslot →
      (∑u∈B.rows,∏s∈B.slots,max 1 (‖B.Q u s‖^2))≤C*(1+height)^J*
        (Z^d)^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_max_row_sum_from_zero_bins_uniform_tau (Slot:=Slot) M H hH
    (cleanWholeBase M H hH ηchar η₀) (wholeSourceAnchor M H hH η₀) bad
    hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I
    hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ hκβ
  refine ⟨J,C,hC,?_⟩
  intro τ hτ hτzero hτheight
  filter_upwards [hcount τ hτ hτzero hτheight] with Z hc
  refine ⟨hc.1,?_⟩
  intro d hd hd' hbase hT B a mesh height i hi' ha ha' hmesh hmeshmax hbin' hwm hh hf hv ht
    hnext hcurrent hmod θ hfamily hQ hmodRay hwidth hfreq hheight
  let ηclean := excluded ηchar (wholeAnchorMask M H hH η₀)
  have hn (u : FreeRow) (hu : u∈B.rows) :
      ∀j,(naturalRow (wholeSourceBase M H hH η₀ ηclean j) u.val u.property.1).character.residue≠1 := by
    intro j
    change (naturalRow (cleanWholeBase M H hH ηchar η₀ j) u.val u.property.1).character.residue≠1
    rw [←hfamily u hu j]
    exact B.retained_nonprincipal M H hH u hu j
  have hfamilyeq (u : FreeRow) (hu : u∈B.rows) :
      (fun j=>(naturalRow (wholeSourceBase M H hH η₀ ηclean j) u.val u.property.1).character)=B.family u :=
    funext (fun j=>(hfamily u hu j).symm)
  let ray := fun (u : FreeRow) (s : Slot)=>relativeRayBase M H hH ηclean η₀ u.val u.property.1 (θ s)
  have hnray (u : FreeRow) (hu : u∈B.rows) (s : Slot) (_hs : s∈B.slots) :
      ∀θ',(twistedFamily M H hH (ray u s) θ').residue≠1 :=
    relative_ray_nonprincipal M H hH ηclean η₀ u.val u.property.1 (hn u hu) (θ s)
  have hnextRay (u : FreeRow) (hu : u∈B.rows) (s : Slot) (hs : s∈B.slots) :
      zeroMaximum (twistedFamily M H hH (ray u s)) (hnray u hu s hs) (3*(i+1:ℕ)*Z^τ)<a+2*e := by
    have hl := relative_ray_maximum_le M H hH ηclean η₀ u.val u.property.1 (hn u hu) (θ s)
      (3*(i+1:ℕ)*Z^τ)
    have hmaxeq : zeroMaximum
        (fun j=>(naturalRow (wholeSourceBase M H hH η₀ ηclean j) u.val u.property.1).character)
        (hn u hu) (3*(i+1:ℕ)*Z^τ)=
        zeroMaximum (B.family u) (B.retained_nonprincipal M H hH u hu) (3*(i+1:ℕ)*Z^τ) := by
      apply zeroMaximum_eq_of_mask
      intro j
      apply coefficient_equality_mask
      intro K
      exact congrArg (fun χ : Character=>idealCoeff χ K) (hfamily u hu j).symm
    exact hl.trans_lt (hmaxeq.symm ▸ hnext u hu)
  have hQray (u : FreeRow) (hu : u∈B.rows) (s : Slot) (hs : s∈B.slots) :
      B.Q u s=rayPrimePolynomial M H (ray u s) W 2 ((Z^d)^(B.widths s))
        (B.sigma s) (B.commonHeight u+B.relativeHeight s) := by
    rw [hQ u hu s hs]
    exact natural_relative_slot_eq_ray M H hH ηclean η₀ u.val u.property.1 (θ s) W 2
      ((Z^d)^(B.widths s)) (B.sigma s) (B.commonHeight u+B.relativeHeight s) (by positivity)
  exact hc.2 d hd hd' hbase hT B (B.retained_nonprincipal M H hH) a mesh height i hi' ha ha'
    hmesh hmeshmax hbin' hwm hh hf hv ht hnext hcurrent hmod ray hnray hQray hnextRay hmodRay
    hwidth hfreq hheight

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
