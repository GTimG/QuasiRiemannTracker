/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Adapted from the saved Record12518109Gain analytic source; immutable originals
and their source-bound verification receipts remain in the prior development. -/
/- Uniform tau quantifiers: the actual weighted and ordinary height degrees
are selected before tau; only the eventual scale threshold depends on tau.
The earlier ordinary face and its six-facet gain are explicit parameters. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.MaxWeighted
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.LocalWitnesses
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open Record12518109GainActual
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open HeckePrimeRay HeckeDetectorSupportedWitness Record12518109Gain DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Buffered actual zeros supply both supported witnesses and the prime
amplitude envelope. All estimates are proved internally; the live inputs
are literal source identities, conductor bounds and zero maxima. -/
theorem actual_max_row_sum_from_zero_bins_uniform_tau
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M) (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (capacity lam cap sourceMesh : ℝ)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀τ : ℝ,0<τ →τ<dmin/2 →4*τ<dmin*ηw →∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d →d≤dmax →2≤Z^d →2<Z^τ →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) (Z^d),
      ∀hn : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →1/2≤2*a-1 →2*a-1≤3/4 →
      0≤mesh →mesh≤sourceMesh →binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤mesh) →0≤height →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) →(∀u∈B.rows,|B.commonHeight u|≤height) →
      (∀(u : FreeRow)(hu : u∈B.rows),HeckeDetectorZeros.zeroMaximum (B.family u) (hn u hu)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀(u : FreeRow)(hu : u∈B.rows),a≤HeckeDetectorZeros.zeroMaximum (B.family u) (hn u hu)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      ∀rayBase : FreeRow→Slot→Character,
      ∀hray : ∀u∈B.rows,∀s∈B.slots,∀θ,(twistedFamily M H hH (rayBase u s) θ).residue≠1,
      (∀u∈B.rows,∀s∈B.slots,B.Q u s=rayPrimePolynomial M H (rayBase u s) W 2
        ((Z^d)^(B.widths s)) (B.sigma s) (B.commonHeight u+B.relativeHeight s)) →
      (∀(u : FreeRow)(hu : u∈B.rows)(s : Slot)(hs : s∈B.slots),
        HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH (rayBase u s)) (hray u hu s hs)
          (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈B.rows,∀s∈B.slots,∀θ,
        (twistedFamily M H hH (rayBase u s) θ).modulus.absNorm≤Z^d) →
      (∀s∈B.slots,rmin≤B.widths s ∧ B.widths s≤Rwidth) →
      (∀u∈B.rows,∀s∈B.slots,|B.commonHeight u+B.relativeHeight s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^ηslot →
      (∑u∈B.rows,∏s∈B.slots,max 1 (‖B.Q u s‖^2))≤C*(1+height)^J*
        (Z^d)^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-gain (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hcount⟩ := ordinary_max_row_sum_uniform (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 capacity lam cap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η hsource hWs hW hbΦ hrad hbin hη hζ hεm hβ
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hcount
  refine ⟨J,C,hC,?_⟩
  intro τ hτ hτzero hτheight
  obtain ⟨Z₀,hw⟩ := ordinary_local_witness_family (Label:=Label) (Slot:=Slot) M H hH
    capacity lam cap dmin dmax τ ε e κ ηw hB0 hlam hh0 hh1 I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hηw hbudget
  have hamp := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W 1 2 (by norm_num) hWs hW
    Rwidth dmin dmax rmin τ εslot e κ ηslot binWidth (33/50) (33/50) hRw hdmin (hdmin.le.trans hdmax)
    hrmin hτ hεslot he he' hκ hηslot hbin hslotBudget hgap
  have hgrow := (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  filter_upwards [hamp,hgrow,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hamp hgrow hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' hbase hT B hn a mesh height i hi' ha ha' hmesh hmeshmax hbin' hwm hh hf hv ht
    hnext hcurrent hmod rayBase hray hQray hnextRay hmodRay hwidth hfreq hheight
  have hU : U₀≤Z^d := hgrow.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hQ : ∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth) := by
    intro u hu s hs
    rw [hQray u hu s hs]
    have hb := hamp d hd hd' hbase hT (rayBase u s) (hray u hu s hs) a i
      (by linarith) (by linarith) (hnextRay u hu s hs) (B.widths s) (B.sigma s)
      (B.commonHeight u+B.relativeHeight s) (hwidth s hs).1 (hwidth s hs).2
      (B.sigmaLower s hs) (B.sigmaUpper s hs) (hmodRay u hu s hs) (hfreq u hu s hs) hheight
    exact hb.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le
      (Real.one_le_rpow (by linarith) (B.widthsPositive s hs).le) (by linarith [hb.2.1]))
  by_cases hne : B.rows.Nonempty
  · obtain ⟨pick,hpick⟩ := hne
    let B' := B.localizeFamily M H hH pick hpick
    have hwit (selected : Finset Slot) (hsel : selected⊆B'.slots) :
        Nonempty (∀u,SupportedWitness (B'.family u) (Z^d) a ε
          (cutoff (2*a-1) capacity lam cap (∑s∈selected,B'.widths s) 1) (Z^τ) ((Z^d)^(τ/(2*dmax))) i) :=
      hw Z hZ₀ d hd hd' B pick hpick hn a i hi' ha ha' hnext hcurrent hmod _
        (Finset.sum_nonneg (fun s hs=>(B.widthsPositive s (hsel hs)).le))
    exact (hU₀ (Z^d) hU).2 B' a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh height i
      ha ha' hε.le hεsmall hmesh hmeshmax hbin' hwm hh hf hv ht hwit hQ
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end
end QRH.Record1252270103Source.High
