/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Adapted from the saved Record12518109Gain analytic source; immutable originals
and their source-bound verification receipts remain in the prior development. -/
/- Uniform tau quantifiers: the actual weighted and ordinary height degrees
are selected before tau; only the eventual scale threshold depends on tau.
The earlier ordinary face and its six-facet QRH.Record1252270103Source.High.gain are explicit parameters. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.RegularRootSupplierTau
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RegularRootSupplier
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.SourceSlotEnvelope
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ExceptionalSupplier
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.Rescale
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.RootPower
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.RootCompletion
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.OrdinaryRoots

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PositiveRadius.Some
noncomputable section
open OAI OAI.SevenEighths
open Record12518109GainWholeGeometry
open HeckeDetectorZeros HeckePrimeRay
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState CenteredMomentPrimeSlot
open Cycle61Moment Record12518109Natural Record12518109GainActual Record12518109Gain
open Record12518109GainRoot QRH.Record1252270103Source.High.Ordinary Record12518109GainExceptional
open QRH.Record1252270103Source.High
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance positiveRadiusSomeRawFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Literal full regular raw convolution. All source premises are zero bins,
actual zeros and explicit physical/conductor geometry, with no count or envelope premise. -/
theorem actual_regular_raw_max_from_source_bins_uniform_tau
    (ηchar η₀ : Character)
    (capacity lam cap sourceMesh : ℝ)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
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
      ∀(F dsource a mesh height : ℝ)(i : ℕ),i≤I →3/4≤a →a≤7/8 →
      0<F →F/12≤Broot →0≤mesh →mesh≤sourceMesh →
      binWidth≤(2*a-1)/2 →0≤height →
      ∀(rows : Finset NonzeroFrequency)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : NonzeroFrequency→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : NonzeroFrequency→Ideal O),
      (∀h∈rows,rawFrequencyNorm h≤Z^F) →
      (∀h∈rows,¬(wholeRegularDictionary M H hH ηchar η₀).exceptionalCore (sixthFrequencyEquiv.symm h).1) →
      (∀h∈rows,mask h≠0) →(∀h∈rows,((mask h).absNorm:ℝ)≤Z^Bmask) →
      let χ:=fun h=>excluded (naturalRow ηchar h.val h.property).character (mask h);
      ∀hn : ∀h∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ h) j).residue≠1,
      (∀h∈rows,∃j s, LFunction (wholeSourceFamily M H hH η₀ (χ h) j) s=0 ∧
        (s≠1 ∨ (wholeSourceFamily M H hH η₀ (χ h) j).residue≠1) ∧a≤s.re ∧|s.im|≤height) →
      (∀h∈rows,∀hh : h∈rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀h∈rows,∀hh : h∈rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh) ((3*i:ℕ)*Z^τ)) →
      (∀s∈slots,wmin≤w s) →(∀s∈slots,(33/50)≤σ s) →(∀s∈slots,σ s≤(33/50)) →
      (∀s∈slots,|v s|≤height) →(∀h∈rows,|t h|≤height) →
      (∀h∈rows,∀s∈slots,|t h+v s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (∀q : ℝ,F/2≤q →q≤F →
        dmin≤q+δ ∧q+δ≤dmax ∧2≤Z^(q+δ) ∧2<Z^τ ∧
        (∀s∈slots,w s/(q+δ)≤mesh) ∧
        2*Real.pi*((Z^(q+δ))^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height ∧
        (∀s∈slots,rmin≤w s/(q+δ) ∧w s/(q+δ)≤Rwidth) ∧
        (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^(q+δ))^ηslot) →
      dmin≤dsource →dsource≤dmax →2≤Z^dsource →
      (∀s∈slots,rmin≤w s/dsource ∧w s/dsource≤Rwidth) →
      (∀h∈rows,∀s∈slots,∀θ',(twistedFamily M H hH ((χ h).product
        (relativeCharacter M H hH η₀ (θ s)).inverse.inverse) θ').modulus.absNorm≤Z^dsource) →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^dsource)^ηslot →
      let S:=∑s∈slots,w s;
      (∑h∈rows,originalNaturalSlotMaximum M H hH ηchar η₀ W Z slots w σ v θ t mask h)≤
        C*(1+height)^J*Z^(QRH.Record1252270103Source.High.rho (2*a-1)*F+(2*a-1)*S-QRH.Record1252270103Source.High.gain (2*a-1) capacity lam cap S F+
          dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+QRH.Record1252270103Source.High.rho (2*a-1)*δ+2*binWidth*S) := by
  obtain ⟨J,C,hC,hsmall⟩:=QRH.Record1252270103Source.High.actual_regular_root_max_from_source_bins_uniform_tau (Slot:=Slot) M H hH ηchar η₀
    capacity lam cap sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hsource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ
  obtain ⟨J₀,C₀,hC₀,hordinary⟩:=actual_ordinary_weighted_fibers
    (wholeRegularDictionary M H hH ηchar η₀) η hη
  obtain ⟨K,hK,hlift⟩:=QRH.Record1252270103Source.High.full_gain_root_completion
  refine ⟨J+J₀,(C+C₀)*K,by positivity,?_⟩
  intro τ hτ hτzero hτheight
  have hamp:=QRH.Record1252270103Source.High.actual_source_slot_envelope (Slot:=Slot) M H hH W (33/50) (33/50) Rwidth dmin dmax rmin τ εslot e κ ηslot binWidth
    hWs hW hRw hdmin (hdmin.le.trans hdmax) hrmin hτ hεslot he he' hκ hηslot hbin hslotBudget hgap
  filter_upwards [hsmall τ hτ hτzero hτheight,hamp] with Z hs ha
  refine ⟨hs.1,?_⟩
  intro F dsource a mesh height i hi' ha0 ha1 hF hFB hmesh hmeshmax hbin' hheight rows slots w σ v t θ mask
    hnorm hregular hmask hmasknorm χ hn hzero hnext hcurrent hw hlo hhi hv ht hfreq hgeom
    hds hds' hbase hwsource hmod hsourceheight S
  let ν:=2*a-1
  let f:=originalNaturalSlotMaximum M H hH ηchar η₀ W Z slots w σ v θ t mask
  let L:=155*ε+mesh+εm+ν*ζ+η
  let loss:=dmax*L+QRH.Record1252270103Source.High.rho ν*δ+2*binWidth*S
  let Cnow:=(C+C₀)*(1+height)^(J+J₀)*Z^loss
  have hZp : 0<Z:=zero_lt_one.trans hs.1
  have hν0 : 1/2≤ν:=by dsimp [ν];linarith
  have hν1 : ν≤3/4:=by dsimp [ν];linarith
  have hνpos : 0≤ν:=le_trans (by norm_num) hν0
  have hS : 0≤S:=Finset.sum_nonneg (fun s hs=>(hwmin.le.trans (hw s hs)))
  have hL : η≤L:=by dsimp [L];nlinarith only [hε.le,hmesh,hεm.le,mul_nonneg hνpos hζ.le]
  have hL0 : 0≤L:=hη.le.trans hL
  have hρ : 0≤QRH.Record1252270103Source.High.rho ν := by
    rw [QRH.Record1252270103Source.High.rho_eq_original]
    exact le_trans (by norm_num) (Record12518109Gain.rho_lower hν1)
  obtain ⟨hdF,hdF',hbaseF,hT,hwmF,hheightF,hwidthF,hhF⟩:=hgeom F (by linarith) le_rfl
  have hFdmax : F≤dmax:=by linarith
  have hheight1 : 1≤1+height:=by linarith
  have hsmallC : C*(1+height)^J≤(C+C₀)*(1+height)^(J+J₀):=
    mul_le_mul (le_add_of_nonneg_right hC₀.le)
      (pow_le_pow_right₀ hheight1 (Nat.le_add_right J J₀)) (by positivity) (by positivity)
  have hordC : C₀*(1+height)^J₀≤(C+C₀)*(1+height)^(J+J₀):=
    mul_le_mul (le_add_of_nonneg_left hC.le)
      (pow_le_pow_right₀ hheight1 (Nat.le_add_left J₀ J)) (by positivity) (by positivity)
  have hf (h : NonzeroFrequency) (hh : h∈rows) : f h≤Z^(ν*S+2*binWidth*S) := by
    have hb:=(ha.2 dsource hds hds' hbase hT (χ h) η₀ (hn h hh) a i
      hν0 hν1 (hnext h hh hh) slots w σ v (t h) θ hwsource hlo hhi
      (hmod h hh) (hfreq h hh) hsourceheight).2
    convert hb using 1 <;> dsimp only [f,originalNaturalSlotMaximum,χ,ν,S] <;> congr 1 <;> ring
  have hR : ∀h∈rows,rawFrequencyNorm h≤Z^F ∧
      orientedActualZeroRow (wholeRegularDictionary M H hH ηchar η₀).data (fun _=>false) a height h := by
    intro h hh
    obtain ⟨j,s,hz,hpole,hre,him⟩:=hzero h hh
    have hz':=source_zero_to_clean_dictionary M H hH ηchar η₀ (χ h) h (mask h) (hmask h hh)
      (fun _=>rfl) j s (by linarith) hz hpole
    refine ⟨hnorm h hh,j,s,?_⟩
    change LFunction ((momentData (cleanWholeBase M H hH ηchar η₀ j)).character h) s=0 ∧
      (s≠1 ∨ ((momentData (cleanWholeBase M H hH ηchar η₀ j)).character h).residue≠1) ∧a≤s.re ∧|s.im|≤height
    exact ⟨hz'.1,hz'.2,hre,him⟩
  have small (B : NZIdeal) (hB : (B.val.absNorm:ℝ)≤Z^(F/12)) :
      (∑u∈sixthFreeFiber rows B,f (sixthFrequencyEquiv (u,B)))≤
        Cnow*Z^(QRH.Record1252270103Source.High.rho ν*(F-6*Real.logb Z (B.val.absNorm:ℝ))+ν*S-
          QRH.Record1252270103Source.High.gain ν capacity lam cap S (F-6*Real.logb Z (B.val.absNorm:ℝ))) := by
    let q:=F-6*Real.logb Z (B.val.absNorm:ℝ)
    have hBN : 1≤(B.val.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hBp : 0<(B.val.absNorm:ℝ):=zero_lt_one.trans_le hBN
    have hq:=root_window hs.1 hBN hB
    obtain ⟨hd,hd',hbaseq,hTq,hwm,hheightq,hwidth,hhq⟩:=hgeom q hq.1 hq.2
    let core:=sixthFreeFiber rows B
    have hmem (u : FreeRow) (hu : u∈core) : sixthFrequencyEquiv (u,B)∈rows:=sixth_fiber_raw_mem rows B u hu
    have hcore : core.filter (fun u=>¬(wholeRegularDictionary M H hH ηchar η₀).exceptionalCore u)=core := by
      apply Finset.filter_eq_self.mpr
      intro u hu
      simpa only [Equiv.symm_apply_apply] using hregular _ (hmem u hu)
    have hcorescale : Z^q=Z^F/(B.val.absNorm:ℝ)^6 := by
      dsimp [q]
      rw [Real.rpow_sub hZp,show 6*Real.logb Z (B.val.absNorm:ℝ)=Real.logb Z (B.val.absNorm:ℝ)*6 by ring,
        Real.rpow_mul hZp.le,Real.rpow_logb hZp hs.1.ne' hBp,Real.rpow_ofNat]
    have hcoreNorm (u : FreeRow) (hu : u∈core) : rowNorm u≤Z^q := by
      rw [hcorescale,le_div_iff₀ (pow_pos hBp 6)]
      simpa only [raw_sixth_norm] using hnorm _ (hmem u hu)
    have hb:=hs.2 q hd hd' hbaseq hTq core slots w σ v
      (fun u=>t (sixthFrequencyEquiv (u,B))) θ
    rw [hcore] at hb
    have hb':=hb hcoreNorm hw hlo hhi B (fun u=>mask (sixthFrequencyEquiv (u,B)))
      (fun u=>χ (sixthFrequencyEquiv (u,B)))
      (hB.trans (Real.rpow_le_rpow_of_exponent_le hs.1.le hFB))
      (fun u hu=>hmask _ (hmem u hu)) (fun u hu=>hmasknorm _ (hmem u hu))
      (fun _ _ _=>rfl) (fun u hu=>hn _ (hmem u hu)) a mesh height i hi' hν0 hν1
      hmesh hmeshmax hbin' hwm hheight hheightq hv (fun u hu=>ht _ (hmem u hu))
      (fun u hu=>hnext _ (hmem u hu) (hmem u hu))
      (fun u hu=>hcurrent _ (hmem u hu) (hmem u hu)) hwidth
      (fun u hu=>hfreq _ (hmem u hu)) hhq
    have hexp : QRH.Record1252270103Source.High.rho ν*(q+δ)+ν*S-QRH.Record1252270103Source.High.gain ν capacity lam cap S (q+δ)+(q+δ)*L+2*binWidth*S≤
        loss+(QRH.Record1252270103Source.High.rho ν*q+ν*S-QRH.Record1252270103Source.High.gain ν capacity lam cap S q) := by
      have hg:=QRH.Record1252270103Source.High.gain_mono (S:=S) (L:=S) (Q:=q) (F:=q+δ) hν0 hν1 hB0 hB1 hlam hh0 hh1.le le_rfl (by linarith)
      have hl:=mul_le_mul_of_nonneg_right hd' hL0
      dsimp [loss]
      nlinarith only [hg,hl]
    have hbexp:=Real.rpow_le_rpow_of_exponent_le hs.1.le hexp
    have hb'' : (∑u∈core,f (sixthFrequencyEquiv (u,B)))≤
        C*(1+height)^J*Z^(loss+(QRH.Record1252270103Source.High.rho ν*q+ν*S-QRH.Record1252270103Source.High.gain ν capacity lam cap S q)) := by
      exact hb'.trans (mul_le_mul_of_nonneg_left hbexp (by positivity))
    rw [Real.rpow_add hZp] at hb''
    have hfactor:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmallC (Real.rpow_nonneg hZp.le loss))
      (Real.rpow_nonneg hZp.le (QRH.Record1252270103Source.High.rho ν*q+ν*S-QRH.Record1252270103Source.High.gain ν capacity lam cap S q))
    exact hb''.trans (by convert hfactor using 1 <;> ring)
  have large (B : NZIdeal) (_hB : Z^(F/12)<(B.val.absNorm:ℝ)) :
      (∑u∈sixthFreeFiber rows B,f (sixthFrequencyEquiv (u,B)))≤
        Cnow*Z^(QRH.Record1252270103Source.High.rho ν*F+ν*S)*(B.val.absNorm:ℝ)^(-6*QRH.Record1252270103Source.High.rho ν) := by
    have hBp : 0<(B.val.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hBN : 1≤(B.val.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hb:=hordinary (fun _=>false) a height (Z^F) (Z^(ν*S+2*binWidth*S))
      ha0 ha1 hheight (by positivity) (by positivity) rows f hR hf B
    have hrho : unmarkedDensity (2*a-1)=QRH.Record1252270103Source.High.rho ν := by
      change Record12518109Gain.rho ν=QRH.Record1252270103Source.High.rho ν
      exact (QRH.Record1252270103Source.High.rho_eq_original ν).symm
    rw [hrho] at hb
    change _≤(C₀*(1+height)^J₀)*Z^(ν*S+2*binWidth*S)*
      (Z^F/(B.val.absNorm:ℝ)^6)^(QRH.Record1252270103Source.High.rho ν+η) at hb
    have hloss : η*F+2*binWidth*S≤loss := by
      have hηF:=mul_le_mul_of_nonneg_left hFdmax hη.le
      have hηd:=mul_le_mul_of_nonneg_right hL (hdmin.le.trans hdmax)
      dsimp [loss]
      nlinarith only [hηF,hηd,mul_nonneg hρ hδ.le]
    exact QRH.Record1252270103Source.High.ordinary_large_root_power hs.1 hBN hη.le (by positivity) hordC hloss hb
  have hb:=hlift ν S F Z Cnow capacity lam cap hν0 hν1 hB0 hB1 hlam hh0 hh1.le (by linarith only [hF]) hs.1 (by dsimp [Cnow];positivity) rows f small large
  convert hb using 1
  dsimp only [Cnow]
  have hexp : QRH.Record1252270103Source.High.rho ν*F+ν*S-QRH.Record1252270103Source.High.gain ν capacity lam cap S F+loss=
      QRH.Record1252270103Source.High.rho (2*a-1)*F+(2*a-1)*S-QRH.Record1252270103Source.High.gain (2*a-1) capacity lam cap S F+
      dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+QRH.Record1252270103Source.High.rho (2*a-1)*δ+2*binWidth*S := by
    dsimp only [loss,L,ν]
    ring
  rw [←hexp,Real.rpow_add hZp]
  ring

end
end QRH.Record1252270103Source.PositiveRadius.Some

#print axioms QRH.Record1252270103Source.PositiveRadius.Some.actual_regular_raw_max_from_source_bins_uniform_tau
