/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual source labels pulled back through the checked full sixth-root supplier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RegularRawSupplierTau
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.FiniteRowPullback
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.StateRawTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.RawConductor

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbePhysical LocalMoment HeckeDetectorZeros
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot HeckePrimeAnnular Cycle61Moment
open Record12518109GainWholeGeometry Record12518109GainExceptional Record12518109Gain WeightedHigh
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_labeled_regular_raw_max_uniform_tau
    (ηchar η₀ : Character)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
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
      ∀(F dsource a mesh height : ℝ)(i : ℕ),i≤I →81/100≤a →a≤7/8 →
      1/25≤F →F/12≤Broot →0≤mesh →mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm →
      binWidth≤(2*a-1)/2 →0≤height →
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
      Set.InjOn row (↑rows:Set Row)→∀(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
      (∀h∈rows,rawFrequencyNorm (row h)≤Z^F) →
      (∀h∈rows,¬(wholeRegularDictionary M H hH ηchar η₀).exceptionalCore (sixthFrequencyEquiv.symm (row h)).1) →
      (∀h∈rows,mask h≠0) →(∀h∈rows,((mask h).absNorm:ℝ)≤Z^Bmask) →
      (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
        (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K)→
      ∀hn : ∀h∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ h) j).residue≠1,
      (∀h∈rows,∀hh : h∈rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀h∈rows,∀hh : h∈rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh) ((3*i:ℕ)*Z^τ)) →
      (∀s∈slots,wmin≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
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
      F+Bmask+δ≤dsource →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^dsource)^ηslot →
      let S:=∑s∈slots,w s;
      (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
        C*(1+height)^J*Z^(rho (2*a-1)*F+(2*a-1)*S-gain (2*a-1) S F+
          dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+rho (2*a-1)*δ+2*binWidth*S) := by
  obtain ⟨J,C,hC,hraw⟩:=actual_regular_raw_max_from_source_bins_uniform_tau (Slot:=Slot) M H hH ηchar η₀
    setup W lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ hκβ
  refine ⟨J,C,hC,?_⟩
  intro τ hτ hτzero hτheight
  filter_upwards [hraw τ hτ hτzero hτheight,eventually_raw_relative_conductor M H hH ηchar η₀ δ hδ] with Z hr hcond
  refine ⟨hr.1,?_⟩
  intro F dsource a mesh height i hi' ha0 ha1 hF hFB hmesh hmeshmax hbin' hheight
    Row _ rows row hinj slots w σ v t θ mask χ hnorm hregular hmask hmasknorm hcoeff hn
    hnext hcurrent hw hlo hhi hv ht hfreq hgeom hds hds' hbase hwsource hsourcecap hsourceheight S
  have hZp : 0<Z:=zero_lt_one.trans hr.1
  let back:=FiniteRows.pullback rows row
  have hbmem (u : NonzeroFrequency)(hu : u∈rows.image row):back u∈rows:=
    FiniteRows.pullback_mem rows row hu
  have hbrow (u : NonzeroFrequency)(hu : u∈rows.image row):row (back u)=u:=
    FiniteRows.row_pullback rows row hu
  have hback (l : Row)(hl : l∈rows):back (row l)=l:=FiniteRows.pullback_row rows row hinj hl
  let χraw:=fun u : NonzeroFrequency=>excluded (naturalRow ηchar u.val u.property).character (mask (back u))
  have hc (u : NonzeroFrequency)(hu : u∈rows.image row)(K : Ideal O) :
      idealCoeff (χ (back u)) K=idealCoeff (χraw u) K := by
    have hh:=hcoeff _ (hbmem u hu) K
    rw [hbrow u hu] at hh
    exact hh
  have hfamily (u : NonzeroFrequency)(hu : u∈rows.image row) :=
    whole_coefficients_congr M H hH η₀ (χ (back u)) (χraw u) (hc u hu)
  let hnraw : ∀u∈rows.image row,∀j,(wholeSourceFamily M H hH η₀ (χraw u) j).residue≠1:=
    fun u hu j=>nonprincipal_coefficients_congr _ _ (hfamily u hu j) (hn _ (hbmem u hu) j)
  have hmax (u : NonzeroFrequency)(hu : u∈rows.image row)(T : ℝ) :
      zeroMaximum (wholeSourceFamily M H hH η₀ (χ (back u))) (hn _ (hbmem u hu)) T=
        zeroMaximum (wholeSourceFamily M H hH η₀ (χraw u)) (hnraw u hu) T :=
    maximum_coefficients_congr _ _ (hfamily u hu) _ _ T
  have hnext' (u : NonzeroFrequency)(hu : u∈rows.image row)(hu' : u∈rows.image row) :
      zeroMaximum (wholeSourceFamily M H hH η₀ (χraw u)) (hnraw u hu) (3*(i+1:ℕ)*Z^τ)<a+2*e :=
    (hmax u hu _).symm.trans_lt (hnext _ (hbmem u hu) (hbmem u hu))
  have hcurrent' (u : NonzeroFrequency)(hu : u∈rows.image row)(hu' : u∈rows.image row) :
      a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χraw u)) (hnraw u hu) ((3*i:ℕ)*Z^τ) :=
    (hcurrent _ (hbmem u hu) (hbmem u hu)).trans_eq (hmax u hu _)
  have hT : (3*i:ℕ)*Z^τ≤height := by
    have hh:=(hgeom F (by linarith) le_rfl).2.2.2.2.2.1
    have hpos : 0≤2*Real.pi*((Z^(F+δ))^(τ/(2*dmax))) := by positivity
    linarith
  have hzero (u : NonzeroFrequency)(hu : u∈rows.image row) :=
    actual_zero_of_current_maximum (wholeSourceFamily M H hH η₀ (χraw u)) (hnraw u hu)
      a ((3*i:ℕ)*Z^τ) height (by linarith) (hcurrent' u hu hu) hT
  have hmod (u : NonzeroFrequency)(hu : u∈rows.image row)(s : Slot)(hs : s∈slots)(θ') :=
    (hcond.2 F Bmask u (by simpa only [hbrow u hu] using hnorm _ (hbmem u hu))
      (mask (back u)) (hmask _ (hbmem u hu)) (hmasknorm _ (hbmem u hu)) (θ s) θ').trans
      (Real.rpow_le_rpow_of_exponent_le hr.1.le hsourcecap)
  have hb:=hr.2 F dsource a mesh height i hi' ha0 ha1 hF hFB hmesh hmeshmax hbin' hheight
    (rows.image row) slots w σ v (fun u=>t (back u)) θ (fun u=>mask (back u))
    (fun u hu=>by simpa only [hbrow u hu] using hnorm _ (hbmem u hu))
    (fun u hu=>by simpa only [hbrow u hu] using hregular _ (hbmem u hu))
    (fun u hu=>hmask _ (hbmem u hu)) (fun u hu=>hmasknorm _ (hbmem u hu))
    hnraw hzero hnext' hcurrent' hw hlo hhi hv (fun u hu=>ht _ (hbmem u hu))
    (fun u hu s hs=>hfreq _ (hbmem u hu) s hs) hgeom hds hds' hbase hwsource hmod hsourceheight
  convert hb using 1
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only [originalNaturalSlotMaximum]
  simp only [hback l hl]
  rw [←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro s hs
  rw [maximum_square _ (norm_nonneg _)]
  congr 2
  unfold labeledRawSlot
  rw [natural_annular_slot_norm _ _ _ _ (fun K hK=>(Finset.mem_filter.mp hK).2.1.ne_zero)
    _ _ _ _ (Real.rpow_pos_of_pos (by linarith : 0<Z) _)]
  congr 1
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro K _
  rw [hcoeff l hl K]

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_labeled_regular_raw_max_uniform_tau
