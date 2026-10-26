import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeActualBin
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeConductor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeRootMaxima

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState CenteredMomentPrimeSlot
open Cycle61Moment Record12518109Natural Record12518109GainActual Record12518109Gain
open Record12518109GainWholeRaw Record12518109GainDeletion DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The regular small-root supplier for literal source rows. Retention,
conductor bounds, actual witnesses, amplitude bounds, root and hole
comparison are proved internally. The live source premise is its genuine
whole-family buffered zero bin. -/
theorem actual_regular_root_max_from_source_bins
    (ηchar η₀ : Character)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth τ ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hτ : 0<τ) (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀q : ℝ,dmin≤q+δ →q+δ≤dmax →2≤Z^(q+δ) →2<Z^τ →
      ∀(rows₀ : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      let rows:=rows₀.filter (fun u=>¬(wholeRegularDictionary M H hH ηchar η₀).exceptionalCore u);
      (∀u∈rows,rowNorm u≤Z^q) →
      (∀s∈slots,wmin≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      ∀(B : NZIdeal)(R : FreeRow→Ideal O)(χ : FreeRow→Character),
      (B.val.absNorm:ℝ)≤Z^Broot →(∀u∈rows,R u≠0) →(∀u∈rows,((R u).absNorm:ℝ)≤Z^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=idealCoeff (excluded
        (naturalRow ηchar (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property).character (R u)) K) →
      ∀hn : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →31/50≤2*a-1 →2*a-1≤3/4 →
      0≤mesh →mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm →binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s/(q+δ)≤mesh) →0≤height →
      2*Real.pi*((Z^(q+δ))^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈slots,|v s|≤height) →(∀u∈rows,|t u|≤height) →
      (∀(u : FreeRow)(hu : u∈rows),HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀ (χ u)) (hn u hu) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀(u : FreeRow)(hu : u∈rows),a≤HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀ (χ u)) (hn u hu) ((3*i:ℕ)*Z^τ)) →
      (∀s∈slots,rmin≤w s/(q+δ) ∧ w s/(q+δ)≤Rwidth) →
      (∀u∈rows,∀s∈slots,|t u+v s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^(q+δ))^ηslot →
      let rawQ:=fun u s=>naturalSlot (χ u) (primePool M H 2 (Z^(w s)))
        (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (t u+v s) K) (Z^(w s));
      (∑u∈rows,∏s∈slots,max 1 (‖rawQ u s‖^2))≤
        C*(1+height)^J*Z^(rho (2*a-1)*(q+δ)+(2*a-1)*(∑s∈slots,w s)-
          gain (2*a-1) (∑s∈slots,w s) (q+δ)+
          (q+δ)*(155*ε+mesh+εm+(2*a-1)*ζ+η)+2*binWidth*(∑s∈slots,w s)) := by
  let bad:=wholeRegularBad M H hH ηchar η₀
  have hbadM (j : WholeSourceIndex M H) : bad j≤M := inf_le_left.trans inf_le_left
  have hbad0 (j : WholeSourceIndex M H) := internalQ_ne_zero (bad j)
    (wholeRegularBad_nonzero M H hH ηchar η₀ j) (wholeSourceAnchor M H hH η₀ j)
  have hbadTop (j : WholeSourceIndex M H) := internalQ_ne_top (bad j)
    (wholeRegularBad_proper M H hH ηchar η₀ j) (wholeSourceAnchor M H hH η₀ j)
  have hbad72 (j : WholeSourceIndex M H) : internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤Ideal.span {(72:O)} :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  obtain ⟨J,C,hC,hcount⟩ := actual_whole_max_row_sum_from_zero_bins (Slot:=Slot) M H hH ηchar η₀ bad
    hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ζ η dmin dmax rmin Rwidth τ ε e κ ηw εslot ηslot I
    hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hτ hτzero hτheight
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ hκβ
  let Kdel : ℝ:=1+∑j : WholeSourceIndex M H,
    ((deletedBase (momentData (cleanWholeBase M H hH ηchar η₀ j))).modulus.absNorm:ℝ)
  have hdel (j : WholeSourceIndex M H) :
      ((deletedBase (momentData (cleanWholeBase M H hH ηchar η₀ j))).modulus.absNorm:ℝ)<Kdel := by
    have hh:=Finset.single_le_sum
      (f:=fun k : WholeSourceIndex M H=>
        ((deletedBase (momentData (cleanWholeBase M H hH ηchar η₀ k))).modulus.absNorm:ℝ))
      (fun k (_ : k∈Finset.univ)=>Nat.cast_nonneg _) (Finset.mem_univ j)
    dsimp [Kdel];linarith
  refine ⟨J,(4:ℝ)^Fintype.card Slot*C,by positivity,?_⟩
  filter_upwards [hcount,eventually_whole_core_conductor M H hH ηchar η₀ δ hδ,
    eventually_whole_original_raw_max_comparison (Slot:=Slot) M H hH ηchar η₀ bad W lo hi Bmask Broot wmin
      hWs hW hBmask hBroot hwmin,
    (tendsto_rpow_atTop hwmin).eventually (eventually_ge_atTop Kdel)] with Z hc hcond hraw hdelZ
  refine ⟨hc.1,?_⟩
  intro q hd hd' hbase hT rows₀ slots w σ v t θ rows hrow hw hσlo hσhi B R χ hBN hR hRN
    hcoeff hn a mesh height i hi' ha ha' hmesh hmeshmax hbin' hwm hh hf hv ht hnext hcurrent hwidth hfreq hheight rawQ
  have hdpos : 0<q+δ := hdmin.trans_le hd
  have hrow' (u : FreeRow) (hu : u∈rows) : ((Ideal.span {u.val}).absNorm:ℝ)≤Z^(q+δ) :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith))
  have hnorm (u : FreeRow) (hu : u∈rows) : ‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤Z^(q+δ) := by
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrow' u hu
  have hkeep:=whole_regular_retained M H hH ηchar η₀ rows₀
  have hlarge (s : Slot) (hs : s∈slots) (j : WholeSourceIndex M H) :
      ((deletedBase (momentData (cleanWholeBase M H hH ηchar η₀ j))).modulus.absNorm:ℝ)<
        (Z^(q+δ))^(w s/(q+δ)) := by
    rw [prime_scale_rescale Z (q+δ) (w s) (by linarith) hdpos]
    exact (hdel j).trans_le (hdelZ.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (hw s hs)))
  let batch:=wholeNaturalBatch M H hH ηchar η₀ bad W lo hi (Z^(q+δ)) hWs rows slots
    (fun s=>w s/(q+δ)) σ v t θ (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hdpos)
    hσlo hσhi hrow' hnorm hkeep hlarge
  have hmaxeq (u : FreeRow) (hu : u∈rows) (T : ℝ) :
      HeckeDetectorZeros.zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hn u hu) T=
      HeckeDetectorZeros.zeroMaximum (batch.family u) (batch.retained_nonprincipal M H hH u hu) T :=
    source_root_maximum_eq_clean M H hH ηchar η₀ (χ u) u B (R u) (hR u hu) (hcoeff u hu)
      (hn u hu) (batch.retained_nonprincipal M H hH u hu) T
  have hnextBatch (u : FreeRow) (hu : u∈rows) :
      HeckeDetectorZeros.zeroMaximum (batch.family u) (batch.retained_nonprincipal M H hH u hu)
        (3*(i+1:ℕ)*Z^τ)<a+2*e :=
    (hmaxeq u hu (3*(i+1:ℕ)*Z^τ)).symm.trans_lt (hnext u hu)
  have hcurrentBatch (u : FreeRow) (hu : u∈rows) :
      a≤HeckeDetectorZeros.zeroMaximum (batch.family u) (batch.retained_nonprincipal M H hH u hu)
        ((3*i:ℕ)*Z^τ) :=
    (hcurrent u hu).trans_eq (hmaxeq u hu ((3*i:ℕ)*Z^τ))
  have hbatch := hc.2 (q+δ) hd hd' hbase hT batch a mesh height i hi' ha ha' hmesh hmeshmax hbin'
    hwm hh hf hv ht
    hnextBatch hcurrentBatch
    (fun u hu j=>(hcond.2 q u (hrow u hu)).1 j)
    θ (fun _ _ _=>rfl) (fun _ _ _ _=>rfl)
    (fun u hu s hs θ'=>(hcond.2 q u (hrow u hu)).2 (θ s) θ') hwidth hfreq hheight
  have hcomparison := hraw.2 (q+δ) hdpos rows slots w σ v t θ hw hσlo hσhi
    hrow' hnorm hkeep hlarge B R hBN hR hRN
  have hrawEq (u : FreeRow) (hu : u∈rows) (s : Slot) : rawQ u s=
      naturalSlot (excluded (naturalRow ηchar (sixthFrequencyEquiv (u,B)).val
        (sixthFrequencyEquiv (u,B)).property).character (R u)) (primePool M H 2 (Z^(w s)))
        (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (t u+v s) K) (Z^(w s)) :=
    naturalSlot_congr_ideal _ _ (hcoeff u hu) _ _ _
  have he : (∑u∈rows,∏s∈slots,max 1 (‖rawQ u s‖^2))≤
      (4:ℝ)^slots.card*(∑u∈rows,∏s∈slots,max 1 (‖batch.Q u s‖^2)) := by
    convert hcomparison using 1
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.prod_congr rfl
    intro s hs
    rw [hrawEq u hu s]
  have hcard : (4:ℝ)^slots.card≤4^Fintype.card Slot :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ slots)
  have hsum : (∑s∈slots,w s/(q+δ))=(∑s∈slots,w s)/(q+δ) := by rw [Finset.sum_div]
  have hpower : (Z^(q+δ))^(rho (2*a-1)+(2*a-1)*(∑s∈slots,w s/(q+δ))-
      gain (2*a-1) (∑s∈slots,w s/(q+δ)) 1+
      155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈slots,w s/(q+δ))+η)=
      Z^(rho (2*a-1)*(q+δ)+(2*a-1)*(∑s∈slots,w s)-gain (2*a-1) (∑s∈slots,w s) (q+δ)+
        (q+δ)*(155*ε+mesh+εm+(2*a-1)*ζ+η)+2*binWidth*(∑s∈slots,w s)) := by
    rw [hsum,←Real.rpow_mul (show 0≤Z by linarith)]
    congr 1
    rw [←gain_rescale (2*a-1) (∑s∈slots,w s) (q+δ) hdpos]
    field_simp [hdpos.ne']
    <;> ring
  dsimp only [batch,wholeNaturalBatch] at hbatch
  rw [hpower] at hbatch
  dsimp only [batch,wholeNaturalBatch] at he
  exact he.trans (by
    have hh:=mul_le_mul hcard hbatch (by positivity) (by positivity : 0≤(4:ℝ)^Fintype.card Slot)
    convert hh using 1 <;> ring)

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
