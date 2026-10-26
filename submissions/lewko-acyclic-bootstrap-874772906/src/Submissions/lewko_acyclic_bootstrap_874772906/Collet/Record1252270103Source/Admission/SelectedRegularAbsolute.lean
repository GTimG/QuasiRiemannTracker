/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected first family has an all-height second absolute envelope.
The cardinality and weighted-volume estimates are derived from its witnesses. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularAbsoluteData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularAbsolute
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentCanonicalFirst CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondInputCapacitySource CenteredMomentSourceMass
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open High.GlobalPhysical SecondSectorDatum SelectedSecondPhase SelectedHighPaid SelectedRegularSourceData
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def exponent (B L BH Brows Bpool:ℝ):ℝ:=14*B+L+BH+Brows+Bpool+3

theorem selected_family_absolute (N:ℕ)(Cs hi ap bp ell radiusMax B L BH Dlo Brows Bpool:ℝ)
    (hCs:1≤Cs)(hhi:1≤hi)(hap:0<ap)(hbp:0≤bp)(hell:0<ell)(hmax:0≤radiusMax)
    (hB:0≤B)(hL:0≤L)(hBH:0≤BH)(hDlo:0≤Dlo)(hBrows:0≤Brows):
    ∃C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label)
      (p:Profiles ap bp)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ),
      Fintype.card α≤N→(∀i,F.s.M i≤Cs)→(∀i,1≤F.s.hi i)→(∀i,F.s.hi i≤hi)→
      (∀i,1≤F.s.P i)→0≤F.s.b₁→0≤F.s.b₂→1≤F.s.lower→
      F.s.W₁=p.profile 0→F.s.W₂=p.profile 1→
      sourceRadius F.s≤Z^B→1≤volume F.s→volume F.s≤Z^B→|Real.logb Z (volume F.s)|≤B→
      F.seed≠0→
      Function.Injective (fun l=>(FirstFamily.firstLabel F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (F.column l),
        (F.column l).2.1.val))→
      (∀l,F.column l∈firstLiveColumns (High.CoupledFirst.geometryFirstSource F.s F.modifier F.R F.seed
        (Z^F.D) Z F.ξ F.hK F.bin) (fun _=>logAnnulus))→
      (∀l,((F.childSeed l).absNorm:ℝ)≤Z^L)→
      (∀l,Z^(-Dlo)≤F.Hmain l)→(∀l,F.Hmain l≤Z^BH)→
      (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^Brows)→
      (∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^Bpool)→
      (∀l,(P l).Nonempty)→(∀l,0<H0 l)→(∀l,0≤radius l+6*F.amp l)→
      (∀l,radius l+6*F.amp l≤radiusMax)→
      ∀(A1 A2 D K:Label→Ideal O)(cellA mesh loss BD:Label→ℝ)(depth:Label→ℕ),
      (∀l,Pool.FixedCellPoolData (P l) Z (cellA l) ell (mesh l) (loss l) (BD l) Bpool (depth l))→
      (∀l,F.childModifier l=SecondRemainder.correctedModifier (P l) (A1 l) (A2 l) (D l) (K l) (fun _=>1))→
      ∀(keep:Keep F)(take:F.Complete→Prop),
      let d:=fun q:{q:F.Complete // take q}=>datum F keep q.val
      let mod:=fun q:{q:F.Complete // take q}=>F.childModifier q.val.1
      let w:=fun q:{q:F.Complete // take q}=>effectivePhase F W P H0 radius ell keep q.val
      let bound:=C*(p.control {(0,0)})^2*Z^(exponent B L BH Brows Bpool)
      secondAbsoluteBudget d mod w≤bound ∧
        ∀(reflected:Bool)(t u:ℝ),modifiedSecondNormalizedSum reflected d mod w t u≤bound := by
  obtain ⟨Da,hDa,halloc⟩:=FirstAbsoluteBudget.allocation_card_cap N
  obtain ⟨Cl,hCl,hfirst⟩:=SecondAbsoluteEnvelope.eventually_selected_first_card B L hB hL
  obtain ⟨Cb,hCb,hblocks⟩:=SecondAbsoluteEnvelope.eventually_complete_family_card BH Dlo B Brows 1
    hBH hDlo hB hBrows (by norm_num)
  let Ca:=amplitudeConstant N Cs 1 ap Da radiusMax ell
  have hCa:0≤Ca:=by dsimp [Ca,amplitudeConstant];positivity
  let Cw:=Ca/lowerFactor N 1 ap
  have hCw:0≤Cw:=div_nonneg hCa (lowerFactor_pos N 1 ap (by norm_num) hap).le
  let C0:=SecondAbsoluteEnvelope.envelopeConstant N Cs hi bp*(Cb*Cl)*Cw
  have hC0:0≤C0:=mul_nonneg (mul_nonneg (SecondAbsoluteEnvelope.envelopeConstant_nonneg N Cs hi bp)
    (mul_pos hCb hCl).le) hCw
  refine ⟨1+C0,by positivity,?_⟩
  filter_upwards [hfirst,hblocks,eventually_ge_atTop (4:ℝ)] with Z hf hb hZ4
  refine ⟨hf.1,?_⟩
  intro α Label instα instLabel a F p W P H0 radius hN hM hslot0 hslot hP hb1 hb2 hlower
    he1 he2 hsource hVlo hVhi hlog hs0 hinj hlive hseedcap hHlo hHhi hfreq hpool
    hPne hH0 hrad hradcap A1 A2 D K cellA mesh loss BD depth hcell hmodifier keep take
  have hz:0<Z:=zero_lt_one.trans hf.1
  have hs1:∀x,F.s.W₁ x≠0→ap≤x:=by
    intro x hx;rw [he1] at hx;exact (p.support 0 hx).1
  have hs2:∀x,F.s.W₂ x≠0→ap≤x:=by
    intro x hx;rw [he2] at hx;exact (p.support 1 hx).1
  have hchildsource (l:Label):sourceRadius (F.input l)≤Z^B:=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t hslot0 hP hb1 hb2).trans hsource
  have hchildvolume (l:Label):volume (F.input l)≤Z^B:=by
    exact ((ForcedCost.child_volume_ordinary_bound F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t hP).trans
      (div_le_self (volume_pos _).le (ForcedCost.ordinaryNorm_ge_one _ _ _))).trans hVhi
  have hcardfirst:(Fintype.card Label:ℝ)≤Cl*Z^(B+L+1):=
    hf.2 F.s F.modifier F.R F.seed (Z^F.D) F.ξ F.hK F.bin F.seed_sf hs0 F.zero₁ F.zero₂ hsource
      Label F.column hinj hlive hseedcap
  have hcard:=hb.2 F.slots F.input F.childModifier F.mask F.childSeed ballProfile F.Hmain F.Tsec
    F.ξ Cl (B+L+1) F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos hHlo hHhi
    (fun l=>by simpa only [one_mul] using hfreq l) hchildsource hCl.le hcardfirst
  have hac (l:Label):((actualAllocations F.s.pools (F.stage l).common).card:ℝ)^2≤Da*Z^B:=by
    exact halloc F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ B F.hK hN F.seed_sf F.zero₁ F.zero₂ hsource
      F.reflected F.bin (F.column l)
  have ha:=amplitude_cap F N Cs 1 ap Da radiusMax ell B hCs (by norm_num) hap hDa.le hmax hell hB
    hN hM hlower hsource hs1 hs2 hlog W P H0 radius hPne hH0 hrad hradcap hac
  have hn:=amplitude_nonneg F W P H0 radius ell hell hrad
  have hw (q:F.Complete):‖phase F W P H0 radius ell keep q‖≤amplitude F W P H0 radius ell q.1/volume F.s:=
    actual_family_weight_parent F.slots F.input F.childModifier F.mask F.childSeed ballProfile F.Hmain F.Tsec
      (fun _=>Z) (fun _=>F.ξ) (fun _=>volume F.s) (amplitude F W P H0 radius ell)
      (fun _=>volume_pos F.s) hn keep q
  have hweighted (q:F.Complete):
      ‖effectivePhase F W P H0 radius ell keep q‖*(datum F keep q).block.outside*
        (CenteredMomentExceptionalAmplitudePair.volume (datum F keep q).input.toData)^2≤Cw*Z^(8*B+0+BH+B+B):=by
    exact effective_weighted_volume_cap N 1 ap (by norm_num) hap (datum F keep)
      (fun q=>F.childModifier q.1) (phase F W P H0 radius ell keep) ballProfile hN
      (fun _=>hlower) (fun _=>hs1) (fun _=>hs2)
      (fun q=>amplitude F W P H0 radius ell q.1) (fun _=>volume F.s)
      (fun _=>volume_pos F.s) (fun q=>hn q.1) hw Z Ca (8*B) 0 BH B B F.hZ hCa (fun q=>ha q.1)
      (fun _=>by simpa only [neg_zero,Real.rpow_zero] using hVlo)
      (fun q=>hHhi q.1) (datum_common_cap F keep B hchildsource) (fun q=>hchildvolume q.1) q
  have henv:=finite_family_envelope F N Cs hi ap bp ell Bpool Brows
    (B+L+1+3*B+1) (8*B+0+BH+B+B) (Cb*Cl) Cw hCs hhi hap hbp hell hBrows
    (mul_pos hCb hCl).le hCw hZ4 p W P H0 radius hN hM hslot he1 he2 hfreq hpool
    A1 A2 D K cellA mesh loss BD depth hcell hmodifier keep take (hcard.2 take) hweighted
  have hbound:SecondAbsoluteEnvelope.envelopeConstant N Cs hi bp*(Cb*Cl)*Cw*(p.control {(0,0)})^2*
      Z^(Brows+1+Bpool+(B+L+1+3*B+1)+(8*B+0+BH+B+B))≤
      (1+C0)*(p.control {(0,0)})^2*Z^(exponent B L BH Brows Bpool):=by
    have he:Brows+1+Bpool+(B+L+1+3*B+1)+(8*B+0+BH+B+B)=exponent B L BH Brows Bpool:=by
      dsimp [exponent];ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C0≤1+C0) (sq_nonneg _)) (Real.rpow_nonneg hz.le _)
  exact ⟨henv.1.trans hbound,fun reflected t u=>(henv.2 reflected t u).trans hbound⟩
end
end QRH.Record1252270103Source.Admission.SelectedRegularAbsolute
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.selected_family_absolute
