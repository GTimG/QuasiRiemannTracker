/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The canonical initial family applies the genuine earlier LOW source at both
positive corners, with one common selected state and control package. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularLowPointData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open CenteredMomentSourceMass CenteredMomentEnergyBands CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61InitialMass LocalMoment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentPrimeSlot CenteredMomentEnergyState Cycle61HighGeometry
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open Record12518109Raw Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph SelectedRegularSourceData SelectedHighCofactorFamily High.GlobalPhysical
open CenteredMomentHeckeSlots CenteredMomentSecondInputCapacitySource
open RayFourExpansion CenteredMomentCommonMaskExpansion Record1252270103Second
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass SelectedSecondPhase
local notation "O"=>HeckeFamily.O
local instance selectedLowPointMainDecEq {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedLowPointMainFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def lowExponent (n:Source)(θ εslot:ℝ)(N:ℕ):ℝ:=
  -8*(n.allowance:ℝ)+θ+θ+6*(θ/100)+θ+θ+(θ/100)*(6+θ)+
    2*εslot*100*N+θ+θ+2*θ+10*(θ/100)+θ

theorem eventually_initial_low_point (Kgraph:ℚ)(n low:Source)(b θloss mesh ξ width εslot τsource:ℝ)
    (sc:Scalar Kgraph n low b θloss mesh ξ width)
    {α:Type}[Fintype α](N:ℕ)(hN:Fintype.card α≤N)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(Q:Ideal O)(hQM:Q≤rayM)(R₀:Ideal O)(hR₀:R₀≠0)
    (Cslot Cpref:ℝ)(JL:ℕ)(SL:Finset (ℕ×ℕ))(CL:ℝ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    RegularLowAt (α:=α) rayM H hH n low b θloss mesh εslot τsource N (fun _=>initialSlotBound W hW hsW)
      W ηanchor η₀ Q hQM Cslot Cpref JL SL CL Z→
    ∀(i:Initial (α:=α) rayM H Z)(r:ℝ),InitialGeometry i n b width mesh r→
    ∀(seed Am₁ Am₂ Dm Km:Ideal O)(Fm:Ideal O→ℂ)(hs:Squarefree seed)
      (bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),
    let a:=i.anchor hH W hW hsW hZ ηanchor η₀ R₀ seed hR₀ hs Am₁ Am₂ Dm Km Fm ξ θloss bin reflected Q
    ∀{Label:Type}[Fintype Label](F:Family a Label),
      (∀l,F.amp l=sourceAReal n low b)→
    ∀{Row:Type}(rows:Finset Row)(G:Selected F Row rows second),Function.Injective G.key→
      (G.L.absNorm:ℝ)≤Z^(4:ℝ)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
        (3*sourceAReal n low b) θloss 2 N (F.first (G.row u).val.1))→
    ∀(P S A:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ),
      Pool.FixedCellPoolData P Z (sourceAReal n low b) (sourceAReal n low b/2) poolMesh θloss BD Bsource depth→
      S⊆P→A⊆S→S.card≤depth→(depth:ℝ)*sourceAReal n low b<5→
      GoodPair (newtonDivisorPair S A)→
    ∀T:Finset α,(∀u,T⊆(G.sel u).full)→
      (∀j∈T,∀I∈primePool rayM H (2:ℝ) (Z^(i.w j)),IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))→
    ∀sh:Shared G rayM H hH η₀ Q hQM S A (highBuffer 1 1 εslot (θloss/16)) τsource,
    ∀(t height:ℝ),0≤height→(∀j∈T,|i.freq j|≤height)→(∀j∈T,|t+i.freq j|≤Z^τsource)→
    ∀(Wa:𝓢(ℝ,ℂ))(H0 mainRadius:Label→ℝ),(∀l,0<H0 l)→
      (∀l,0≤mainRadius l+6*sourceAReal n low b ∧ mainRadius l+6*sourceAReal n low b≤32)→
    ∀corner:Bool,
      (∑l∈Finset.univ.filter (fun l:(Finset.univ:Finset rows)=>
        bufferValue (highBuffer 1 1 εslot (θloss/16)) (sh.select l.val)<((n.q:ℝ)+1)/2),
        ‖regularSelectedCorner G S A T t corner l.val‖^2*
          selectedPaidWeight (G.sel l.val) (residualWeight F.datum
            (regularFamilyWeight F Wa (fun _=>P) H0 mainRadius (sourceAReal n low b/2)) (G.row l.val).val))≤
      CL*(i.p.control SL)^2*(1+|t|+height)^JL*
        (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
          forcedProfileCost F.s*(max 1 (forcedProfileCost F.s))^2)*Cslot^N*Z^(lowExponent n θloss εslot N):=by
  have hnB:(n.B:ℝ)≤1:=by exact_mod_cast sc.parent.2.1
  have hnL:1≤(n.L:ℝ):=by exact_mod_cast sc.parent.2.2.1.le
  have hncap:(n.cap:ℝ)≤1:=by exact_mod_cast sc.parent.2.2.2.2.le
  filter_upwards [InitialTruncated.eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hnB hnL hncap,
    SelectedRegularCanonicalGeometry.eventually_canonical_selected_geometry ηanchor R₀ hR₀,
    SelectedRegularCanonicalGeometry.eventually_mask_ten ηanchor R₀ hR₀,
    eventually_selected_frequency θloss N sc.loss_pos,
    eventually_low_scalar Kgraph n low b θloss ξ sc.geometry sc.parent sc.low_parent sc.allowance_pos
      sc.loss_pos sc.loss_small sc.loss_step sc.xi_pos (sc.xi_loss.trans sc.loss_step) N]
    with Z hcaps hgeo hmaskZ hfreq hscalar
  refine ⟨hcaps.1,?_⟩
  intro hZ hAt i r hi seed Am₁ Am₂ Dm Km Fm hs bin reflected second a Label instLabel F hamp Row rows G
    hinj hLcap hT P S A poolMesh BD Bsource depth hp hS hA hdepth hcost hgood T hfull havoid sh t height
    hheight hfh hth Wa H0 mainRadius hH0 hrad corner
  have hy:1≤ i.Y₂:=by rw [hi.reference];exact Real.one_le_rpow hZ.le hi.r_nonneg
  have hc:=hcaps.2 hZ rayM H hH W hW hsW ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hi.widths_nonneg hi.face hy
    (by rw [hi.reference];exact hi.long_left) (by rw [hi.reference];exact hi.long_right)
  have hs2:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s≤Z^(2:ℝ):=hc.2.1
  have hs6:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s≤Z^(6:ℝ):=
    hs2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hnorm:=selected_common_norm_caps F rows second G hs2
    (fun _=>by change 1≤(2:ℝ);norm_num)
    (fun j=>Real.one_le_rpow hZ.le (hi.widths_nonneg j)) (by change 0≤(9/4:ℝ);norm_num) (by change 0≤(9/4:ℝ);norm_num)
  have hpoolne:∀q∈P,q≠0:=fun q hq=>(hp.prime q hq).ne_zero
  have hcorn(u:rows):SelectedRegularCanonicalGeometry.CornerBounds (G.sel u).finalInput S A Z ∧
      SelectedRegularCanonicalGeometry.corner₁ (G.sel u).finalInput S A true*SelectedRegularCanonicalGeometry.corner₂ (G.sel u).finalInput S A true=
        SelectedRegularCanonicalGeometry.corner₁ (G.sel u).finalInput S A false*SelectedRegularCanonicalGeometry.corner₂ (G.sel u).finalInput S A false ∧
      (geometryRawFixedMask F.s R₀*G.L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)≠0 ∧
      (((geometryRawFixedMask F.s R₀*G.L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)).absNorm:ℝ)≤Z^(10:ℝ):=
    hgeo.2 rayM H hH W hW hsW η₀ i.θ i.w i.freq i.t₀ i.p i.X₁ i.X₂ i.Y₁ i.Y₂
      i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) r hnB hnL hi.widths_nonneg
      hi.face hi.r_nonneg hi.long_left hi.long_right hi.reference hZ reflected second
      (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D R₀ (G.sel u) G.L G.L_ne hLcap
      P S A depth (sourceAReal n low b) hS hA hdepth sc.geometry.a_pos.le hcost hpoolne hp.norm_upper
  have hm:fixedBadMask*idealGenerator R₀≠0:=mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R₀ hR₀)
  have hml:goodLambda∣fixedBadMask*idealGenerator R₀:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
  have hm2:(2:O)∣fixedBadMask*idealGenerator R₀:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
  have hlabel:=hfreq.2 a F rows second G n low b Am₁ Am₂ Dm Km Fm rfl rfl rfl sc.xi_loss hT
  have plain:length Z F.s.X₁+length Z F.s.X₂≤PhysicalLowReserve.plainBudget n b width:=by
    have hf:length Z i.X₁+length Z i.X₂+(n.L:ℝ)*(∑j,i.w j)≤(n.B:ℝ):=by
      simpa only [globalFace,mul_one] using hi.face.2.2.2.2.2.2
    dsimp [PhysicalLowReserve.plainBudget,sourceTReal]
    change length Z i.X₁+length Z i.X₂≤_
    nlinarith [mul_le_mul_of_nonneg_left hi.cell_lower (zero_le_one.trans hnL)]
  have hslot(j:α)(I:Ideal O)(hI:I∈primePool rayM H (2:ℝ) (Z^(i.w j))):
      ‖idealCoeff (relativeCharacter rayM H hH η₀ (i.θ j)) I*
        HeckePrimeAnnular.annularWeight W (Z^(i.w j)) (33/50) (i.freq j) I‖≤ initialSlotBound W hW hsW:=
    F.s.coefficient_bound j I hI
  have hslotcap(j:α)(I:Ideal O)(hI:I∈primePool rayM H (2:ℝ) (Z^(i.w j)))
      (hne:idealCoeff (relativeCharacter rayM H hH η₀ (i.θ j)) I*
        HeckePrimeAnnular.annularWeight W (Z^(i.w j)) (33/50) (i.freq j) I≠0):
      (I.absNorm:ℝ)≤2*Z^(i.w j):=by
    have hv:=F.s.support j (mul_ne_zero_iff.mp hne).2
    have hP:0<F.s.P j:=F.s.P_pos j
    exact (div_le_iff₀ hP).mp hv.2
  let labels : Finset rows := Finset.univ
  let omega : labels→ℝ := fun l=>residualWeight F.datum
    (regularFamilyWeight F Wa (fun _=>P) H0 mainRadius (sourceAReal n low b/2)) (G.row l.val).val
  have hphase(u:rows):=actual_regular_phase F N 1 (1/4) (by norm_num) (by norm_num) hN (by change 1≤(1:ℝ);rfl)
    (fun x hx=>(i.p.support 0 hx).1) (fun x hx=>(i.p.support 1 hx).1) Wa (fun _=>P) H0 mainRadius
    (sourceAReal n low b/2) (by linarith [sc.geometry.a_pos]) (fun l=>by rw [hamp l];exact (hrad l).1)
    rows second G u
  have hmaskall:((geometryRawFixedMask F.s R₀*G.L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))≠0 ∧
      (((geometryRawFixedMask F.s R₀*G.L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)).absNorm:ℝ)≤Z^(10:ℝ):=by
    exact hmaskZ.2 α F.s rfl G.L G.L_ne hLcap P S A depth (sourceAReal n low b)
      hS hA hdepth sc.geometry.a_pos.le hcost hpoolne hp.norm_upper
  -- The uniform mask estimate is independent of the row carrier, including empty families.
  have hcall:=hAt T reflected second F.s Am₁ Am₂ Dm Km R₀ seed Fm 1 ξ F.hK bin hR₀ hs hZ rfl
    θloss (fixedBadMask*idealGenerator R₀) hm hml hm2 F.zero₁ F.zero₂ F rows G hinj S A hgood
    hmaskall.1 hmaskall.2 i.p i.θ i.w (fun _=>33/50) i.freq t height
    (fun j _=>hi.widths_nonneg j) (fun j _=>hi.widths_mesh j) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
    hheight hfh (fun j _ I hI=>F.s.prime j I hI) (fun j _ I hI=>hslot j I hI)
    (fun j _ I hI hne=>hslotcap j I hI hne) corner omega
    (fun l=>residualWeight_nonneg _ _ _) havoid
    (fun l=>by
      have hh:=((hcorn l.val).1 corner).2.2.2.2.2
      dsimp only [SelectedRegularCanonicalGeometry.corner₁,SelectedRegularCanonicalGeometry.corner₂] at hh
      dsimp only
      rw [mul_assoc]
      exact hh)
    (fun l=>missing_norm_from_key_caps (G.key l.val) Z _ (sh.gates l.val).2.2.2.2.2)
    sh.states sh.fixed sh.keep sh.select sh.gates
    (fun j _=>hi.widths_nonneg j) (fun j hj=>by
      have hw:i.w j≤∑j,i.w j:=Finset.single_le_sum (fun k _=>hi.widths_nonneg k) (Finset.mem_univ j)
      have hs:(∑j,i.w j)≤(n.cap:ℝ):=by simpa only [globalFace,mul_one] using hi.face.2.2.2.2.2.1
      linarith)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) hth (fun _=>θloss) (fun _=>frequencyLoss Z 32 ξ) width Wa
    (fun l=>hfull l.val) rfl rfl (fun _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl) hi.widths_nonneg hi.cell_upper
    (by change 1≤(1:ℝ);rfl) (by change (2:ℝ)≤2;rfl) hs6 plain sc.mesh_nonneg sc.mesh_small sc.width_nonneg sc.width_step
    (by linarith [sc.loss_small]) (by linarith [sc.loss_small]) (fun _=>by linarith [sc.loss_small])
    (fun _=>hscalar.2.1) (fun l=>(hlabel l.val).1) hscalar.2.2.1 hscalar.2.2.2.1
    (fun _=>hscalar.2.2.2.2 width sc.width_step)
    (fun l=>by
      change radial G n low b l.val≤_+θloss
      change radial G n low b l.val≤childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
        (F.first (G.row l.val).val.1) (G.datum l.val).C (G.datum l.val).D (G.datum l.val).inactive
        Z 1 (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ θloss θloss) θloss 2+θloss
      rw [←(hlabel l.val).2.1];exact le_add_of_nonneg_right sc.loss_pos.le)
    (fun l _=>by
      change radial G n low b l.val≤2
      have hd:=le_max_right (labelD F.reflected (F.first (G.row l.val).val.1) Z-labelC F.reflected (F.first (G.row l.val).val.1) Z) 0
      have hω:0≤frequencyLoss Z 32 F.ξ:=hscalar.2.1.1
      dsimp only [radial,sourceFReal]
      linarith only [hd,hω,sc.geometry.a_pos])
    (fun l _=>by
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change rawFrequencyNorm (nonzeroJointSourceRow (G.key l.val))≤Z^(radial G n low b l.val)
      exact (hlabel l.val).2.2)
    (fun l _=>by simpa only [SelectedRegularCanonicalGeometry.corner₁,SelectedRegularCanonicalGeometry.corner₂,Real.rpow_one] using ⟨((hcorn l.val).1 corner).2.2.1,((hcorn l.val).1 corner).2.2.2.1⟩)
    P poolMesh BD Bsource depth (fun l=>H0 (G.row l.val).val.1.1) (fun l=>mainRadius (G.row l.val).val.1.1)
    hp (fun l=>hH0 _) (fun l=>hrad _) (fun l=>(hnorm l.val).1) (fun l=>(hnorm l.val).2)
    (fun l=>by
      have hh:=hphase l.val
      unfold SelectedHighPaid.PhaseBound SelectedHighPaid.mainExtra at hh
      rw [hamp _] at hh
      exact hh)
  exact hcall
end
end QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.eventually_initial_low_point
