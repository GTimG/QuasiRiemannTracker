/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Actual buffered detector/conductor cells, their full finite sum, and the exact
finite numerator. Adapted from PR69 Finite/{Geometry,Summation,Transfer,Bridge}.
Only actual generic partitions and arbitrary-saving conversion estimates are
reused; all numerical guards are proved at our parameters. No old Bounds or
PhysicalSchedule instance, no assumed count/energy/numerator conclusion.

-/
import Candidate.SilPrior.FourthPower.ReturnFullNumerator
import Candidate.SilPrior.FourthPower.ReturnNumeratorCarrier
import Candidate.SilPrior.FourthPower.TransportFinal
import Candidate.SilPrior.FourthPower.ReturnFiniteError
import Candidate.SilPrior.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnFiniteNumerator
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI OAI.SevenEighths
open HeckeFamily ProbeHighRowFamily ProbePhysical HeckeInverseAmplification
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open QRH.Record12518109Count QRH.Record12518109Existence
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Assembly
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open Candidate.SilPrior.FourthPower.ReturnNumeratorCarrier
open QRH.Record1252270103Return.GenericPhysical.FourthPowerFinalAssembly
open SilFourthPowerTransportHighTransport
open ReturnCertificate ReturnWindows ReturnSourceFaces ReturnOldCount
open ReturnSourceInputs ReturnMaskedCount ReturnPacketSummation ReturnFullNumerator
local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : TransportBounds := TransportBounds.of_exact_values rfl rfl rfl rfl
local instance : CountScheme := ReturnWindows.countScheme

theorem actual_geometry_h : Geometry.h=Candidate.SilPrior.FourthPower.h := by
  change 1+ell-x=h
  dsimp [x]
  ring

theorem actual_geometry_dplus : Geometry.dPlus=dplus := by
  dsimp only [Geometry.dPlus,dplus]
  rw [actual_geometry_h]

theorem actual_signal_shift : Assembly.signalShift=ReturnAnalyticFinish.signalShift := by
  change -(5/6-x/3-ell/6)=-(4+y-x)/6
  linarith [geometry_identities.1]

private theorem padded_cutoff {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D) :
    Geometry.h+ReturnCarrierInterfaces.rowPadding+2*A.D.t≤Geometry.dPlus := by
  rw [actual_geometry_h,actual_geometry_dplus]
  have hp := P.t_padding
  dsimp only [ReturnCarrierInterfaces.rowPadding,dplus]
  linarith

/-- All cell geometry is uniform before the live row labels. -/
theorem actual_cell_geometry {extraMesh : ℝ} (A : GapData extraMesh) (P : TransportParameters A.D) (η : Character) (τ : ℝ) (n : ℕ) :
    ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η ReturnCarrierInterfaces.rowPadding A.D.e τ n Z idx grid →
      ∀k i j : ℕ,(cellRows A.D A.F Z idx grid k i j).Nonempty →
        CellFacts A.D A.F η Z τ (cellRows A.D A.F Z idx grid k i j)
          (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) QRH.Record1252270103Return.GenericArithmetic.dp A.D.t
    (QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding) (by norm_num) (by norm_num) A.D.t_pos
    (padded_cutoff A P),eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  intro idx grid hsel k i j hne
  let R := selectedRows A.D A.F Z grid
  let Rij := cellRows A.D A.F Z idx grid k i j
  have hsubk : Rij⊆R∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsub : Rij⊆R := hsubk.trans Finset.inter_subset_left
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hg:=hgeo R (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
    (hne.mono hsubk)
  obtain ⟨u,hu⟩ := hne
  have hmem := (mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
  have hgu := ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).2.2
  have hjpos : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero (hmem.2.2 ▸ hgu)
  have ha : (51/100:ℝ)<51/100+A.D.e*j := by nlinarith [A.D.e_pos]
  have hai : 51/100+A.D.e*j≤7/8 := by simpa only [hmem.2.2] using (hsel.2.1 u).2.1
  have hZp : 0< Z := zero_lt_one.trans hZ
  refine ⟨hg.2.2.1,hg.2.2.2.1,ha,hai,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
      (hrows u (hsub hu)).2.2.1,hg.2.2.2.2.2 u (hsubk hu)⟩
  · intro u hu
    constructor
    · rw [←Real.rpow_mul hZp.le]
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans (hrows u (hsub hu)).2.1
      have hd:=hg.2.2.2.1
      have hcap : QRH.Record1252270103Return.GenericArithmetic.dp≤1 := by
        change Geometry.dPlus≤1
        rw [actual_geometry_dplus]
        exact feedback_domain.2.1.le
      nlinarith
    · exact (hg.2.2.2.2.2 u (hsubk hu)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [A.D.t_pos]))
  · intro u hu
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 u (hsubk hu)).1
  · intro u hu
    exact (hsel.2.2 u ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).1
      (hrows u (hsub hu)).2.2.1).1
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    rwa [hm.2.1,hm.2.2] at hb
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    simpa only [hm.2.1,hm.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb
def FullWCellsAt {extraMesh : ℝ} (A : GapData extraMesh) (τ : ℝ) (n : ℕ) (η : Character) (C Z : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η ReturnCarrierInterfaces.rowPadding A.D.e τ n Z idx grid →
    ∀k∈smallDyadicIndices (Z^(QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/A.D.e⌋₊+1),
      (cellRows A.D A.F Z idx grid k i j).Nonempty →
      ‖fullW A.D A.F η Z (cellRows A.D A.F Z idx grid k i j)
        (fun _=>51/100+A.D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*Z^(sourceTarget+A.D.t/8)

theorem cell_exponent_le {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D) :
    sourceTarget+A.D.t/4≤HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma := by
  have hc := A.count_error
  change 159*A.D.ε+609*A.D.t≤(HeckeZeroSupremum.beta-theta)/10000 at hc
  have he := A.D.epsilon_pos
  have ht := A.D.t_pos
  have hs := P.sigma_small
  have hr : 0<reserve := by norm_num [reserve]
  rw [actual_signal_shift]
  dsimp only [sourceTarget,ReturnAnalyticFinish.signal]
  linarith

theorem fullW_sum_bound {extraMesh : ℝ} (A : GapData extraMesh) (P : TransportParameters A.D) (τ : ℝ) (n : ℕ) (η : Character)
    (C : ℝ) (hC : 0< C) :
    ∃Csum : ℝ,0< Csum ∧ ∀ᶠZ : ℝ in atTop,
      FullWCellsAt A τ n η C Z → ∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η ReturnCarrierInterfaces.rowPadding A.D.e τ n Z idx grid →
      ‖fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
        (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        Csum*Z^(HeckeZeroSupremum.beta+QRH.Record1252270103Return.GenericPhysical.Assembly.signalShift-P.sigma) := by
  have ht:=A.D.t_pos
  obtain ⟨Cd,hCd,hdyad⟩:=canonical_dyad_cost (A.D.t/8) (by positivity)
  let m : ℕ:=⌊(49/100:ℝ)/A.D.e⌋₊
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  intro hcell idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hb:=fullW_cells_norm_bound A.F.S A.F.exclusions A.F.maximal η
    (selectedRows A.D A.F Z grid) (primePool A.D A.F Z) (poolOutside A.D A.F Z)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W
    (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z A.D.e (Z^τ) (Z^(QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding))
    idx grid n m (normalizer A.D A.F Z) (C*Z^(sourceTarget+A.D.t/8)) (by positivity)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u _=>⟨(hsel.1 u).2.1,(hsel.1 u).2.2.1⟩) (hcell idx grid hsel)
  have htop : QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding≤1 := by
    change Geometry.h+ReturnCarrierInterfaces.rowPadding≤1
    rw [actual_geometry_h]
    norm_num [h,ReturnCarrierInterfaces.rowPadding]
  have hd:=hdyad Z (QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding) hZ htop
  have hexp:=Real.rpow_le_rpow_of_exponent_le hZ (cell_exponent_le A P)
  calc
    _ ≤ ((smallDyadicIndices (Z^(QRH.Record1252270103Return.GenericArithmetic.h+ReturnCarrierInterfaces.rowPadding))).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*
        (C*Z^(sourceTarget+A.D.t/8)) := hb
    _ ≤ (Cd*Z^(A.D.t/8))*(n+1:ℕ)*(m+1:ℕ)*(C*Z^(sourceTarget+A.D.t/8)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity))
        (by positivity)
    _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*Z^(sourceTarget+A.D.t/4) := by
      have hp : Z^(A.D.t/8)*Z^(sourceTarget+A.D.t/8)=Z^(sourceTarget+A.D.t/4) := by
        rw [←Real.rpow_add hZp]
        congr 1
        ring
      calc
        _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*(Z^(A.D.t/8)*Z^(sourceTarget+A.D.t/8)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
/-- The proved original-row error applies to the literal new-geometry numerator. -/
theorem actual_selected_error {extraMesh : ℝ} (A : GapData extraMesh) (τ : ℝ) (hτ : 0< τ) :
    ∃C : ℝ,0≤ C ∧ ∀ᶠZ : ℝ in atTop,∀n : ℕ,∀η : Character,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η ReturnCarrierInterfaces.rowPadding A.D.e τ n Z idx grid →
      normalizer A.D A.F Z≠0 ∧
      ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
        1 2 ReturnCarrierInterfaces.rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid/normalizer A.D A.F Z-
        fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
          (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩:=ReturnFiniteError.actual_normalized_cube_fullW_arbitrary_saving
    A.F.modulus ⊤ le_top A.D.N τ 1 1 2 1 ReturnCarrierInterfaces.rowPadding (A.D.t/8)
    hτ (by norm_num) (by norm_num) (by norm_num) (by norm_num [ReturnCarrierInterfaces.rowPadding])
    (by have ht:=A.D.t_pos;positivity) A.D.e A.D.e_pos A.D.e_small
    A.F.S A.F.exclusions A.F.maximal A.F.first A.D.length A.D.slots_pos A.D.slots_injective A.D.slots_sum
    (fun _=>A.F.w) (fun _=>A.F.smooth) (fun _=>A.F.compact) (fun _=>A.F.support)
    (fun _=>A.F.bounded) (fun _=>A.F.nonzero) A.F.W A.F.W 1 2 1 2 (by norm_num) (by norm_num)
    A.F.complex_support A.F.complex_support A.F.real A.F.real A.F.nonnegative A.F.nonnegative
    A.F.complex_nonzero A.F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℝ)] with Z he hT hZ
  intro n η idx grid hsel
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hbin : ∀u∈selectedRows A.D A.F Z grid,
      (51/100:ℝ)≤51/100+A.D.e*grid u ∧ 51/100+A.D.e*grid u≤1 ∧ 2< Z^τ ∧
      Z^τ≤(3*idx u+1:ℕ)*Z^τ ∧ (3*idx u+1:ℕ)*Z^τ≤(3*idx u+2:ℕ)*Z^τ ∧
      detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+A.D.e*grid u+2*A.D.e := by
    intro u hu
    refine ⟨(hsel.2.1 u).1,(hsel.2.1 u).2.1.trans (by norm_num),hT,?_,?_,(hsel.2.1 u).2.2.2.2.1⟩
    · have hm : (1:ℝ)≤(3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
    · have hm : ((3*idx u+1:ℕ):ℝ)≤(3*idx u+2:ℕ) := by
        exact_mod_cast (by omega : 3*idx u+1≤3*idx u+2)
      exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
  have hb:=he η (selectedRows A.D A.F Z grid)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u=>51/100+A.D.e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx hbin
  convert hb using 1 <;> rfl

private theorem target_positive {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D) (hgap : theta<HeckeZeroSupremum.beta) :
    0<HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma := by
  rw [actual_signal_shift]
  have hh : (1/10:ℝ)<theta+ReturnAnalyticFinish.signalShift := by
    norm_num [theta,ReturnAnalyticFinish.signalShift,x,y,ell,h]
  have hs := P.sigma_small
  have ht := P.t_padding
  linarith

/-- All genuine count/moment/physical inputs are consumed through FullW.
The finite cells, every dyadic conductor and buffered detector label, and the
cube conversion error are summed before the source probe is reconstructed.
The only unfinished analytical input is precisely the full source face. -/
theorem actual_finite_numerator (hPrior : OlderIncumbentContract.OlderIncumbentInput) {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hgap : theta<HeckeZeroSupremum.beta) :
    ∃J : ℝ,0≤J ∧ ∀η : Character,∃tau : ℝ,
      ReturnCarrierInterfaces.HeightAdmissible A.D P J tau ∧ FixedFiniteNumeratorInputAt A.D A.F P tau η := by
  have hloss := transport_height_loss_bounds P
  obtain ⟨J,hJ,hfull⟩ := actual_fullW_cells hPrior A P hsource hgap
    (transportHeightLoss P) hloss.1 hloss.2
  refine ⟨J,hJ,?_⟩
  intro η
  obtain ⟨tau,htau,hcells⟩ := hfull η
  have hheight : ReturnCarrierInterfaces.HeightAdmissible A.D P J tau :=
    ⟨htau.pos,htau.zero_rows,htau.detector_cost,htau.count_scale,
      count_height_transport_gate P hJ htau,htau.physical_height.trans hloss.2⟩
  refine ⟨tau,hheight,?_⟩
  intro n _hn
  obtain ⟨Cw,hCw,hcell⟩ := hcells n
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ := Cw*(η.modulus.absNorm:ℝ)^(2*P.eps)
  have hC : 0<C := by dsimp only [C]; positivity
  obtain ⟨Csum,hCsum,hsum⟩ := fullW_sum_bound A P tau n η C hC
  obtain ⟨Ce,hCe,herror⟩ := actual_selected_error A tau htau.pos
  change ∃Ctot : ℝ,0<Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η ReturnCarrierInterfaces.rowPadding A.D.e tau n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 ReturnCarrierInterfaces.rowPadding A.D.e tau (fun _=>A.F.w) A.F.W A.F.W η Z idx grid‖≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcell,hsum,herror,actual_cell_geometry A P η tau n,
    eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),eventually_ge_atTop (1:ℝ)]
    with Z hc hs he hg hlarge hZ
  have hcAll : FullWCellsAt A tau n η C Z := by
    intro idx grid hsel k hk i hi j hj hne
    have hf := hg idx grid hsel k i j hne
    have hrow : ∀u∈cellRows A.D A.F Z idx grid k i j,
        (rowCharacter A.F.S A.F.exclusions.prime u).residue≠1 := by
      intro u hu
      exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
        u (hf.source_rows u hu).1 (hf.source_rows u hu).2.2.1
    have hdmax : sourceDyadConductor Z A.D.t k≤dplus := by
      have hd := hf.d_upper
      change sourceDyadConductor Z A.D.t k≤Geometry.dPlus at hd
      rwa [actual_geometry_dplus] at hd
    have hb := hc.2 (cellRows A.D A.F Z idx grid k i j)
      (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i hf.d_lower hdmax
      hf.a_lower hf.a_upper (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      hf.source_rows hf.moment_rows hrow hf.frequency_lower hf.next_maximum hf.current_maximum
    convert hb using 1 <;> rfl
  intro idx grid hsel
  have hb := hs hcAll idx grid hsel
  obtain ⟨hN,herr⟩ := he n η idx grid hsel
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma) :=
    Real.one_le_rpow hZ (target_positive A P hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 ReturnCarrierInterfaces.rowPadding A.D.e tau (fun _=>A.F.w) A.F.W A.F.W η Z idx grid
  let W := fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
    (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^tau)
  let N := normalizer A.D A.F Z
  let E := Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)
  have hnormalized : ‖V/N‖≤(Csum+1)*E := by
    calc
      _ = ‖(V/N-W/N)+W/N‖ := by rw [sub_add_cancel]
      _ ≤ ‖V/N-W/N‖+‖W/N‖ := norm_add_le _ _
      _ ≤ 1+Csum*E := add_le_add (herr.trans hsaving) hb
      _ ≤ (Csum+1)*E := by dsimp only [E];nlinarith only [hone]
  rw [norm_div] at hnormalized
  have hraw := (div_le_iff₀ (norm_pos_iff.mpr hN)).mp hnormalized
  simpa only [V,N,E,mul_assoc,mul_comm,mul_left_comm] using hraw

/-- The complete finite numerator package is actually constructed from the
one full-source input. The detector, its slot system, both saved amplifier
pairs, source and transport parameters precede every character. The height
may depend on that character and the common physical degree, but precedes
every cutoff index and buffered selection. No independent count, moment,
finite-numerator or transport-compatibility hypothesis is requested. -/
theorem exists_finite_numerator (hPrior : OlderIncumbentContract.OlderIncumbentInput)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hgap : theta<HeckeZeroSupremum.beta)
    (extraMesh : ℝ) (hextra : 0<extraMesh) :
    ∃A : GapData extraMesh, ∃P : TransportParameters A.D,
      ∃J : ℝ, 0≤J ∧ ∀η : Character, ∃tau : ℝ,
        ReturnCarrierInterfaces.HeightAdmissible A.D P J tau ∧
          FixedFiniteNumeratorInputAt A.D A.F P tau η := by
  have herror : 0<(HeckeZeroSupremum.beta-theta)/10000 :=
    div_pos (sub_pos.mpr hgap) (by norm_num)
  obtain ⟨A,⟨P⟩⟩ := ReturnClassApplication.exists_compatible_joint
    hsource hgap ((HeckeZeroSupremum.beta-theta)/10000)
    ((HeckeZeroSupremum.beta-theta)/10000) extraMesh herror herror hextra
  obtain ⟨J,hJ,hfinite⟩ := actual_finite_numerator hPrior A P hsource hgap
  exact ⟨A,P,J,hJ,hfinite⟩

end
end Candidate.SilPrior.FourthPower.ReturnFiniteNumerator
