/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B006
import Submissions.affine_local_20261013.Bundles.B013
import Submissions.affine_local_20261013.Bundles.B014
import Submissions.affine_local_20261013.Bundles.B054
import Submissions.affine_local_20261013.Bundles.B070
import Submissions.affine_local_20261013.Bundles.B072
import Submissions.affine_local_20261013.Bundles.B078
import Submissions.affine_local_20261013.Bundles.B084
import Submissions.affine_local_20261013.Bundles.B124

/- BEGIN ORIGINAL MODULE Global.Numerator.Scalar.LocalSourcePacket ; sha256 68142345558da4450d7165f6221ff32d8b41d1fdeb1992623b355590682f7dfa -/
section


noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator.Scalar
theorem local_source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d delta q epsilon eps t mesh C Ccount C0 B : ℝ)
    (hZ : 0 < Z) (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (C*(Ccount*C0*Z^(3*t))*B*((Z^d)^(ly/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(t+q*(ell/d)-q*(_root_.Local44.Physical.baseCapacity (1-ly/d))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+2*t)/4+
        delta*mesh/4+delta*t+t*(ell/d))) =
    (C*Ccount*C0*B)*Z^(localNumeratorExponent kap d delta (q/delta)+
      localSourceLoss d delta epsilon eps t mesh) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E : ℝ := t+q*(ell/d)-q*(_root_.Local44.Physical.baseCapacity (1-ly/d))/2+
    (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
      159*epsilon+9*t)+1+2*t)/4+delta*mesh/4+delta*t+t*(ell/d)
  calc
    _ = (C*Ccount*C0*B)*
        ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
          Z^(-(4/25:ℝ)*ell)*Z^(3*t)*((Z^d)^(ly/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = (C*Ccount*C0*B)*Z^(d*(2*eps)+d*(-(17/50:ℝ))+(17/25)*t+
        -(4/25:ℝ)*ell+3*t+(d*(ly/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      unfold localNumeratorExponent localSourceLoss
      dsimp only [E, _root_.Local44.Physical.baseCapacity]
      field_simp
      ring

end Submission20261012.Global.Numerator.Scalar
end
/- END ORIGINAL MODULE Global.Numerator.Scalar.LocalSourcePacket -/

/- BEGIN ORIGINAL MODULE Physical.LocalOriginalFourth ; sha256 0512060326caac246762d7df9dce42565b9e21536c28e1afbc59f25b27606860 -/
section




noncomputable section
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Local44.Physical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator.PhysicalTail Cycle25.Weighted.Numerator CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

theorem certified_transport_original_numerator_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ)
    (hloss : 0< loss) (hxi : 0< xi) (hb : 0< b) (hCslot : 0< Cslot) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(data : ∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows→ℝ)(Y m n : ℝ),
      0< Y → (∀i,0< N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      _root_.Local44.Physical.BareWindow n → n ≤ m+xi →
      (∀i,(data i).combinedConductor ≤ (fixedConductorConstant F.S:ℝ)*U^m*(Y/N i)) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ transportMomentMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ _root_.Local44.Physical.transportCapacity n (m+xi-n) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ Cslot*U^q) →
      (∑i:rows,‖HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0‖^4*
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0< Ccond := by dsimp [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  obtain ⟨degree,Cr,hCr,hret⟩ := certified_transport_retained_fixed_profile F hbeta hbetaTop G loss Ccond Ccond xi
    hloss hCcond hCcond hxi
  obtain ⟨Ct,hCt,htail⟩ := subtype_discarded_fourth_negligible (xi/2) 0 q b Ccond Cslot
    (by positivity) hb hCcond hCslot G
  refine ⟨degree,8*(Cr+Ct),by positivity,?_⟩
  filter_upwards [hret] with U hret
  have hU := hret.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N Y m n hY hN hm hmmax hn hnm hcombined T width z height hw hwmax hz hheight hzim hcap hQ
  let τ (i:rows) := (data i).presentation
  let ψ (i:rows) := (data i).primitive
  let R (i:rows) := retainedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let tail (i:rows) := discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let Q (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let P (i:rows) := HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
  have hc (i:rows) : (data i).combinedConductor ≤ Ccond*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property).2 hCcond.le)
  have hred (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U :=
    (data i).redundant_le_combined.trans (hc i)
  have hr := hret.2 rows hrows τ ψ (fun i=> Y/N i) m n (fun i=>(data i).element_eq)
    (fun i=> div_pos hY (hN i).1) hm hmmax hn hnm hred hcombined T width z height
    hw hwmax hz hheight hzim hcap
  have ht := htail rows τ ψ N Q Y U hY hU.le hN (fun u hu=>(hrows u hu).2) hc hQ
  simp only [show (xi/2)/2=xi/4 by ring,neg_zero,Real.rpow_zero,mul_one] at ht
  have hsplit (i:rows) : P i=(data i).phase*(R i+tail i) :=
    (data i).split G (Y/N i) (U^(xi/4)) (div_pos hY (hN i).1)
  have hh := original_split_weighted_fourth Finset.univ P R tail (fun i=>(data i).phase) Q
    (fun _=>1) (Cr*(1+height)^degree*U^(1+D.t+loss)) Ct
    (fun _ _=> le_rfl) (fun i _=>(data i).phase_norm) (fun i _=> hsplit i)
    (by simpa only [Complex.ofReal_one,div_one] using hr) ht
  simp only [Complex.ofReal_one,div_one] at hh
  have hH : 1 ≤ (1+height)^degree := one_le_pow₀ (by linarith)
  have hpow : 1 ≤ U^(1+D.t+loss) := Real.one_le_rpow hU.le (by linarith [D.t_pos])
  have hcost : 1 ≤ (1+height)^degree*U^(1+D.t+loss) := one_le_mul_of_one_le_of_one_le hH hpow
  have hCt' := mul_le_mul_of_nonneg_left hcost hCt.le
  exact hh.trans (by nlinarith)

end OAI.SevenEighths.Local44.Physical
end


/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The original restoration and tail proofs are retained; the certified physical
moment now uses the local/old/empty transport capacity. -/

#print axioms OAI.SevenEighths.Local44.Physical.certified_transport_original_numerator_fourth
end
/- END ORIGINAL MODULE Physical.LocalOriginalFourth -/

/- BEGIN ORIGINAL MODULE Global.Final.Endpoint ; sha256 90fced52f5a156eecb8a360e21f06ac5511f0601e4dba28e8e707a7d4005f0c5 -/
section


/-! Conditional transfer of the new raw source estimate to the actual
L-functions. The raw analytic input remains an explicit hypothesis here. -/
namespace Submission20261012.Global
open OAI.SevenEighths

/-- The exact rational endpoint follows once the physical raw contract is supplied. -/
theorem beta_le_theta_of_raw_fullW_input
    (hinput : ProbeAssembly.RawFullWAnalyticInput) : HeckeZeroSupremum.beta ≤ theta :=
  Cycle25.beta_le_of_common_probe theta_gt_half.le theta_lt_seven_eighths.le
    (ProbeAssembly.common_probe_of_raw_fullW_input hinput)

theorem hecke_nonzero_of_raw_fullW_input
    (hinput : ProbeAssembly.RawFullWAnalyticInput)
    (χ : HeckeFamily.Character) (s : ℂ)
    (hs : theta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_raw_fullW_input hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_raw_fullW_input
    (hinput : ProbeAssembly.RawFullWAnalyticInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : theta < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 :=
  Cycle25.dirichlet_of_hecke theta_pos (hecke_nonzero_of_raw_fullW_input hinput) χ s hs hexc

theorem zeta_nonzero_of_raw_fullW_input
    (hinput : ProbeAssembly.RawFullWAnalyticInput)
    (s : ℂ) (hs : theta < s.re) : riemannZeta s ≠ 0 :=
  Cycle25.zeta_of_hecke theta_pos (hecke_nonzero_of_raw_fullW_input hinput) s hs

/-- The catalogue boundary is the exact new rational theta, without rounding. -/
theorem zeta_nonzero_rational_of_raw_fullW_input
    (hinput : ProbeAssembly.RawFullWAnalyticInput)
    (s : ℂ) (hs : (4374347:ℝ)/5000000 < s.re) : riemannZeta s ≠ 0 :=
  zeta_nonzero_of_raw_fullW_input hinput s hs

end Submission20261012.Global

#print axioms Submission20261012.Global.beta_le_theta_of_raw_fullW_input
#print axioms Submission20261012.Global.hecke_nonzero_of_raw_fullW_input
#print axioms Submission20261012.Global.dirichlet_nonzero_of_raw_fullW_input
#print axioms Submission20261012.Global.zeta_nonzero_rational_of_raw_fullW_input
end
/- END ORIGINAL MODULE Global.Final.Endpoint -/

/- BEGIN ORIGINAL MODULE Physical.LocalActiveFourth ; sha256 d81cb73358ed5291bc21b32eede02d74c87af84a67de19c7a92c56efaf96c416 -/
section





/-! Actual rowwise coefficient choices on one finite dilation box. Inactive
choices are replaced by a positive admissible scale before invoking the moment
bound, and their nonnegative contribution is subsequently discarded. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Local44.Physical
open Cycle25.Weighted.Numerator Cycle25.Weighted.Numerator.PhysicalMoment Cycle25.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma eventually_transport_cutoff_le_base (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ U : ℝ in atTop, 1 < U ∧ ∀ n : ℝ,
      _root_.Local44.Physical.BareWindow n → b*U^(1-n) ≤ U := by
  have he : ∀ᶠ U : ℝ in atTop, b ≤ U^(2/5:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/5)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro n hn
  have hn' : 1-n ≤ 3/5 := by rcases hn with ⟨hlo,hhi⟩; linarith
  calc
    _ ≤ U^(2/5:ℝ)*U^(3/5:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hn')
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)]; norm_num

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem certified_transport_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop:HeckeZeroSupremum.beta ≤ 7/8)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀n:ℝ,_root_.Local44.Physical.BareWindow n →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ transportMomentMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ _root_.Local44.Physical.transportCapacity n
        ((j:ℝ)*boxWidth+boxWidth+annulusSlack) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^((1-n))
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_transport_original_numerator_fourth F hbeta hbetaTop G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_transport_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN n hn j hj T width z height hw hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^((1-n))
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-(1-n)+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i:rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i:rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 n hn).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i:rows) (hi:active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hb' : max 1 ((data i).combinedConductor*N i/(Ccond*rowNorm i.val)) ≤
        U^((j:ℝ)*boxWidth+boxWidth) := by
      have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
        dsimp only [Lc]
        ring
      have hexp : ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth := by ring
      rw [hprod,hexp] at hspec
      exact hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U ((1-n)) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    simpa only [m,add_assoc] using hc
  let Nsafe (i:rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i:rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range boxWidth hbox j hj
  have hm : 0 ≤ m := by
    rcases hn with ⟨hlo,hhi⟩
    dsimp [m]
    linarith
  have hmmax : m+annulusSlack ≤ 2 := by
    rcases hn with ⟨hlo,hhi⟩
    dsimp [m]
    linarith
  have hnm : n ≤ m+annulusSlack := by dsimp [m]; linarith
  have hcapacity : (∑i,width i) ≤
      _root_.Local44.Physical.transportCapacity n (m+annulusSlack-n) := by
    have he : m+annulusSlack-n = (j:ℝ)*boxWidth+boxWidth+annulusSlack := by dsimp [m]; ring
    rwa [he]
  have hQ' (i:rows) : ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m n hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax hn hnm (fun i=>(hsafe i).2.2) T width z height hw hwmax hz hh him hcapacity hQ'
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul]
    positivity

end OAI.SevenEighths.Local44.Physical
end

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

#print axioms OAI.SevenEighths.Local44.Physical.certified_transport_active_box_fourth
end
/- END ORIGINAL MODULE Physical.LocalActiveFourth -/

/- BEGIN ORIGINAL MODULE Physical.LocalSourceBin ; sha256 97b82c7445119dc1806fa4d8f6d74bbdc5243810aba5a1391b1f8bc581974b02 -/
section




/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace OAI.SevenEighths.Local44.Physical
open Cycle25.Numerator Cycle25.Weighted Cycle25.Weighted.Numerator
open _root_.Local44.Physical
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount
local notation "O" => HeckeFamily.O

theorem source_packet_selected_bin_local {D : MomentData}
    (F : WeightedSourceData D) (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta≤7/8) (eSmall : D.e≤1/1000)
    (hfine : ∀j,D.ell j≤ transportMomentMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/200:ℝ)≤ d → U=Z^d →
      ∀bare:ℝ,BareWindow bare →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount L : ℝ),
      0≤ q → q≤(2*a-1)/2 → 1≤ Ccount → (rows.card:ℝ)≤ Ccount*U^R →
      (∀i,‖P i‖≤ U^(q*L)) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.ell s/d)≤ transportCapacity bare ((j:ℝ)*D.t+D.t+D.t)) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*transportCapacity bare ((j:ℝ)*D.t+D.t+D.t)-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖≤ U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
        (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(1-bare))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(1-bare))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*L-q*(baseCapacity bare)/2+
            (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t) := by
  obtain ⟨Cm,hCm,hpacket⟩ := actual_label_half_packet_bin_bound_uniform (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := certified_transport_active_box_fourth F hbeta hbetaTop F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤ Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_transport_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hUZ bare hn η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount L hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := by linarith
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.ell s/d)=Z^(D.ell s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by dsimp only [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  let Ts (s : J) := sourcePrimePool F Z s.val
  let hTs := fun s:J=> source_prime_pool_outside F Z s.val
  let Q (j : ℕ) (i : rows) := ∏s∈selected j,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(D.ell s.val/d)) z) = Q j i := by
    calc
      _ = ∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (Z^(D.ell s.val)) z := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hscale s.val]
      _ = _ := by
        exact Finset.prod_coe_sort (selected j)
          (fun s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z)
  have hwpos (s : Fin D.N) : 0 < D.ell s/d := div_pos (D.slots_bounds s).1 hd0
  have hwmax (s : Fin D.N) : D.ell s/d≤ transportMomentMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := transportMomentMesh_pos D.t D.t_pos
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤ Z^(D.ell s.val) := Real.one_le_rpow hZ.le (D.slots_bounds s.val).1.le
  have hY : 0< U^(1-bare) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(1-bare)≤ U^((coefficientBoxCount D.t:ℝ)*D.t) := by
    apply (hcutU.2 bare hn).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (coefficientBoxCount_extent D.t D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := half_mass_contour_gates ha hatop D.e_pos
    (show 4*D.e≤16*D.e by linarith [D.e_pos])
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(1-bare) ∧
        dilationBox U D.t (coefficientBoxCount D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(1-bare)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+2*D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=> lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      bare hn j hj (selected j) (fun s=> D.ell s.val/d) (fun _=> z) height
      (fun s=> hwpos s.val) (fun s=> hwmax s.val) (fun _=> hz) hheight (fun _=> hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=> D.ell s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.ell s.val/d)) z)‖≤ U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    simp only [show 1+D.t+D.t=1+2*D.t by ring] at hh'
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(1-bare) ∧
      dilationBox U D.t (coefficientBoxCount D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(1-bare)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤ Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket bare hn F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=> hη s.val Q hQ) Pbase (fun _=> F.W) (fun s=> Z^(D.ell s.val)) hYp
    (fun _=> F.complex_support) (fun _ y=> source_complex_profile_norm F y) x z a D.e ha
    (by linarith) D.e_pos eSmall hx hz rows Subtype.val F.W 1 2 (U^(1-bare))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY U D.t D.t (coefficientBoxCount D.t) Cu Ccond Q P
    R q L (2*a-1) selLoss (2*D.t) Ccount
    (Cr'*(1+height)^degree) hmom.1.le D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=> hrow i.val i.property) hcut (by simpa using hcard) hselected hfull hmomentInput
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*L-q*(baseCapacity bare)/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t) =
      U^D.t*U^(q*L-q*(baseCapacity bare)/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end OAI.SevenEighths.Local44.Physical

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

#print axioms OAI.SevenEighths.Local44.Physical.source_packet_selected_bin_local
end
/- END ORIGINAL MODULE Physical.LocalSourceBin -/

/- BEGIN ORIGINAL MODULE Global.Numerator.LocalSourceClass ; sha256 75ac17b1b40f5271d8fc2850d954227f3ae0d6ec6a02d616cb9d253e7dac67d1 -/
section



/-! The actual full amplitude class supplies the selected-prime and upper-product
premises of the original-numerator packet estimate. The class count remains an
explicit premise and is not recomputed on an error-dependent or selected subset. -/
noncomputable section
set_option maxHeartbeats 2600000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open _root_.Local44.Physical OAI.SevenEighths.Local44.Physical
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem source_packet_amplitude_class_local {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (hfine:∀j,D.ell j≤ transportMomentMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z → (1/2:ℝ)≤ d → Endpoint.junction≤ d → d≤ Submission20261012.Global.h+rowExtension → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=> D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀R Ccount:ℝ,1≤ Ccount → (rows'.card:ℝ)≤ Ccount*U^R →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
        (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(ly/d))*(∏s∈main,Q i.val s)‖) ≤
        C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*(baseCapacity (1-ly/d))/2+
            (3*R+1+2*D.t)/4+(2*a-1)*transportMomentMesh D.t/4+(2*a-1)*D.t+D.t*(ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := source_packet_selected_bin_local F hbeta hbetaTop D.e_small.le hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdlocal hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=> D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0≤2*a-1 := by linarith
  have hδtop : 2*a-1≤3/4 := by linarith
  have hU0 : 0< U := zero_lt_one.trans hbin.1
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hbare := local_source_bare_window d hdlocal hdmax
  have hselection (j:ℕ) := source_class_main_transport_selection D F hfine Z d ((j:ℝ)*D.t+2*D.t) (2*a-1)
    hZ hd (by positivity) hδ hbare z rows main bin hne
  have hq0 : 0≤ q := (hselection 0).1
  have hqtop : q≤(2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected⊆main ∧
      (∑s∈selected,D.ell s/d)≤ transportCapacity (1-ly/d) ((j:ℝ)*D.t+2*D.t) ∧
      ∀u∈rows',
        (Z^d)^(2*q*transportCapacity (1-ly/d) ((j:ℝ)*D.t+2*D.t)-
          (2*a-1)*transportMomentMesh D.t)≤‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖≤(Z^(D.ell s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
          ‖∏s∈main,Q u s‖≤(Z^d)^(q*(ell/d)+D.t*(ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖≤ U^(q*(ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(ell/d)) (D.t*(ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.ell s/d) ≤ transportCapacity (1-ly/d) ((j:ℝ)*D.t+D.t+D.t) := by
    simpa only [two_mul,add_assoc] using hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*transportCapacity (1-ly/d) ((j:ℝ)*D.t+D.t+D.t)-
        ((2*a-1)*transportMomentMesh D.t/2)) ≤ ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    have he : (j:ℝ)*D.t+D.t+D.t=(j:ℝ)*D.t+2*D.t := by ring
    rw [he]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (transportMomentMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖≤ U := by
    rw [hUZ]
    exact source_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ (by linarith) hUZ (1-ly/d) hbare η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=> hrows u (hsub hu)) (fun u hu=> hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*transportMomentMesh D.t/2) Ccount (ell/d) hq0 hqtop hCc hcard hfull hcap hlow hcrude
  simp only [sub_sub_cancel] at hb
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=> labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
      (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(ly/d))) Pmain U (D.t*(ell/d))
    (D.t+q*(ell/d)-q*(baseCapacity (1-ly/d))/2+
      (3*R+1+2*D.t)/4+((2*a-1)*transportMomentMesh D.t/2)/2+(2*a-1)*D.t)
    (C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*transportMomentMesh D.t/2)/2=(2*a-1)*transportMomentMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.LocalSourceClass -/
