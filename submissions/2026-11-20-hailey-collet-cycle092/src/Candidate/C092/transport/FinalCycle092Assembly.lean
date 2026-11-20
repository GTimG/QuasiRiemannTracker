/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Authentic lower and nonmixed packets leave only the mixed upper phase sum. -/
import Candidate.C092.transport.FinalCycle092Geometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.Final
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The mesh and all fees are fixed before the authentic source; one degree
then precedes one common height, which precedes the native transport order.
The sole analytic premise concerns mixed upper bins on the original cells. -/
theorem actual_finite_of_mixed (contact : ℝ)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval contact)
    (hboundary : Geometry.theta=Cycle090.theta)
    (hh : Cycle090.hLower ≤ Geometry.h) (hh' : Geometry.h ≤ Cycle090.hUpper)
    (hell : Geometry.ell=Physical.ell) (hmixed : MixedUpperEstimate contact) :
    ActualFiniteInput := by
  intro hgap
  have hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have ht := ActualGeometry.WidenedCoreBounds.theta_bounds.1
    linarith
  let affineError : ℝ := 1/10000000000000000
  let loss : ℝ := 1/10000000000000000
  have haff : 0 < affineError := by norm_num [affineError]
  have hloss : 0 < loss := by norm_num [loss]
  obtain ⟨mcl,hmcl,hlower⟩ := NaturalPacketLow.actual_natural_lower_whole_final_fee_established hβ loss hloss
  obtain ⟨mcu,hmcu,mpu,hmpu,hupper⟩ := actual_upper_sector_phase_sum_final_fee hβ
    Incumbent.established_moment affineError haff loss hloss
  obtain ⟨mcm,hmcm,mpm,hmpm,hmixed⟩ := hmixed hgap affineError loss haff hloss
  let extra : ℝ→ℝ := fun t=>min (mcl t) (min (mcu t) (min (mcm t)
    (min mpu (min mpm (Cycle25.Energy.commonMesh 2 0 1 (t/4))))))
  have hextra : ∀t,0 < t → 0 < extra t := by
    intro t ht
    exact lt_min (hmcl t ht) (lt_min (hmcu t ht) (lt_min (hmcm t ht)
      (lt_min hmpu (lt_min hmpm (Cycle25.Energy.commonMesh_pos _ _ _ _ (by norm_num) (by norm_num) (by positivity))))))
  obtain ⟨D,F,P,hκ,hbudget,hsource,hcommon,hextraD,hselection⟩ :=
    SelectedActualData.compatible_source_with_selection
      (kappa:=Direct.kap) (budget:=1/10000000000000000)
      (by norm_num [Direct.kap,QRH.ContactCertificate.alphaHi])
      (by norm_num [Direct.kap,QRH.ContactCertificate.alphaHi])
      (by norm_num) (by rw [hboundary];norm_num [Cycle090.theta]) extra hextra
  have fine (m : ℝ) (hm : extra D.t ≤ m) : ∀s,D.length s ≤ m/200 :=
    fun s=>(hextraD s).trans (div_le_div_of_nonneg_right hm (by norm_num))
  have fl : ∀s,D.length s ≤ mcl D.t/200 := fine _ (min_le_left _ _)
  have fu : ∀s,D.length s ≤ mcu D.t/200 := fine _ ((min_le_right _ _).trans (min_le_left _ _))
  have fm : ∀s,D.length s ≤ mcm D.t/200 := fine _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have fpu : ∀s,D.length s ≤ mpu/200 := fine _ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have fpm : ∀s,D.length s ≤ mpm/200 := fine _ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have fc : ∀s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200 :=
    fine _ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hkβ : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa := by rw [hκ];exact Incumbent.established_moment
  let padding := Cycle090.rowPad/2
  let saving := reserve/8
  let allowance := reserve/8
  have hpadding : 0 < padding := by norm_num [padding,Cycle090.rowPad]
  have hpadSmall : padding ≤ Cycle090.rowPad := by
    have hp : (0:ℝ) < Cycle090.rowPad := by norm_num [Cycle090.rowPad]
    dsimp [padding];linarith
  have hdonor := SelectedActualData.Q_donor_padding D P
  have hp12 : padding ≤ 1/1000000000000 := hpadSmall.trans (by norm_num [Cycle090.rowPad,pow_succ])
  have hpad : padding+2*D.t ≤ 1/10000000000 := by
    have hp := hdonor.2
    have hr : Cycle090.rowPad ≤ (1/10000000000:ℝ) := by norm_num [Cycle090.rowPad,pow_succ]
    exact hp.trans hr
  have hsaving : 0 < saving := by norm_num [saving,reserve]
  have hsaving1 : saving ≤ 1 := by norm_num [saving,reserve]
  have hallowance : 0 < allowance := by norm_num [allowance,reserve]
  have heps := transport_eps_le_t D P
  have fee : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*Cycle090.rowPad ≤ 1/100000000000000 := by
    have ht := D.t_pos
    have he := P.e_tsmall
    have hm := P.mesh_small
    have hr : Cycle090.rowPad ≤ (1/10000000000000000:ℝ) := by norm_num [Cycle090.rowPad,pow_succ]
    dsimp [affineError,loss]
    linarith
  have feeUpper : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*Cycle090.rowPad ≤ 1/250000000 := fee.trans (by norm_num)
  have feeLower : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+loss ≤ 1/5000000 := by
    have hp : 0 ≤ Cycle090.rowPad := by norm_num [Cycle090.rowPad]
    linarith
  have htarget : Cycle090.theta-reserve ≤ HeckeZeroSupremum.beta-saving-3*allowance := by
    rw [hboundary] at hgap
    dsimp [saving,allowance]
    have hr : 0 < reserve := by norm_num [reserve]
    linarith
  refine ⟨D,F,padding,P.sigma,saving,hpadding,P.sigma_pos,hsaving,?_⟩
  apply finite_data_of_pointwise_source D F P padding saving allowance Cycle090.sourceCost
    hpadding hpadSmall hsaving1 hallowance hgap.le
  intro η
  obtain ⟨ml,Cl,hCl,hlower⟩ := hlower D F fl hsource η
  obtain ⟨mu,Cu,hCu,hupper⟩ := hupper D F fu hsource fpu fc hkβ η
  obtain ⟨mm,Cm,hCm,hmixed⟩ := hmixed D F fm hsource fpm fc hkβ η
  let degree : ℕ := ml+mu+mm
  let S : ℝ := Cl+Cu+Cm
  have hS : 0 < S := by dsimp [S];linarith
  refine ⟨(degree:ℝ),Nat.cast_nonneg _,?_⟩
  intro τ hτ hheight n hn
  apply pointwise_of_final D F padding τ saving allowance P.eps (degree:ℝ) Cycle090.sourceCost n η hpadding hpad
  refine ⟨2*S,by positivity,?_⟩
  have hτcost : 4*τ < (1/200:ℝ)*D.cost := by linarith [hτ.2.1]
  filter_upwards [hlower P padding τ hτ.1 hτcost hpad n,
    hupper P padding τ hτ.1 hτcost hpad n,hmixed P padding τ hτ.1 hτcost hpad n,
    actual_cell_geometry D F padding hpadding hpad,actual_cell_conductor D F padding] with Z hl hu hm hg hc
  intro idx grid hsel k hk i hi j hj hne
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  have geom := hg τ n η idx grid hsel k hk i j hne
  have hd : 0 < d := geom.1
  have hdh : d ≤ Geometry.h+Cycle090.rowPad := by
    have h := (hc idx grid k hk i j hne).2.1
    have hp := hdonor.2
    dsimp [padding] at h
    linarith
  dsimp only
  intro q hq
  let x : ℂ := ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I)
  let z : ℂ := ((17/50:ℂ)+q.2*Complex.I)
  have hxz : x.re=a+16*D.e := by simp [x]
  have hzz : z.re=17/50 := by simp [z]
  have hzim : |z.im| ≤ (3*i+1:ℕ)*Z^τ := by simpa [z] using hq.2
  let target := HeckeZeroSupremum.beta-saving-3*allowance
  let rhs := fun (C : ℝ) (m : ℕ) (t : ℝ)=>C*(3+(3*i+1:ℕ)*Z^τ)^m*
    (Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*P.eps*d+17*D.t/25) t)
  have normalize (C : ℝ) (m : ℕ) (t : ℝ) (hC : 0 ≤ C) (hCS : C ≤ S) (hm : m ≤ degree) (ht : t ≤ target) :
      rhs C m t ≤ rhs S degree target :=
    upper_normalized_rhs_mono hl.1.le hd hC hCS hm ht
  have hbound : packetNorm D F rows η Z x z (Z^Geometry.y) ≤ rhs (2*S) degree target := by
    by_cases hdl : d ≤ 19/25
    · have raw := hl.2 idx grid hsel k hk i hi j hne hdl x z hxz hzz hzim hh hh' hell P.eps P.eps_pos.le P.mesh_pos.le feeLower
      have ht : Cycle090.theta-1/5000000 ≤ target := by dsimp [target];norm_num [reserve] at htarget ⊢;linarith
      have hn := normalize Cl ml _ hCl.le (by dsimp [S];linarith) (by dsimp [degree];omega) ht
      have hn2 := upper_normalized_rhs_mono (C:=S) (C':=2*S) (m:=degree) (m':=degree) (target:=target) (target':=target)
        hl.1.le hd hS.le (by linarith) le_rfl le_rfl (a:=a) (τ:=τ) (fee:=16*D.e+2*P.eps*d+17*D.t/25) (i:=i)
      exact raw.trans (hn.trans hn2)
    · have hd19 : (19/25:ℝ) < d := lt_of_not_ge hdl
      let response := fun b : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t=>
        classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) b/(2*a-1)
      let A := fun b=>upperSectorAdmission (2*a-1) (response b)
      let bu := Finset.univ.filter A
      let bm := Finset.univ.filter (fun b=>¬A b)
      have hadmitU : ∀ b∈bu,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty → A b := by
        intro b hb _;exact (Finset.mem_filter.mp hb).2
      have hadmitM : ∀ b∈bm,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty →
          ¬A b ∧ ActualMixedPrice.MixedPaid Geometry.h contact d (2*a-1,response b) := by
        intro b hb hneBin
        have hnA := (Finset.mem_filter.mp hb).2
        refine ⟨hnA,?_⟩
        rcases actual_upper_sector_or_mixed hh hh' hx (by linarith : (1/2:ℝ) ≤ d) hdh
          (amplitude_original_domain D F Z d a rows z b hd geom.2.1 geom.2.2.1 hneBin) with hU|hM
        · exact False.elim (hnA hU)
        · exact hM
      have rawU := hu.2 idx grid hsel k hk i hi j hne (by linarith : (1/2:ℝ) ≤ d) hdh x z hxz hzz hzim
        bu hadmitU hh hh' hell P.eps P.eps_pos.le P.mesh_pos.le feeUpper
      have rawM := hm.2 idx grid hsel k hk i hi j hne hd19 hdh x z hxz hzz hzim bm hadmitM fee
      have htU : Cycle090.theta-1/250000000 ≤ target := by dsimp [target];norm_num [reserve] at htarget ⊢;linarith
      have hU := rawU.trans (normalize Cu mu _ hCu.le (by dsimp [S];linarith) (by dsimp [degree];omega) htU)
      have hM := rawM.trans (normalize Cm mm _ hCm.le (by dsimp [S];linarith) (by dsimp [degree];omega) htarget)
      rw [NaturalPacketLow.natural_packet_amplitude_partition D F rows η Z d a x z (Z^Geometry.y),
        phase_sum_split Finset.univ A]
      calc
        _  ≤  rhs S degree target+rhs S degree target := add_le_add hU hM
        _ = _ := by dsimp [rhs];ring
  have he : -4*Geometry.ell/25=-(4/25:ℝ)*Geometry.ell := by ring
  simpa only [Real.rpow_natCast,he] using hbound

end QRH.Cycle092.Final
#print axioms QRH.Cycle092.Final.actual_finite_of_mixed
