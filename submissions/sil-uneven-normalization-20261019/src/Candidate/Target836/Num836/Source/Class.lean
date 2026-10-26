import Candidate.Target836.Num836.Source.Parameters
import Candidate.Cycle25.Numerator.SourceSelection

/- Original module: Candidate.Target836.Num836.Source.Selection. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
open scoped Classical BigOperators
namespace Target836.Numerator.Source
open Target836.Arithmetic Target836.Numerator.Capacity
open Cycle25.Numerator
open OAI OAI.SevenEighths Target836DetectorCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

lemma scheduled_whole_slots (D : BaselineData)
    (hfine : ∀j,D.length j ≤ Cycle25.sourceMesh D.t/200)
    (d v delta : ℝ) (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) (hdelta : 0 ≤ delta)
    (main : Finset (Fin D.N)) (g : Fin D.N → ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ delta/2) (herror : ∀j,j ∉ main → g j=0) :
    let widths := fun j=>D.length j/d
    let q := weightedMean Finset.univ widths g
    q=(∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ delta/2 ∧
    ∃selected : Finset (Fin D.N),selected ⊆ main ∧ (∀j∈selected,0< g j) ∧
      (∑j∈selected,widths j) ≤ scheduledCapacity d v ∧
      q*scheduledCapacity d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      q*scheduledCapacity d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      ∀U:ℝ,1 ≤ U → ∀Q:Fin D.N → ℂ,
        (∀j,0< g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) → 
        U^(2*q*scheduledCapacity d v-delta*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hdp:=Target836.Physical.physical_d_pos hd.1
  let widths:=fun j=>D.length j/d
  have hsum:(∑j,widths j)=ell/d:=by dsimp [widths];rw [←Finset.sum_div,D.slots_sum]
  have hL:0<∑j,widths j:=by rw [hsum];exact div_pos ell_pos hdp
  have hw (j:Fin D.N):0 ≤ widths j:=(div_pos (D.slots_pos j) hdp).le
  have hm:=Cycle25.sourceMesh_pos D.t_pos
  have hwm (j:Fin D.N):widths j ≤ Cycle25.sourceMesh D.t :=
    Target836.Numerator.Fourth.rescaled_slot_mesh D (Cycle25.sourceMesh D.t) d
      ((by norm_num [dMinus,h] : (1/200:ℝ) ≤ dMinus).trans hd.1) hfine j
  have hcap:scheduledCapacity d v ≤ ∑j,widths j:=by rw [hsum];exact scheduledCapacity_le_supply hd hv
  obtain ⟨hq,hqtop⟩:=weightedMean_bounds Finset.univ widths g delta (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTcap,hgain,hspike⟩:=SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta (Cycle25.sourceMesh D.t) (scheduledCapacity d v)
    hdelta hm.le (fun j _=>hw j) (fun j _=>hwm j) hL (fun j _=>hg j)
    (fun j _=>herror j) (scheduledCapacity_nonneg hd hv) hcap
  refine ⟨?_,hq,hqtop,T,hT,hTpos,hTcap,hgain,hgain,?_⟩
  · unfold weightedMean;rw [hsum]
  · intro U hU Q hQ;exact hspike U hU Q (fun j _=>hQ j)

theorem source_class_main_selection (D : BaselineData)
    (F : BaselineSourceData D)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : dMinus  ≤  d ∧ d  ≤  dPlus) (hv : 0  ≤  v) (hδ : 0  ≤  δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main g)
    0  ≤  q ∧ q  ≤  δ/2 ∧ ∃selected : Finset (Fin D.N),selected ⊆ main ∧
      (∑j∈selected,D.length j/d)  ≤  scheduledCapacity d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*scheduledCapacity d v-
          δ*Cycle25.sourceMesh D.t)  ≤  ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t))  → 
          ‖∏j∈main,Q u j‖  ≤  (Z^d)^(q*(Target836.Arithmetic.ell/d)+D.t*(Target836.Arithmetic.ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := Target836.Physical.physical_d_pos hd.1
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0  ≤  g j ∧ g j  ≤  δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0  ≤  maskedGain main g j ∧ maskedGain main g j  ≤  δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    scheduled_whole_slots D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=>by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.length j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_pos j) hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.length j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=>D.length j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_pos j) hdpos).le)
      (by rw [hL];exact div_pos Target836.Arithmetic.ell_pos hdpos) (by
        intro j hj
        calc
          _  ≤  (Z^(D.length j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


theorem source_selected_product_crude (D : BaselineData)
    (Z d δ : ℝ) (hZ : 1 < Z) (hd : dMinus  ≤  d) (hδ : 0  ≤  δ) (hδ' : δ  ≤  3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N → ℂ)
    (hQ : ∀j,‖Q j‖  ≤  (Z^(D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖  ≤  Z^d := by
  have hdhalf : (1/2:ℝ) ≤ d := (by norm_num [dMinus,h] : (1/2:ℝ) ≤ dMinus).trans hd
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := D.t_pos
  have hlength : ∑j∈selected,D.length j  ≤  (1/5:ℝ) := by
    apply le_trans _ (by norm_num [Target836.Arithmetic.ell] : Target836.Arithmetic.ell ≤ (1/5:ℝ))
    rw [←D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _=>(D.slots_pos j).le)
  calc
    _  ≤  ∏j∈selected,Z^(D.length j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(D.length j)) (δ/2) D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t  ≤  δ/2+D.t)
        (D.slots_pos j).le
    _ = Z^((∑j∈selected,D.length j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _  ≤  Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength
        (by positivity : 0  ≤  δ/2+D.t)
      nlinarith only [hh,hδ',D.t_small,hdhalf]


end Target836.Numerator.Source

#print axioms Target836.Numerator.Source.scheduled_whole_slots
#print axioms Target836.Numerator.Source.source_class_main_selection
#print axioms Target836.Numerator.Source.source_selected_product_crude
end

/- Original module: Candidate.Target836.Num836.Source.SelectedBin. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace Target836.Numerator.Source
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Target836.Arithmetic Target836.Numerator.Capacity Target836.Numerator.Fourth
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount Target836DetectorCount
local notation "O" => HeckeFamily.O

theorem source_packet_selected_bin (D : BaselineData)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (bPhi mesh affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j≤ mesh/200)
    (hfine : ∀j,D.length j≤ Cycle25.sourceMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → dMinus≤ d → d≤ dPlus → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤ q → q≤(2*a-1)/2 → 1≤ Ccount → (rows.card:ℝ)≤ Ccount*U^R →
      (∀i,‖P i‖≤ U^(q*(Target836.Arithmetic.ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.length s/d)≤ scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖≤ U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Target836.Arithmetic.ell/d)-q*zeroCapacity d/2+
            (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
  obtain ⟨Cm,hCm,hpacket⟩ := actual_label_packet_bin_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := baseline_active_box_fourth D F hbeta hkbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤ Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,source_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [BaselineData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num [dMinus,Target836.Arithmetic.h]) hd
  have hdhalf : (1/2:ℝ)≤ d := (by norm_num [dMinus,Target836.Arithmetic.h] : (1/2:ℝ)≤ dMinus).trans hd
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.length s/d)=Z^(D.length s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by dsimp only [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  let Ts (s : J) := sourcePrimePool F Z s.val
  let hTs := fun s:J=>source_prime_pool_outside F Z s.val
  let Q (j : ℕ) (i : rows) := ∏s∈selected j,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(D.length s.val/d)) z) = Q j i := by
    calc
      _ = ∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (Z^(D.length s.val)) z := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hscale s.val]
      _ = _ := by
        exact Finset.prod_coe_sort (selected j)
          (fun s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z)
  have hwpos (s : Fin D.N) : 0 < D.length s/d := div_pos (D.slots_pos s) hd0
  have hwmax (s : Fin D.N) : D.length s/d≤ Cycle25.sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos D.t_pos
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤ Z^(D.length s.val) := Real.one_le_rpow hZ.le (D.slots_pos s.val).le
  have hY : 0< U^(y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(y/d)≤ U^((coefficientBoxCount D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hdhalf).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (coefficientBoxCount_extent D.t D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
        dilationBox U D.t (coefficientBoxCount D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+D.t+affineError+D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun s=>D.length s.val/d) (fun _=>z) height
      (fun s=>hwpos s.val) (fun s=>rescaled_slot_mesh D mesh d (by linarith only [hdhalf]) hfineAffine s.val) (fun s=>hwmax s.val) (fun _=>hz) hheight (fun _=>hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=>D.length s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.length s.val/d)) z)‖≤ U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+affineError+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
      dilationBox U D.t (coefficientBoxCount D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤ Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.length s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>source_complex_profile_norm D F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(y/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY d U D.t D.t (coefficientBoxCount D.t) Cu Ccond Q P
    R q (Target836.Arithmetic.ell/d) (2*a-1) selLoss (D.t+affineError+D.t) Ccount
    (Cr'*(1+height)^degree) ⟨hd,hdmax⟩ hmom.1.le D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull (by simpa only [add_assoc] using hmomentInput)
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(Target836.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) =
      U^D.t*U^(q*(Target836.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end Target836.Numerator.Source

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

#print axioms Target836.Numerator.Source.source_packet_selected_bin
end

/- Original module: Candidate.Target836.Num836.Source.Class. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 2600000
open scoped Classical BigOperators ContDiff
open Filter
namespace Target836.Numerator.Source
open Target836.Arithmetic Target836.Numerator.Capacity Target836.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Target836DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem source_packet_amplitude_class (D:BaselineData)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa)
    (bPhi mesh affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z  →  dMinus ≤ d  →  d ≤ dPlus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*(∏s∈main,Q i.val s)‖)  ≤ 
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Target836.Arithmetic.ell/d)-q*zeroCapacity d/2+
            (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Target836.Arithmetic.ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := source_packet_selected_bin D F hbeta hkbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδtop : 2*a-1 ≤ 3/4 := by linarith
  have hU0 : 0< U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := source_class_main_selection D F hfine Z d (2*((j:ℝ)*D.t+D.t+D.t)) (2*a-1)
    hZ ⟨hd,hdmax⟩ (by positivity) hδ z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected ⊆ main ∧
      (∑s∈selected,D.length s/d) ≤ scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t)) ∧
      ∀u∈rows',
        (Z^d)^(2*q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-
          (2*a-1)*Cycle25.sourceMesh D.t) ≤ ‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖ ≤ (Z^(D.length s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
          ‖∏s∈main,Q u s‖ ≤ (Z^d)^(q*(Target836.Arithmetic.ell/d)+D.t*(Target836.Arithmetic.ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(Target836.Arithmetic.ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖ ≤ U^(q*(Target836.Arithmetic.ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(Target836.Arithmetic.ell/d)) (D.t*(Target836.Arithmetic.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.length s/d)  ≤  scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t)) := by
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-
        ((2*a-1)*Cycle25.sourceMesh D.t/2))  ≤  ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖ ≤ U := by
    rw [hUZ]
    exact source_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=>labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))) Pmain U (D.t*(Target836.Arithmetic.ell/d))
    (D.t+q*(Target836.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*(D.t+D.t)/2)
    (C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore


end Target836.Numerator.Source

#print axioms Target836.Numerator.Source.source_packet_amplitude_class
end
