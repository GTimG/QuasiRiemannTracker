/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Numerator.Source.OldSelected
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.HighRows.WeightedSourceSelection
import Candidate.Cycle25.Assembly.HighData
import Candidate.Cycle25.Assembly.Count.MaskedCount

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Numerator_Source_OldClass : Cycle63.AffineLedger := Cycle153.Root.rootLedger


noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle153Endpoint.Numerator.Source
open Cycle153Endpoint.Arithmetic Cycle153Endpoint.Numerator.OldFourth
open Cycle25.Numerator
open OAI OAI.SevenEighths Cycle153EndpointDetectorCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle153EndpointProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

lemma old_whole_slots (D : BaselineData)
    (hfine : ∀j,D.length j ≤ Cycle25.sourceMesh D.t/200)
    (d v delta : ℝ) (hd : d0 ≤ d ∧ d ≤ dMinus) (hv : 0 ≤ v) (hdelta : 0 ≤ delta)
    (main : Finset (Fin D.N)) (g : Fin D.N → ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ delta/2) (herror : ∀j,j ∉ main → g j=0) :
    let widths := fun j=>D.length j/d
    let q := weightedMean Finset.univ widths g
    q=(∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ delta/2 ∧
    ∃selected : Finset (Fin D.N),selected ⊆ main ∧ (∀j∈selected,0<g j) ∧
      (∑j∈selected,widths j) ≤ capOld D.momentKappa d v ∧
      q*capOld D.momentKappa d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      q*capOld D.momentKappa d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      ∀U:ℝ,1 ≤ U → ∀Q:Fin D.N → ℂ,
        (∀j,0<g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*capOld D.momentKappa d v-delta*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hdp:=d0_pos.trans_le hd.1
  let widths:=fun j=>D.length j/d
  have hsum:(∑j,widths j)=ell/d:=by dsimp [widths];rw [←Finset.sum_div,D.slots_sum]
  have hL:0<∑j,widths j:=by rw [hsum];exact div_pos ell_pos hdp
  have hw (j:Fin D.N):0 ≤ widths j:=(div_pos (D.slots_pos j) hdp).le
  have hm:=Cycle25.sourceMesh_pos D.t_pos
  have hwm (j:Fin D.N):widths j ≤ Cycle25.sourceMesh D.t :=
    Cycle153Endpoint.Numerator.Fourth.rescaled_slot_mesh D (Cycle25.sourceMesh D.t) d
      hd.1 hfine j
  have hcap:capOld D.momentKappa d v ≤ ∑j,widths j:=by rw [hsum];exact capOld_le_supply D.momentKappa_lo hd hv
  obtain ⟨hq,hqtop⟩:=weightedMean_bounds Finset.univ widths g delta (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTcap,hgain,hspike⟩:=WeightedQRH.WeightedSlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta (Cycle25.sourceMesh D.t) (capOld D.momentKappa d v)
    hdelta hm.le (fun j _=>hw j) (fun j _=>hwm j) hL (fun j _=>hg j)
    (fun j _=>herror j) (capOld_nonneg D.momentKappa d v) hcap
  refine ⟨?_,hq,hqtop,T,hT,hTpos,hTcap,hgain,hgain,?_⟩
  · unfold weightedMean;rw [hsum]
  · intro U hU Q hQ;exact hspike U hU Q (fun j _=>hQ j)

theorem old_source_class_main_selection (D : BaselineData)
    (F : BaselineSourceData D)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : d0  ≤  d ∧ d  ≤  dMinus) (hv : 0  ≤  v) (hδ : 0  ≤  δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=>D.length j/d) (WeightedQRH.maskedGain main g)
    0  ≤  q ∧ q  ≤  δ/2 ∧ ∃selected : Finset (Fin D.N),selected ⊆ main ∧
      (∑j∈selected,D.length j/d)  ≤  capOld D.momentKappa d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*capOld D.momentKappa d v-
          δ*Cycle25.sourceMesh D.t)  ≤  ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t))  →
          ‖∏j∈main,Q u j‖  ≤  (Z^d)^(q*(Cycle153Endpoint.Arithmetic.ell/d)+D.t*(Cycle153Endpoint.Arithmetic.ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := d0_pos.trans_le hd.1
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0  ≤  g j ∧ g j  ≤  δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := WeightedQRH.amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0  ≤  WeightedQRH.maskedGain main g j ∧ WeightedQRH.maskedGain main g j  ≤  δ/2 := by
    intro j
    unfold WeightedQRH.maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    old_whole_slots D hfine d v δ hd hv hδ main
      (WeightedQRH.maskedGain main g) hg (fun j hj=>by simp [WeightedQRH.maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)=g j := by
    have he := WeightedQRH.amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [WeightedQRH.maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : WeightedQRH.maskedGain main g j=g j := by simp [WeightedQRH.maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.length j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_pos j) hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.length j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := WeightedQRH.masked_main_product_upper main (fun j=>D.length j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_pos j) hdpos).le)
      (by rw [hL];exact div_pos Cycle153Endpoint.Arithmetic.ell_pos hdpos) (by
        intro j hj
        calc
          _  ≤  (Z^(D.length j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh

theorem old_source_selected_product_crude (D : BaselineData)
    (Z d v δ : ℝ) (hZ : 1<Z) (hd : d0≤d ∧ d≤dMinus) (hv : 0≤v)
    (hδ : 0≤δ) (hδtop : δ≤3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N→ℂ)
    (hcap : (∑j∈selected,D.length j/d)≤ capOld D.momentKappa d v)
    (hQ : ∀j,‖Q j‖≤(Z^(D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖≤Z^d := by
  have hdp := d0_pos.trans_le hd.1
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0<D.momentKappa := by linarith [D.momentKappa_lo]
  have hc : capOld D.momentKappa d v≤1 := by
    unfold capOld
    apply max_le (by norm_num)
    apply (div_le_iff₀ (by positivity : 0<6*D.momentKappa)).mpr
    linarith [min_le_left (1:ℝ) (2*y/d-1),D.momentKappa_lo]
  have hsum : (∑j∈selected,D.length j)≤d := by
    rw [←Finset.sum_div] at hcap
    exact (div_le_one hdp).mp (hcap.trans hc)
  calc
    _ ≤ ∏j∈selected,Z^(D.length j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
      intro j hj
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      apply mul_le_mul_of_nonneg_left _ (D.slots_pos j).le
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds (Z^(D.length j)) (δ/2) D.t (Q j) (by positivity)).2
      linarith
    _ = Z^((∑j∈selected,D.length j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hm := mul_le_mul_of_nonneg_right hsum (by linarith [D.t_pos] : 0≤δ/2+D.t)
      have he : δ/2+D.t≤1 := by linarith [D.t_small]
      nlinarith

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem old_source_packet_amplitude_class (D:BaselineData)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀(Z d:ℝ),1<Z  →  d0 ≤ d  →  d ≤ dMinus  →  U=Z^d  →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  →
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  →
      (∀P:∀i:J,WeightedQRH.Numerator.sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  →
      (∀i P,P∈WeightedQRH.Numerator.sourcePrimePool F Z i → IsCoprime P.val η.modulus)  →
      (∀i:J,WeightedQRH.Numerator.sourcePrimePool F Z i.val)  →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (WeightedQRH.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  →
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  →
      (∑i:rows',‖WeightedQRH.Numerator.labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>WeightedQRH.Numerator.sourcePrimePool F Z s.val) (fun s=>WeightedQRH.Numerator.source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*(∏s∈main,Q i.val s)‖)  ≤
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle153Endpoint.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
            (3*R+1+D.t+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle153Endpoint.Arithmetic.ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := old_source_packet_selected_bin D F hbeta hkbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (WeightedQRH.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδtop : 2*a-1 ≤ 3/4 := by linarith
  have hU0 : 0<U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := old_source_class_main_selection D F hfine Z d ((j:ℝ)*D.t+D.t+D.t) (2*a-1)
    hZ ⟨hd,hdmax⟩ (by positivity) hδ z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected ⊆ main ∧
      (∑s∈selected,D.length s/d) ≤ capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t) ∧
      ∀u∈rows',
        (Z^d)^(2*q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-
          (2*a-1)*Cycle25.sourceMesh D.t) ≤ ‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖ ≤ (Z^(D.length s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  →
          ‖∏s∈main,Q u s‖ ≤ (Z^d)^(q*(Cycle153Endpoint.Arithmetic.ell/d)+D.t*(Cycle153Endpoint.Arithmetic.ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(Cycle153Endpoint.Arithmetic.ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖ ≤ U^(q*(Cycle153Endpoint.Arithmetic.ell/d)) := by
    apply WeightedQRH.Numerator.upper_bin_normalized (Pmain i) U (q*(Cycle153Endpoint.Arithmetic.ell/d)) (D.t*(Cycle153Endpoint.Arithmetic.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) :
      (∑s∈selected j,D.length s/d)  ≤  capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t) := by
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) (i:rows') :
      U^(q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-
        ((2*a-1)*Cycle25.sourceMesh D.t/2))  ≤  ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    exact WeightedQRH.squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖ ≤ U := by
    rw [hUZ]
    exact old_source_selected_product_crude D Z d ((j:ℝ)*D.t+D.t+D.t) (2*a-1) hZ ⟨hd,hdmax⟩ (by positivity) hδ hδtop (selected j) (Q i.val)
      (hcapacity j) (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := WeightedQRH.Numerator.restore_upper_bin_loss Finset.univ
    (fun i:rows'=>WeightedQRH.Numerator.labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>WeightedQRH.Numerator.sourcePrimePool F Z s.val) (fun s=>WeightedQRH.Numerator.source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))) Pmain U (D.t*(Cycle153Endpoint.Arithmetic.ell/d))
    (D.t+q*(Cycle153Endpoint.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*(D.t+D.t)/2)
    (C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore

end Cycle153Endpoint.Numerator.Source
