/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B001
import Submissions.gao_cycle61_plane_20261013.Bundles.B057
import Submissions.gao_cycle61_plane_20261013.Bundles.B058
import Submissions.gao_cycle61_plane_20261013.Bundles.B066
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/- BEGIN ORIGINAL Cycle61.Numerator.Source.ActualBin; sha256 5b7e3b3c0446ea859f6ccfc829c600f09e5d24218d23d100d8880b891f075a6e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                  
                                           

noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Numerator.Capacity Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem actual_label_packet_bin_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp dp Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤alpha → alpha≤1 → 0<eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0<a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0<Y →
      ∀(d U xi ann : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L delta loss momentEps Ccount Cmoment : ℝ),
      dMinus≤d ∧ d≤dPlus → 1≤U → 0≤xi → 0≤ann → 1≤Ccount → 1≤Cmoment → 0≤q → q≤delta/2 →
      0≤delta/2 → delta/2≤1 →
      1-alpha-6*eps≤1/2-delta/2 → -(1/100:ℝ)≤1/2-delta/2 →
      1+firsteps≤x.re+(1/2-delta/2) → 0<Ccond →
      (∀i,0≤Cu i) → (∀i,Cu i≤Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*scheduledCapacity d (2*((j:ℝ)*xi+xi+ann))-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*zeroCapacity d/2+(3*R+1+momentEps)/4+loss/2+delta*(xi+ann)/2) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY d U xi ann n Cu Ccond Q P
    R q L delta loss momentEps Ccount Cmoment hd hU hxi hann hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=>physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0<N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0<M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ)<(Ideal.span {(u i).val}:Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast FiniteConductor.absNorm_le_of_le (Ideal.le_radical (I := (Ideal.span {(u i).val}:Ideal O)))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/2) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2))≤M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤b*Y) :
      max 1 (Lc i*N i e)≤U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := packet_weighted_bins (fun i=>labelPacketBase S (u i) T Pbase) A Sp N hNp Lc d U xi ann n
    (fun i e=>N i e≤b*Y) Q P R q L delta loss momentEps Ccount Cmoment M hd hM hU hxi hann hc hm
    hq hqdelta hcard hzoff hupp hseries (fun i=>(hms i).1) hmassU hselected hfull hselection
  have heq : (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) =
      Y^(-(1/2:ℝ))*(∑i,‖(∑'e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold labelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)


end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.ActualBin -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Parameters; sha256 0007e9bd8ce421ec86e256085f60f68aa27af66d7318ad6b177b7b2fe6de0192 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                         
                                      
                                      

noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic
open OAI OAI.SevenEighths Cycle61DetectorCount HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧
    -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he:=D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

lemma source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

lemma source_cutoff_le_base (b : ℝ) (hb : 0≤b) :
    ∀ᶠU:ℝ in atTop,1<U ∧ ∀d:ℝ,(1/2:ℝ)≤d → b*U^(y/d)≤U := by
  have he : ∀ᶠU:ℝ in atTop,b≤U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0<d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=by norm_num [y]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Parameters -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.SelectedBin; sha256 32b98b7697a0848390cc4c2b563ec1892595961b0bce302f7011e529d8be18f0 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                          

/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle61.Arithmetic Cycle61.Numerator.Capacity Cycle61.Numerator.Fourth
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount Cycle61DetectorCount
local notation "O" => HeckeFamily.O

theorem source_packet_selected_bin (D : BaselineData)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j≤ mesh/200)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → dMinus≤d → d≤dPlus → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤height → |z.im|≤height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤q → q≤(2*a-1)/2 → 1≤Ccount → (rows.card:ℝ)≤Ccount*U^R →
      (∀i,‖P i‖≤U^(q*(Cycle61.Arithmetic.ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.length s/d)≤ scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖≤U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
            (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
  obtain ⟨Cm,hCm,hpacket⟩ := actual_label_packet_bin_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := baseline_active_box_fourth D F hbeta hkbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,source_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [BaselineData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num [dMinus,Cycle61.Arithmetic.h]) hd
  have hdhalf : (1/2:ℝ)≤d := (by norm_num [dMinus,Cycle61.Arithmetic.h] : (1/2:ℝ)≤dMinus).trans hd
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
  have hwmax (s : Fin D.N) : D.length s/d≤Cycle25.sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos D.t_pos
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤Z^(D.length s.val) := Real.one_le_rpow hZ.le (D.slots_pos s.val).le
  have hY : 0<U^(y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(y/d)≤U^((coefficientBoxCount D.t:ℝ)*D.t) := by
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
          (U^(D.length s.val/d)) z)‖≤U
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

  have hCM : 1≤Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.length s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>source_complex_profile_norm D F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(y/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY d U D.t D.t (coefficientBoxCount D.t) Cu Ccond Q P
    R q (Cycle61.Arithmetic.ell/d) (2*a-1) selLoss (D.t+affineError+D.t) Ccount
    (Cr'*(1+height)^degree) ⟨hd,hdmax⟩ hmom.1.le D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull (by simpa only [add_assoc] using hmomentInput)
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) =
      U^D.t*U^(q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end Cycle61.Numerator.Source

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

end
/- END ORIGINAL Cycle61.Numerator.Source.SelectedBin -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MaskedCount; sha256 484525dd10b6ef7995edb6020839f34d737077b5d6b52921264439b15569b51b -/
section
                                      
                                                                  
                                                               
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators

theorem coefficient_antitone {κ x y : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : coefficient y κ≤coefficient x κ := by
  have hdx : 0<denominator x κ := lt_of_lt_of_le (by norm_num) (denominator_lower hx (hxy.trans hy) hk hk1)
  have hdy : 0<denominator y κ := lt_of_lt_of_le (by norm_num) (denominator_lower (hx.trans hxy) hy hk hk1)
  let a : ℝ := 1/(3*κ)
  have ha : 0≤a := by dsimp [a]; positivity
  have ha1 : a≤10/21 := (div_le_iff₀ (show 0<3*κ by linarith)).mpr (by linarith)
  have hbx : b x κ=x*a := by unfold b; dsimp [a]; ring
  have hby : b y κ=y*a := by unfold b; dsimp [a]; ring
  have he : primeWeight x κ*denominator y κ-primeWeight y κ*denominator x κ=
      (y-x)*(4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y) := by
    unfold primeWeight denominator
    rw [hbx,hby]
    ring
  have hsum : x+y≤1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum ha
  have hp : 0≤4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y := by
    have hp := mul_nonneg (mul_nonneg (mul_nonneg ha (by linarith : 0≤1+2*a)) hx) (hx.trans hxy)
    nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hp
  unfold coefficient
  apply (div_le_div_iff₀ hdy hdx).mpr
  linarith

theorem rowCount_antitone {δ κ x y : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : rowCount δ y κ≤rowCount δ x κ := by
  have hc := coefficient_antitone hk hk1 hx hxy hy
  have hcx := coefficient_nonneg hx (hxy.trans hy) hk hk1
  have hcy := coefficient_nonneg (hx.trans hxy) hy hk hk1
  have hv : 0<V δ := by unfold V; linarith
  have hdx : 0<2*(V δ+δ*coefficient x κ) := by positivity
  have hdy : 0<2*(V δ+δ*coefficient y κ) := by positivity
  unfold rowCount
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ hdy hdx).mpr
  have hh := mul_nonneg (mul_nonneg hδ (sq_nonneg (V δ))) (sub_nonneg.mpr hc)
  nlinarith
def maskedGain {α : Type*} [DecidableEq α] (main : Finset α) (g : α→ℝ) (i : α) : ℝ :=
  if i∈main then g i else 0

theorem maskedMean_bounds {α : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (δ : ℝ)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2) :
    0 ≤ weightedMean slots width (maskedGain main g) ∧
    weightedMean slots width (maskedGain main g) ≤ weightedMean slots width g ∧
    weightedMean slots width g ≤ δ/2 := by
  have hmasked : ∀j∈slots,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j hj
    unfold maskedGain
    split_ifs with hm
    · exact hg j hj
    · have hh := hg j hj
      exact ⟨le_rfl,by linarith⟩
  have hb := weightedMean_bounds slots width (maskedGain main g) δ hw hL hmasked
  have hfull := weightedMean_bounds slots width g δ hw hL hg
  refine ⟨hb.1,?_,hfull.2⟩
  unfold weightedMean
  apply div_le_div_of_nonneg_right _ hL.le
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  unfold maskedGain
  split_ifs with hm
  · exact le_rfl
  · exact (hg j hj).1

/-- A card bound in the original full physical bins remains true at the
weaker diluted main-slot mean. Both means divide by the full slot length. -/
theorem masked_row_count_transfer {α ι : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (rows : Finset ι)
    (δ κ U C loss : ℝ) (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2)
    (hcard : (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width g/δ) κ+loss)) :
    (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width (maskedGain main g)/δ) κ+loss) := by
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width g δ hw hL hg
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply rowCount_antitone hδ.le hδtop hk hk1
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    linarith


/-- Every amplitude in a nonempty original class equals its fixed bin value. -/
theorem amplitude_class_value {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0 < mesh) (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots cap mesh) (u : Row)
    (hu : u∈HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U cap mesh hm width Q bin)
    (j : Slot) (hj : j∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(width j)) cap mesh (Q u j)=
      HeckeDetectorFiberPartition.binValue slots cap mesh bin j := by
  have he := (Finset.mem_filter.mp hu).2
  have hv := congrArg (fun f : HeckeDetectorFiberPartition.BinLabel slots cap mesh=>(f ⟨j,hj⟩).val) he
  simpa only [HeckeDetectorFiberPartition.amplitudeLabel,HeckeDetectorFiberPartition.binValue,
    dite_eq_left hj] using hv

/-- Direct count transfer on an actual full amplitude class. The full bin is
retained, while main amplitudes are zeroed only after the count is proved. -/
theorem masked_amplitude_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(rowCount δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ) κ+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(rowCount δ (q/δ) κ+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  exact masked_row_count_transfer slots main width _ _ δ κ U C loss hδ hδtop hk hk1 hU hC hw hL hg hcard

end
end OAI.SevenEighths.Cycle25DetectorRowCount

end
/- END ORIGINAL Cycle25.Assembly.Count.MaskedCount -/
