import WeightedQRH.NumeratorSourceParameters
import WeightedQRH.NumeratorActiveFourth

/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor ProbeFinalAssemblyCertifiedBands
local notation "O" => HeckeFamily.O

theorem source_packet_selected_bin {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine : ∀j,D.ell j≤weighted_detectorMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/2:ℝ)≤d → d≤WeightedQRH.h+rowExtension → U=Z^d →
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
      (∀i,‖P i‖≤U^(q*(ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.ell s/d)≤ selectedCapacity ((2*(ly/d)-1)/(9/2)-4*D.t/9) ((j:ℝ)*D.t+D.t)) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*selectedCapacity ((2*(ly/d)-1)/(9/2)-4*D.t/9) ((j:ℝ)*D.t+D.t)-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z‖≤U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.ell s.val)) x z F.W (U^(ly/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
            (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) := by
  obtain ⟨Cm,hCm,hpacket⟩ := actual_label_packet_bin_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := certified_active_box_fourth F hbeta F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_physical_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [HighParameters.HighData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
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
  let hTs := fun s:J=>source_prime_pool_outside F Z s.val
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
          (fun s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell s)) z)
  have hwpos (s : Fin D.N) : 0 < D.ell s/d := div_pos (D.slots_bounds s).1 hd0
  have hwmax (s : Fin D.N) : D.ell s/d≤weighted_detectorMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := weighted_detectorMesh_pos D.t_pos
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤Z^(D.ell s.val) := Real.one_le_rpow hZ.le (D.slots_bounds s.val).1.le
  have hY : 0<U^(ly/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(ly/d)≤U^((coefficientBoxCount D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hd).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (coefficientBoxCount_extent D.t D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(ly/d) ∧
        dilationBox U D.t (coefficientBoxCount D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(ly/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+2*D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun s=>D.ell s.val/d) (fun _=>z) height
      (fun s=>hwpos s.val) (fun s=>hwmax s.val) (fun _=>hz) hheight (fun _=>hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=>D.ell s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.ell s.val/d)) z)‖≤U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    simp only [show 1+D.t+D.t=1+2*D.t by ring] at hh'
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(ly/d) ∧
      dilationBox U D.t (coefficientBoxCount D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(ly/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.ell s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>source_complex_profile_norm F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(ly/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY U D.t (coefficientBoxCount D.t) Cu Ccond Q P
    R q (ell/d) ((2*(ly/d)-1)/(9/2)-4*D.t/9) (2*a-1) selLoss (2*D.t) Ccount
    (Cr'*(1+height)^degree) hmom.1.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull hmomentInput
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) =
      U^D.t*U^(q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
      (3*R+1+2*D.t)/4+selLoss/2+(2*a-1)*D.t/4) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end WeightedQRH.Numerator
