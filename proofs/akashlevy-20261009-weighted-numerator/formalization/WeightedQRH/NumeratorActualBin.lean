import WeightedQRH.NumeratorPhysicalPacketMass
import WeightedQRH.NumeratorAmplitudeLoss

/-! The actual physical numerator on a finite amplitude bin. Its only moment
input is a fourth moment of the original row-character polynomial on active
scales; the coefficient masses and all infinite sums are proved here. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

def labelPolynomialPacket {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Yp : ι→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex S u T,
    labelPacketCoefficient S hS η u T hT
      (fun i P=>physicalSlotWeight P.val (W i) (Yp i) z) x z e*
    (labelPacketScale S u T e:ℂ)^(-(1/2:ℂ))*
    HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
      (Y/(labelPacketScale S u T e:ℝ)) 0 0

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
      ∀(U xi : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L zcap delta loss momentEps Ccount Cmoment : ℝ),
      1≤U → 0≤xi → 1≤Ccount → 1≤Cmoment → 0≤q → q≤delta/2 →
      0≤delta/4 → delta/4≤1 →
      1-alpha-6*eps≤1/2-delta/4 → -(1/100:ℝ)≤1/2-delta/4 →
      1+firsteps≤x.re+(1/2-delta/4) → 0<Ccond →
      (∀i,0≤Cu i) → (∀i,Cu i≤Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*selectedCapacity zcap ((j:ℝ)*xi+xi)-loss)≤‖Q j i‖) →
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
          Ccount*Cmoment*U^(q*L-q*zcap/2+(3*R+1+momentEps)/4+loss/2+delta*xi/4) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY U xi n Cu Ccond Q P
    R q L zcap delta loss momentEps Ccount Cmoment hU hxi hc hm hq hqdelta hrho hrho1
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
    alpha eps (delta/4) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/4))≤M := by
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
  have hb := packet_weighted_bins (fun i=>labelPacketBase S (u i) T Pbase) A Sp N hNp Lc U xi n
    (fun i e=>N i e≤b*Y) Q P R q L zcap delta loss momentEps Ccount Cmoment M hM hU hxi hc hm
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

theorem errorLabelNumerator_eq_packet {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y =
      labelPolynomialPacket S hS η u (fun i:J=>T i.val) (fun i=>hT i.val)
        (fun i=>W i.val) (fun i=>Yp i.val) x z W1 Y := by
  exact errorLabelNumerator_reconstruction S hS firsteps hfirst η u hrow J T hT hdis hη hQ
    W Yp x z hx hz hmargin W1 a b ha hsupp hW Y hY

end WeightedQRH.Numerator
