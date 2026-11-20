/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B046
import Candidate.Bundles.B052
import Candidate.Bundles.B054

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelPacket; sha256 fbb573d9153e8f64563215d9cc6d68cee92e5f70a4ba5d0874cd7a194c9f19a9 -/
section
                                                      
                                                       

/-! The complete coefficient packet after summing all physical error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def labelPrimes (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) :
    Finset ProbePhysical.PrimeIdeal := Finset.univ.image (fun i => (P i).val)

theorem labelSupported (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
    (P : ∀ i, T i) : ∀ Q ∈ labelPrimes T P, Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad _ (hT i _ (P i).property)

def LabelPacketIndex (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) := Σ P : ∀ i, T i, ErrorPacketIndex S u (labelPrimes T P)

def errorPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset ProbePhysical.PrimeIdeal) : ErrorPacketIndex S u T :=
  ⟨(fun _ => 0), (fun _ => 0), ⟨∅, fun _ => 0⟩⟩

def labelPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) : LabelPacketIndex S u T :=
  ⟨P,errorPacketBase S u (labelPrimes T P)⟩

instance labelPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) : Countable (LabelPacketIndex S u T) := by
  unfold LabelPacketIndex
  infer_instance

def labelPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ i P, P ∈ T i → P.val ∉ S) (weight : ∀ i, T i → ℂ) (x z : ℂ)
    (e : LabelPacketIndex S u T) : ℂ :=
  (∏ i, weight i (e.1 i)) *
    errorPacketCoefficient S hS η u (labelPrimes T e.1) (labelSupported S hS T hT e.1) x z e.2

def labelPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (e : LabelPacketIndex S u T) : ℝ≥0 := errorPacketScale S u (labelPrimes T e.1) e.2

theorem labelPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (e : LabelPacketIndex S u T) :
    1 ≤ labelPacketScale S u T e := errorPacketScale_one_le S u (labelPrimes T e.1) e.2

/-- Uniform in every error-label tuple, row, finite exclusion set and height. -/
theorem actual_label_packet_mass (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (weight : ∀ i, T i → ℂ) (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        (C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon) *
          ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  obtain ⟨C,hC,hpref⟩ := coefficient_prefactor_subpower epsilon hepsilon
  refine ⟨C,hC,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
  have hL : 0 ≤ L := div_nonneg hCu0 (mul_nonneg hCcond.le (by positivity))
  let M := C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon
  have hpacket (P : ∀ i, T i) :
      Summable (fun e : ErrorPacketIndex S u (labelPrimes T P) =>
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ∧
      (∑' e : ErrorPacketIndex S u (labelPrimes T P),
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ≤
        M * errorProductSize u (labelPrimes T P) := by
    have hηP : ∀ Q ∈ labelPrimes T P, IsCoprime Q.val η.modulus := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hη i _ (P i).property
    have hQP : ∀ Q ∈ labelPrimes T P, (4 : ℝ) ≤ Q.val.absNorm := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact_mod_cast hS.tail.norm_four _ (hT i _ (P i).property)
    have hc := actual_conductor_packet_cap u (labelPrimes T P) (labelSupported S hS T hT P)
      Ccond Cu hCcond hCu
    obtain ⟨hs,hm⟩ := error_packet_damped_mass S hS firsteps hfirst η u (labelPrimes T P)
      (labelSupported S hS T hT P) hηP x z alpha eps rho L hQP halpha halpha1 heps heps1 hx hz
      hrho hrho1 hline hleft hmargin hL hc
    refine ⟨hs,hm.trans ?_⟩
    have hp := mul_le_mul_of_nonneg_right (hpref (markExclusions S (labelPrimes T P)) u)
      (errorProductSize_nonneg u (labelPrimes T P))
    simpa only [mul_assoc,M] using hp
  have hh := finite_label_damped_mass
    (fun P => errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z)
    (fun P e => (errorPacketScale S u (labelPrimes T P) e : ℝ))
    (fun P e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u (labelPrimes T P) e))
    (fun P => ∏ i, weight i (P i)) (fun P => errorProductSize u (labelPrimes T P)) L rho M
    (fun P => (hpacket P).1) (fun P => (hpacket P).2)
  refine ⟨hh.1,?_⟩
  change _ ≤ M * _
  exact hh.2.trans_eq (congrArg (fun t : ℝ => M*t) (error_label_mass_factor u T hdis weight))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelPacket -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorIntegral; sha256 7dbe518afc46e6c6b48f757cbf95984be86a51f855546f3e2242af4e53ed896e -/
section
                                                       

/-! The actual complete-w error numerator, bounded after reconstructing its
Dirichlet polynomial.  No pointwise bound on L along the central line is used. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def errorNumeratorIntegral (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
    (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
    HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
    ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
        η u x ((1 / 2 : ℂ) + t * I) z))

theorem actual_error_numerator_bound (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y M : ℝ) (hY : 0 < Y) (hM : 0 ≤ M)
    (hpoly : ∀ N : ℝ, 1 ≤ N → N ≤ b * Y →
      ‖HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W (Y / N) 0 0‖ ≤
        M * max 1 (L * N)^rho) :
    ‖errorNumeratorIntegral S hS η u T hT x z W Y‖ ≤
      Y^(-(1 / 2 : ℝ)) * (M * (2 *
        (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) * errorProductSize u T))) := by
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hmarginc : 1 + firsteps ≤ x.re + 1 / 2 := by linarith
  have he := actual_error_packet_mellin S hS firsteps hfirst η u hrow T hT hη x z hQ
    hx' hz.ge hmarginc W a b ha hsupp hW Y hY
  change ‖_‖ ≤ _
  rw [show errorNumeratorIntegral S hS η u T hT x z W Y = _ from he]
  obtain ⟨hmass,hmb⟩ := error_packet_damped_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho L hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hL hcap
  apply reconstructed_numerator_bound (rowCharacter S hS.prime u) W a b Y L rho M _
    hsupp hY hM (errorPacketCoefficient S hS η u T hT x z)
    (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) hmass hmb
  intro e hecut
  exact hpoly _ (by exact_mod_cast errorPacketScale_one_le S u T e) hecut

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorIntegral -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorIntegrable; sha256 521057b704b7aa1f0ffa22f43bbec20d54a2a236355d782dd2fc10a1f0c69ca4 -/
section
                                                   
                                                          

/-! Absolute integrability before the finite error subsets are interchanged. -/
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem actual_error_packet_integrable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (hη : ∀P∈T,IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀P∈T,(4:ℝ)≤P.val.absNorm)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*I)*
      ((∏P:T,rawErrorSlot η u P.val (hT P.val P.property) x ((1/2:ℂ)+t*I) z)*
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x ((1/2:ℂ)+t*I) z)) := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1/2:ℂ)+t*I) z hQ hx hz (by simp;norm_num) (by simpa using hmargin)
  simp_rw [he]
  simp only [HeckeOrigin.continued,ite_eq_right hrow]
  have hh := MellinReconstruction.coefficient_series_integrable
    (errorPacketCoefficient S hS η u T hT x z) (fun e=>(errorPacketScale S u T e:ℝ))
    (fun e=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) (1/2)
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)
    _ (MellinReconstruction.reconstruction_kernel_integrable (rowCharacter S hS.prime u) hrow
      W a b ha hsupp hW Y hY)
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh

def finsetImageEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α→β) (hf : Function.Injective f) : s≃s.image f :=
  Equiv.ofBijective (fun i:s=>⟨f i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩)
    ⟨by intro i j hij;apply Subtype.ext;exact hf (congrArg Subtype.val hij),by
      intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩⟩

theorem error_product_image {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val) (x w z : ℂ) :
    (∏i∈I,rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z := by
  rw [←Finset.prod_coe_sort I]
  exact Fintype.prod_equiv (finsetImageEquiv I P hP) _ _ (fun _=>rfl)

theorem weightedErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I P hPS W Yp x w z=
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)*
      ((∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (I.image P))
          (markedSourceExclusions S hS (I.image P)) η u x w z) := by
  unfold weightedErrorTuple
  rw [Finset.prod_mul_distrib,error_product_image S hS η u I P hP hPS hT]
  ring


theorem weightedErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (P : Fin K → HeckeInverseAmplification.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (hη : ∀Q∈I.image P,IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈I.image P,(4:ℝ)≤Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      weightedErrorTuple S hS η u I P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    (I.image P) hT hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)
  apply hi.congr
  filter_upwards with t
  rw [weightedErrorTuple_packet S hS η u I P hP hPS hT]
  ring

theorem partialErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    partialErrorTuple S hS η u I T hT P W Yp x w z=
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x w z) := by
  have hp : (∏i:I,rawErrorSlot η u (P i).val
      (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z)=
      ∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z := by
    let e : I ≃ Finset.univ.image (fun i:I=>(P i).val) :=
      Equiv.ofBijective (fun i=>⟨(P i).val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
        ⟨by intro i j hij;exact hP (congrArg Subtype.val hij),by
          intro Q
          obtain ⟨i,hi,hieq⟩ := Finset.mem_image.mp Q.property
          exact ⟨i,Subtype.ext hieq⟩⟩
    exact Fintype.prod_equiv e _ _ (fun _=>rfl)
  unfold partialErrorTuple
  rw [Finset.prod_mul_distrib,hp]
  ring

theorem partialErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (hη : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),(4:ℝ)≤Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    _ hTS hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)
  apply hi.congr
  filter_upwards with t
  rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  ring

theorem partialErrorTuple_mellin {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z)=
    (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:I=>(P i).val)) hTS x z W1 Y := by
  simp_rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  unfold errorNumeratorIntegral
  rw [show (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z)))=
      (fun t : ℝ=>(∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
        ((Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z))) by funext t;ring]
  rw [integral_const_mul]
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorIntegrable -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorReconstruction; sha256 63b458af3d864fa21577b08f227b417e37b7c7cfb8772557758099523a3ec78c -/
section
                                                          
                                                     

/-! Exact reconstruction of the actual prime tuples, with finite interchanges
justified before taking any absolute value or splitting rows into amplitudes. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (P : Fin K→HeckeInverseAmplification.PrimeIdeal)
    (hP : ∀i,(P i).val∉S) : ∀Q∈J.image P,Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i) (hP i)

theorem partial_image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:J,T i.val) :
    ∀Q∈Finset.univ.image (fun i:J=>(P i).val),Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)

theorem calibrated_tuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hQ : ∀i,(4:ℝ)≤(P i).val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      calibratedTupleValue S hS hmax η u P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hη' (J : Finset (Fin K)) : ∀Q∈J.image P,IsCoprime Q.val η.modulus := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hη i
  have hQ' (J : Finset (Fin K)) : ∀Q∈J.image P,(4:ℝ)≤Q.val.absNorm := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hQ i
  have hi (J : Finset (Fin K)) :=
    (weightedErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J P hP hPS
      (image_supported S hS J P hPS) (hη' J) (hQ' J) W Yp x z hx hz hmargin
      W1 a b ha hsupp hW Y hY).mul_const (physicalMainTuple u J P W Yp z)
  have hsum := (integrable_finsetSum Finset.univ.powerset (fun J _=>hi J)).const_mul
    (numeratorFreeRowScalar S hS hmax η u x z)
  apply hsum.congr
  filter_upwards with t
  rw [calibratedTupleValue_error_subsets firsteps S hS hfirst hmax P hP hPS η u W Yp x
    ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

/-- A literal finite error-label numerator; its coefficients are those reconstructed
from the original row integral. -/
def errorLabelNumerator {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (J : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑P:(∀i:J,T i.val),(∏i:J,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
    errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:J=>(P i).val))
      (partial_image_supported S hS J T hT P) x z W1 Y

/-- The normalized full-w integral of the actual calibrated prime tuples equals
its error-label numerators times the remaining, unaltered prime sums. -/
theorem normalized_prime_tuple_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0<Y) :
    (1/(2*Real.pi):ℂ)*(∑P:(∀i,T i),FullWContour.rowNumeratorIntegral S hS hmax η u
      (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp W1 Y x z)=
    numeratorFreeRowScalar S hS hmax η u x z*
      ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val))) := by
  let kern (t : ℝ) := (Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)
  let f (J : Finset (Fin K)) (P : ∀i:J,T i.val) (t : ℝ) :=
    kern t*HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z
  let main (J : Finset (Fin K)) :=
    ∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
      (-star (idealRowHom u.val P.val.val))
  have hi (P : ∀i,T i) := calibrated_tuple_kernel_integrable S hS hmax firsteps hfirst η u hrow
    (fun i=>(P i).val) (hdisAll P) (fun i=>hT i _ (P i).property)
    (fun i=>hη i _ (P i).property) (fun i=>hQ i _ (P i).property)
    W Yp x z hx hz hmargin W1 a b ha hsupp (W1.smooth ⊤) Y hY
  have hfi (J : Finset (Fin K)) (P : ∀i:J,T i.val) : Integrable (f J P) := by
    apply partialErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J T hT P (hdis J P)
      (partial_image_supported S hS J T hT P) _ _ W Yp x z hx hz hmargin
      W1 a b ha hsupp (W1.smooth ⊤) Y hY
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hη i.val _ (P i).property
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hQ i.val _ (P i).property
  have hsum (J : Finset (Fin K)) : Integrable (fun t=>(∑P:(∀i:J,T i.val),f J P t)*main J) :=
    (integrable_finsetSum Finset.univ (fun P _=>hfi J P)).mul_const (main J)
  have he (t : ℝ) :
      (∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
        (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=
      numeratorFreeRowScalar S hS hmax η u x z*
        ∑J∈Finset.univ.powerset,(∑P:(∀i:J,T i.val),f J P t)*main J := by
    rw [←Finset.mul_sum,calibrated_prime_error_slots_separate firsteps S hS hfirst hmax η u T hT
      hdisAll W Yp x ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
    simp only [Finset.mul_sum,f,main]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    ring
  unfold FullWContour.rowNumeratorIntegral
  rw [←integral_finsetSum Finset.univ (fun P _=>hi P)]
  change (1/(2*Real.pi):ℂ)*(∫t : ℝ,∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=_
  simp_rw [he]
  rw [integral_const_mul,integral_finsetSum Finset.univ.powerset (fun J _=>hsum J)]
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [integral_mul_const,integral_finsetSum Finset.univ (fun P _=>hfi J P)]
  change (1/(2*Real.pi):ℂ)*((∑P:(∀i:J,T i.val),∫t : ℝ,f J P t)*main J)=_
  rw [←mul_assoc,Finset.mul_sum]
  change (∑P:(∀i:J,T i.val),(1/(2*Real.pi):ℂ)*(∫t : ℝ,f J P t))*main J=_
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  exact partialErrorTuple_mellin S hS η u J T hT P (hdis J P)
    (partial_image_supported S hS J T hT P) W Yp x z W1 Y


def reconstructedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑u∈R,frequencyWeight z ⟨u.val,u.property.1⟩ * numeratorFreeRowScalar S hS hmax η u x z *
    ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
      (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
        (-star (idealRowHom u.val P.val.val)))

theorem integratedDyadValue_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (R : Finset FreeRow)
    (hrow : ∀u∈R,(rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0<Y) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      (2*Real.pi:ℂ)*reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
  have he : (1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
    unfold FullWContour.integratedDyadValue reconstructedDyadValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [FullWContour.integratedRowValue,←Finset.mul_sum]
    rw [mul_left_comm,normalized_prime_tuple_reconstruction S hS hmax firsteps hfirst η u
      (hrow u hu) T hT hdis hdisAll hη hQ W Yp x z hx hz hmargin W1 a b ha hsupp Y hY]
    ring
  have hc : (2*Real.pi:ℂ)*(1/(2*Real.pi):ℂ)=1 := by
    apply mul_one_div_cancel
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    _ = (2*Real.pi:ℂ)*((1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue
        S hS hmax η R T hT W Yp W1 Y x z) := by rw [←mul_assoc,hc,one_mul]
    _ = _ := by rw [he]

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorReconstruction -/
