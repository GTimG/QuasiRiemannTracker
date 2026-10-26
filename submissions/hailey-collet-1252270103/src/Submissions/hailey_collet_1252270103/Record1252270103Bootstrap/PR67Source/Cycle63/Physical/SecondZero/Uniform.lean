import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.SecondZero.Radius
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.NominalRadius
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle63SecondZero
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance uniformDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Fixed envelope chosen before allocations, characters, and all heights. -/
def controlEnvelope (N : ℕ) (Cs bs hi ε : ℝ) : ℝ :=
  4*Cs^(2*N)*(1+bs^N*hi*hi)^(1+ε)

lemma controlEnvelope_pos (N : ℕ) (Cs bs hi ε : ℝ) (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) :
    0 < controlEnvelope N Cs bs hi ε := by
  have hc : 0 < Cs := zero_lt_one.trans_le hCs
  have hb : 0 ≤ bs^N := pow_nonneg (zero_le_one.trans hbs) _
  have hr : 0 < 1+bs^N*hi*hi := by nlinarith [mul_nonneg hb (sq_nonneg hi)]
  unfold controlEnvelope
  exact mul_pos (mul_pos (by norm_num) (pow_pos hc _)) (Real.rpow_pos_of_pos hr _)

lemma zeroControl_fixed {ι : Type*} [Fintype ι] (N : ℕ) (Cs bs ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε)
    (s : Input ι) (hcard : Fintype.card ι ≤ N)
    (hM : ∀ i, s.M i ≤ Cs) (hs : s.upper ≤ bs) {lo hi : ℝ} (p : Profiles lo hi) :
    zeroControl s p ε ≤ controlEnvelope N Cs bs hi ε*(p.control {(0,0)})^2 := by
  have hpc := Profiles.control_nonneg p {(0,0)}
  have hm0 (i : ι) : 0 ≤ s.M i := zero_le_one.trans (s.M_ge_one i)
  have hmp : (∏ i,s.M i) ≤ Cs^N := by
    calc
      _ ≤ ∏ _i : ι,Cs := Finset.prod_le_prod₀ (fun i _ => hm0 i) (fun i _ => hM i)
      _ = Cs^(Fintype.card ι) := by simp
      _ ≤ Cs^N := pow_le_pow_right₀ hCs hcard
  have hhp : (∏ i,max 0 (s.hi i)) ≤ bs^N := by
    calc
      _ ≤ ∏ _i : ι,bs := Finset.prod_le_prod₀ (fun i _ => le_max_left _ _)
        (fun i _ => max_le (zero_le_one.trans hbs) ((s.upper_ge i).trans hs))
      _ = bs^(Fintype.card ι) := by simp
      _ ≤ bs^N := pow_le_pow_right₀ hbs hcard
  have hpr : (1+(∏ i,max 0 (s.hi i))*hi*hi)^(1+ε) ≤ (1+bs^N*hi*hi)^(1+ε) := by
    apply Real.rpow_le_rpow _ _ (by linarith)
    · have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
      nlinarith [mul_nonneg hp (sq_nonneg hi)]
    · have hh := mul_le_mul_of_nonneg_right hhp (sq_nonneg hi)
      nlinarith
  have hsq : (2*p.control {(0,0)}*(∏ i,s.M i))^2 ≤ (2*p.control {(0,0)}*Cs^N)^2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hm0 i)))
    exact mul_le_mul_of_nonneg_left hmp (by positivity)
  unfold zeroControl controlEnvelope
  calc
    _ ≤ (2*p.control {(0,0)}*Cs^N)^2*(1+bs^N*hi*hi)^(1+ε) :=
      mul_le_mul hsq hpr (Real.rpow_nonneg (by
        have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
        nlinarith [mul_nonneg hp (sq_nonneg hi)]) _) (sq_nonneg _)
    _ = _ := by rw [pow_mul]; ring

variable [Cycle63.AffineLedger] in
/-- One constant absorbs the actual fixed source caps for both radius branches. -/
theorem uniform_radius_certificates (N : ℕ) (Cs bs hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
    ∀ lo : ℝ, 0 < lo → 0 ≤ hi → ∀ (s : Input ι) (p : Profiles lo hi),
    (∀ i,s.M i ≤ Cs) → s.upper ≤ bs → s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop → 0 ≤ M →
    A ≤ M*Cycle63.AffineLedger.totalA beta → a ≤ M*Cycle63.AffineLedger.amp beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    let bound := C*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*Cycle63.AffineLedger.zeroReserve+nominalLoss+δ+reserve+ε*B-s₀)
    Z^(-a-(A-c+Rw+E+Bc))*radiusTerm s R seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤ bound ∧
    ∀ (q : O), q ≠ 0 → ∀ k : ℕ, k=1 ∨ k=6 ∨ k=7 → 0 ≤ a →
    Z^(-a-(A-c+Rw+E+Bc))*(localErrorCost q (k-1)*radiusTerm s R seed W
      (errorCommonRadius Z d K0 c (3*a) δ reserve q k)) ≤ bound := by
  obtain ⟨C,hC,hbound⟩ := actual_main_second_zero N ε hε
  refine ⟨C*controlEnvelope N Cs bs hi ε,
    mul_pos hC (controlEnvelope_pos N Cs bs hi ε hCs hbs),?_⟩
  intro ι _ hcard lo hlo hhi s p hM hs h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E K0
    nominalLoss δ reserve B s₀ hZ hb hM0 hA ha hc hd hBc hK0 hvol hseedN
  have hm := hbound hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E
    K0 nominalLoss δ reserve B s₀ hZ hb hM0 hA ha hc hd hBc hK0 hvol hseedN
  have hf := zeroControl_fixed N Cs bs ε hCs hbs hε s hcard hM hs p
  have hout : Z^(-a-(A-c+Rw+E+Bc))*radiusTerm s R seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤
      (C*controlEnvelope N Cs bs hi ε)*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*Cycle63.AffineLedger.zeroReserve+nominalLoss+δ+reserve+ε*B-s₀) := by
    apply hm.trans
    have hh := mul_le_mul_of_nonneg_left hf hC.le
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (norm_nonneg (paperRadialFourier W 0)))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le
        (-M*Cycle63.AffineLedger.zeroReserve+nominalLoss+δ+reserve+ε*B-s₀))
    simpa only [mul_assoc] using hh'
  refine ⟨hout,?_⟩
  intro q hq k hk ha0
  exact (mul_le_mul_of_nonneg_left
    (actual_extracted_second_zero_le_main s R seed W Z d K0 c a δ reserve hZ ha0 q hq k hk)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hout

lemma ideal_log_nonneg (I : Ideal O) (hI : I ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Real.logb Z (I.absNorm : ℝ) := by
  apply Real.logb_nonneg hZ
  have hn : 0 < I.absNorm := by exact_mod_cast norm_pos I hI
  exact_mod_cast Nat.succ_le_iff.mpr hn

end
end OAI.SevenEighths.Cycle63SecondZero

end Record1252270103Bootstrap.PR67
