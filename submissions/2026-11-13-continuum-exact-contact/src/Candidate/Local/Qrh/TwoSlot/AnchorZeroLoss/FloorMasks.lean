/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The averaged floor packet with every physical error mask and prime front.
Uses Hailey Collet's exact packet reconstruction and physical-front identities. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.PhysicalFloorPacket
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalCollect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily
open HeckeInverseAmplification ProbeHighRowFamily ProbePhysical

/-- The deterministic total-slot cap also bounds any complementary main
product. Error slots are retained in the total length, with a harmless
positive upper bound; no row-dependent amplitude is inverted. -/
theorem floor_main_cap {D : Cycle25.Weighted.MomentData}
    (Q : Fin D.N → ℂ) (Z : ℝ) (hZ : 1 ≤ Z) (J : Finset (Fin D.N))
    (hQ : ∀j, ‖Q j‖ ≤ Z^(D.ell j*(1/100+D.t))) :
    ‖∏j∈Finset.univ\J,Q j‖ ≤ Z^((1/100+D.t)*∑j,D.ell j) := by
  have hZp := zero_lt_one.trans_le hZ
  rw [norm_prod]
  calc
    _ ≤ ∏j∈Finset.univ\J,Z^(D.ell j*(1/100+D.t)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hQ j)
    _ = Z^(∑j∈Finset.univ\J,D.ell j*(1/100+D.t)) := by
      rw [Real.rpow_sum_of_pos hZp]
    _ ≤ Z^((1/100+D.t)*∑j,D.ell j) := by
      apply Real.rpow_le_rpow_of_exponent_le hZ
      rw [←Finset.sum_mul]
      have hs : (∑j∈Finset.univ\J,D.ell j) ≤ ∑j,D.ell j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun j _ _ => (D.slots_bounds j).1.le)
      nlinarith [D.t_pos]

/-- One literal physical error mask, including its complementary prime
front. The scalar is bounded only after the exact signed identity has
identified the packet. All prime/row masks and natural zeros remain present. -/
theorem physical_floor_mask {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (kap : ℝ)
    (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (he : D.e ≤ 1/1000)
    (J : Finset (Fin D.N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (Z : ℝ), 1 ≤ Z → ∀ (η : Character) (x z : ℂ),
    x.re=51/100+16*D.e → z.re=17/50 →
    ∀ rows : Finset FreeRow,
    (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue ≠ 1) →
    (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i => (P i).val)) →
    (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus) →
    (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm) →
    (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell i)) →
    (∀i:J,sourcePrimePool F Z i.val) →
    (∀u∈rows,∀i,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
      F.W 2 (Z^(D.ell i)) z‖ ≤ Z^(D.ell i*(1/100+D.t))) →
    ∀ (v A : ℝ), 0 < v → v ≤ 99 → 0 ≤ A →
    (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ A) →
    ‖sourceMaskContribution F η rows J Z x z (U^v)‖ ≤
      C*A*(U^v)^(-(1/2:ℝ))*Z^((-3/20+D.t)*∑j,D.ell j)*
        U^(1+(38/25:ℝ)*D.t) := by
  obtain ⟨C,hC,hpacket⟩ := physical_floor_packet (ι:=J) F kap hkaplo hkaphi
    hkapbeta hbeta he 1 2 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hpacket] with U hp
  refine ⟨hp.1,?_⟩
  intro Z hZ η x z hx hz rows hrows hrow hdis hη hQ hS Pbase hmain v A hv hvhi hA hscalar
  have hZp := zero_lt_one.trans_le hZ
  let cap : ℝ := Z^((1/100+D.t)*∑j,D.ell j)
  have hcap : 0 < cap := Real.rpow_pos_of_pos hZp _
  let main (i:rows) : ℂ := ∏j∈Finset.univ\J,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.ell j)) z
  have hm (i:rows) : ‖main i‖ ≤ cap :=
    floor_main_cap (fun j => HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val
      F.W 2 (Z^(D.ell j)) z) Z hZ J (hmain i.val i.property)
  have hWB (y:ℝ) : ‖F.W y‖ ≤ 1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded y).1]
    exact (F.bounded y).2
  have hb := hp.2 η (fun i:J => sourcePrimePool F Z i.val)
    (fun i => source_prime_pool_outside F Z i.val) hdis
    (fun i => hη i.val) Pbase (fun _ => F.W) (fun i => Z^(D.ell i.val))
    (fun i => Real.one_le_rpow hZ (D.slots_bounds i.val).1.le)
    (fun _ => F.complex_support) (fun _ y => hWB y) x z hx hz rows hrows hrow
    (fun i => main i/(cap:ℂ)) (normalized_main_bound main hcap hm) v hv hvhi
  let B : ℝ := C*(U^v)^(-(1/2:ℝ))*(∏i:J,(Z^(D.ell i.val))^(-(4/25:ℝ)))*
    U^(1+(38/25:ℝ)*D.t)
  have herr (u:FreeRow) (hu:u∈rows) := errorLabelNumerator_eq_packet
    F.S F.exclusions (4*D.e) F.first η u (hrow u hu) J (sourcePrimePool F Z)
    (fun i => source_prime_pool_outside F Z i) hdis hη hQ (fun _ => F.W)
    (fun i => Z^(D.ell i)) x z (by rw [hx]; linarith [D.e_pos]) hz.ge
    (by rw [hx]; linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support
    (F.W.smooth ⊤) (U^v) (Real.rpow_pos_of_pos (zero_lt_one.trans hp.1) _)
  have hlabel : (∑u∈rows,‖errorLabelNumerator F.S F.exclusions η u J
      (sourcePrimePool F Z) (fun i => source_prime_pool_outside F Z i)
      (fun _ => F.W) (fun i => Z^(D.ell i)) x z F.W (U^v)*
      (∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
        F.W 2 (Z^(D.ell j)) z)‖) ≤ cap*B := by
    have hs : (∑u∈rows, ‖errorLabelNumerator F.S F.exclusions η u J
        (sourcePrimePool F Z) (fun i => source_prime_pool_outside F Z i)
        (fun _ => F.W) (fun i => Z^(D.ell i)) x z F.W (U^v)*
        (∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
          F.W 2 (Z^(D.ell j)) z)‖) =
        ∑i:rows, ‖labelPolynomialPacket F.S F.exclusions η i.val
          (fun j:J => sourcePrimePool F Z j.val) (fun j => source_prime_pool_outside F Z j.val)
          (fun _ => F.W) (fun j => Z^(D.ell j.val)) x z F.W (U^v)*main i‖ := by
      rw [←Finset.sum_coe_sort rows]
      apply Finset.sum_congr rfl
      intro u hu
      rw [herr u.val u.property]
    rw [hs]
    rw [restore_main_cap _ main hcap]
    exact mul_le_mul_of_nonneg_left hb hcap.le
  have hpfront := source_mask_physical_front F η rows J Z hZp x z hz (U^v) hS
    A (cap*B) hA hscalar hlabel
  apply hpfront.trans_eq
  dsimp only [cap,B]
  have hsplit : (∑j:{i:Fin D.N//i∉J},D.ell j.val) + (∑j:J,D.ell j.val) = ∑j,D.ell j := by
    have hc : (∑j:{i:Fin D.N//i∉J},D.ell j.val) =
        ∑j∈Finset.univ\J,D.ell j :=
      (Finset.sum_subtype (Finset.univ\J) (by simp) D.ell).symm
    rw [hc,Finset.sum_coe_sort]
    exact Finset.sum_sdiff (Finset.subset_univ J)
  have hprod : (∏i:J,(Z^(D.ell i.val))^(-(4/25:ℝ))) = Z^(-(4/25:ℝ)*∑i:J,D.ell i.val) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_sum_of_pos hZp]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hprod]
  rw [show (-3/20+D.t)*(∑j,D.ell j) =
    -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val)+
      ((1/100+D.t)*∑j,D.ell j)+(-(4/25:ℝ)*(∑i:J,D.ell i.val)) by
        rw [←hsplit]; ring]
  simp_rw [Real.rpow_add hZp]
  ring

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.physical_floor_mask
