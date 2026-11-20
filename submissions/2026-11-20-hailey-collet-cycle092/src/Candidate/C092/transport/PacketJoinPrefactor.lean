/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform absorption of the authentic native slice prefactors. -/
import Candidate.C092.transport.PacketJoinFinal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open HeckeDetectorFiberPartition HeckeDetectorRawFiber HeckeDetectorClassBudget
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def phaseCardBound (D : BaselineData) : ℝ := (alphabetBound D.t)^D.N

lemma phase_card_le (D : BaselineData) (a : ℝ) (ha : a ≤ 7/8) :
    (Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ) ≤ phaseCardBound D := by
  have h := bin_card_le (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t
    (by linarith : (2*a-1)/2 ≤ 1/2) D.t_pos
  simp only [← Nat.card_eq_fintype_card] at h
  simpa only [phaseCardBound,Finset.card_univ,Fintype.card_fin,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr h

lemma prime_front_identity (D : BaselineData) (J : Finset (Fin D.N)) (Z : ℝ) (hZ : 0 < Z) :
    mainFront D J Z*(∏ s:J,(Z^(D.length s.val))^(-(4/25:ℝ))) = Z^(-(4/25:ℝ)*Geometry.ell) := by
  have hs : (∑ s : {s : Fin D.N // s ∉ J}, D.length s.val)+(∑ s:J,D.length s.val)=Geometry.ell := by
    rw [Finset.sum_coe_sort J]
    have hc : (∑ s : {s : Fin D.N // s ∉ J}, D.length s.val) = ∑ s∈Jᶜ,D.length s := by
      exact (Finset.sum_subtype (Jᶜ) (fun s=>by simp) D.length).symm
    rw [hc,Finset.sum_compl_add_sum J D.length,D.slots_sum]
  have hp : (∏ s:J,(Z^(D.length s.val))^(-(4/25:ℝ))) = Z^((∑ s:J,D.length s.val)*(-(4/25:ℝ))) := by
    simp_rw [← Real.rpow_mul hZ.le]
    rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]
  rw [hp,mainFront,←Real.rpow_add hZ]
  congr 1
  nlinarith [hs]

lemma nativeHeight_le (Z d τ : ℝ) (i : ℕ) (hZ : 1 ≤ Z) (hd : d ≤ 7/8) (hτ : 0 ≤ τ) :
    1+nativeHeight Z d τ i ≤ (2*Real.pi+2)*(3+(3*i+1:ℕ)*Z^τ) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have he : d*(τ/(2*(7/8:ℝ))) ≤ τ := by
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hd hτ]
  have hr : (Z^d)^(τ/(2*(7/8:ℝ))) ≤ Z^τ := by
    rw [←Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ he
  have ht : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hi : (1:ℝ) ≤ (3*i+1:ℕ) := by exact_mod_cast (show 1 ≤ 3*i+1 by omega)
  have hprod : Z^τ ≤ (3*i+1:ℕ)*Z^τ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (hr.trans hprod) (by positivity : 0 ≤ 2*Real.pi)
  unfold nativeHeight
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le (mul_nonneg (by positivity : (0:ℝ) ≤ (3*i+1:ℕ)) ht)]

lemma dyadic_cost_uniform (loss : ℝ) (hloss : 0 < loss) :
    ∃ L : ℝ,0 ≤ L ∧ ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ ∀ d : ℝ,1/2 ≤ d →
      (dyadicLength (Z^d):ℝ)^2 ≤ L*(Z^d)^loss := by
  obtain ⟨L,hL,h⟩ := dyadic_cost_eventually loss hloss
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp h
  refine ⟨L,hL,?_⟩
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually (eventually_ge_atTop b)),eventually_ge_atTop (1:ℝ)] with Z hZb hZ
  refine ⟨hZ,fun d hd=>hb _ (hZb.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le hZ hd

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.prime_front_identity
