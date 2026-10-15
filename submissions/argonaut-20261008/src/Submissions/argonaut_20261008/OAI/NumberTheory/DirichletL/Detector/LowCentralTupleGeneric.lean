import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBoundGeneric
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMassGeneric
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowSlotScalesGeneric

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_central_compensated_tuple_generic
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (Etotal lx ly : ℝ) (hEtotal : 0≤Etotal) (hEtotal1 : Etotal≤1/5)
    (hxy : lx+ly=1-Etotal) (hElx : Etotal<lx) (hlxly : lx<ly)
    (hgap : Etotal<2*lx-ly)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤Etotal)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧
        (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→
      X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1
            (fun i=>(p i).val) J (Z^lx) (Z^ly) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(lx/2+(ly-lx)/12+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized_generic
    η S hS hbad Etotal lx ly hEtotal hEtotal1 hxy hElx hlxly hgap
    ell hell hsum a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_lower_bound_generic K a ha
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales_generic
    (calibrationForSet S hS) Etotal lx ly hElx hlxly hgap
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  let d := lowUnselectedLength ell J
  let corr := max 0 (5*Etotal-1+d)/8
  let g := lx/2+(ly-lx)/12
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 :=
    fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^lx) (Z^ly) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(g+ly*ε/2)
  let V := Ci*(1+‖t‖)^degree*Z^(corr+507*ε/2)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^lx/L) (Z^ly/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^lx/L) (Z^ly/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*
        Z^(g+ly*ε/2+corr+507*ε/2))*
        (‖lowUnselectedWeight slots J W Yp p‖*
          L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS)
        (Z^lx/L) (Z^ly/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb
        (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^lx/L) (Z^ly/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^lx/L) (Z^ly/L) (div_pos (by positivity) hL)
          (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        simpa only [G,V,q,L,Q,g,slots,Yp,div_eq_mul_inv,mul_assoc] using hh.trans hh2
      _=(Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*
          Z^(g+ly*ε/2+corr+507*ε/2))*
          (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
        rw [low_compensated_sqrt_factor q L hq.le hL]
        dsimp only [G,V]
        rw [show g+ly*ε/2+corr+507*ε/2 = (g+ly*ε/2)+(corr+507*ε/2) by ring,
          Real.rpow_add hz (g+ly*ε/2) (corr+507*ε/2)]
        ring
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass ell Z hInv.1.le T hT
    (fun i P hP=>(hnorm i P hP).1) J W Yp hW
  have hlen := lowLength_bounds_generic Etotal ell hell hsum J
  have hd : 0≤d := by simpa only [d] using hlen.1
  have hcorr : corr-d/2≤0 := by
    simpa only [corr,d] using low_length_correction_absorbed
      Etotal (lowUnselectedLength ell J) hlen.1 hEtotal1
  have hly1 : ly≤1 := by linarith
  have hlyε : ly*ε≤ε := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hly1 hε.le
  have hexp : g+ly*ε/2+corr+507*ε/2-d/2≤g+254*ε := by
    linarith
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*
        Z^(g+ly*ε/2+corr+507*ε/2))*(Cu*Z^(-d/2))) := by gcongr
    _=C0*(1+‖t‖)^degree*Z^(g+ly*ε/2+corr+507*ε/2-d/2) := by
      dsimp only [C0]
      rw [show g+ly*ε/2+corr+507*ε/2-d/2 =
        (g+ly*ε/2+corr+507*ε/2)+(-d/2) by ring,
        Real.rpow_add hz (g+ly*ε/2+corr+507*ε/2) (-d/2)]
      ring
    _≤C0*(1+‖t‖)^degree*Z^(g+254*ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hInv.1.le hexp) (by positivity)
    _=_ := by dsimp only [g]

end SevenEighths.ProbePhysical
end

end OAI
