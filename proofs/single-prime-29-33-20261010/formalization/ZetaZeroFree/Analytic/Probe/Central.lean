import OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeBound
import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import ZetaZeroFree.Exponent

namespace ZetaZeroFree.Analytic.Probe
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem sourcePoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_unmarked_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀r : Fin N→ℝ,(∀j,rmin≤r j) → (∀j,r j≤R) →
      let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>sourcePoolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+(a-1/2)+mesh)) := by
  obtain ⟨C,hC,hbound⟩ := actual_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  dsimp only
  intro hdis t ht
  have h := hb d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr' hdis t ht
  dsimp only at h
  apply h.2.trans
  apply mul_le_mul_of_nonneg_left _ (by unfold rowNorm;positivity)
  apply Finset.prod_le_prod₀
  · intro j hj
    positivity
  · intro j hj
    apply Real.rpow_le_rpow_of_exponent_le
    · exact Real.one_le_rpow (Real.one_le_rpow hZ (hdmin.trans_le hd).le) (hrmin.trans_le (hr j)).le
    · linarith [(h.1 j).2.1]

theorem actual_fixed_scale_central_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) 
    (ell : Fin N→ℝ) (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hellsum : ∑j,ell j=(5/33:ℝ)) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>sourcePoolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)) := by
  obtain ⟨C,hC,hbound⟩ := actual_unmarked_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (0:ℝ)] with Z hb hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin
  dsimp only
  intro hdis t ht
  have hd0 : 0<d := hdmin.trans_le hd
  let r : Fin N→ℝ := fun j=>ell j/d
  have hr (j : Fin N) : rmin≤r j := by
    dsimp [r]
    apply (le_div_iff₀ hd0).mpr
    simpa [mul_comm] using (mul_le_mul_of_nonneg_right hd' hrmin.le).trans (hello j)
  have hr' (j : Fin N) : r j≤R := by
    dsimp [r]
    apply (div_le_iff₀ hd0).mpr
    exact (hellhi j).trans (by nlinarith)
  have hY : (fun j=>(Z^d)^(r j))=(fun j=>Z^(ell j)) := by
    funext j
    dsimp [r]
    rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ (ne_of_gt hd0)]
  have hh := hb d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  rw [hY] at hh
  have hx := hh hdis t ht
  apply hx.trans_eq
  have hpow : (∏j,(Z^(ell j))^(-(4/25:ℝ)+(a-1/2)+mesh))=
      Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hellsum]
  rw [hpow]

lemma central_physical_scale_identity {Z a e : ℝ} (hZ : 0<Z) :
    (Z^(13/33:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(15/33:ℝ))^(-a-6*e)=
      Z^((6/11)*a-197/330+(146/11)*e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

theorem actual_fixed_scale_central_integral (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) 
    (ell : Fin N→ℝ) (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hellsum : ∑j,ell j=(5/33:ℝ)) 
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ‖finiteCentralCubeRows S hS hmax η rows T (sourcePoolOutside M H S N c b Y) W Y W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss)*
          (∑u∈rows,rowNorm u^(a-1/2+12*e+eps*(N+8)-17/50)) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_scale_central_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB ell hello hellhi hellsum
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ,eventually_gt_atTop (0:ℝ)] with Z hb hheightZ hZ
  intro d hd hd' rows hrows a i hi ha ha1 hbin
  dsimp only
  intro hdis
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Arow : FreeRow→ℝ := fun u=>C*(η.modulus.absNorm:ℝ)^(2*eps)*
    rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh))
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha ha1 hheightZ.2
    (by have hz : 0≤Z^τ := Real.rpow_nonneg hZ.le _;push_cast;nlinarith)
    S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T (sourcePoolOutside M H S N c b Y)
    (rayCubeFamily M H hH) hbin W Y (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
    (by positivity) (by positivity) hZ Arow (by intro u hu;unfold Arow rowNorm;positivity) (by
      intro t ht u hu
      rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
      exact hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha1 (hbin u hu) hdis t ht)
  apply hp.trans_eq
  rw [central_physical_scale_identity hZ]
  have hs : (∑u∈rows,rowNorm u^(-(17/50:ℝ))*Arow u)=
      (C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)))*
        (∑u∈rows,rowNorm u^(a-1/2+12*e+eps*(N+8)-17/50)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hu0 : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
    have heq : rowNorm u^(-(17/50:ℝ))*rowNorm u^(a-1/2+12*e+eps*(N+8))=
        rowNorm u^(a-1/2+12*e+eps*(N+8)-17/50) := by
      rw [←Real.rpow_add hu0]
      congr 1
      ring
    dsimp [Arow]
    calc
      _ = (C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)))*
        (rowNorm u^(-(17/50:ℝ))*rowNorm u^(a-1/2+12*e+eps*(N+8))) := by ring
      _ = _ := by rw [heq]
  rw [hs]
  have hz : Z^((6/11)*a-197/330+(146/11)*e)*Z^loss*
      Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh))=
      Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss) := by
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ = (D*C)*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((6/11)*a-197/330+(146/11)*e)*Z^loss*Z^((5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)))*
        (∑u∈rows,rowNorm u^(a-1/2+12*e+eps*(N+8)-17/50)) := by ring
    _ = _ := by rw [hz]

lemma row_shell_power {Z v q : ℝ} (hZ : 0<Z) (hq : q≤2) (u : FreeRow)
    (hlo : Z^v≤rowNorm u) (hhi : rowNorm u≤2*Z^v) :
    rowNorm u^q≤4*Z^(v*q) := by
  have hbase : 0<Z^v := Real.rpow_pos_of_pos hZ _
  by_cases hq0 : 0≤q
  · calc
      _ ≤ (2*Z^v)^q := Real.rpow_le_rpow (by unfold rowNorm;positivity) hhi hq0
      _ = (2:ℝ)^q*Z^(v*q) := by rw [Real.mul_rpow (by norm_num) hbase.le,←Real.rpow_mul hZ.le]
      _ ≤ 4*Z^(v*q) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
        convert Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤2 by norm_num) hq using 1; norm_num
  · calc
      _ ≤ (Z^v)^q := Real.rpow_le_rpow_of_nonpos hbase hlo (le_of_not_ge hq0)
      _ = Z^(v*q) := (Real.rpow_mul hZ.le v q).symm
      _ ≤ 4*Z^(v*q) := by nlinarith [Real.rpow_nonneg hZ.le (v*q)]

lemma row_shell_sum {Z v q cardExponent C0 : ℝ} (hZ : 0<Z) (hq : q≤2)
    (rows : Finset FreeRow) (hrows : ∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v)
    (hcard : (rows.card:ℝ)≤C0*Z^cardExponent) :
    (∑u∈rows,rowNorm u^q)≤4*C0*Z^(cardExponent+v*q) := by
  calc
    _ ≤ ∑_u∈rows,4*Z^(v*q) := Finset.sum_le_sum (fun u hu=>row_shell_power hZ hq u (hrows u hu).1 (hrows u hu).2)
    _ = (rows.card:ℝ)*(4*Z^(v*q)) := by simp
    _ ≤ (C0*Z^cardExponent)*(4*Z^(v*q)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [Real.rpow_add hZ];ring

lemma row_shell_crude_sum {Z v q : ℝ} (hZ : 1≤Z) (hv : 0≤v) (hq : q≤2)
    (rows : Finset FreeRow) (hrows : ∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) :
    (∑u∈rows,rowNorm u^q)≤1024*Z^(v*(1+q)) := by
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hbase : 1≤Z^v := Real.one_le_rpow hZ hv
  have hc := freeRow_count rows (2*Z^v) (by linarith) (fun u hu=>(hrows u hu).2)
  have hc' : (rows.card:ℝ)≤256*Z^v := hc.trans_eq (by ring)
  have hh := row_shell_sum hZ0 hq rows hrows hc'
  simpa only [show (4*(256:ℝ))=1024 by norm_num,show v+v*q=v*(1+q) by ring] using hh

lemma floor_source_exponent :
    ((6/11:ℝ)*(51/100)-197/330)+(5/33)*(-(4/25)+(51/100-1/2))+
      (25/33)*(1+(51/100)-1/2-17/50)=137/825 := by norm_num

lemma floor_source_gap : (20/99:ℝ)-137/825=89/2475 := by norm_num

lemma floor_exponent_with_buffer {v ζ e eps loss mesh : ℝ} {N : ℕ}
    (hv : v≤(25/33:ℝ)+ζ) (he : 0≤e) (heps : 0≤eps) :
    ((6/11)*(51/100)-197/330+(146/11)*e)+
      (5/33)*(-(4/25)+(51/100-1/2)+mesh)+loss+
      v*(1+51/100-1/2+12*e+eps*(N+8)-17/50)≤
    137/825+(67/100)*ζ+(146/11)*e+((25/33)+ζ)*(12*e+eps*(N+8))+(5/33)*mesh+loss := by
  have hb : 0≤(67/100:ℝ)+12*e+eps*(N+8) := by positivity
  nlinarith [mul_nonneg (by linarith : 0≤(25/33:ℝ)+ζ-v) hb]

lemma central_total_exponent (a beta d countLoss e eps loss mesh : ℝ) :
    ((6/11)*a-197/330+(146/11)*e) +
      d*(Exponent.R0 (2*a-1)+countLoss+a-1/2+12*e+9*eps-17/50)+
      (5/33)*(-4/25+(a-1/2)+mesh)+loss =
      beta-(67/99)+Exponent.E (2*a-1) beta d+
        (146/11)*e+d*(countLoss+12*e+9*eps)+(5/33)*mesh+loss := by
  unfold Exponent.E Exponent.a Exponent.h Exponent.x Exponent.y Exponent.ell Exponent.slope Exponent.z0
  ring

end
end ZetaZeroFree.Analytic.Probe
