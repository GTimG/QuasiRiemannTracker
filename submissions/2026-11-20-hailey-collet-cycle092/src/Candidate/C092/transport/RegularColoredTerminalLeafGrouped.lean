/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The full independently colored regular sum on actual native labels.
The native variable dyad/anchor grouping, weighted divisor fibers, extraction
savings and Price Lipschitz bookkeeping are retained. Only the explicit
earlier StrongPair energy call on actual sixth-free fibers is isolated.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafRectangles
import Candidate.C092.transport.RegularColoredGroupedLeaves
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight scale_pos)
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafGrouped_c6f48124c8c6ae03_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}



/-- The full regular sum over the actual original labels. Dyadic and anchor
classes are counted only after physical-label reduction. Its sole analytic
input is the explicit earlier StrongPair leaf on actual sixth-free fibers. -/
theorem terminal_frame_grouped_at (price : Price) (Mmin Mmax : ℝ) (hMmin : 0≤ Mmin)
    (θ : GData L) (hL : 0≤ L) (ε : ℝ) (hε : 0<ε) (J deg : ℕ) :
    ∃ controls : Finset (ℕ×ℕ),∃ Ctot : ℝ,0< Ctot ∧
    ∀ (mesh Z : ℝ),0< mesh → mesh≤1/2 → (3+price.lip)*mesh≤ε/8 → 1< Z →
      Mmax+mesh+Real.logb Z 2≤2 →
      ((Fintype.card DictIdx:ℝ)*2^θ.N)*(L*Real.logb 2 Z+Real.logb 2 θ.b+2)^2≤ Z^(ε/16) →
      (1+3*price.lip)*Real.logb Z 3≤ε/16 → Real.logb Z 3≤1/2 → (2:ℝ)≤ Z^(3/2:ℝ) →
    ∀ (η ω₁ ω₂ : Character) (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
      (w₀ H Hsource Cterm v : ℝ),0≤ Cterm →
      Second.AdmissibleGroup (frameSideFrame L θ mesh ω₁ ω₂ η Z) Mmin Mmax mesh ε Z r labels H →
      let M := Real.logb Z (2*Z^(H+mesh))
      let Pbd := gP r+2*Real.logb Z 3
      frameRectangularLeaves θ η ω₁ ω₂ r v M Hsource
        (price.f w₀ Pbd (∑i,r.w i) M-(5/6)*max 0 (Hsource-M))
        (Cterm*r.height^deg*(1+‖v‖)^(2*deg)) Pbd J →
      (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η r x v) ≤
        Ctot*Cterm*gAmp L θ mesh η Z r deg controls*(1+‖v‖)^(2*deg)*
          Z^(r.colLog+r.twistLog+price.f w₀ (gP r) (∑i,r.w i) H+ε) := by
  obtain ⟨controls,Cclass,hCclass,hclass⟩ := frame_native_class_uniform θ (ε/8) (by positivity) J
  obtain ⟨Cred,hCred,hred⟩ := frame_label_reduction_native θ (ε/8) (by positivity)
    (ε/(48*max 1 θ.Bmask)) (by positivity)
  refine ⟨controls,4*Cred*Cclass,by positivity,?_⟩
  intro mesh Z hmesh0 hmesh1 hmeshε hZ1 hMmax hcount hl3 hl3' hZ32 η ω₁ ω₂ r labels w₀ H Hsource Cterm v hCterm hadm
  dsimp only
  intro hterminal
  obtain ⟨hHmin,hHmax,henv,-,hfib⟩ := hadm
  have henv' : ∀x∈labels,|gEnvelope r x-H|≤ mesh := henv
  have hfib' : ∀y:O,y≠0 → ((Ideal.span {y}).absNorm:ℝ)≤ Z^(Mmax+2) →
      ∑x∈labels.filter (fun x=> x.twist∣y),gWeight x≤ Z^(ε/8) := hfib
  have hZ0 : 0< Z := by linarith
  have hnorm0 : 0≤ r.norm := div_nonneg (Real.rpow_nonneg hZ0.le _) (sq_nonneg _)
  have hvol := r.vol_pos hZ0
  set tgt := r.colLog+r.twistLog+price.f w₀ (gP r) (∑i,r.w i) H+ε with htgt
  have hRHS0 : 0≤(4*Cred*Cclass)*Cterm*gAmp L θ mesh η Z r deg controls*(1+‖v‖)^(2*deg)*Z^tgt := by
    have : 0≤ gAmp L θ mesh η Z r deg controls := by unfold gAmp; have := r.one_le_height; positivity
    have := Real.rpow_nonneg hZ0.le tgt
    positivity
  by_cases hne : ∃x∈labels,Fits η r x
  swap
  · push_neg at hne
    have h0 : (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η r x v)=0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [framegEnergy,dif_neg (hne x hx),mul_zero]
    rw [h0];exact hRHS0
  obtain ⟨x₀,hx₀,hfx₀⟩ := hne
  have hHle : H≤ r.twistLog+(2*r.colLog-r.kLog+mesh)+mesh := by
    have h1 := (abs_le.mp (henv' x₀ hx₀)).1
    rw [gEnvelope_eq r x₀ hfx₀.twist_ne] at h1
    linarith [hfx₀.dual]
  have hpn : ∀ x : GLabel θ mesh Z,
      0 ≤ (x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) * pairNorm x.d :=
    fun x => mul_nonneg (by positivity) (by unfold pairNorm; positivity)
  -- (1) selection of one child per label
  let mass : GLabel θ mesh Z → ℝ := fun x =>
    labelMass Cred Z (ε/8) (ε/(48 * max 1 θ.Bmask)) r.w r.X₁ r.X₂ x.G x.D x.d
  have hsel : ∀ x ∈ labels, ∃ c : Finset (Fin θ.N) × ℝ × ℝ,
      gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ 0 ∨
      (Fits η r x ∧ 0 < c.2.1 ∧ 0 < c.2.2 ∧
        ((c.2.1 ≤ r.X₁ ∧ c.2.2 ≤ r.X₂) ∨ (c.2.1 ≤ r.Y₁ ∧ c.2.2 ≤ r.Y₂)) ∧
        gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ r.norm * (gWeight x *
          ((x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) * pairNorm x.d * mass x) * frameChildE ω₁ ω₂ η r v (x.anchor r) c.1 c.2.1 c.2.2 (r.V₀ * x.twist) (dyadicScale (x.n 1)))) := by
    intro x _
    by_cases hf : Fits η r x
    · rcases hred mesh Z (by linarith) η ω₁ ω₂ r x hf v with h0 | ⟨A, X₁', X₂', h1, h2, h3, h4⟩
      · refine ⟨(∅, 1, 1), Or.inl ?_⟩
        rw [framegEnergy, dif_pos hf]
        exact mul_nonpos_of_nonneg_of_nonpos (gWeight_nonneg x)
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hpn x) hnorm0) h0)
      · refine ⟨(A, X₁', X₂'), Or.inr ⟨hf, h1, h2, h3, ?_⟩⟩
        rw [framegEnergy, dif_pos hf]
        calc gWeight x * ((x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) * pairNorm x.d * r.norm * frameRawEnergy ω₁ ω₂ η r x hf v)
            ≤ gWeight x * ((x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) * pairNorm x.d * r.norm * (mass x *
                frameChildE ω₁ ω₂ η r v (x.anchor r) A X₁' X₂' (r.V₀ * x.twist) (dyadicScale (x.n 1)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4
                (mul_nonneg (hpn x) hnorm0)) (gWeight_nonneg x)
          _ = _ := by ring
    · exact ⟨(∅, 1, 1), Or.inl (by rw [framegEnergy, dif_neg hf, mul_zero])⟩
  choose! c hc using hsel
  let E : GLabel θ mesh Z → ℝ := fun x =>
    frameChildE ω₁ ω₂ η r v (x.anchor r) (c x).1 (c x).2.1 (c x).2.2 (r.V₀ * x.twist) (dyadicScale (x.n 1))
  let wt : GLabel θ mesh Z → ℝ := fun x =>
    gWeight x * ((x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) * pairNorm x.d * mass x)
  set good := labels.filter (fun x => 0 < gWeight x * framegEnergy ω₁ ω₂ η r x v) with hgood_def
  have hgood : ∀ x ∈ good, x ∈ labels ∧ Fits η r x ∧ 0 < (c x).2.1 ∧ 0 < (c x).2.2 ∧
      (((c x).2.1 ≤ r.X₁ ∧ (c x).2.2 ≤ r.X₂) ∨ ((c x).2.1 ≤ r.Y₁ ∧ (c x).2.2 ≤ r.Y₂)) ∧
      0 < gWeight x * framegEnergy ω₁ ω₂ η r x v ∧
      gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ r.norm * (wt x * E x) := by
    intro x hx
    obtain ⟨hxl, hpos⟩ := Finset.mem_filter.mp hx
    rcases hc x hxl with h | ⟨hf, h1, h2, h3, h4⟩
    · exact absurd h (not_le.mpr hpos)
    · exact ⟨hxl, hf, h1, h2, h3, hpos, h4⟩
  have hstep1 : ∑ x ∈ labels, gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ r.norm * ∑ x ∈ good, wt x * E x := by
    rw [← Finset.sum_filter_add_sum_filter_not labels (fun x => 0 < gWeight x * framegEnergy ω₁ ω₂ η r x v)]
    have hneg : ∑ x ∈ labels.filter (fun x => ¬ 0 < gWeight x * framegEnergy ω₁ ω₂ η r x v),
        gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ 0 :=
      Finset.sum_nonpos fun x hx => not_lt.mp (Finset.mem_filter.mp hx).2
    rw [Finset.mul_sum]
    have hpos : ∑ x ∈ good, gWeight x * framegEnergy ω₁ ω₂ η r x v ≤ ∑ x ∈ good, r.norm * (wt x * E x) :=
      Finset.sum_le_sum fun x hx => (hgood x hx).2.2.2.2.2.2
    linarith
  -- (2) a contributing child has both lengths above the first ideal norm
  have hb0 : 0 < θ.b := lt_of_lt_of_le zero_lt_one θ.hb1
  have hE0 : ∀ x ∈ good, E x ≠ 0 := by
    intro x hx hE
    obtain ⟨-, hf, -, -, -, hpos, hle⟩ := hgood x hx
    rw [hE, mul_zero, mul_zero] at hle
    linarith
  have hlow : ∀ x ∈ good, 1 / θ.b ≤ (c x).2.1 ∧ 1 / θ.b ≤ (c x).2.2 := by
    intro x hx
    obtain ⟨-, -, h1, h2, -, -, -⟩ := hgood x hx
    constructor
    · by_contra hlt
      push_neg at hlt
      apply hE0 x hx
      exact frameChildE_eq_zero_small ω₁ ω₂ η r v _ _ _ _ _ _
        (Or.inl ⟨h1,by rw [lt_div_iff₀ hb0] at hlt;linarith⟩)
    · by_contra hlt
      push_neg at hlt
      apply hE0 x hx
      exact frameChildE_eq_zero_small ω₁ ω₂ η r v _ _ _ _ _ _
        (Or.inr ⟨h2,by rw [lt_div_iff₀ hb0] at hlt;linarith⟩)
  -- lengths of a child
  have hup : ∀ x ∈ good, (c x).2.1 ≤ Z^L ∧ (c x).2.2 ≤ Z^L ∧
      length Z (c x).2.1 + length Z (c x).2.2 ≤ gP r := by
    intro x hx
    obtain ⟨-, -, h1, h2, h3, -, -⟩ := hgood x hx
    rcases h3 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · refine ⟨a1.trans r.hX₁L, a2.trans r.hX₂L, ?_⟩
      exact (add_le_add (length_mono Z _ _ hZ1 a1) (length_mono Z _ _ hZ1 a2)).trans
        (le_max_left _ _)
    · refine ⟨a1.trans r.hY₁L, a2.trans r.hY₂L, ?_⟩
      exact (add_le_add (length_mono Z _ _ hZ1 a1) (length_mono Z _ _ hZ1 a2)).trans
        (le_max_right _ _)
  have hl30 : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hZ1 (by norm_num)
  have hscaled : ∀ (X : ℝ) (e : Fin 2), 0 < X →
      length Z (scale e * dyadicTop X) ≤ length Z X + Real.logb Z 3 := by
    intro X e hX
    have hs := ProfileSeparation.scale_mem e
    have hT := dyadicTop_spec X hX
    have h3 : scale e * dyadicTop X ≤ 3 * X := by nlinarith [hs.2, dyadicTop_pos X]
    exact (length_mono Z _ _ hZ1 h3).trans (length_mul_le Z 3 X hZ1 (by norm_num))
  -- (3) classes
  let key : GLabel θ mesh Z → DictIdx × Finset (Fin θ.N) × ℤ × ℤ := fun x =>
    (x.anchor r, (c x).1, dyadicIndex (c x).2.1, dyadicIndex (c x).2.2)
  set img := good.image key with himg
  set Kc : ℝ := 2 * Z^(H + mesh) with hKc
  have hKc0 : 0 < Kc := by positivity
  have hlogKc : Real.logb Z Kc = Real.logb Z 2 + (H + mesh) := by
    rw [hKc, Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hZ0 _).ne',
      Real.logb_rpow hZ0 hZ1.ne']
  have hl2 : 0 ≤ Real.logb Z 2 := Real.logb_nonneg hZ1 (by norm_num)
  have hl23 : Real.logb Z 2 ≤ Real.logb Z 3 := Real.logb_le_logb_of_le hZ1 (by norm_num) (by norm_num)
  set Pbd := gP r + 2 * Real.logb Z 3 with hPbd
  set loss := price.f w₀ Pbd (∑i,r.w i) (Real.logb Z Kc)-(5/6)*max 0 (Hsource-Real.logb Z Kc) with hloss
  set Kterm := Cterm*r.height^deg*(1+‖v‖)^(2*deg) with hKterm
  have hKterm0 : 0≤ Kterm := by unfold Kterm;have := r.one_le_height;positivity
  have hM0 : 0≤ Real.logb Z Kc := by rw [hlogKc];linarith
  have hM2 : Real.logb Z Kc≤2 := by rw [hlogKc];linarith
  set Bclass := (4*(Cred*Z^(ε/8+3*(ε/(48*max 1 θ.Bmask))*θ.Bmask)*r.vol*Z^(ε/8)))*
      Cclass*Kterm*(sourceControl controls r.W₁*sourceControl controls r.W₂)^2*
      Z^(Real.logb Z Kc+price.f w₀ Pbd (∑i,r.w i) (Real.logb Z Kc)+ε/8) with hBclass
  have hclassB : ∀k∈img,∑x∈good.filter (fun x=> key x=k),wt x*E x≤ Bclass := by
    intro k hk
    obtain ⟨x₁,hx₁,hkx₁⟩ := Finset.mem_image.mp hk
    set F := good.filter (fun x=> key x=k) with hF
    have hFk : ∀x∈F,x.anchor r=k.1 ∧ (c x).1=k.2.1 ∧ dyadicIndex (c x).2.1=k.2.2.1 ∧
        dyadicIndex (c x).2.2=k.2.2.2 := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp only [key,Prod.ext_iff] at h
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩
    have hEF : ∀x∈F,E x=frameChildE ω₁ ω₂ η r v k.1 k.2.1 (c x).2.1 (c x).2.2
        (r.V₀*x.twist) (dyadicScale (x.n 1)) := by
      intro x hx
      obtain ⟨h1,h2,-,-⟩ := hFk x hx
      simp only [E];rw [h1,h2]
    obtain ⟨hk1,hk2,hk3,hk4⟩ : x₁.anchor r=k.1 ∧ (c x₁).1=k.2.1 ∧
        dyadicIndex (c x₁).2.1=k.2.2.1 ∧ dyadicIndex (c x₁).2.2=k.2.2.2 := by
      simp only [key,Prod.ext_iff] at hkx₁
      exact ⟨hkx₁.1,hkx₁.2.1,hkx₁.2.2.1,hkx₁.2.2.2⟩
    obtain ⟨-,-,hx1p,hx2p,-,-,-⟩ := hgood x₁ hx₁
    obtain ⟨hu1,hu2,hu3⟩ := hup x₁ hx₁
    have hY₁ : (2:ℝ)^k.2.2.1=dyadicTop (c x₁).2.1 := by rw [dyadicTop,hk3]
    have hY₂ : (2:ℝ)^k.2.2.2=dyadicTop (c x₁).2.2 := by rw [dyadicTop,hk4]
    have hlen1 : ∀e:Fin 2,length Z (scale e*(2:ℝ)^k.2.2.1)≤ length Z (c x₁).2.1+Real.logb Z 3 :=
      fun e=> by rw [hY₁];exact hscaled _ e hx1p
    have hlen2 : ∀e:Fin 2,length Z (scale e*(2:ℝ)^k.2.2.2)≤ length Z (c x₁).2.2+Real.logb Z 3 :=
      fun e=> by rw [hY₂];exact hscaled _ e hx2p
    have hsource := hterminal k.2.1 k.1 ((2:ℝ)^k.2.2.1) ((2:ℝ)^k.2.2.2)
      (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
      (by
        have ht₁ := (dyadicTop_spec (c x₁).2.1 hx1p).1
        have ht₂ := (dyadicTop_spec (c x₁).2.2 hx2p).1
        rw [hY₁,hY₂]
        rcases (hgood x₁ hx₁).2.2.2.2.1 with ⟨h1,h2⟩|⟨h1,h2⟩
        · exact Or.inl ⟨by linarith,by linarith⟩
        · exact Or.inr ⟨by linarith,by linarith⟩)
      (fun e=>⟨(hlen1 e).trans (by linarith [length_le_of_le_rpow Z _ L hZ1 hL hu1]),
        (hlen2 e).trans (by linarith [length_le_of_le_rpow Z _ L hZ1 hL hu2])⟩)
      (fun e=> by change _≤ gP r+2*Real.logb Z 3;linarith [hlen1 e.1,hlen2 e.2])
    have hscaleF : ∀x∈F,2*(((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*dyadicScale (x.n 1))≤ Z^(Real.logb Z Kc) := by
      intro x hx
      have hxg := (Finset.mem_filter.mp hx).1
      have hf := (hgood x hxg).2.1
      have hxl := (hgood x hxg).1
      have hp : 0<((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*dyadicScale (x.n 1) :=
        mul_pos (absNorm_span_pos _ (mul_ne_zero r.hV₀ hf.twist_ne)) (dyadicScale_pos _)
      have he : ((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*dyadicScale (x.n 1)=Z^(gEnvelope r x) :=
        (Real.rpow_logb hZ0 hZ1.ne' hp).symm
      rw [Real.rpow_logb hZ0 hZ1.ne' hKc0,he,hKc]
      have hh : gEnvelope r x≤ H+mesh := by linarith [(abs_le.mp (henv' x hxl)).2]
      have := Real.rpow_le_rpow_of_exponent_le hZ1.le hh
      linarith
    have hfibreF : ∀y:O,y≠0 → ‖eisEmbedding y‖^2≤ Z^(Real.logb Z Kc) →
        ∑x∈F.filter (fun x=> x.twist∣y),gWeight x≤ Z^(ε/8) := by
      intro y hy hyK
      have hKcM : Kc≤ Z^(Mmax+2) := by
        have hle : H+mesh≤ Mmax+1/2 := by linarith
        have h1 := Real.rpow_le_rpow_of_exponent_le hZ1.le hle
        have h2 : Z^(Mmax+2)=Z^(Mmax+1/2)*Z^(3/2:ℝ) := by rw [←Real.rpow_add hZ0];ring_nf
        have h3 : 0≤ Z^(Mmax+1/2) := Real.rpow_nonneg hZ0.le _
        rw [hKc,h2];nlinarith
      have hyN : ((Ideal.span {y}).absNorm:ℝ)≤ Z^(Mmax+2) := by
        rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span y]
        rw [Real.rpow_logb hZ0 hZ1.ne' hKc0] at hyK
        exact hyK.trans hKcM
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx=>?_) (fun x _ _=> gWeight_nonneg x))
        (hfib' y hy hyN)
      obtain ⟨hxF,hxy⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(hgood x (Finset.mem_filter.mp hxF).1).1,hxy⟩
    have hb := hclass k.2.1 mesh Z η ω₁ ω₂ r v k.1 (Real.logb Z Kc) Hsource loss Kterm Cred
      (ε/8) (ε/(48*max 1 θ.Bmask)) (Z^(ε/8)) hM0 hM2 hKterm0 hCred.le (by positivity)
      (Real.rpow_nonneg hZ0.le _) F (fun x hx=>(hgood x (Finset.mem_filter.mp hx).1).2.1)
      hscaleF (fun x=>(c x).2.1) (fun x=>(c x).2.2) ((2:ℝ)^k.2.2.1) ((2:ℝ)^k.2.2.2)
      (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
      (fun x hx=> by
        obtain ⟨h1,h2,h3,h4⟩ := hFk x hx
        have hxg := (Finset.mem_filter.mp hx).1
        obtain ⟨-,-,hp1,hp2,-,-,-⟩ := hgood x hxg
        have e1 : (2:ℝ)^k.2.2.1=dyadicTop (c x).2.1 := by rw [dyadicTop,h3]
        have e2 : (2:ℝ)^k.2.2.2=dyadicTop (c x).2.2 := by rw [dyadicTop,h4]
        rw [e1,e2]
        exact ⟨hp1,(dyadicTop_spec _ hp1).1,(dyadicTop_spec _ hp1).2,
          hp2,(dyadicTop_spec _ hp2).1,(dyadicTop_spec _ hp2).2⟩) hfibreF hsource
    apply (le_of_eq ?_).trans (hb.trans_eq ?_)
    · apply Finset.sum_congr rfl
      intro x hx
      rw [hEF x hx]
      rfl
    · change _=Bclass
      unfold Bclass loss
      congr 1
      congr 1
      ring
  -- (4) count of classes
  set klo := ⌈- Real.logb 2 θ.b⌉
  set khi := ⌈L * Real.logb 2 Z⌉
  have himg_sub : img ⊆ (Finset.univ : Finset DictIdx) ×ˢ (Finset.univ : Finset (Finset (Fin θ.N))) ×ˢ
      (Finset.Icc klo khi ×ˢ Finset.Icc klo khi) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hl1, hl2⟩ := hlow x hx
    obtain ⟨hu1, hu2, -⟩ := hup x hx
    obtain ⟨-, -, hp1, hp2, -⟩ := hgood x hx
    simp only [key, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
    exact ⟨⟨dyadicIndex_lower _ _ hb0 hl1, dyadicIndex_upper _ Z L hp1 hZ0 hu1⟩,
      ⟨dyadicIndex_lower _ _ hb0 hl2, dyadicIndex_upper _ Z L hp2 hZ0 hu2⟩⟩
  have hcard : (img.card : ℝ) ≤ Z^(ε/16) := by
    have h1 : (img.card : ℝ) ≤ ((Fintype.card DictIdx : ℝ) * 2^θ.N) *
        ((Finset.Icc klo khi).card : ℝ)^2 := by
      have := Finset.card_le_card himg_sub
      rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
        Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at this
      have : (img.card : ℝ) ≤ ((Fintype.card DictIdx * (2^θ.N * ((Finset.Icc klo khi).card *
          (Finset.Icc klo khi).card)) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have h2 := card_dyadic_le L θ.b Z hL θ.hb1 hZ1.le
    have h3 : ((Finset.Icc klo khi).card : ℝ)^2 ≤ (L * Real.logb 2 Z + Real.logb 2 θ.b + 2)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
    have h4 : 0 ≤ (Fintype.card DictIdx : ℝ) * 2^θ.N := by positivity
    calc (img.card : ℝ) ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h4
      _ ≤ _ := hcount
  -- (5) sum over classes
  have hsum : ∑ x ∈ good, wt x * E x ≤ (img.card : ℝ) * Bclass := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem key hx)]
    calc ∑ k ∈ img, ∑ x ∈ good.filter (fun x => key x = k), wt x * E x
        ≤ ∑ _k ∈ img, Bclass := Finset.sum_le_sum hclassB
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- (7) exponent
  have hpriceT : price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) ≤
      price.f w₀ (gP r) (∑ i, r.w i) H + price.lip * (2 * Real.logb Z 3) +
        price.lip * (Real.logb Z 2 + mesh) := by
    have h1 := price.lipP w₀ (gP r) (∑ i, r.w i) (Real.logb Z Kc) (2 * Real.logb Z 3)
      (by linarith)
    have h2 := price.lipM w₀ (gP r) (∑ i, r.w i) H (Real.logb Z 2 + mesh)
    rw [show H + (Real.logb Z 2 + mesh) = Real.logb Z Kc by rw [hlogKc]; ring,
      abs_of_nonneg (by linarith)] at h2
    linarith
  have hexp : r.kLog - r.colLog + (ε/8 + ε/16) + ε/8 + ε/16 +
      (Real.logb Z Kc + price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) + ε/8) ≤ tgt := by
    have hlip := price.lip_nonneg
    have a1 := mul_le_mul_of_nonneg_left hl23 hlip
    have e1 : (1 + 3*price.lip) * Real.logb Z 3 = Real.logb Z 3 + 3*(price.lip*Real.logb Z 3) := by
      ring
    have e2 : (3 + price.lip) * mesh = 3*mesh + price.lip*mesh := by ring
    have e3 : price.lip * (2 * Real.logb Z 3) = 2*(price.lip*Real.logb Z 3) := by ring
    have e4 : price.lip * (Real.logb Z 2 + mesh) = price.lip*Real.logb Z 2 + price.lip*mesh := by
      ring
    linarith [hl3, e1, hmeshε, e2, hpriceT, e3, e4, a1, hlogKc, hHle, hl23, hl2, htgt]
  have hzpart := zpart Z r.kLog r.colLog
    (Real.logb Z Kc + price.f w₀ Pbd (∑ i, r.w i) (Real.logb Z Kc) + ε/8) tgt (img.card : ℝ)
    r.vol (ε/8 + ε/16) (ε/8) (ε/16) hZ1 (Real.rpow_logb hZ0 hZ1.ne' hvol).symm hvol
    (Nat.cast_nonneg _) hcard hexp
  have hδB : 3*(ε/(48*max 1 θ.Bmask))*θ.Bmask≤ε/16 := by
    have hp : 0< max 1 θ.Bmask := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have h1 := mul_le_mul_of_nonneg_left (le_max_right 1 θ.Bmask)
      (show 0≤3*(ε/(48*max 1 θ.Bmask)) by positivity)
    have he : 3*(ε/(48*max 1 θ.Bmask))*max 1 θ.Bmask=ε/16 := by field_simp;ring
    linarith
  have hzδ : Z^(ε/8+3*(ε/(48*max 1 θ.Bmask))*θ.Bmask)≤ Z^(ε/8+ε/16) :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have hp : 0≤(4*Cred*Cclass)*Cterm*gAmp L θ mesh η Z r deg controls*(1+‖v‖)^(2*deg) := by
    have : 0≤ gAmp L θ mesh η Z r deg controls := by unfold gAmp;have := r.one_le_height;positivity
    positivity
  have hzpart' : Z^r.kLog/r.vol^2*Z^(ε/8+3*(ε/(48*max 1 θ.Bmask))*θ.Bmask)*r.vol*
      Z^(ε/8)*(img.card:ℝ)*Z^(Real.logb Z Kc+price.f w₀ Pbd (∑i,r.w i) (Real.logb Z Kc)+ε/8)≤ Z^tgt := by
    apply le_trans ?_ hzpart
    gcongr
  calc (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η r x v)
      ≤ r.norm*((img.card:ℝ)*Bclass) := hstep1.trans (mul_le_mul_of_nonneg_left hsum hnorm0)
    _ = ((4*Cred*Cclass)*Cterm*gAmp L θ mesh η Z r deg controls*(1+‖v‖)^(2*deg))*
        (Z^r.kLog/r.vol^2*Z^(ε/8+3*(ε/(48*max 1 θ.Bmask))*θ.Bmask)*r.vol*
          Z^(ε/8)*(img.card:ℝ)*Z^(Real.logb Z Kc+price.f w₀ Pbd (∑i,r.w i) (Real.logb Z Kc)+ε/8)) := by
        rw [hBclass,hKterm];unfold GSrc.norm gAmp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hzpart' hp

#print axioms terminal_frame_grouped_at
end
end QRH.Cycle092.RegularColoredForward
