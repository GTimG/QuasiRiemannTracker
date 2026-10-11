# A local physical moment with capacity 4.498

**11 October 2026 — internally reviewed manual source proof; formal interface pending.**
This is a proposed arithmetic strengthening of the physical two-plain
moment near the quartic corner. Its proof uses the existing moment with
capacity \(9/2\) on every remaining child, and the existing unmarked
zero-density bound. It does not introduce an improved moving-character
induction. This manuscript has not passed Lean or kernel verification.
A stronger tracker theorem still requires its complete numerator adapter,
endpoint certificate, original family recovery and verification.

## 1. Exact local statement

Use the original physical natural family of B3.4 of the
[pinned Cycle25 manuscript](https://github.com/HaileyStorm/QuasiRiemannTracker/blob/58344dfdbe756cf2f743da1908ffe0582418cf5b/public/proofs/cycle25-quartic-20261010/paper.tex).
The parent whole-product character is a fixed finite ray character times
\(\chi_n(k)\); its defining ray modulus is fixed independently of \(U\).
An arbitrary common puncture of norm at most \(U^B\) is allowed, with
every original nonunit zero retained. There is **no parent moving
character factor of positive width**. Fixed defining moduli are handled
by their original arbitrarily small width padding.

Put \(U=Z^M\), with \(M>0\), \(A=n_1+n_2+z\), and require
\[
 \frac{41M}{100}\le n_i\le\frac{11M}{25},\qquad
 \frac{3M}{100}\le z\le\frac M{25},\qquad
 n_1+n_2+\frac{2249}{500}z\le M.
 \tag{LP.1}
\]
The slots are genuine canonical good-prime slots with the original one
common smooth profile and individual fixed relative ray characters.
Their real norm powers and heights may be independent; the two plain
profiles, real powers and heights may also be independent. The original
literal FixedInducingRow eligibility predicate is used. For every
requested \(\epsilon>0\), the proposed conclusion is
\[
 \boxed{\quad
 \sum_{k\ {\rm eligible}}
 |S_k(Z^{n_1})S_k(Z^{n_2})Q_{k,I}|^2
 \ll Z^{M+\epsilon}\mathcal H_J .
 \quad}
 \tag{LP.2}
\]
Here \(\mathcal H_J\) is the original finite-seminorm and polynomial-height
allowance. The common fine mesh is selected before the arithmetic data,
eventual fixed slot count, profiles and heights, in the original order.
The conclusion includes the four annular derivative-profile pairs and
the bounded scale-box recovery used by the physical numerator.

For the proof retain the already proved B3.40 moment with
\(C_{\rm base}=9/2\), available from the imported \(7/8\) theorem.
Set
\[
 g=(n_1+n_2+(9/2)z-M)_+,\qquad
 a=M/2000,\qquad \sigma=3a,\qquad k_0=7/10.
 \tag{LP.3}
\]
LP.1 implies \(g\le M/12500<M/10000\). The auxiliary prime pool has
norms \(Z^a/2<Np\le Z^a\). Choose the live-slot mesh much smaller than
\(a\), so the pool is disjoint from every live slot window. Normalizing
the base to \(U\) makes \(a/M=1/2000\) fixed; no new width-band induction
is performed.

## 2. Parent comparisons and terminal branches retain strict slack

LP.1 gives \(A\ge85M/100>5M/6\), \(n_i>M/4\), and
\[
 A\le M-\frac{1749}{500}z\le\frac{44753}{50000}M<M-M/10.
 \tag{LP.4}
\]
Center the original source using \(L=M/4\) and the two equal-product
rectangles of (B3.50). Their common product, whole-product norm power,
natural mask and original slot coefficients are unchanged.

The unreflected comparison lengths are \(M/4,n_1+n_2-M/4\).
Reflect the longer comparison factor only when bounding this comparison
separately, by the exact whole-factor reflection (B3.44). Its plain total
is at most \(3M/2-(n_1+n_2)+\xi\); consequently its base capacity is
at most
\[
 3M/2-(n_1+n_2)+(9/2)z+\xi\le 43M/50+\xi<M.
 \tag{LP.5}
\]
The existing \(9/2\) moment bounds it directly. This does not apply a
Poisson formula to an eligibility indicator.

For an additional common mask, expand that mask **only when bounding
the comparison**, using (B3.41). Its two divisor normalizers and frozen
prime-slot coefficients have total mass \(Z^{o(1)}\). The first natural
plain daughter is at most \(M/4\); reflect the second natural daughter
only if it exceeds \(M/2\), by (B3.44). Each retained second daughter
then has length at most \(M/2+\xi\). Thus every comparison daughter has
plain total at most \(3M/4+\xi\), and global-base capacity at most
\(3M/4+(9/2)M/25+\xi=93M/100+\xi<M\).
Nonempty clipped scales have the original bounded dilation. This
proves uniform comparison payment without applying LP.1 to shortened
mask daughters. The mask in the original centered difference is retained
on the whole product in both rectangles.

The first zero frequency is paid exactly as in B3.6. The second zero
frequency's excess (B3.61) is at most
\(A-M+5\sigma/3+\delta_1\), which is strictly negative by LP.4.
The added zero Gauss row is not amplified and retains (B3.57)'s direct
count.

Fixed-inducing children retain the exact centered rectangle cancellation
in B3.9, including their forced congruence residues, original masks and
all raw extraction scalars. In (B3.80) the actual maximum over \(v\ge0\)
is \(A-M\), attained at \(v=M/4\). Keep this negative value instead of
replacing it by \((A-M)_+\). Thus its fixed terminal loss \(3\sigma\)
and all support padding fit into LP.4's strict reserve. This is essential:
with fixed \(a=M/2000\), the old coarse terminal loss cannot be relabeled
as an arbitrarily small requested \(\epsilon\).

For the main norm enlarged to the envelope in LP.10, check the first
exceptional reserve again rather than assuming its former row radius.
Substitution in B3.75 gives
\(F_1=(c+5d+R+E)/6+B_c-5a\) when \(c\ge d\), and
\(F_1=c+(R+E)/6+B_c-5a\) when \(c\le d\).
The definition \(B_c=(3c-5d-R)_+/6\) implies in both cases
\(F_1\ge2c/3-5a\). Together with the unchanged
\(F_2\ge2b_2/3\), this preserves the centered exceptional estimate
with error at most \(3\sigma\). The error alternatives retain their
original row enlargements.

## 3. Low-zero nonexceptional main children use the old moment

Complete both Poisson transformations, full mutual coprimality projectors,
priority allocations, all natural masks and exact child eligibility as
in B3.6--B3.8. At the second nonexceptional child, form buffered zero bins
for one fixed conjugation-stable group containing both sides' reciprocity
ray expansions, their inverses, and all possible surviving relative slot
characters. Choose this group before live arithmetic labels. Attach the
buffered bin to the effective integer row \(w\) of §4; the complete
projector allocation changes only outside scalars and masks, not its
primitive character or bin. The moving row factor is retained.
The classification occurs after Poisson; its indicator is not Poisson
summed.

Its additional common mask is also kept throughout this calculation.
The pointwise plain estimate uses
\(L(s,\psi^*)\prod_{p\mid R}(1-\psi^*(p)(Np)^{-s})\); on the buffered
positive half-plane the polynomial-size deleted product has the original
arbitrarily small power cost. Deleting masked primes from a canonical
prime sum changes it by only its centrally normalized \(O(\log Z)\)
prime terms. Consequently both pointwise costs remain uniform, with
the original literal zeros, even when the mask depends on frozen labels.

Call a bin low when its buffered maximum zero parameter is at most
\(k_0=7/10\), with sufficiently small boundary buffering. On these actual
rows, the pointwise prime estimate (B0.16) charges at most \(k_0 d_z\)
in squared norm for removing slots of total width \(d_z\), plus its
reserved small errors. It retains the original natural zeros.

The exact global-base child defect of (B3.71), with the relaxed parent
condition, is
\[
 F_{\rm act}\le g+6a+\delta_1+2\theta_N.
 \tag{LP.6}
\]
A single greedy prefix removes this defect at rate \(9/2\) per slot width.
After removal, apply the **existing** \(9/2\) child moment to the exact
canonical natural state, enlarging its nonnegative norm only at this
point. If no slot remains, apply the existing unrestricted zero-slot
moment. No improved low-zero child theorem is called.

Since \(\Delta\ge a\), the strict numerical reserve before the mesh and
support errors is
\[
 a-\frac{k_0}{9/2}(6a+g)
 \ge\frac M{2000}-\frac7{45}
       \left(\frac{3M}{1000}+\frac M{10000}\right)
 =\frac{4M}{225000}>0.
 \tag{LP.7}
\]
Choose the mesh and aggregate buffering errors much smaller than this
fixed reserve. The common two-side count and extraction scalars still
obey (B3.69); the Cauchy step averages the two costs rather than doubling
them. Row-dependent holes are retained in the canonical state and every
fixed-inducing child is handled in §2.

## 4. High-zero main children are counted jointly with the labels

Here the parent old moving width is zero. Let the first common-support
widths be \(c,d,p\), the active common conductor width \(R\), and the
mask-divisor width \(E\). Let \(T=(c-d)_+\), and let
\(\delta\in[7/10,3/4]\) denote a buffered high-zero bin parameter.
Use the existing unmarked zero density
\[
 R_0(\delta)=1-\frac{10\delta}{3(5-2\delta)}.
 \tag{LP.8}
\]
It counts all raw non-fixed-inducing rows, not just sixth-power-free rows:
write \(j=k b^6\) and sum
\((H/(Nb)^6)^{R_0(\delta)+\epsilon}\). This converges because
\(R_0(\delta)\ge2/7>1/6\). Positive-real zeros of the primitive
character are unchanged by the retained imprimitive Euler holes.

The actual first CRT factor in (B3.52) is
\(\chi_a(br)\overline{\chi_b(ar)}\overline{\xi_r(ab)}\).
Thus its two separated column twists have opposite \(\xi_r\) signs:
on the C-side a prime of net exponent \(t\) contributes
\(e_C=(1-t)\bmod6\); on the D-side it contributes
\(e_D=(1+t)\bmod6\). Fixed reciprocity ray phases belong to one fixed
finite character list. If a residue is zero its original puncture remains.

On the C-side put
\[
 L_C=\sum_{p\mid r}e_C(p)\log_ZNp,\qquad
 R_{\rm zero}=\sum_{\substack{p\mid r\\e_C(p)=0}}\log_ZNp.
 \tag{LP.9}
\]
The first enlarged row width, with its original main density, has
\[
 K+g_{\rm enl}=K_0+(d-c)_++6a,\qquad
 K_0=2A-c-d+R+E-M.
 \tag{LP.10}
\]
Use this envelope as the actual smooth main row ball before the second
Poisson transformation. Its extra radius is
\(g_{\rm enl}=K_0-K+(d-c)_++6a\), with the original frequency padding
reserved separately. The initially retained positive row norm is bounded
by this enlargement. This choice gives the main child increment
\(6a-\min(c,d)-(c_2-g_2)-t_2\le6a\), so LP.6 is preserved.
After the second full-common-support extraction the true character row
is the **integer**
\[
 w=F_C\,e\,G_cV_{\rm id}h',\qquad
 F_C=\prod_{p\mid r}p^{e_C(p)},
 \quad \log_Z Nw\le M-R-T+L_C-6a+o(1).
 \tag{LP.11}
\]
Its zero-extended whole-product character is a fixed ray character times
\(\chi_n(w)\), with all canceled-prime holes retained.
If the nominal bound on \(\log_ZNw\) is negative beyond the aggregate
support tolerance, its integral row range is empty. On a nonempty
bounded or subunit window it is at least minus that tolerance; replacing
it by zero costs only the same reserved support error. Density is never
applied as a count smaller than one on a nonempty integral window.

At fixed \(w\), every active first common prime, every mask-divisor prime
and every second common prime is reconstructible from its divisors.
Indeed \(G_cV_{\rm id}\mid w\), and
\(\operatorname{rad}(D_2E_2)\mid G_c\); the first residual projector
label \(s\) divides this second radical. Bounded-range powers, priority
allocations and fixed slot assignments have the source's arbitrarily
small divisor cost. The first primes absent from this integer index
must be counted separately: their total width is
\[
 p-R-E+R_{\rm zero}.
 \tag{LP.12}
\]
This includes all inactive net-zero common primes. They are not declared
divisors of \(w\). Counting their radical and then bounded-range powers
costs that width plus an arbitrarily small power.

The first common-label and projector counts must therefore stay inside
the positive norm until LP.11--12 are used. Removing an independent
\(Z^{p+s_0}\) count and subsequently treating the twists as fixed is a
different, weaker estimate. The complete projector is retained, including
its original Möbius signs; after its actual allocations (B3.67--69), all
remaining row weights and scalars are bounded only in positive or
absolute expressions. Its normalized divisor count and both central
extraction scalars cancel as in (B3.69). The label \(s\) is also divisor
many at fixed \(w\), so no extra \(s_0\) tax appears.
This is a norm aggregated over the original \(s\)-labels: its target
has no \(-s_0\), and there is no subsequent \(Z^{s_0}\) multiplication.
The low-bin per-\(s\) incumbent bound instead retains \(-s_0\);
its label count cancels that term in the original manner.

Let \(b_2,g_2,t_2\) be the second common widths. The two centrally
normalized residual whole products have paired pointwise exponent
\(\delta(A-c-b_2)\). The actual second outside exponent is
\[
 A-\min(c,d)+R+E-M+5a+g_2-t_2-b_2.
 \tag{LP.13}
\]
The full kernel is separated by the original common-profile lemma with
its uniformly weighted Fourier measure outside all label and row sums.
Construct that measure on the ambient sector box, including the aggregate
norm ratios of \(F_C\) and \(e\), before choosing live labels or bins.
Relations among their norms restrict evaluation points, not the measure.
Apply the first Cauchy inequality to the Hilbert space with the first
common and projector labels still present; only then count the high part
by joint reconstruction and the low part by the incumbent per-label bound.
All independent plain heights, derivative profiles and original zeros
stay in this measure or the exact arithmetic coefficient, as appropriate.

Consequently, against the C-side **joint** nominal allowance
\(p+A-c+R+E+B_c\), its high contribution has excess at most
\[
 \begin{aligned}
 &M(R_0(\delta)-1)+\delta A+a(5-6R_0(\delta))\\
 &\quad +(1-R_0(\delta))T-\delta c-(1+R_0(\delta))R
     -E-B_c+R_0(\delta)L_C+R_{\rm zero}\\
 &\quad +g_2-t_2-(1+\delta)b_2+\epsilon.
 \end{aligned}
 \tag{LP.14}
\]
This is an exact exponent ledger before the small support padding.
The second line is nonpositive. To see this, write
\(c=\min(c,d)+T\), use \(R_0(\delta)+\delta>1\),
\(\min(c,d)\ge p\), \(L_C\le5(R-R_{\rm zero})\), and \(R\le p\).
Since \(R_0(\delta)\ge2/7\), its \(R_{\rm zero}\) coefficient
\(1-5R_0(\delta)\) is negative. The resulting upper bound is
\[
 (4R_0(\delta)-1-\delta)p-E-B_c
 \le-\frac{79}{270}p-E-B_c<0
 \quad(p>0).
 \tag{LP.15}
\]
The final common-support line is at most
\(-\delta b_2-t_2\), because \(g_2\le b_2\). The D-side is obtained
by exchanging the original sides, with no identification of their
independent heights.

It remains to pay the first line of LP.14. LP.1 implies the weaker gate
\(A\le M-(16/5)z\), \(z\ge3M/100\).
The function \(R_0(\delta)+\delta A/M\) decreases for
\(7/10\le\delta\le3/4\). At \(\delta=7/10\) its strict deficit is at
least \(259/16875\). Since \(a=M/2000\) and
\(5-6R_0(\delta)\le23/7\), every total support, coefficient, height
and buffering power loss below \(M/1000\) leaves a deficit greater
than \(M/100\). Thus each joint high norm is paid with a positive-power
reserve. Weighted Cauchy over the shared first labels now uses the
original balance (B3.56); it does not add their count a second time.

## 5. Extracted amplifier errors use their existing strict reserves

For the three actual valuation alternatives \(1,6,7\), use the unamplified
second transform and the existing \(9/2\) moment. With
\(\lambda=\log_ZNp\), their actual pairs are
\[
 (w,w_o)=(\lambda,\lambda),(6\lambda,0),(7\lambda,\lambda),
 \qquad \lambda\ge\sigma/4
 \tag{LP.16}
\]
after increasing the eventual threshold. The normalized prime average
is retained; no second prime count is introduced.

The fine (B3.70) inequality is
\[
 F_{\rm act}\le g+\sigma+w-w_o+\delta_1+2\theta_N.
 \tag{LP.17}
\]
When its \(J\ge0\), the sharper increment is
\(\sigma-c-w\); when \(J<0\), it is
\(\sigma+w-w_o+\delta_1\). The base cost is at most
\(F_{\rm act}/6\), whereas \(\Delta\ge w\). With
\(\sigma=3M/2000\), \(g\le M/10000\), the reserves before padding
are at least
\[
 \frac{13M}{120000},\qquad
 \frac{193M}{120000},\qquad
 \frac{119M}{60000},
 \tag{LP.18}
\]
respectively. These calculations retain every moving phase in the
valuation-one and valuation-seven errors, their squared extraction
coefficient, common puncture and all previous holes. No zero-bin
heredity is required in these error branches.

## 6. Uniform errors, recovery and verification obligations

Fix the requested final loss first. Choose all support, frequency,
coefficient, mask and buffered-bin losses below the minimum of a small
share of that loss and a small share of LP.7's fixed reserve. Choose one
greedy mesh smaller than this reserve and smaller than \(a/10\).
After fixing the finite slot system, use the one aggregate support
tolerance \(\theta_N\), the original exact clippings, and the complete
divisor bounds. Greedy overshoot is one mesh, not a loss per slot.

The current proof has only the two genuine transforms plus calls to
already proved moments and row density. Choose finite profile and height
orders backwards through this finite graph, then choose the analytic
height exponent, and finally the eventual \(U\)-threshold. Fourier
parameters remain outside the arithmetic sums; their weighted masses
pay the requested independent heights and derivatives. Original
principal/fixed-inducing source terms are treated by §2, not omitted.
Additional fixed masks stay in the original centered source. Their
comparison-only expansion and uniform pointwise payment were specified
in §§2--3; no local-capacity assertion is made for arbitrarily shortened
mask daughters.

The translation from this manual source proof to the literal physical
initialState and its Euler packet requires independent interface review.
The joint high-bin reconstruction, low-child use of the incumbent moment,
common-mask comparison and fixed-amplifier reserves passed independent
internal review of the actual source formulas. LP.2 still awaits its formal
physical-state implementation; these are not kernel acceptance claims. A complete
tracker theorem must also retain the numerator's powerful conductor
deficits, free Euler shifts, original supremum recovery, principal
signal and all three function families. No target or receipt may claim
this extension before its actual source proof and all dependencies have
been verified.
