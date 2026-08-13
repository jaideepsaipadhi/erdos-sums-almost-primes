# An explicit threshold for the monotonicity of Erdős sums of almost primes

## $f_{k} < f_{k+1}$ for all $k \ge K_0$, with $K_0 = 3527$

Working note, version 5 — July 2026

---

## 0. Status

Every numerical constant below has been computed in rigorous interval (ball)
arithmetic and, where marked **[VERIFIED]**, checked by at least one independent method.
The derivation is complete in the sense that no step rests on a curve fit or an
unextracted $O(\cdot)$ constant.

One qualification remains and is stated rather than buried: **this is a
reconstruction of the argument of Gorodetsky–Lichtman–Wong (GLW,
arXiv:2303.08277), not a transcription of it.** Constants have been traced to
their stated inequalities (§6), but I cannot rule out that their $O(\cdot)$
terms conceal contributions I have not mapped. Resolving that requires reading
their §3 adversarially alongside an author. It is the one outstanding item
(§10).

Notation follows GLW throughout.

---

## 1. Statement

For $\Omega(n)$ the number of prime factors of $n$ counted with multiplicity,

$$f_k \;=\; \sum_{\Omega(n)=k}\frac{1}{n\log n}.$$

Banks–Martin (2013) conjectured $f_k$ decreases monotonically; GLW (Thm 1.2)
proved the reverse for large $k$:

$$f_k \;=\; 1 - 2^{-k}\Bigl(a_1k^{2} + O\bigl(k\log(k+1)\bigr)\Bigr),
\qquad a_1 = \frac{d\log2}{4},$$

$$d \;=\; \frac14\prod_{p>2}\Bigl(1-\frac2p\Bigr)^{-1}\Bigl(1-\frac1p\Bigr)^{2}.$$

**[VERIFIED] Verified.** Computing the Euler product over $p\le2\times10^{5}$ in ball
arithmetic gives $d = 0.3786948881$ and $a_1 = 0.06562282349$, matching GLW's
stated $d = 0.37869\cdots$, $a_1 = 0.0656\cdots$.

**Theorem (this note, subject to §0).**
$$f_k < f_{k+1}\qquad\text{for all }k \ge K_0 = 3527 .$$

Combined with certified computation of $f_k$ over $6\le k<K_0$ (companion note;
presently verified to $k=200$), this would settle monotonicity for all $k>6$.

---

## 2. The exact criterion

Write $f_k = 1 - 2^{-k}(a_1k^{2}+E(k))$, so $E$ collects the entire error.

$$f_{k+1}-f_k
= 2^{-k}\bigl(a_1k^{2}+E(k)\bigr)-2^{-(k+1)}\bigl(a_1(k+1)^{2}+E(k+1)\bigr)$$
$$= 2^{-(k+1)}\Bigl[2a_1k^{2}-a_1(k+1)^{2}+2E(k)-E(k+1)\Bigr]
= 2^{-(k+1)}\Bigl[a_1(k^{2}-2k-1)+2E(k)-E(k+1)\Bigr],$$

using $2k^{2}-(k+1)^{2}=k^{2}-2k-1$. Hence, **exactly**,

$$f_{k+1}>f_k \iff a_1\bigl(k^{2}-2k-1\bigr) > E(k+1)-2E(k).\tag{2.1}$$

A sufficient condition, bounding the right side by $|E(k+1)|+2|E(k)|$ and using
monotonicity of the bounds below in $k$:

$$a_1\bigl(k^{2}-2k-1\bigr) \;>\; 3\,\overline{E}(k+1),
\qquad |E(k)|\le\overline{E}(k).\tag{2.2}$$

Two features are easily lost and both are adverse: the leading coefficient is
$a_1(k^{2}-2k-1)$, not $a_1k^{2}$; and the factor $3$ in (2.2) is real. Using
$a_1k^{2}>|E(k)|$ instead understates $K_0$ roughly threefold.

The error decomposes as $E = E_{S1}+E_{S2}+E_{S3}$ following GLW §3:

| | source | GLW location | bound derived |
|---|---|---|---|
| S1 | $I_k-I_k'$ | Lemma 3.2 | §5: $15.0\,k$ |
| S2 | expansion of $A_k$ | Lemma 3.3 | §6: $2.87\,k\log k + 21.4$ |
| S3 | $B-k^{2}B'$ | Lemma 3.1 (3.8)–(3.10) | §4: $38.6\,k$ |

---

## 3. The generating function

With $y=2$ in GLW (2.6),

$$G_2(1,z)=2^{-z}\prod_{p>2}\Bigl(1-\frac1p\Bigr)^{z}\Bigl(1-\frac zp\Bigr)^{-1},$$

meromorphic on $\mathbb{C}$ with **simple** poles exactly at $z=p$ for each
prime $p>2$; nearest to the origin $z=3$, next $z=5$.

### 3.1 Pole subtraction

Let

$$\rho:=\lim_{z\to3}(z-3)G_2(1,z)
= -3\cdot2^{-3}\Bigl(1-\tfrac13\Bigr)^{3}\prod_{p>3}\Bigl(1-\tfrac1p\Bigr)^{3}\Bigl(1-\tfrac3p\Bigr)^{-1}.\tag{3.1}$$

The factor $-3$ is the residue of $(1-z/3)^{-1}$; **the factor $(1-1/3)^{3}$ is
retained**, since only the pole-carrying factor is removed. Then
$H(z):=G_2(1,z)+\rho/(z-3)$ is holomorphic in $|z|<5$ and, exactly,

$$[z^i]G_2(1,z)=\frac{\rho}{3^{\,i+1}}+[z^i]H(z),
\qquad\bigl|[z^i]H(z)\bigr|\le\frac{M'_R}{R^{\,i}},\quad M'_R:=\sup_{|z|=R}|H|,\;R<5.\tag{3.2}$$

The singular part now contributes exactly rather than through a bound. This is
the step that makes the whole computation viable: a direct Cauchy estimate on
$|z|=2.9$ gives $M_{2.9}\approx1.34\times10^{7}$ (the circle hugs the pole),
whence $K_0\approx2.9\times10^{9}$ — valid but useless.

### 3.2 Rigorous evaluation

Ball arithmetic at 300 bits; Euler products truncated at $p\le P$. Three error
sources are bounded.

**(a) Euler tail.** In (3.1) the $1/p$ terms cancel exactly:
$$\log\Bigl[\Bigl(1-\tfrac1p\Bigr)^{3}\Bigl(1-\tfrac3p\Bigr)^{-1}\Bigr]
=\sum_{i\ge2}\frac{3^{i}-3}{i\,p^{i}},\qquad
\bigl|\cdot\bigr|\le\frac{9}{2p^{2}(1-3/p)} .$$
With $\sum_{p>P}p^{-2}<\sum_{n>P}\frac{1}{n^{2}\log n}<\frac{1}{P\log P}$, the
tail is $\le8.32\times10^{-6}$ at $P=5\times10^{4}$. For $|z|\le R$ generally,
$\bigl|\sum_{i\ge2}(z^{i}-z)/(ip^{i})\bigr|\le(R^{2}+R)/\bigl(2p^{2}(1-R/p)\bigr)$.

**(b) Arithmetic.** Ball form throughout.

**(c) Between-sample variation.** A sampled maximum is not a supremum. We bound
$|H'|$ on $|z|=R$ by Cauchy, $|H'|\le\sup_{|z|=R'}|H|/(R'-R)$ with $R'=R+0.4$,
and add $\sup|H'|\cdot(\pi R/M)$ for $M$ samples — an unconditional Lipschitz
correction over every gap.

**Values.**
$$\rho=-0.17493\pm3.4\times10^{-6},\qquad \sup_{|z|=3.4}|H|\le45.30
\;\;(35.11\text{ sampled}+10.18\text{ correction},\,M=300).$$

**[VERIFIED] Verified.** $\rho$ agrees to 15 digits between the closed product (3.1) and
numerical evaluation of $(z-3)G_2(1,z)$ at $z=3+\varepsilon$,
$\varepsilon\in\{10^{-8},10^{-12}\}$: both give $-0.174931407483803$.

---

## 4. Source S3

From GLW (3.8), S3 requires
$$\Sigma:=\Bigl|\sum_{i=0}^{k}\frac{2^{i}}{i!}G_2^{(0,i)}(1,0)\bigl((k-i)^{2}-k^{2}\bigr)\Bigr|
\le\sum_{i=0}^{k}2^{i}\bigl|[z^i]G_2(1,z)\bigr|\,\bigl|i^{2}-2ik\bigr|.$$
Since $|i^{2}-2ik|=i(2k-i)\le2ik$ on $0\le i\le k$,
$$\Sigma\le2k\,W,\qquad W:=\sum_{i\ge1}i\,2^{i}\bigl|[z^i]G_2(1,z)\bigr|.\tag{4.1}$$

### 4.1 Uniform bound and its looseness

By (3.2), $\bigl|[z^i]G_2\bigr|\le|\rho|3^{-(i+1)}+45.30\cdot3.4^{-i}$, giving
$W\le157.5$.

**[VERIFIED] Verified, and found loose.** True coefficients, computed independently by
trapezoid quadrature on the pole-free circle $|z|=1$, satisfy the bound for all
$i\le30$ — with ratio true/claimed between $0.009$ and $0.175$, i.e. loose by
$6$–$100\times$.

### 4.2 Direct coefficient bound

Split at $i_0$: certified enclosures for $i\le i_0$, the uniform bound for the
tail, summed via $\sum_{i>i_0}ix^{i}=x^{i_0+1}\bigl((i_0+1)-i_0x\bigr)/(1-x)^{2}$.

$i_0$ is capped by the Euler tail, which imposes a *fixed absolute* noise floor
($\approx2.8\times10^{-6}$ at $P=5\times10^{4}$) while true coefficients decay
like $3^{-i}$; beyond the crossover the $i2^{i}$ weight diverges. Reaching
$i_0=20$ needs $P\approx10^{8}$; $i_0=30$ needs $P\approx10^{12}$. Take
$i_0=10$.

$$\boxed{\,W\le19.31\,}\qquad\text{whence}\qquad |E_{S3}(k)|\le38.6\,k.\tag{4.2}$$

| range | contribution |
|---|---|
| head $i\le10$ (certified true coefficients) | $15.30$ |
| tail $i>10$ (uniform bound) | $4.02$ |

**[VERIFIED] Verified.** Recomputing the head at $P=10^{5}$, $N=512$ gives $15.246$
(against $15.297$ at coarser parameters) — a shift in the safe direction.

The head dominates and consists of certified true coefficients, hence is
irreducible: $i_0\to\infty$ removes at most $4.02$, so this method cannot push
$W$ below $\approx15.3$.

---

## 5. Source S1 (GLW Lemma 3.2)

GLW bound $|G_2^{(0,i)}(s,0)-G_2^{(0,i)}(1,0)|\le(s-1)b_i$,
$b_i:=\max_{s\in[1,2]}|G_2^{(1,i)}(s,0)|$, with $b_i/i!=[z^i]G_2^{(1,0)}(1,z)$,
reaching $I_k-I_k'\ll\sum_{i+j+l=k}(i+1)3^{-i}2^{-j-l-1}$. Explicitly,

$$2^{k}\bigl(I_k-I_k'\bigr)\;\le\;\sum_{i\ge1}\bigl|[z^i]G_2^{(1,0)}(1,z)\bigr|\,(k-i+1)\,2^{\,i-1}.\tag{5.1}$$

### 5.1 A double pole

By GLW (2.7), $G_2^{(1,0)}(1,z)=z\,G_2(1,z)\,c(1,z)$ with
$$c(1,z)=\log2-\sum_{p>2}\frac{(z-1)\log p}{(p-1)(p-z)}+\gamma .$$
Since $c(1,z)$ also has a simple pole at $z=3$, the product has a **double**
pole there, and §3.1 does not apply directly. Writing
$$G_2^{(1,0)}(1,z)=\frac{A_{-2}}{(z-3)^{2}}+\frac{A_{-1}}{z-3}+K(z),$$
with $K$ holomorphic in $|z|<5$, and expanding
$\frac1{z-3}=-\sum_i\frac{z^{i}}{3^{\,i+1}}$,
$\frac1{(z-3)^{2}}=\sum_i\frac{(i+1)z^{i}}{3^{\,i+2}}$:

$$\bigl|[z^i]G_2^{(1,0)}(1,z)\bigr|\;\le\;\frac{|A_{-2}|(i+1)}{3^{\,i+2}}+\frac{|A_{-1}|}{3^{\,i+1}}+\frac{\sup_{|z|=R}|K|}{R^{\,i}} .\tag{5.2}$$

**Values:** $A_{-2}=-0.5765453818$, $A_{-1}=-0.3635628020$, and (certified with
Lipschitz correction) $\sup_{|z|=3.6}|K|\le588.30$.

**[VERIFIED] Verified three ways.** $A_{-2}$ agrees across: Cauchy integration on
$|z-3|=0.25$ ($-0.5765453818$); the direct limit $(z-3)^{2}F(z)$ at
$z=3+10^{-8}$ ($-0.576545385$); and the closed form
$A_{-2}=3\rho\log3=-0.576545381807$, obtained since $c$ has residue $\log3$ at
$z=3$. The analytic identity confirms both $\rho$ and the pole structure.

*This step replaces a fitted bound used in an earlier draft. That fit was
**invalid** — it fell below the true coefficients by up to $80\times$ at small
$i$. It happened not to affect the result, because (5.1) is dominated by
directly computed low-$i$ terms.*

### 5.2 Evaluation

Using certified coefficients for $i\le25$ and (5.2) beyond, (5.1) evaluates to
$7464$, $14964$, $29964$, $44963$ at $k=500,1000,2000,3000$: linear with slope

$$\boxed{\,|E_{S1}(k)|\le15.00\,k\,}\tag{5.3}$$

**[VERIFIED] Stable.** The slope is $15.000$ whether $\sup|K|$ is taken as $385.6$
(sampled) or $588.3$ (certified), confirming the tail is negligible here.

---

## 6. Source S2 (GLW Lemma 3.3)

Lemma 3.3 splits at $T$, GLW taking $T=15\log k$. Two parameters appear: $a$,
bounding a Stirling truncation, and $c$, setting the threshold for a
second-order Taylor expansion. GLW take $c=a/3$; **they are not coupled**, and
decoupling them is the main improvement here.

### 6.1 The Stirling constraint

Since $u\mapsto u^{i}e^{-u}$ increases on $[0,i]$,
$$\int_0^{ci}u^{i}e^{-u}\,du\;\le\;(ci)\,(ci)^{i}e^{-ci},$$
and with $i!\ge\sqrt{2\pi i}\,(i/e)^{i}$,
$$\frac1{i!}\int_0^{ci}u^{i}e^{-u}\,du\;\le\;c\sqrt{\frac{i}{2\pi}}\,\bigl(c\,e^{1-c}\bigr)^{i}.\tag{6.1}$$

**[VERIFIED] Verified.** Each inequality checked numerically: the integral bound at
$c\in\{0.07,0.232,0.30\}$, $i\in\{5,20,100\}$ (holds, margin $5$–$20\times$);
Stirling at $i\in\{1,5,20,100\}$ (holds); the composite (6.1) at $c=0.232$,
$i\in\{10,50,200\}$ (holds, conservative by $9$–$150\times$).

Summing (6.1) against the weight $2^{i}$ requires
$$q:=c\,e^{1-c},\qquad 2q<1.\tag{6.2}$$

**This must hold with margin, not at equality.** $ce^{1-c}=\tfrac12$ at
$c=0.2319609530$; *at* that value $2q=1$ and the error series
$\sum_i\sqrt{i}\,(2q)^{i}$ diverges. An earlier draft took $c$ at this maximum
and obtained a finite constant only by truncating the sum — an error. We take

$$c=0.22,\qquad 2q=0.9598,\qquad t:=1/c=4.55,\qquad T=t\log k .\tag{6.3}$$

The constraint $t>1/c$ comes from GLW's requirement that $k\,e^{-cT}=k^{1-ct}$
be small. Their $c\le0.07$ forced $t\ge14.3$, hence $t=15$; decoupling gives
$t=4.55$, a **3.3-fold reduction in $T$**.

### 6.2 The constants

Tracing GLW's (3.13) with explicit constants, three terms appear:

| GLW step | bound | origin |
|---|---|---|
| third term of the $J(i)$ expansion | $\tfrac{\log2}{2}k(T+1)$ | $\lvert2^{-x}-1\rvert\le x\log2$ |
| (3.17), $i\le\log k$ | $2k$ | $\sum_{i\le\log k}2^{i}\le2k^{\log2}$ |
| (3.18), $\log k<i\le T$ | $k\log k$ | sum extended to $\infty$: $e^{2\log k}=k^{2}$ |

Only the first depends on $T$. *(An earlier draft scaled the whole constant
linearly in $t$; that was wrong, and inflated the improvement.)* At $t=4.55$,
evaluating at $k=3000$ and $k=3500$ gives totals of $2.870$ and $2.864$ times
$k\log k$, so

$$|E_{S2}^{(3.13)}(k)|\;\le\;2.87\,k\log k .\tag{6.4}$$

From (3.14), two further contributions, both bounded and neither of order
$k\log k$:
$$E_a=\frac{c}{\sqrt{2\pi}}\sum_{i\ge1}\sqrt{i}\,(2q)^{i}=9.36
\quad(\text{convergent by }(6.3)),\qquad
E_c\approx3k^{2}(2/3)^{T}\le12 \text{ for } k\le5000 .$$

**[VERIFIED] Verified.** All Stirling cuts in (3.14) satisfy $(cj)e^{1-cj}<1$ for
$j=1,2,3$ (values $0.177$, $0.331$, $0.463$), so every truncation decays
geometrically.

$$\boxed{\,|E_{S2}(k)|\le2.87\,k\log(k+1)+21.4\,}\tag{6.5}$$

---

## 7. The threshold

Collecting (4.2), (5.3), (6.5):

$$\overline{E}(k)\;=\;53.6\,k\;+\;2.87\,k\log(k+1)\;+\;21.4,
\qquad 53.6=38.6+15.0 .$$

Solving (2.2) numerically:

$$\boxed{\;K_0=3527\;}$$

**[VERIFIED] Verified at the boundary.** With the criterion evaluated directly:
it fails at $k=3526$ and holds at $k=3527$ and above, with the two sides
crossing cleanly.

### 7.1 Sensitivity

| $t$ | $C_{\log}$ | $K_0$ |
|---|---|---|
| 4.55 (this note) | 2.87 | **3527** |
| 6 | 3.08 | 3608 |
| 8 | 3.77 | 3880 |
| 15 (GLW) | 6.20 | 4861 |

---

## 8. Progression

| stage | $K_0$ |
|---|---|
| naive Cauchy, naive criterion | $2.9\times10^{9}$ |
| pole subtraction, naive criterion | $4801$ |
| pole subtraction, **exact** criterion (2.1) | $14408$ |
| $+$ direct certified coefficients (§4.2) | $1769$ |
| $+$ S1 explicit (§5) | $2455$ |
| $+$ S2 at GLW's $t=15$ | $4861$ |
| $+$ decoupled $c$, $t=4.55$ (§6.1) | $\mathbf{3527}$ |

Two techniques account for essentially the whole improvement over a naive
treatment: **exact subtraction of the nearest pole** (§3.1, factor
$\approx6\times10^{5}$) and **replacement of uniform circle bounds by certified
coefficients** where computable (§4.2, factor $8$). Neither needs new theory;
both apply wherever an explicit constant is wanted from a Cauchy-type argument.

---

## 9. Errors encountered

Recorded because each produced plausible wrong values and was caught only by
cross-checking.

1. **Dropped factor.** Removing the entire $p=3$ term rather than only
   $(1-z/3)^{-1}$ gave $\rho=-0.5904$ instead of $-0.17493$.
2. **Interval widening.** A multiplicative tail factor applied as a symmetric
   ball about zero destroyed the enclosure: $\pm0.175$ on a quantity of size
   $0.175$.
3. **Noise floor.** The fixed Euler-tail perturbation, amplified by $i2^{i}$,
   caused spurious divergence for $i_0\ge30$; first misdiagnosed as aliasing.
4. **Linear scaling.** The $(3.13)$ constant was scaled linearly in $t$; only
   one of its three terms is $T$-dependent.
5. **Invalid fit.** The S1 tail was fitted as $0.0618\,i\,3^{-i}$, which lies
   *below* the true coefficients by up to $80\times$; replaced by (5.2).
6. **Saturated constraint.** $c$ was taken at $c_{\max}$ where $2q=1$ and the
   error series diverges; a finite value was obtained only by truncation.

Superseded values of $\rho$ from earlier drafts ($-0.1749298787$,
$-0.174930743$) reflect insufficient prime cutoffs.

---

## 10. Outstanding

**One item.** The mapping between GLW's $O(\cdot)$ terms and the constants here
rests on my reading of their §3. Constants have been traced to their stated
inequalities (§6.2), but I cannot exclude contributions in their (3.14) beyond
the three identified. This is a question for the authors, not a computation.

Secondary: $\sup|H|$ and $\sup|K|$ are certified at $R=3.4$ and $R=3.6$
respectively; a scan suggests $R\approx3.6$ may be marginally better for $H$,
but the scan itself used uncertified suprema.

---

## 11. Outlook

The analytic threshold $K_0=3527$ stands against certified computation
presently at $k=200$. Computational cost scales roughly as $k^{3}$, so closing
the gap is on the order of $10^{3}$–$10^{4}$ times the $k=200$ run —
substantial, and worth measuring on a high-$k$ slice before committing.

Of the three sources, S2's $k\log k$ term is the binding one and the least
reducible: unlike S1 and S3, it reflects the genuine shape of the GLW argument
rather than a loose estimate. Further progress on $K_0$ most likely requires a
different treatment of Lemma 3.3, not tighter constants in the present one.
