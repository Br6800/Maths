#import "@preview/cetz:0.4.0"
#import "@preview/cetz-plot:0.1.2"
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox(
 "theorem", // identifier
 "Theorem", // head
 fill: rgb("#e8e8f8")
)
#let ex = thmbox(
 "example", // identifier
 "Example", // head
 fill: rgb("#e8e8f8")
)
#let defn = thmbox(
 "definition", // identifier
 "Definition", // head
 fill: rgb("#e8e8f8")
)
#let defthm = thmbox(
 "definition", // identifier
 "Definition/Theorem", // head
 fill: rgb("#e8e8f8")
)
#let lemma = thmbox(
 "theorem", // identifier - same as that of theorem
 "Lemma", // head
 fill: rgb("#efe6ff")
)
#let cor = thmbox(
 "corollary", // identifier
 "Corollary", // head
 base: "theorem", // base - use the theorem counter
 fill: rgb("#f8e8e8")
)
#let proof = thmproof("proof", "Proof")
#let circ = $∘$
#let emptyset = $∅$
#let del = $δ$
#let sig = $σ$
#let int = $integral$
#let Sig = $Σ$/*$Ω$*/
#let eps = $ϵ$
#let lm = $λ$
#let Lm = $Λ$
#let Chi = $χ$
#let nm(x) = $norm(#x)$
#let implies = $⟹$
#let impliesnot = $cancel(⟹, length:#70%, stroke:#1.5pt)$
#let notimplies = $cancel(⟹, length:#70%, stroke:#1.5pt)$
#let iff = $arrow.l.r.double.long$
#let to = $arrow.r$
#let neq = $eq.not$
#let cdot = $dot.op$
#let gm = $γ$
#let Gm = $Γ$
#let nb = $∇$
#let phi = $ϕ$
#let vphi = $φ$
#let oplus = $⊕$
#let otimes = $⊗$
#let iso = $≃$

#let ev = $eps^((i))$
#let xv = $x^((i))$
#let yv = $y^((i))$
#let ht = $h_(theta)$
#let Gaco = $sqrt(2 pi sigma^2)$
#let mgaco = $(1)/((2pi)^(1/d) abs(Sig))$
#let mga = $e^(-1/2 (x-mu)^top Sig^(-1)(x-mu))$
#let dom = math.op("Dom")
#let ran = math.op("Range")
#let diam = math.op("Diam")
#let argmax = math.op("Argmax")
#let argmin = math.op("Argmin")
#let epi = math.op("Epi")
#let jac = math.op("Jac")
#let adu = math.op("Adug")
#let conv = math.op("Conv")
#let cone = math.op("Cone")
#let aff = math.op("Aff")
#let relint = math.op("Relint")
#let span = math.op("Span")
#let ker = math.op("Ker")
#let var = math.op($"Var"$)
#let cov = math.op($"Cov"$)
#let erf = math.op("Erf")
#let erfc = math.op("Erfc")
#let sgn = math.op("Sign")
#let lcm = math.op("Lcm")
#let mapsto = $arrow.r.bar$
#let otimes = $otimes$
#let cap = $inter$
#let cup = $union$
#let bitlim = $2147483647$
#let sseq = $(x_(n_k))_(k >= 1)$
#let infty = $infinity$
#let prod = $product$
#let seq = $(x_n)_(n >= 1)$
#let fseq = $(f_n)_(n >= 1)$
#let Si(x) = math.op($1/(1+e^(-#x))$)
#let inner(x,y) = math.op($lr(chevron.l #x,#y chevron.r)$)
#let Ga(x) = math.op($1 / sqrt(2 pi sigma^2) e^(-(#x)^2 / (2 sigma^2))$)
#let Df(f, x) = math.op($(partial #f) / (partial #x)$)
#let proj(x, y) = math.op($"Proj"_(#x)(#y)$)
#let Gapo = $(yv - theta xv)^2$
#let cred(x) = text(fill: red)[$#x$]
#let cgreen(x) = text(fill: rgb("#199517"))[$#x$]
#let cblue(x) = text(fill: blue)[$#x$]
#let diag(x) = math.op($mat(#x, , ; , dots.down; ,,#x)$)
#let diag2(x,y) = math.op($mat(#x, , ; , dots.down; ,,#y)$)
#set heading(numbering: "1.")

#set page(fill: rgb(238, 238, 238))
#align(horizon + left)[

  #text(size: 24pt, [Machine Learning \ CS229])



  Notes



  Brendan Matthews

]

#align(bottom + left)[#datetime.today().display()]

#pagebreak()

/*
BEGIN DOCUMENT
*/

= Linear Regression
Let $xv in RR^n$ be the $i'"th"$ feature variable
of some data with $m$ feature variables.
We shall be abusing notation to write $theta^top xv$ as $theta xv$.
Assume $yv = theta xv + ev in RR$ where $ev ~ N(0, sigma^2)$ are iid for
$i=1, dots.h, m$ so that $yv ~ N(theta xv,sig^2)$.
The density of this normal distribution for $yv$ is $
P(yv|xv;theta) = Ga(yv-theta xv)
$ and so
$
L(theta) &= P(y | x; theta) "Likelihood of" theta \
&= product_(i=1)^m P(yv|xv;theta) "by our independence assumption" \
& implies \
ell(theta) &= log  product_(i=1)^m Ga(yv - theta xv) "log likelihood is monotonic so" ell(theta) "has identical maximum to "L(theta) \
&= sum_(i=1)^m log Ga(yv - theta xv) \
&= m log(Gaco) - 1 / (2 sig^2) sum_(i=1)^m Gapo.
$
Since $sig^2 >= 0$ 
#footnote($"We did not specify" sig^2, 
"so our justification for LSE is reliant strictly on the independently norm dist assumption."$), maximising that is equivalent to
minimising $ J: RR^n to RR,  #h(1cm) J(theta) = 1 / 2 sum_(i=1)^m Gapo. $
You oughta know that means you need multivariable calculus. For a function $f:RR^n to RR$,
a derivative is a gradient,
a double derivative is a hessian and
you might even need the chain rule. #linebreak()
N.B. For the express purpose of confusing people, Andrew uses avg loss sometimes. Same minimiser.
== Convexity
=== Definitions and Basic Results
We need some convex analysis to understand minima properly.
A function $f:RR^n to RR_infinity$ is convex if its epigraph ${(x,t) in
RR^n times RR: f(x) <= t }$ is convex. For $lm in [0,1]$, TFAE:
$
lm f(x_1) + (1-lm)f(x_2) >= f(lm x_1 + (1-lm) x_2) &implies \
lm t_1 + (1-lm)t_2 >= lm f(x_1) + (1-lm)f(x_2) >=  f(lm x_1 + (1-lm) x_2) &implies \
lm(x_1, t_1) + (1-lm)(x_2,t_2) in epi(f) " and " \
lm(x_1, f(x_1)) + (1-lm)(x_2,f(x_2)) in epi(f) &implies \
f(lm x_1 + (1-lm) x_2) <= lm f(x_1) + (1-lm)f(x_2).
$
#lemma()[
A twice differentiable function $f:RR to RR$ is convex iff it has an increasing derivative and nonnegative second derivative.
] <1d_equiv>
#proof()[
Suppose $f$ is convex. Fix $x<= y in RR$ and $0 < t < y-x$ and let $lm = t / (y-x)$.
We have $(f(y)-f(x)) / (y-x) >= (f(x+t)-f(x)) / t$
and  $(f(y)-f(x)) / (y-x) <= (f(y)-f(y-t)) / t$ since
$
lm f(y)+(1-lm)f(x) >= f(x+t) = f(x+(y-x)lm) = f(lm y + (1-lm)x) implies \
t f(y)-t f(x) >= (y-x)f(x+t) - (y-x)f(x).
$
and
$
lm f(x)+(1-lm)f(y) >= f(y-t) = f(y-(y-x)lm) = f(lm x + (1-lm)y) implies \
t f(x)-t f(y) >= (y-x)f(y-t) - (y-x)f(y) .
$
It follows that $f'(y) >= (f(y)-f(x)) / (y-x) >= f'(x)$. So $f'$ is increasing and $f''$ must be nonnegative. #linebreak() #linebreak()
Conversely, suppose $f'$ is increasing and fix $x,z in RR$ and let $y = lm x + (1-lm)z$.
By MVT, $exists (t_1,t_2) in [x,y] times [y,z]$ with $ f'(t_1) = (f(y)-f(x)) / (y-x) " and " f'(t_2)
= (f(z)-f(y)) / (z-y). $
Since $t_2 >= t_1$, we have
$ (f(z)-f(y)) / (z-y) >= (f(y)-f(x)) / (y-x) $
so that $f$ is convex.
]
#lemma()[
A function $f: RR^n to RR$ is convex iff for $x,r in RR^n$, the functions $phi:RR to RR$ given by $phi(t) = f(x+t r)$ are all convex.
] <1d_fun>
#proof()[
If $f$ is convex it's easy to see that $phi$ is convex. Pick any $x,y in RR^n$
and let $r = y-x$. Then by assumption the function $phi(t) = f(x+t r)$ is convex.
Then $f$ is convex because
$ lm f(x)+ (1-lm)f(y) = lm phi(0) + (1-lm)phi(1) >= phi(1-lm) = f(lm x + (1-lm)y). $
]
#theorem()[
A twice differentiable function $f: RR^n to RR$ is convex iff
for each $x in RR^n$ we have $H(f)(x) >= 0$ where $H$ is the Hessian matrix of partial derivatives.
]
#pagebreak()
#proof()[
Suppose that $H(f)(x) >= 0$ for all $x in RR^n$.
Pick any $x,r in RR^n$ and define $phi:RR to RR$ by $phi(t) = f(x+t r)$.
Then
for $g(t) = x+t r$ we have $g'(t) = r^top$,
so $
phi''(t) &= (dif^2) / (dif t^2) f(x+tr) \
&= (dif) / (dif t)[f'(g(t))g'(t)^top] " multidimensional derivatives of "f,g\
&= (dif) / (dif t)[g'(t)f'(g(t))^top] "because real numbers are equal to their transpose"\
&= (dif) / (dif t)[g'(t)(nabla f)(g(t))]  \
&= r^top (dif) / (dif t)[(nabla f)(g(t))] \
&= r^top (dif) / (dif t) mat(
(h_1 circ g)(t) ;
dots.v ;
(h_n circ g)(t))
"where" h_i: RR^n to RR "is given by" h_i(x) = (nabla f)_i (x)\
&= r^top mat(
h'_1 (g(t)) g'(t)^top ;
dots.v ;
h'_n (g(t)) g'(t)^top
) "apply the derivative to the gradient by components using the chain rule" \
&= r^top mat(
h'_1(g(t)) ;
dots.v ;
h'_n (g(t))
) r \
&= r^top H(f)(g(t))r \
&>= 0.
$
Then $phi$ is convex by the lemma and $f$ is convex by the other lemma. #linebreak() #linebreak()
Now suppose that $f$ is convex and fix $x in RR^n$. Then for any $r in RR^n$ the lemmas give $phi''(0) = r^top H(f)(x)r >= 0$, so $H(f)(x)$ is PSD.
]
=== Unconstrained Optimisation of Convex Functions
#defn()[
A point $x_0 in X$ is a local minimiser of $f$ over $X$
if there is a ball around $x_0$ such that for $y in B_(eps)(x_0) inter X$ we have $f(y) >= f(x_0)$.
We say that $f(x_0)$ is a local minimum.
]
#theorem("Fundamental Theorem of Convex Optimisation")[
Suppose $f$ is convex with a minimum $M$.
Then $A = {x:f(x) <= M}$ is convex #footnote[$A$ is a (sub)level set and $A = {x: f(x) = M}$.
Any quasi-convex function has convex sub-level sets.] and every local minimum is in
$f(A)$. It is possible that $|A| = |RR|$ via #cetz.canvas({
import cetz.draw: *
import cetz-plot: *
plot.plot(size: (1, 0.4), axis-style: none, {
// Sampling a function:
plot.add(domain: (-2, 2), x => calc.max(calc.abs(x) - 1,0)) 
/*
plot.add(domain: (4, 8), x => calc.max(calc.abs(x - 6) - 1,0))
*/
})}

)
A stictly convex $f$ has $|A| = 1$. The converse is false, $nm(.)_1, #h(0.2cm) nm(.)_infinity$ are not strictly convex.
]
#proof()[
Let $f(x_0) = M$ and suppose $x_1 \neq x_0$ is a local minimum in a ball $B_{eps_0}$.
Let $eps = min{eps_0,  slash nm(x)}$. Since
$f$ is convex and $eps in (0,1)$, we have $eps f(x_0) + (1-eps)f(x_1) >=
f(eps x_0 + (1-eps)x_1)$ but $nm(x)$ and $f(eps x_0 + (1-eps)x_1) >= f(x_1)$. Then $eps (f(x_0)-f(x_1)) >= 0$ and since $eps > 0$ we have $f(x_0) >= f(x_1)$ which means $f(x_0) = f(x_1) = M$. It is easy to see that if $f$ is strictly convex, there is a contradiction, so $|A| = 1$.
]
#defn()[
  The limit inferior of a sequence $seq$ is the largest number that eventually bounds $seq$ below.
]
#defn()[
  A function $f:RR^n to RR$ is lower semicontinuous at $x in RR^n$ if $ "for all " (x_n) to x " we have "  f(x) <= liminf_(n to infinity) f(x_n)$. A function is continuous iff it is both upper and lower semicontinuous.
]
#defn()[
  A function $f:RR^n to RR$ is coercive if $f(x_n) to infinity$ whenever $nm(x_n) to infinity$.
]
#theorem("Extreme Value AKA Weierstrass Theorem")[
Suppose that $C$ is compact and $f: C to RR$ is upper/lower semicontinuous. Then $f$ attains a maximum/minimum on $C$. 
]
#cor("Existence of Solutions to Unconstrained Minimisation Problems")[
  Let $S$ be a nonempty and closed subset of $RR^n$. Suppose that $f:S to R$ is lower semicontinuous and coercive. Then $f$ attains a minimum on $S$.]
#proof()[If $S$ is bounded it is compact and we're done. If not, fix $x_0 in S$. Since $f$ is coercive, there exists $R > 0$ such that for $norm(x) > R$ we have $f(x) >= f(x_0)$. By Weierstrass theorem, $f$ attains a minimum $M$ on the compact ball $overline(B)_(R + nm(x_0)) (x_0)$. Pick any any $x in S$. If $x in S without  overline(B)_(R+nm(x_0)) (x_0)$ then $nm(x) + nm(x_0) >= nm(x-x_0) > R+nm(x_0) implies  nm(x) > R$ so $f(x) >= f(x_0) >= M$. If not, $f(x) >= M$ by definition. So $M$ is the minimum of $f$ on $S$.
  ]
#theorem("Lipshitz Continuity of Convex Functions")[
Let $f:RR^n to RR_(infinity)$ be a convex function
and $D subset relint(dom(f))$ be compact and convex. Then $f$ is Lipshitz over $D$.
]
Everything in CS229 is continuous anyway.
#pagebreak()
== The Linear Regression Cost Function is Convex
  #link("https://math.stackexchange.com/questions/1187687/
expansion-of-the-square-of-the-sum-of-n-numbers")[ -Explainer for 2nd last line-]
$ H(J (theta))_(j k) &= (partial) / (partial theta_j theta_k) [ (1) / (2)sum_(i=1)^m Gapo] \
&= (partial) / (partial theta_j theta_k) [ (1) / (2)sum_(i=1)^m (yv^2-2 yv (theta xv) + (sum_(q=1)^n theta_q xv_q )^2 ) ] \
&= (partial) / (partial theta_j theta_k) [(1) / (2)sum_(i=1)^m (sum_(q=1)^n theta_q xv_q )^2 ] \
&= (partial) / (partial theta_j theta_k) [ (1) / (2)sum_(i=1)^m sum_(q=1)^n (theta_q xv_q)^2 + sum_(i=1)^m sum_{r = 1}^m sum_(s=1)^{r-1} theta_r xv_r theta_s xv_s ] \
&= sum_(i=1)^m xv_j xv_k.
implies
H = X^top X $
Since partials commute $H = H^top$ and $z^top H(J(theta)) z 
= z^top X^top X z = (X z)^top (X z)  = (nm(X z)_2)^2 >= 0$, 
$H(J(theta))$ is PSD and $J$ is convex.
Old mate $J$ is continuous and looks coercive enough to me. 
So $J$ has a minimum and any algorithm guaranteed to converge to a local minimum will minimise $J$.
== Matrix Derivatives
=== Rules
Constants, sums and traces all pass through and the product rule holds.
=== Results
$ nabla_x (x^top b) = b $
$ nabla_x (x^top A x) = (A+A^top)x, #h(1cm) H(x^top A x) = A + A^top #h(1cm) "note: simplification when symmetric" $
#proof()[ Let $f: RR^n to RR$ be given by $f(x) = 
inner(x,A x)$ then
$ f(x)-f(x_0) &= inner(x,A x) - inner(x_0, A x_0) \
&= inner(x - x_0, A x_0) + inner(x - x_0, A (x - x_0)) + inner(x_0, A (x - x_0)) \
&= inner(A x_0, x-x_0) + 0.5 inner(x-x_0, (A+A^top)(x-x_0)) + inner(A^top x_0, x - x_0) \
&= inner((A+A^top)x_0,x-x_0) + 0.5 inner(x-x_0, (A+A^top)(x-x_0)) \
"So "nb f(x) &= vec(Df(f,x_1)(x) , dots.v , Df(f,x_n)(x))  \ 
&= lim_(h to 0) #h(0.1cm) 1/h #h(0.1cm) 
vec(f(x_1+h,dots.h,x_n) - f(x_1,dots.h,x_n) , dots.v , f(x_1,dots.h,x_n+h) - f(x_1,dots.h,x_n)) \ 
&= lim_(h to 0) 1/h (A+A^top) h x + 1/(2h) vec(2 h^2 A_(11),dots.v,h^2 (A_(n 1)+A_(1n))) \
&= (A+A^top)x $]
== Solving Linear Regression Explicitly
Let $X in RR^(m times n)$ be the vector with features $xv$ as 
rows and let $arrow(y) in RR^m$ vectorise the target variables.
#image("CS229/Screenshot-20241208164111-485x246.png", width: 50%)
setting to zero (see @fred) gives the global minimiser
$ theta = (X^top X)^(-1) X^top arrow(y). $
you need to ensure that $X^top X$ has full rank because otherwise the kernel is not zero.
= Logistic Regression
Suppose you have a binary classification problem.
You shouldn't use linear regression.
Define $ht(x) = Si(theta x) in (0,1)$. Notice that $g(x) = Si(x)$ has $g'(x) = g(x)(1-g(x))$ Define $ht$ as the probability of the $yv$ taking the value of 1.
Then $ P(y|x;theta) = ht(x)^y (1-ht(x))^(1-y) implies ell(theta) =  sum_(i=1)^m yv log(ht(xv)) + (1-yv) log(1 - ht(xv)) $
which gives the loss function $J(theta) = -(1) / (m) ell(theta)$ 
with $H(J(theta)) >= 0$. In the following, $g(X theta) in RR^(m)$ is treated like a row vector in numpy:
#image("CS229/loghessian.png") N.B. The red products are those done by $*$ in 
numpy. The dot function is identical to numpy's matmul function for a 2D array. For multidimensional arrays, they work differently:
#image("CS229/npdot.jpg")
= Algorithms for Solving GLM Problems
== Gradient Descent
=== Batch Gradient Descent
This method is good for less than a million examples. It has slower
convergence per step than Newtons method 
but the steps are less costly. The update rule minimising $J$ is
$ "While True: " theta := theta - alpha nb J(theta) = theta + alpha sum_(i=1)^m (yv-ht(xv))xv $
where $alpha > 0$ is the learning rate. This also maximises the likelihood of $theta$ because 
$log$ is increasing. 
=== Stochastic Gradient Descent
This method is good for more than a million examples. It has less reliable convergence
than batch gradient descent
but the steps are less costly. The update rule is
$ "While True: For "i=1,dots.h,m; #h(0.5cm) theta := theta + alpha (yv -ht(xv)) xv $
Guaranteed convergence is still possible by decaying $alpha$.
== Newtons Method
Suppose you wanna find the zero of a function $f$. Pick an $x_1 in RR$.
Set $x_2 = x_1 - (f(x_1)) / (f'(x_1))$ and you will converge on the zero. Assuming one global extremum,
Newtons method applied to $f'$ will find $x$ such that $f$ is minimised or maximised. 
In our case for $ell(theta)$,  we maximise via the update rule 
$ theta := theta - H^(-1)(ell)(theta) nb ell(theta) "unless " nb ell(theta) = 0 dots.h $
It is fairly obvious that there is no notion of ascent or descent 
like there is in the gradient algorithms 
because the zeros of $-f$ and $f$ coincide. *We require that $H(ell)(theta)$ is positive/negative definite*.
= These algorithms are well and good but why do they work?
#defn("Directional Derivative")[
  Let $f:RR^n to RR$ and  $phi(t) = f(x+t d)$. We say that $f$ has a directional derivative at $x in RR^n$ in the direction $d in RR^n$ if $phi'(0) = inner(nb f(x),d)$ exists.
] 
#image("CS229/descent.png", height: 15%)
== Gradient Descent
=== Why Does the Algorithm give a Descent direction? <neg_grad>
Fix $J in (RR^n)^RR inter C^1$, $theta in RR^n$ and $eps > 0$. From now on we will denote $-nb J(theta)$ by $v$.
Define $phi in RR^RR$ by $phi(t) = J(theta + t v)$.
Since $J in C^1$, the Taylor series for $phi$ about $0$ gives 
$ J(theta
+t v) &= phi(t) = phi(0) +
t phi'(0) + o(t)\ 
&= J(theta)
+ t inner(nb J(theta ), v) + o(t)  \
&= J(theta) - t nm(v)^2+o(t)  \
&< J(theta) "for small enough" t > 0 " and " v neq 0. $
The above calculation shows that if $nb J(theta) neq 0$ then there is a small enough step in the direction of $-nb J(theta)$ that decreases $J$, so $theta$ is not a local minimum. The contrapositive yields @necessary_conditions.
=== What Does Steepest Descent Even Mean?
By definition, the angle $vphi$ between a descent direction $p$ and the vector $nb J(theta)$ is given by 
$ cos(vphi) = inner(nb J(theta), p) / (nm(nb J(theta))nm(p)). $
When $p = -alpha nb J(theta)$, we have
$ cos(vphi) = (- alpha inner(nb J(theta), nb J(theta))) / (alpha nm(nb J(theta))nm(nb J(theta))) = -1, $       
so that $inner(nb J(theta),p) = cos(vphi)nm(nb J(theta)) nm(p)$ is minimised.
We call this the direction of steepest descent.
== Newton's Method
=== Why Does the Algorithm give a Descent direction? <neg_hess>
Fix $J in (RR^n)^RR inter C^2$, $theta in RR^n$ and $eps > 0$. From now on we will denote $-H^(-1)(J(theta)) nb J(theta)$ by $v$.
Define $phi in RR^RR$ by $phi(t) = J(theta + t v)$.
Since $J in C^2$, the Taylor series for $phi$ about $0$ gives 
$ J(theta
+t v) &= phi(t) = phi(0) +
t phi'(0)+ o(t)\ 
&= J(theta)
+ t inner(nb J(theta ), v) + o(t)  \
&= J(theta) - t inner(nb J(theta),H^(-1)(J(theta)) nb J(theta))+o(t)  \
&< J(theta) "for small enough" t > 0 "and" nb J(theta) neq 0" since " H^(-1) > 0. $
We can replace $H^(-1) > 0$ with any $Q > 0$. *N.B the learning rate
must be sufficiently small to guarantee descent; 
however this is not done in practice, see @backtracking.* What if $nb J(theta) = 0$ at a saddle point?

=== How do we Modify Descent Algorithms at STATIONARY Points <neg_hess2>
Fix $J in (RR^n)^RR inter C^2$, $theta in RR^n$ and $eps > 0$. 
Assume that $H(J(theta))$ is *not* positive semidefinite, if it is 
then $theta$ typically a local minimiser, but
it might not be unless $H$ is PD.
Let $v$ be an eigenvector of $H(J(theta))$ with eigenvalue $lm < 0$.
Define $phi in RR^RR$ by $phi(t) = J(theta + t v)$.
Since $J in C^2$, the Taylor series for $phi$ about $0$ gives 
$ J(theta
+t v) &= phi(t) = phi(0) +
t phi'(0) + t^2/2 phi''(0) + o(t^2)\ 
&= J(theta)
+ t inner(nb J(theta ), v) + t^2/2 inner(H(J(theta)) v,v)+ o(t^2)  \
&= J(theta)
+ (lm t^2)/2 nm(v)^2+ o(t^2)  \
&< J(theta) "for small enough" t > 0. $
=== Why is Newton's Method Any Good? <quadopt>
If $J in (RR^n)^RR inter C^2$ then the second order approximation 
of $phi(t) = J(theta+t p)$ gives $ phi(1) &approx 
phi(0) + phi'(0) + 1/2 phi''(0) \
"'Amount of Ascent'" &=  J(theta + p) -J(theta) \
&approx vphi_x (p) = inner(nb J(theta), p) + 
1/2 inner(H(J(theta)) p,p). $
The quadratic approximation $phi_x (p)$ is strictly convex since $H>0$. We have
$ nb phi_x (p) = nb J(theta) + H(J(theta)) p. $
Setting this to zero yields $p = -H^(-1)(J(theta)) nb J(theta)$. 
So the amount of descent 
of the quadratic approximation is maximised when $alpha = 1$ in Newton's 
method.
#image("CS229/ac9O7.png", width: 9cm, height: 5cm)
=== In What Sense is it the Steepest Descent Direction? 
Any symmetric matrix defines an inner 
product $inner(x,y)_A = inner(x,A y)$ and a norm too if $A$ 
is PD. Let $f:(RR^n,inner(.,.)_"generic") to RR$.
Fix $x in RR^n.$
Since $D f(x): (RR^n,inner(.,.)_"generic") to RR$ given by 
$ D f(x)[d] = lim_(t to 0) (f(x+t d) - f(x)) / (t) $ 
is a continuous linear functional
the Riesz representation theorem says there 
is a unique vector $g$ such that 
$ inner(d,g)_"generic" =  D f(x)[d] #h(1cm) forall d in RR^n. $ 
We call $g$ the gradient of $f$ at the point $x$.
In the Hessian geometry, the gradient of $f$ at $x$ 
is $g = H^(-1)(f)(x) nb f(x)$ since 
$ inner(d,g)_H = inner(d,nb f(x))_("2-norm") =  lim_(t to 0) (f(x+t d) - f(x)) / (t). $ 
The step size in Newtons method is $ nm(H^(-1)(f)(x) nb f(x))$, which is 
the norm of the gradient in the Hessian geometry: $nm(Delta theta)_H = nm( H^(-1)(f)(x) nb f(x))_H = nm(g)_H$. 
#footnote($"there is a cool duality that" nm(nb f(x))_(H^(-1)) = 
nm(Delta theta)_H$). The function value changes according to $1/2 nb f(x)^top H^(-1)(f)(x)nb f(x) 
= 1/2 nm( H^(-1)(f)(x) nb f(x))^2_(H) = 1/2 nm(g)_H^2$ by @quadopt and so the 
method updates the function value according to the magnitude of the
square of the gradient in the Hessian geometry, the same as 
gradient descent does in Euclidean geometry.
=== Convergence <backtracking>
@neg_hess
= Why Does Setting the Gradient to Zero Work? <fred>
The gradient is zero at minimisers of $C^2$ functions and points where the gradient is zero are minimisers if the Hessian is locally PD or the function is convex. 
#theorem("Necessary Conditions for Minimisers of C1 & C2 Functions")[Let $f in (RR^n)^RR inter C^1$. If $theta$ is a local minimiser of $f$, then $nb f(theta) = 0$. Furthermore, if $f in C^2$ then for $w in RR^n$ and $t>0$ $ f(theta
+t w)-f(theta) &= phi(t) -f(theta)= phi(0) +
t phi'(0) + (t^2) / (2) phi''(0) -f(theta)+ o(t^2)\ 
&= t inner(nb f(theta ), w)  + (t^2) / (2) inner(H(f(theta)) w,w)+o(t^2)  \
&= (t^2) / (2) inner(H( f(theta)) w,w)+o(t^2)  \
&>= 0 "for small enough" t
"because" theta "is a local minimiser." \
$
So $H( f(theta))$ is positive semidefinite. If $theta$ is a strict local minimiser, then $H( f(theta))$ is PD.

- $f$ need not be convex.
- Converse is false, $f(x) = x^3$ has $f'(0) = 0$ and $f''(0) = 0$ but $0$ is not a local minimiser.
#proof()[For the $C^1$ condition, see @neg_grad.]
] <necessary_conditions>

#cor("Sufficient Conditions for Minimisers of C2 Functions")[
Let $f in (RR^n)^RR inter C^2$. If $nb f(theta) = 0$ and $H(f(theta))$ is PD then $theta$ is a strict local minimiser. This only works for $H(f(theta)) = eps > 0$ because we can control $t$ so that $o(t^2)< eps$.
]
The $C^1$ calculation in @neg_grad gives us a bit more, if we think of $v neq 0$ 
as an arbitrary vector then $J(theta + t v) = J(theta) + 
t inner(nb J(theta), v) + o(t) < J(theta)$ for small enough $t$ if $inner(nb J(theta), v) < 0$. 
So $v$ is a decent direction. 
#theorem()[Suppose $f: RR^n to RR$ is differentiable everywhere. Then $f$ is convex 
iff $ f(y) >= f(x)+inner(nb f(x), y-x) iff  inner(nb f(y) - nb f(x), y-x) &>= 0 . $
#proof()[
If $f$ is convex then for $lm in (0,1)$,
$ lm (f(y)-f(x)) >= f(x + lm(y-x)) -f(x)$
so $ f(y)-f(x) >= (f(x + lm(y-x)) -f(x)) / lm >= lim_(lm to 0^+) (f(x+lm(y-x))-f(x))/(lm) = inner(nb f(x), y-x)$
Conversely... $ inner(nb f(y),y-x) &>= f(y) - f(x) \
-inner(nb f(x),y-x) &>= f(x) - f(y)\
implies \
 inner(nb f(y) - nb f(x), y-x) &>= 0. $
 Let $phi(t) = f(x+t(y-x))$. Fix $t_2 > t_1$. 
 Then $ phi'(t_2) - phi'(t_1) &= inner(nb f(x+t_2(y-x)),y-x) - inner(nb f(x+t_1(y-x)),y-x) \
 &= 1 /(t_2-t_1)inner(nb f(a) - nb f(b),a-b) >= 0. $
Then by @1d_equiv, $phi$ is convex and so $f$ is too by @1d_fun.
]
]
#cor("Sufficient Conditions for Minimisers of C1 Convex Functions")[
Let $J:RR^n to RR$ be continuously differentiable and convex. If $nb J(theta) = 0$ then $theta = argmin(J)$ since $ J(vphi) >= J(theta) + inner(nb J(theta), vphi - theta) = J(theta)$.
]
= Generalised Linear Models
== Introduction
#defn()[
A GLM consists of
- a distribution from the exponential family,
- a linear predictor
$ eta(theta) 
= vec(theta_1^top , dots.v, theta_k^top) x in RR^k "with" eta_i = theta_i^top x "for" i=1, dots.h,k 
"and" theta = (theta_1,dots.h,theta_k)^top in RR^(n k) "with" theta_i in RR^n. $
- a link function $g$ such that $E(T(y)|x)= nb A(eta)$ provided $A neq 0$.
- It is true that $"Var"(T(y);eta)= H(A)(eta)$ provided $A neq 0.$
The canonical link function is $g = nb A$ where $A$ is the log-partition function.]
The density of an exponential family distribution is
$ P(y;eta) = b(y) e^(inner(eta, T(y)) - A(eta)). $
More often we are interested in the
log-likelihood function 
$ ell(theta) = log prod P(yv|xv;theta) = sum_(i=1)^m b(yv) + inner(vec(theta_1^top xv,dots.v,theta_k^top xv), T(yv)) - A circ vec(theta_1^top xv,dots.v,theta_k^top xv). $
The Bernoulli distribution has 
$ eta = log(phi/(1 - phi))#h(1cm) T(y) = y, #h(1cm) b(y) = 1 #h(1cm) A(eta) = log(1+e^(eta)). $
While training a model with the ASSUMPTION $P(y = 1|x;theta) =
 phi$, we completely ignore $eta = log(phi / (1-phi))$ this is used to determine $phi$ for new examples once $theta$ is optimised, which then allows classification.

The Poisson distribution 
$(lm^(y) e^(-lm)) / y! = 1 / y!e^(y log(lm) - lm)$ 
has $ eta = log(lm),#h(1cm)T(y) = y, #h(1cm) b(y) = 1 / (y!), 
#h(1cm) A(eta) = e^(eta). $
The distribution $N(mu,1)$ has 
$ eta = mu, #h(1cm)T(y) = y, #h(1cm) b(y) 
= 1 / sqrt(2 pi) e^(-y^2 / (2)),#h(1cm) A(eta) = eta^2 / 2. $
=== 2D Example: Categorical Distribution
Suppose $yv in {1,dots.h,k}$ and $P(yv = i|xv";"theta) =
 phi_i$ where $sum phi_i = 1$ 
 and $eta_i = theta_i^top xv$.
The dimensionality of the distribution is $k-1$ 
since $phi_k = 1- sum_(i=1)^(k-1) phi_i$.
For $T(y) = cases(e_y"," y < k, bold(0)", otherwise") in RR^(k-1)$ we have 
$ P(yv=k) = 
phi_k^(1-sum_(i=1)^(k-1) (y=i))prod_(i=1)^(k-1) phi_i^((yv = i)) 
= exp(inner(log vec(phi_1 / (1-sum phi_i),dots.v,phi_(k-1) / (1-sum phi_i)),T(yv)) +log(1-sum_(i=1)^(k-1) phi_i)) $
so $ eta_j = log(phi_j / (1-sum_(i=1)^(k-1) phi_i)),#h(0.2cm) T(yv) =
cases(e_(yv)", "yv<k,bold(0)", otherwise")$ and $A(eta) = log(1+sum_(j=1)^(k-1) e^(eta_j)). $
The log-likelihood function is
$ ell(theta) = sum_(i=1)^m [log(1+sum_(j=1)^(k-1) e^(eta_j^((i)))) + sum_(j=1)^k (yv = j) 
eta_j^((i))]  $   
== Properties of Canonical Exponential Family
=== Derivatives
The log-likelihood function is confusingly written as
$ ell(theta) = sum_(i=1)^m log(b(yv)) + (eta^((i)))^top T(yv) 
- A(eta^((i))). $
We first find the transpose of the Jacobian of $eta^((i)): RR^(n k) to RR^k$ given by $eta^((i))_j (theta) = theta_j^top xv$:
$ (eta^(i)'(theta))^top &= J^top (eta^((i)))(theta) \
&= 
mat(Df(eta_1,theta_(11)),dots.h,Df(eta_1,theta_(1k)),,Df(eta_1,theta_(n 1)),dots.h,Df(eta_1,theta_( n k));
dots.v, dots.down,dots.v , dots.h, dots.v, dots.down, dots.v; 
Df(eta_k,theta_(11)),dots.h,Df(eta_k,theta_(1k)),, Df(eta_k,theta_(n k)),dots.h,Df(eta_k,theta_(n k)))^top \
&= diag2(nb_(theta_1)eta_1,nb_(theta_k) eta_k)_(n k times k) \ 
&= diag(xv)_( n k times  k) $
The grad chain rule says that for $f:RR^k to RR$ and $g:RR^m to RR^k$ 
we have $nb (f circ g) = J(g)^top (nb f) circ g$. 
$ nb ell(theta) &= sum_(i=1)^m nb_theta del(eta^((i))(theta)), 
#h(1cm) "with" del: RR^k to RR "given by " del(x) = x^top T(yv)-A(x) \
&= sum_(i=1)^m  J^top (eta^((i)))(theta) nb del (eta^((i))) \
&= sum_(i=1)^m  diag(xv)_(n k times k) (T(yv)- nb A(eta^((i)))) iff sum_(i=1)^m (T(yv)-A'(eta^((i)))) xv "when" k = 1. \
&= sum_(i=1)^m (T(yv) - nb A(eta^((i)))) otimes xv " (Kronecker Product)" \
$
The Hessian chain rule says that for $f:RR^k to RR$ and $g:RR^m to RR^k$ we have  $ H(f circ g)(x) = J(g)(x)^top H(f)(g(x)) J(g)(x) + sum_(i=1)^k (nb f)_i (g(x)) H(g_i)(x). $
So $ H(ell)(theta) &= sum_(i=1)^m H(del circ eta^((i)))(theta) \
&= sum_(i=1)^m J^top (eta^((i)))(theta) H(del)(eta^((i))) J(eta^((i)))(theta) 
+ sum_(j=1)^k (nb del)_j (eta^((i))) H(eta^((i))_j)(theta) \
&= sum_(i=1)^m diag(xv)_(n k times k) H(del)(eta^((i))) 
diag(xv)_(k times n k)^top + sum_(j=1)^k (T(yv)- nb A(eta^((i))))_j times 0_(n k times n k) \
&= -sum_(i=1)^m diag(xv)_(n k times k) H(A)(eta^((i))) diag(xv)_(k times n k)^top \
&= -sum_(i=1)^m mat(x_1h_(11), dots, x_1 h_(1k);
,dots.v,;
x_n h_(11), dots, x_n h_(1 k);
,dots.v,;
,dots.v,;
x_1h_(k 1), dots, x_1 h_(k k);
,dots.v,;
x_n h_(k 1), dots, x_n h_(k k);) mat(
  x_1,dots,x_n;
  ,,, x_1, dots, x_n;
  ,,,,,,dots.down;
,,,,,,,x_1,dots, x_n
)
 \
 &= -sum_(i=1)^m mat(x_1^2h_(11),dots,x_1x_n h_(11), dots, x_1^2 h_(1k), dots, x_1 x_n h_(1k);
 ,,,dots.v;
 x_n x_1 h_(11), dots, x_n^2 h_(11), dots, x_1 x_n h_(1 k), dots, x_n^2 h_(1 k);
 ,,,dots.v;
 ,,,dots.v;
x_1^2h_(k 1),dots,x_1x_n h_(k 1), dots, x_1^2 h_(k k), dots, x_1 x_n h_(k k);
 ,,,dots.v;
 x_n x_1 h_(k 1), dots, x_n^2 h_(k 1), dots, x_1 x_n h_(k k), dots, x_n^2 h_(k k);
 )\
$
$
&=-sum_(i=1)^m H(A)(eta^((i))) otimes xv xv^top in RR^(n k times n k) iso RR^(k times k) otimes RR^(n times n) \ 
/*mat(
  xv_1 (H(A)_1^top otimes xv^top);
  dots.v ;
  xv_n (H(A)_1^top otimes xv^top);
  dots.v;
  xv_1 (H(A)_k^top otimes xv^top);
  dots.v;
  xv_n (H(A)_k^top otimes xv^top)
)*/ \
& iff 
-sum_(i=1)^m "Var"(T(yv);eta^((i))) xv xv^top <= 0 "when" k = 1 "since " -sum_(i=1)^m "Var"(T(yv);eta^((i))) w^top xv (w^top xv)^top <= 0. \ 
$
So 1D GLM's are concave but higher dimensional GLM's need not be.
=== Convexity
The canonical $k$-dim exponential family has probability density $
                                                          p(x;theta) = h(x)e^(sum_(i=1)^k [theta_i T_i (x)] - A(theta))
                                                         $ 
*We assume in this section that the distribution is canonicial*. The joint distribution of a bunch of iid exp. dist. random variables is 
exp. dist. with sufficient statistic $sum_i T_i (X_i)$. The Hessian of the log partition function is equal to the covariance
matrix of $T(X)$, i.e. $H(A)_(i j) = cov(T(X)_i,T(X)_j)$ which is positive definite. The Hessian of the log likelihood of $m$ iid samples is then $-m H(A)$ which is concave. So a GLM is concave in the natural parameters.      
= Averages of independent random variables concentrate around their expectation
Some course objectives for students in machine learning include: (1) Predict which kinds
of existing machine learning algorithms will be most suitable for which sorts of tasks, based
on formal properties and experimental results. (2) Evaluate and analyze existing learning
algorithms.
#defn()[For discrete random variables $X,Y:Omega to RR$ we define $ P(X=Y) = sum_(lm in X(Omega)) P(X^(-1){lm} cap Y^(-1){lm}). $ A CDF of a random variable $X:Omega to RR$ is a function $F:RR to [0,1]$, $ F(x) = P(X<=x) = integral_(-infty)^(x) F'(y) dif y " or " sum_(lm <= x) P(X=lm) "where " P(X=lm) = P(X^(-1){lm}) $ is a right continuous #footnote("nondecreasing of course") function such that $lim_(x to -infty) F(x) = 0$ and $lim_(x to infty) F(x) = 1$.
#image("CS229/pdf.png") If the sample space $Omega$ is 
countable, $X$ is discrete with PMF given by the 
probabilities of preimages as above. 
This is NOT true of a PDF, which can be unbounded at some points. 
We say that $X =^d Y$ if $F_X = F_Y impliesnot X = Y$. 
#linebreak() #linebreak() The Inverse CDF is given by $F^(-1)(q) = 
inf{x in RR:F(x) > q}$.
]
#defthm()[We define $EE(g(X)) = int_RR g(x)p_X (x) dif x$ and $var(g(X)) = EE[(g X-EE(g X))^2]$ and cov is defined easily from that. 
Correlation is cov divided by the product of the variances. From the above, we get the law of iterated expectation:
$ EE(cred(EE(Y|X))) &= int_RR EE(Y|X=x) p_X (x) dif x \
&=int_RR int_RR y p_(Y|X)(y|x) p_X (x) dif x dif y "by Fubini " (RR "is "sig"-finite")\
&=int_RR y(int_(RR) p_(X, Y)(x,y) dif x) dif y "by defn of " p_(Y|X)(y|x)\
&= EE(Y) "by the marginal distribution." $
and $ var(Y)   = EE(cred(var(Y|X))) + var(cred(EE(Y|X))) $
since
$
  EE(cred(var(Y|X))) = EE(cred(EE(Y^2|X))-cred(EE(Y|X))^2) = EE(Y^2)-EE(cred(EE(Y|X))^2)
$
$
  var(cred(EE(Y|X))) = EE(cred(EE(Y|X))^2)-EE(Y)^2. 
$
The red terms are random variables, not fixed numbers. In particular, $
  EE(Y|X):Sig to RR, #h(1cm)EE(Y|X)(omega) = EE(Y|X=X(omega))
                                                                      $
]
#defn()[
  The MGF of an RV is a negative double sided Laplace transform: $
                                                   M_X (t) = EE(e^(t X))=int_RR e^(t x)p_X (x)dif x
                                                 $
We have $M_X^((n))(0) = EE(X^n)$ since $ (d^n) / (d t^n) EE(e^(t X)) =^("dom. conv.") EE((d^n) / (d t^n) e^(t X)) 
= EE(X^n e^(t X)).   $
The characteristic function is the Fourier transform $ EE(e^(i t X))$.
]
== CDFs of Transformations
For $Y = g(X)$, $
                                                          F_Y (y) = P(Y <= y) = P(x "given" g(x) <= y) = int_A(y) p_X (x) dif x.
                                                        $
                                                        Take $Y = g(X) = log(X)$ and $p_X (x) = e^(-x), #h(0.2cm) x> 0$. 
                                                        Then $
                                                        A(y) = {x:log(x) <= y} = {x:x <= e^y}
                                                        $
                                                        $
                                                          F_Y (y) = int_0^(e^y) e^(-x) dif x = 1-e^(-e^y), #h(1cm) p_Y (y) = e^y e^(-e^y), #h(1cm) y in RR.
                                                        $ 
  Similar notions make sense if $g:RR^n to RR^(m <= n)$, but the region $A$ is harder to integrate over.
  Take independent $X,Y ~ "Unif"(0,1)$ and $Z = X slash Y$ so that
  $ 
  p_(X,Y) (x,y) = {0<x<1}{0<y<1} " and " F_(Z) (z)=F_X (Z^(-1))= int int_{x <= z y} p_(X,Y)(x,y) dif x dif y.  $
  The density weighted volume under the region with this 
particular density is just its area. If $z <=0$, the region is empty so the area is zero.
  Fix $z$ between 0 and 1, say $z=0.8$. The region in 3D space 
  we are integrating under is $d: x≥0 ∧ x≤1 ∧ y≥0 ∧ 1≥y ∧ 0.8 y≥x$. The region reaches as far as $z$ in the $x$ direction. 
  #cetz.canvas({
  import cetz.draw: *
  import cetz-plot: *
  plot.plot(
    size: (5, 5),
    x-tick-step: 1,
    y-tick-step: 1,
    axis-style: "school-book",
    {
      plot.add-fill-between(
        domain: (0, 1),
        x => calc.min((5/4)*x,1),
        x => 1,
        label:$int_0^z int_(x slash z)^1 p_(X,Y)dif y dif x = z slash 2 #v(1.5cm)$
      )
      plot.add(domain:(0,4/5),x => calc.min((5/4)*x,1),label:$y=5x slash 4 = x slash z$)
    },
  )
})
For $z >= 1$, say $z = 1.2$, the region extends to one in the $x$ direction:
#cetz.canvas({
  import cetz.draw: *
  import cetz-plot: *
  plot.plot(
    size: (5, 5),
    x-tick-step: 1,
    y-tick-step: 1,
    axis-style: "school-book",
    {

      plot.add-fill-between(
        domain: (0, 1),
        x => (5/6)*x,
        x => 1,
        label:$int_0^1 int_(x slash z)^1 p_(X,Y) dif y dif x = 1 - 1 / (2z) #v(1.5cm)$
      )
      plot.add(domain: (0, 1), x => (5/6)*x,label:$y = 5x slash 6 = x slash z$)
    },
  )
})
  #linebreak() #linebreak() Another thing we can do is use the vector to vector transform when $g:RR^n to RR^n$ #image("CS229/pdftransform.png")
  to get 
  an expression for $p_(Z,Y)$ and then marginalise the joint PDF to get $p_Z$ and $F_Z$. 
  Consider
  the transform $G(X,Y) = (X slash Y,Y)$. The formula above yields 
  $
    p_G (g_1,g_2) = p_(X,Y) (g_1 g_2, g_2)abs("det"mat(g_2,g_1;0,1)) 
    = p_(X,Y)(g_1g_2,g_2)abs(g_2) 
    = p_(Z,Y)(g_1,g_2),
  $
  so $
       f_Z (z) &= 
        int_RR p_(Z,Y)(z,y) dif y \
      &= int_RR p_(X,Y)(z y, y) abs(y) dif y \
      &= int_RR {0 < z y < 1}{0 < y < 1}abs(y) dif y \
      &= {z > 0} int_0^min(1,1 slash z) y dif y \
      &= cases(0","#h(0.2cm) z<= 0,1/2","#h(0.2cm) 1 > z > 0,
      1/(2z^2)","#h(0.2cm) z>=1) $
      and
      $
      F_Z (z) = cases(0","#h(0.2cm) z<= 0,
      z slash 2","#h(0.2cm) 1>z>0,
      1 -1/(2z)","#h(0.2cm) z>=1 ) 
     $
    == Distributions
    === Normal
    Ye old $
             mgaco mga  
           $
           As expected $A times N(mu,Sig)+b = N(A mu+b, A Sig A^top)$.
    As not so expected $M(t) = e^(mu^top t + (t^top Sig t)/2)$.
    #linebreak() #linebreak()
    #theorem()[
      Suppose that $X_1,dots,X_n ~ N(mu,sig)$ #footnote("This notation apparently implies independence")
      - $overline(X) ~ N(mu, sig^2 / n)$  
      - $((n-1) S^2) / sig^2 ~ Chi_(n-1)^2$
      - $S^2$ and $overline(X)$ are independent.
      These are not obvious.
    ]
    === Chi Squared
    The sum of squares of $p$ 
    standard normal distributions $Y = (Y_1,dots,Y_p)$ has Chi-squared dist parameter $p$.
    If the normal distributions are not standard 
    but have unit variance $Z ~N(nu,I_p)$ then the sum of squares 
    has a non-central Chi-squared distribution
    $Z^top Z ~ Chi_p^2 (nu^top nu)$.
    If $Y ~ N(mu, Sig)$, the covariance matrix is symmetric PSD and has an 
    eigen decomposition that allows square roots, which leads to $Y^top Sig^(-1) Y 
    ~ Chi^2_p (mu^top Sig^(-1) mu)$ via $Z = Sig^(-1/2) Y$, $Z ~ N(Sig^(-1/2)mu,1)$ by symmetry of $Sig^(-1/2)$.
    === Multinomial
    $p(x) = binom(n,x_1\,dots\,x_k)p_1^(x_1),dots,p_k^(x_k)$,
    where $x_1,dots,x_k$ are the numbers of 
    cards drawn from each of the $k$ categories after $n$ draws.
== Tail Behaviour of RV's
#theorem("Markov Inequality")[
Suppose $X >= 0$ and fix $t > 0$. Then $
                         EE(X) = int_0^infinity x p(x) dif x >=_("since " p >= 0) t int_t^infty p(x) dif x = t PP(X >= t). 
                       $
]
#cor("Chebyshev's Inequality")[
  Viewing $(X-EE(X))^2$ as a random variable,
$
  PP(abs(X-EE(X)) >= t) = PP((X-EE(X))^2 >= t^2) <= sig^2 / t^2 "where " t^2 = lm > 0,
$
provided that $EE(X^2)$ is finite. Similarly,
$
  PP((X-EE(X))^k >= t^k) <= EE((X-EE(X))^k)/ t^k
$
given that $EE(X^k)$ is finite.
]
#ex()[
  Suppose that $X_1,dots,X_n ~ N(mu,sig)$. Then
  $ PP(abs(overline(X)-mu) >= t) <= (var(overline(X)) 
  + EE^2(overline(X))-mu^2) / (t^2) = (sig^2)/ (n t^2) $
  and also $PP(abs(overline(X)-mu)>= (t sig) / (sqrt(n))) = 1 / t^2$.
]
These work well on nasty sums of random variables too. The ones that follow don't.
=== We can do a lot better with the additional assumption that RV's are Independent.
We need to know that #set text(size: 15pt) 
$M_X (t) = e^(t mu + 1/2 (t sig)^2)$ 
#set text(size: 11pt)
for normal distributions. 
#theorem("Chernoff's Bound")[
Suppose that $M_X$ is bounded in a neighbourhood of the origin $[-b,b]$. Then for any $t in [0,b]$
#set text(size: 14pt)
$
  PP(X-mu >= u) = PP(e^(t(X-mu)) >= e^(t u)) <= EE(e^(t(X-mu))) / e^(t u) = (M_X (t)) / e^(t(u+mu))
$
#set text(size: 11pt)
and since the infimum is the greatest lower bound,
#set text(size: 14pt)
$
  PP(X-mu >= u) <= inf_(0 <= t <= b) e^(-t(mu + u)) M_X (t). 
$
#set text(size: 11pt)
]
#ex()[
  Suppose that $X ~ N(mu,sig)$. Then the MGF is finite for $t>=0$ so by calculus
  #set text(size: 14pt)
  $
    PP(X-mu >= u ) <= inf_(0 <= t < infty) e^(-t(mu+u)) e^(t mu + 1/2 (t sig)^2) = inf_(0 <= t < infty) e^(-t u + 1/2 sig^2 t^2) = e^(-u^2/(2 sig^2))
  $
  #set text(size: 11pt)
  and
  #set text(size: 14pt)
  $
    PP(-X+mu >= u ) <= inf_(0 <= t < infty) e^(-t(-mu+u)) e^(-t mu + 1/2 (t sig)^2) = inf_(0 <= t < infty) e^(-t u + 1/2 sig^2 t^2) = e^(-u^2/(2 sig^2))
  $
  #set text(size: 11pt)
  Then since $PP(A cup B) <= PP(A) + PP(B)$,
  #set text(size: 14pt)
  $
    PP(abs(X-mu) >= u) <= 2 e^(-u^2/(2sig^2))
  $
  #set text(size: 11pt)
  and in particular since $overline(X) ~ N(mu,sig / sqrt(n))$ we have 
  #set text(size: 14pt)
  $
  PP(abs(overline(X) -mu) >= t) <= 2 e^(-(n t^2) / (2 sig^2))
                                                                      $
#set text(size: 11pt)                                                                     
and also
#set text(size: 14pt) 
$PP(abs(overline(X) -mu) >= (t sig) / (sqrt(n))) <= 2 e^(-t^2 slash 2)$. 
#set text(size: 11pt)
These bounds control the difference between 
a sample mean and mean of iid normal RV's much better than Chebyshev.                                                                      
]
#defn("Sub-Gaussian RV's")[
  The same bounds hold for any RV with 
  #set text(size: 14pt)
  $EE(e^(t(X-mu))) <= e^((t sig)^2/2)$.
  #set text(size: 11pt)
  Rademacher RV's are an example.
]
== Dimensionality Reduction
