#import "@preview/cetz:0.4.0"
#import "@preview/cetz-plot:0.1.2"
#import "@preview/ctheorems:1.1.3": *
#import "@preview/scaffolder:0.2.1": get-page-margins
#let big(img) = context {
  let size = measure(img)
  set image(width: size.width, height: size.height)
  img
}
#let textwidth() = context {
  return page.width - get-page-margins().left - get-page-margins().right
}
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
#let dee = $cal(d)$
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
#let inner(x,y) = math.op($lr(angle.l #x,#y angle.r)$)
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

  #text(size: 24pt, [Multivariable Calculus])



  Notes



  Brendan Matthews

]

#align(bottom + left)[#datetime.today().display()]

#pagebreak()

/*
BEGIN DOCUMENT
*/
#set page(margin: (left: 0cm,right:0cm))

= Implicit and Inverse function theorems
#defn("Frechet Derivative on Banach Spaces")[
Taking a derivative requires taking a limit point in the domain, so arbitrarily small neighbourhoods of the point need to exist. Every point in an open set satisfies this property. This is why we see $U subset V$ be defined as open when defining $f:U to W$. The derivative of $f$ at a point $x in U$ exists iff there is a bounded linear operator $A:V to W$ such that 
$
  #scale(auto,x:2cm)[$ lim_(norm(h) to 0) $] #h(1cm) norm(f(x+ h)-f(x) - A h)_W / (norm(h)_V) #h(1cm) #scale(auto,x:2cm)[$=0.$]
$
If $A$ exists then we write $f'(x) = A$.   
]

#image("multiv/bounded_inverse.png")
#set page(margin: (left:1cm,right:1cm))

#lemma("Major and Minor Balls of Perturbation of Open Ball")[
Fix a banach space $X$, an open ball $B(a,r) subset X$ and a contraction $g:B(a,r) to B(a,r)$ with constant $c$. Let $dee:B(a,r) to X$ 
be given by $dee(x) = x + g(x)$. Then reverse triangle says 
$
  norm(dee(x)-dee(y))_X >= (1-c)norm(x-y)_X
$
so $dee$ is injective. The triangle says that 
$
  norm(dee(x)-dee(y))_X <= (1+c)norm(x-y)_X < (1+c)r,
$
for any $x,y in B(a,r)$. In particular, if $g(a) = 0$ then $dee(a) = a$ and so $
  norm(dee(x)-a)_X < (1+c)r$ and $dee(B(a,r)) subset B(a,(1+c)r)$. This is a ball bounding the major axis 
  of the ellipse $dee(B(a,r))$ shown:
 // #textwidth()
#image("multiv/Figure_1.png")
We want to show that the inner circle in orange $B(a,(1-c)r)$ is contained within the ellipse.
For $x in B(a,(1-c)r)$ it is hard to construct $lm$ such that $lm + g(lm) = x$. We need to use the completeness of $X$ to invoke the fixed point theorem on the function $h$, $y mapsto x-g(y)$. Fix $0<r'<r$ and $alpha,beta in overline(B)(a,r')$. Then $ norm(h(alpha)-h(beta))_X = norm(g(beta)-g(alpha))_X <= c norm(beta-alpha)_X$ so $h$ is indeed a contraction on a complete metric space (closed subset of complete space is complete). It follows from Banach's fixed point theorem that $h$ has a fixed point $lm$ such that $lm = h(lm) = x-g(lm)$, so $x = dee(lm) in dee(B(a,r))$ and $B(a,(1-c)r) subset dee(B(a,r)) subset B(a,(1+c)r)$.
]
#pagebreak()
#theorem("Inverse Function Theorem")[
  Let $X$ be a Banach Space such as $RR^n$. 
  Fix an open set $A subset X$, 
  a smooth function $f in X^A cap C^1$ 
  and a point $a in A$ such that 
  $F = f'(a) in X^X$ is an invertible linear operator. 
  Then $f$ is locally invertible at $a$, i.e. there are neighbourhoods $V_a$ and $W_(f(a))$ such that $f:V_a to W_(f(a))$ is a bijection.
Furthermore, for $b = f(a)$ we have $(f^(-1))'(b) = F^(-1)$.
]
#proof()[
  Fix a point in an open set $a in A subset X$ and let $f:A to X$. 

We are given that $f in C^1$ on $A subset X$. We would like to show that $f^(-1):W_(f(a)) to V_a$ exists and is in $C^1$. Let 
$ dee(x) = a+[f'(a)]^(-1) circ (f(x)-f(a)) "N.B. Inverse is linear operator " X to X $ 
so that $dee(a) = a$ and $dee'(a) = iota:X to X$ and let $g = dee - iota$. 
Then $g$ is similar enough to $f$ that $g in C^1$. 
Fix $c$ in the interval $ 
lr((0,lr(lr(lr(||F^(-1)||)||)F||))) subset [0,1)$.
Since $g'$ is cts, there is some $r > 0$ such that $norm(g'(z)-g'(a))=norm(g'(z)) <= c$ for any $z in B(a,r)$. 
Fix $x,y in B(a,r)$. Then
$
  norm(g(x)-g(y)) &<= norm(x-y) sup_(1>t>0) norm(g'(x+t(y-x))) "by the MVT" \
  &<= c norm(x-y) " since balls are convex" 
$
so $GG:B(a,r) to B(a,r)$ given by $GG(x) = g(x)$ is a contraction as in the lemma. 
It follows from the first half of the lemma that $dee$ and $f$ 
are injections on $B(a,r)$. Since $dee$ is cts, $dee^(-1){B(a,(1-c)r)}$ 
is open. The second half of the lemma says that 
$ B(a,(1-c)r) subset dee(B(a,r)) " so " 
dee^(-1){B(a,(1-c)r)} subset B(a,r). $ 
It is then evident that 
$cal(D):dee^(-1){B(a,(1-c)r)} to B(a,(1-c)r)$ given by $cal(D)(x) = dee(x)$ 
is a bijection so invertible. Let $T_z (x) = x+z$ be the translation by $z$, which is an open map. 
We can write 
$
  f(x)=T_(f(a)) circ f'(a) circ T_(-a) circ dee(x)
$
Now $f:dee^(-1){B(a,(1-c)r)} to T_(f(a)) circ f'(a) circ T_(-a) (B(a,(1-c)r))$ 
is invertible with 
$
  f^(-1)(x) = cal(D)^(-1) circ T_a circ [f'(a)]^(-1) circ T_(-f(a))(x).
$
We need to show that $Q = T_(f(a)) circ f'(a) circ T_(-a) (B(a,(1-c)r))$ 
is an open set that contains $f(a)$.
Since $f'(a)$ is a bounded linear map and surjective, 
the open mapping theorem says that $f'(a)$ is an open map, so $Q$ is open as it is 
the image of a composition of open maps of an open set. Since $a in B(a,(1-c)r)$, 
we have 
$
  Q in.rev T_(f(a)) circ f'(a) circ T_(-a)(a) = [T_(f(a)) circ f'(a)](0) = T_f(a)(0) =f(a).
$
For $x in B(a,(1-c)/(1+c) r)$ We have $norm(dee(x)-a) = norm(dee(x)-dee(a)) 
= norm(x-a+g(x)-g(a)) <= (1+c)norm(x-a) < (1-c)r$ so that $dee(x) in B(a,(1-c)r)$. In particular, 
$dee(a) in B(a,(1-c)r)$ and this is in the domain of $cal(D)^(-1)$, so we have $a = cal(D)^(-1)(dee(a)) in dee^(-1){B(a,(1-c)r)}$ which is an open set. So we are done with the first part of the theorem, 
$f$ is invertible between open neighbourhoods of $a$ and $f(a)$.

Now we need to show that the derivative of $f^(-1)$ exists at the point $b=f(a)$.
Suppose for a moment that $f'$ is invertible at $a$. 
Then
$(f^(-1) circ f)'(a) = iota'(a) = iota:X to X$ tells us we can write $(f^(-1))'(b)$ as $ [f'(a)]^(-1)$. 
Fix $eps>0$. 
We want to show that there exists $del > 0$ such that for $k in Q$ with $norm(k)<del$ we have
$
eps > norm(f^(-1)(b+k)-f^(-1)(b)-F^(-1) k) /norm(k). $
Since $f$ 
is differentiable at $a$, we can choose $del'>0$ such that for $h in X$ with
$
  norm(h) < del' "we have" norm(F h - f(a+h)+f(a)) /norm(h)
  < (eps (1-c lr(lr(lr(||F^(-1)||)||)F||)))/(norm(F^(-1))^2).
$
Since $f^(-1)$ is cts at $b$ there exists $del''>0$ such that for all $k in Q$ with $norm(k)<del''$ we have $norm(f^(-1)(b+k)-f^(-1)(b)) < min(del',(1-c)r)$.
Pick $del=del'' >0$ and fix $k in Q$ such that $norm(k)<del$. Let $h=f^(-1)(b+k)-a$ so that
$
norm(h) < del' "and" a+h in B(a,(1-c)r).$ 
Then we have

$
norm(k-F h) 
&= norm(k+b-b-F h) \
&= norm(f(a+h)-f(a)-F h) \
&= norm(T_(f(a)) circ F circ T_(-a) circ dee(a+h) - T_(f(a)) circ F circ T_(-a) circ dee(a)-F h) \
&= norm(F circ T_(-a) circ dee(a+h) - F circ T_(-a) circ dee(a)-F h) \
&<= norm(F)_"spectal" norm(dee(a+h)-dee(a)-h) "by definition of the spectral norm"\
&= norm(F) norm(g(a+h)-g(a)) \
&<= c norm(F) norm(h)  "by the earlier estimate"\
"and"\
norm(h) &=norm(h-F^(-1)k+F^(-1)k) \
&<= norm(F^(-1)) norm(F h-k)+norm(F^(-1))norm(k) "  N.B." F^(-1) "is bounded by bounded inverse theorem"\
&<= c norm(F) norm(F^(-1)) norm(h)+norm(F^(-1))norm(k),
$
so $ norm(h) / norm(k) <= norm(F^(-1))/(1-c norm(F) norm(F^(-1))) "because we choose" c "in such a way the denominator on the RHS is positive". $
Then as desired,
$
norm(f^(-1)(b+k)-f^(-1)(b)-F^(-1) k)/norm(k) &= 
norm(h-F^(-1) k)/norm(k) \
&<= (norm(F^(-1)) norm(F h-(f(a+h)-f(a))))/norm(k) \
&<= (norm(F^(-1))^2)/(1-c lr(lr(lr(||F^(-1)||)||)F||)) norm(F h - f(a+h)+f(a)) /norm(h)\
&< eps,
$
so $f^(-1)$ is differentiable at $b$ with derivative $F^(-1)$. Since $F:X to X$ is a bounded linear operator, 
so too is $F^(-1)$ by the bounded inverse theorem. So $f^(-1)$ is continuous at $b$.
]
