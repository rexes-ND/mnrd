
*Exercise 1.2.1.*

(a)
For contradiction, let's assume that $exists p, q in ZZ : (p/q)^2 = 3$.
We may also assume that p and q have no common factor because if they had one we could simply cancel it out.
Now, the equation implies $p^2 = 3 q^2$.
From this, we can see that $p$ must be divisible by 3 since the square of the number that is not divisible by 3 is not divisible by 3.
This allows us to write $p = 3 r$.
If we substitute $3 r$ for $p$ in the equation, then a little algebra yields the relationship $3 r^2 = q^2$.
Now, the last equation imples that q is divisible by 3 too.
Thus, we have shown that p and q are both divisible by 3 when they were originally assumed to have no common factor.
From this logical impasse, we can only conclude that the original equation cannot hold for any integers p and q, and thus the theorem is proved. $square$

The similar argument works for $sqrt(6)$.
$exists p, q in ZZ : (p/q)^2 = 6$, implying $p^2 = 6 q^2$.
By above argument, p is divisible by 3 and $exists r in ZZ : p = 3 r$.
After substituting $3 r$ for $p$, $3 r^2 = 2 q^2$.
Now, the last equation implies that q is divisible by 3 too.
Thus, we have shown that p and q are both divisible by 3. $square$

(b) The proof of Theorem 1.1.1 breaks down in this case since we cannot conclude that $exists r in ZZ : p = 4 r$ from $p^2 = 4 q^2$.

*Exercise 1.2.2*

For contradiction, let's assume that $exists p, q in ZZ : 2^(p/q) = 3$.
The equation implies $2^p = 3^q$.
From this, we could see that $2^p$ is divisible by 3, which is impossible.
This is no such $p$ and $q$. $square$

*Exercise 1.2.3*

(a) False.
Consider $A_n = {n, n+1, n+2, ...}$ from *Example 1.2.2*.
$inter.big_(n=1)^infinity A_n = emptyset$.

(b) True.
Since $inter.big_(n=1)^infinity A_n subset.eq A_1$, the intersection is finite.
For contradiction, let's assume that the intersection is empty.
Suppose $A_1 = {a_1, a_2, ..., a_k}$.
There must exists $A_i_1$ such that $a_1 in.not A_i_1$ since otherwise $a_1$ in the intersection.
We can pick $i_2, i_3, ..., i_k$ in similar manner.
Now, $A_(max(i_1, ..., i_k)+1) = emptyset$ since it doesn't contain $a_1, a_2, ..., a_k$.
This is impossible since every $A_i eq.not emptyset$. $square$

(c) False.
Consider a case where $A = emptyset$ and $C eq.not emptyset$.

(d) True.
It can easily follow from the fact that $a in B inter C =>$ $a in B$ and $a in C$.

(e) True.
Suppose $a in A inter (B union C)$.
Then, $a in A$ and $a in B union C$.
$B$ or $C$ contains $a$.
We can safely assume that $a in B$.
$a in A inter B => a in (A inter B) union (A inter C)$.
Thus, $A inter (B union C) subset.eq (A inter B) union (A inter C)$.
The other direction can be proven in similar manner. $square$

*Exercise 1.2.4*

Let's define $A_k$ as a set of numbers where each number's smallest prime divisor is k-th smallest prime.
The one exception is $A_1$, which is set of even number and 1.
Now, every element of $NN$ belong to one of $A_k$ and for all $i < j$, $A_i inter A_j = emptyset$.

*Exercise 1.2.5*

(a)
If $x in (A inter B)^complement$, $x in.not A inter B$.
Then, $x$ cannot be in both $A$ and $B$.
We can assume that $x in.not A$.
From this, $x in A^complement$.
Now, we can conclude that $x in A^complement union B^complement$.

(b) The other direction can be proven in similar manner.

(c) Use similar logic as (a) and (b).

*Exercise 1.2.6*

(a)
If $a$ and $b$ are both positive, $|a+b| = |a| + |b| = a + b$.
If $a$ and $b$ are both negative, $|a+b| = |a| + |b| = (-a) + (-b)$.

(b)
$(a + b)^2 = a^2 + 2 a b + b^2 = |a|^2 + 2 a b + |b|^2 <= |a|^2 + 2 |a b| + |b|^2 = |a|^2 + 2 |a| |b| + |b|^2 = (|a| + |b|)^2$.

(c)
$|a - c| + |c - d| >= |a - c + c - d| = |a - d|$.
$|a - d| + |d - b| >= |a - d + d - b| = |a - b|$.

(d)
$|a| <= |a - b| + |b|$ and $|b| <= |b - a| + |a|$.
$|a| - |b| <= |a - b|$ and $|b| - |a| <= |a - b|$.
$||a| - |b|| <= |a - b|$.

*Exercise 1.2.7*

(a)
$f(A) = [0, 4]$.
$f(B) = [1, 16]$.
$f(A inter B) = f([1, 2]) = [1, 4] = [0, 4] inter [1, 16] = f(A) inter f(B)$.
$f(A union B) = f([0, 4]) = [0, 16] = [0, 4] union [1, 16] = f(A) union f(B)$.

(b)
When $A = [-1, 2]$ and $B = [-2, 1]$,
$f(A inter B) = f([-1, 1]) = [0, 1]$.
$f(A) inter f(B) = [0, 4] inter [0, 4] = [0, 4]$.
$f(A inter B) = [0, 1] != [0, 4] = f(A) inter f(B)$.

(c)
It follows from the fact that $g(A inter B) subset.eq g(A)$ and $g(A inter B) subset.eq g(B)$.

(d)
$g(A union B) eq g(A) union g(B)$.
Assume $c in A union B$.
Then, $g(c) in g(A)$ or $g(c) in g(B)$, which implies $g(c) in g(A) union g(B)$.
Assume $c in A$. $g(c) in g(A)$ and $g(c) in g(A union B)$.

*Exercise 1.2.8*

(a) $f(x) = 2 x$. There is no $x$ such that $f(x) = 1$ and when $x != y$, $f(x) != f(y)$.

(b) $f(x) = cases(
  (x+1)/2 "if" x "is odd",
  x/2 "else"
)$

The $f$ is onto since $f(2x) = x$ but 1 and 2 maps to same value (not 1-1).

(c) $f(x) = cases(
  x/2 "if" x "is even",
  -(x+1)/2 "else"
)$

*Exercise 1.2.9*

(a)
$f^(-1)(A) = [-2, 2]$.
$f^(-1)(B) = [-1, 1]$.

$f^(-1)(A inter B) = [-1, 1] = f^(-1)(A) inter f^(-1)(B)$.
$f^(-1)(A union B) = [-2, 2] = f^(-1)(A) union f^(-1)(B)$.

(b)
If $c in g^(-1)(A inter B)$, $g(c) in A inter B$.
Then, $g(c) in A$ and $g(c) in B$.
Thus, $c in g^(-1)(A)$ and $c in g^(-1)(B)$.
We can conclude that $c in g^(-1)(A) inter g^(-1)(B)$.

If $c in g^(-1)(A) inter g^(-1)(B)$, $g(c) in A inter B$.
Thus, $c in g^(-1)(A inter B)$.

Both direction is true for $g^(-1)(A inter B) = g^(-1)(A) inter g^(-1)(B)$.

The similar method can be used for $g^(-1)(A union B) = g^(-1)(A) union g^(-1)(B)$.

*Exercise 1.2.10*

(a)
False.
For $a = b$, $a < b + epsilon$ for every $epsilon > 0$.

(b)
False.
See (a).

(c)
True.
If $a <= b$, $a < b + epsilon$ for every $epsilon > 0$.
Now let's prove the other direction by contradiction.
Assume that $a > b$.
When $epsilon = a - b$, $a < b + epsilon = a$, which is impossible.

*Exercise 1.2.11*

(a)
There exists real numbers satisfying a < b, $a + 1/n >= b$ is true for every $n in NN$.
The original statement is true.

(b)
For every real number $x > 0$, there exists $n in NN$ such that $x >= 1/n$.
The negation is true.

(c)
There exists two distinct real numbers such that there are only irrational numbers between them.

*Exercise 1.2.12*

(a)
For $n = 1$, $y_1 > -6$.
Now, we want to show that if we have $y_n > -6$, then it follows that $y_(n+1) > -6$.
$y_(n+1) = (2 y_n - 6)/3 > (-12 - 6)/3 = -6$.
By induction, the claim is proved for all $n in NN$.

(b)
Let's prove that for every $n in NN$, $y_n > y_(n+1)$.
For $n = 1$, $y_2 = (2 y_1 - 6) / 3 = 2 < y_1$.
Now, we want to show that if we have $y_n > y_(n+1)$,
then it follows that $y_(n+1) > y_(n+2)$.
$(2 y_n - 6) / 3 > (2 y_(n+1) - 6) / 3 => y_(n+1) > y_(n+2)$.
By induction, the sequence is decreasing.

*Exercise 1.2.13*

(a)
Let's prove that for any finite $n in NN$, $(A_1 union A_2 union ... union A_n)^complement = A_1^complement inter A_2^complement inter ... inter A_n^complement$.
For $n = 1$, $(A_1)^complement = A_1^complement$.
Now, we want to show that if we have $(A_1 union A_2 union ... union A_n)^complement = A_1^complement inter A_2^complement inter ... inter A_n^complement$,
then it follows that $(A_1 union A_2 union ... union A_n union A_(n+1))^complement = A_1^complement inter A_2^complement inter ... inter A_n^complement inter A_(n+1)^complement$.

By *Exercise 1.2.5*,
$(A_1 union A_2 union ... union A_n union A_(n+1))^complement = (A_1 union A_2 union ... union A_n)^complement inter A_(n+1)^complement$.
By induction, the claim is proved for all $n in NN$.

(b)
Consider *Example 1.2.2*.

(c)
Consider $a in (union.big_(i=1)^infinity A_i)^complement$.
Then $a in.not union.big_(i=1)^infinity A_i$, implying for every $i in NN$, $a in.not A_i$ or $a in A_i^complement$.
Thus $a in inter.big_(i=1)^infinity A_i^complement$.

Consider $a in inter.big_(i=1)^infinity A_i^complement$.
Then, for every $i in NN$, $a in A_i^complement$ or $a in.not A_i$.
Thus, $a in.not union.big_(i=1)^infinity A_i$, implying $a in (union.big_(i=1)^infinity A_i)^complement$.
$square$

*Exercise 1.3.1*

(a)
A real number $s$ is the _greatest lower bound_ for a set $A subset.eq RR$ if it meets the following two criteria:
#set enum(numbering: "(i)")
+ s is a lower bound for $A$;
+ if $l$ is any lower bound for $A$, then $l <= s$.

(b)
Assume $s in RR$ is an lower bound for a set $A subset.eq RR$.
Then, $s = inf A$ if and only if, for every choice of $epsilon > 0$,
there exists an element $a in A$ satisfying $s + epsilon > a$.

($==>$) For the forward direction, we assume $s = inf A$ and consider $s + epsilon$,
where $epsilon > 0$ has been arbitrarily chosen.
Because $s + epsilon > s$, part (ii) implies that $s + epsilon$ is not lower bound.
If this is the case, then there must be some element $a in A$ for which $a < s + epsilon$
(because otherwise $s + epsilon$ would be a lower bound).

($<==$) Conversely, assume $s$ is a lower bound with the property that no matter how $epsilon > 0$ is chosen,
$s + e$ is no longer a lower bound for $A$.
Notice that what this implies is that if $l$ is any number more than $s$,
then $l$ is not a lower bound.
Because we have just argued that any number more than $s$ cannot be a lower bound,
it follows that if $l$ is some other lower bound for $A$,
then $s >= l$.

*Exercise 1.3.2*

(a)
Any B with one element satisfy $inf B >= sup B$.

(b)
The supremum of the finite set is its largest element.
Therefore, it is impossible.

(c)
$S = {r in QQ : 0 < r <= 1}$

*Exercise 1.3.3*

(a)
By the Axiom of Completeness,
we know that $sup B$ exists since $B$ is bounded from above by any element of $A$.
In order for $sup B = inf A$, $sup B$ must be lower bound of $A$ and for every lower bound $l$ of $A$,
$l <= sup B$.
Therefore, we only need to show that $sup B$ is a lower bound of $A$.
Assume that there exist $a in A$ such that $a < sup B$.
By *Lemma 1.3.8*, if we choose $epsilon = sup B - a$,
there exists $b in B$ such that $sup B - epsilon = a < b$.
It is a contradictions since $b$ is a lower bound of $A$.

(b)
By the Axiom of Completeness, $sup B$ exists,
which is also the greatest lower bound of $A$.

*Exercise 1.3.4*

(a)
$sup (A union B) >= sup A$ since $sup (A union B)$ is an upper bound of $A union B$ (and $A$).
$sup (A union B) >= max(sup A, sup B)$.
Moreover, every $c in A union B$ satisfies $c <= sup A$ or $c <= sup B$.
Therefore, $c <= max(sup A, sup B)$, implying $sup (A union B) <= max(sup A, sup B)$.
Thus, $sup (A union B) = max(sup A, sup B)$.

We can even extend this to $sup (union.big_(k=1)^n A_k) = max(sup A_1, sup A_2, ..., sup A_n)$.

(b)

Since $union.big_(k=1)^infinity A_k$ can be unbounded, the supremum cannot exist.

*Exercise 1.3.5*

(a)
Since $c a <= c sup A$ for every $a in A$,
$c sup A$ is an upper bound of $c A$.

Now, it is enough to show that for every $epsilon > 0$,
there exist $a in A$ such that $c sup A - epsilon < c a$.
Since $c = 0$ case is obvious, assume that $c > 0$.
Then, it is enough to prove that for every $epsilon > 0$,
there exists $a in A$ such that $sup A - epsilon / c < a$.
Since $epsilon / c > 0$, the last statement is true by *Lemma 1.3.8*.

(b)
Now, $c a <= c inf A$ for every $a in A$.
In other words, $c inf A$ is an upper bound of $c A$.
In order to show that $c inf A = sup (c A)$,
it is enough to prove that, for every $epsilon > 0$,
there exists $a in A$ such that  $c inf A - epsilon < c a$.
The last part is equivalent to $inf A + epsilon / (-c) > a$,
which is true by *Exercise 1.3.1 (b)*.

*Exercise 1.3.6*

(a)
Since, for every $a in A, b in B$, $a <= s$ and $b <= t$ by definition.
From $a + b <= s + t$, we can see that $s + t$ is an upper bound.

(b)
Assume that $u$ is an upper bound of $A + B$.
If we fix $a in A$, then, for every $b in B$, $a + b <= u$ or $b <= u - a$.
Since $u - a$ is an upper bound of $B$, $t <= u - a$.

(c)
For every $a in A$, $t + a <= u$.
Thus, $sup (t + A) = t + sup A = t + s <= u$ by *Example 1.3.7*.
Finally, we proved that $sup (A + B) = s + t$ since $u >= t + s$ for every upper bound $u$.

(d)
Since $s + t$ is an upper bound of $A + B$,
it is enough to prove that for every $epsilon > 0$,
there exists $a in A, b in B$ such that $s + t - epsilon < a + b$.
By *Lemma 1.3.8*, there exists $a in A$ such that $s - epsilon / 2 < a$ and $b in B$ such that $t - epsilon / 2 < b$.
If we combine these, we achieve what we want.

*Exercise 1.3.7*

$sup A >= a$ since $sup A$ is an upper bound of A.
Since $a$ is an upper bound of A, $a >= sup A$.
Thus, $a = sup A$.

*Exercise 1.3.8*

(a)
the supremum is 1.
The infimum is 0.

(b)
The supremum is 1.
The infimum is -1.

(c)
The supremum is $1/3$.
The infimum is $1/4$.

(d)
The supremum is $1$.
The infimum is $0$.

*Exercise 1.3.9*

(a)
For every $epsilon > 0$,
there exist $b in B$ such that $sup B - epsilon < b$.
If $epsilon = sup B - sup A$, $sup A < b$.
This b is an upper bound for $A$.

(b)
$A = [0, 1]$ and $B = [0, 1)$.
There is no element of $B$ that is no less than 1.

*Exercise 1.3.10*

(a)
There exist $sup A$ and $inf B$ by the Axiom of Completeness.
Assume $sup A > inf B$.
For every $epsilon_a > 0$,
there exists $a in A$ such that $sup A - epsilon_a < a$.
For every $epsilon_b > 0$,
there exists $b in B$ such that $inf B + epsilon_b > b$.
If we choose $epsilon_a = sup A - inf B$,
there exists $a in A$ such that $inf B < a$.
If we choose $epsilon_b = a - inf B$,
there exists $b in B$ such that $a > b$.
This is a contradiction.

Now, assume $sup A < inf B$.
Choose $c = (sup A + inf B) / 2$, which satisfies the following: $sup A < c < inf B$.
Since $c$ is more than every element of A and less then every element of B,
it is not in A and B.
However, $A union B = RR$. This is a contraction.

Therefore, $sup A = inf B$, which is also $c$.

(b)

$B = {b in RR | "there is no" e in E "such that" b < e}$.
In other words, B is the set of upper bounds of E.

$A = {a in RR | "there is" e in E "such that" a < e}$.

$A union B = RR$. $A$ and $B$ are disjoint.
For any $a in A, b in B$, there exists $e in E$ such that $a < e$.
Since $b$ cannot be less than $e$ by its definition, $e <= b$.
Thus, $a < b$. By the Cut Property, there exist $c in RR$ such that whenever $x in B$,
$x >= c$. This $c$ is $sup E$.

(c)
Let $A = {a in QQ | a < sqrt(2)}$ and $B = {a in QQ | sqrt(2) <= b}$.
A and B are nonempty, disjoint sets with $A union B = QQ$.
Assume that there exists $c in QQ$ such that
$x <= c$ whenever $x in A$ and
$x >= c$ whenever $x in B$.
$c$ cannot be $sqrt(2)$ since it is irrational number.
Assume $c < sqrt(2)$,
we can always pick $d in Q$, which satisfy $c < d < sqrt(2)$.
Since $d in A$ ($d < sqrt(2)$), $d <= c$.
This is contradication.
We can reach similar contradiction when $c > sqrt(2)$.
Therefore, the Cut Property is not a valid statement in $QQ$.

*Exercise 1.3.11*

(a)
True.
$sup B >= b$ for every $b in B$, which also true when $b in A$ since $A subset.eq B$.
$sup B$ is an upper bound for $A$. Thus, $sup A <= sup B$.

(b)
True.
$c = (sup A + inf B) / 2$, satisfies $a <= sup A < c < inf B <= b$ for every $a in A, b in B$.

(c)
False.
Let $A = [0, 1)$, $B = (1, 2]$, and $c = 1$.
$a < c < b$ for all $a in A$ and $b in B$.
$sup A = 1 = inf B = 1$.

*Exercise 1.4.1*

(a)
There exist $a_1, a_2, b_1, b_2 in ZZ$ such that $a = a_1 / a_2 "and" b = b_1 / b_2$.

$a b = (a_1 b_1) / (a_2 b_2) in QQ "since" a_1 b_1, a_2 b_2 in ZZ$.

$a + b = (a_1 b_2 + a_2 b_1) / (a_2 b_2) in QQ "since" a_1 b_2 + a_2 b_1, a_2 b_2 in ZZ$.

(b)
$"If" a + t in QQ "and" a in QQ$, then $t in Q$. Thus, $a + t in II$.
If $a t, a in QQ$ and $a != 0$. Then $(a t) / a = t in QQ$. Thus, $a t in II$.

(c)
If $s = -t = sqrt(2)$, $s + t = 0 "and" s t = -2$. Thus, $II$ is not closed under addition or multiplication.
We can only say that $s + t "and" s t in RR$.

*Exercise 1.4.2*

For all $n in NN$, $sup A <= s + 1 / n$ and $s - 1 / n < sup A$.
This is equivalent to $-1 / n <= s - sup A < 1 / n$, which implies $|s - sup A| <= 1 / n$.
If $s != sup A$, then $|s - sup A| > 0$ and by *Theorem 1.4.2*, there must be $n in N$ satisfying $1 / n < |s - sup A|$.
Thus, $s = sup A$.

*Exercise 1.4.3*

Assume $s in inter.big_(n=1)^infinity (0, 1 / n)$.
Then, $0 < s < 1 / n$ for all $n in NN$.
However, by *Theorem 1.4.2*, there exists $n in N$ such that $1 / n < s$.
Thus, the intersection is empty.

*Exercise 1.4.4*

There exists $r in QQ$ such that $a < r < b$ by *Theorem 1.4.3*.
Thus, $T$ is nonempty and bounded from above.
$sup T <= b$ since $b$ is an upper bound of $T$.
Also, note that $a < r <= sup T$.
If $sup T < b$, there exists $q in QQ$ such that $sup T < q < b$.
Also, $q in T$, which is leads to contradiction.
Thus, $sup T = b$.

*Exercise 1.4.5*

By *Theorem 1.4.3*, there exists $r in QQ$ such that $a - sqrt(2) < r < b - sqrt(2)$ or $a < r + sqrt(2) < b$.
By *Exercise 1.4.1*, $r + sqrt(2) in II$.

*Exercise 1.4.6*

(a)
When $a = 0 "and" b = 1 / 11$, $0 < p / q < 1 / 11$, implying $0 < p$ and $11 p < q <= 10$.
This is impossible. Thus, the set is not dense in $RR$.

(b)
There exists $n in NN$ satisying $1 / n < b - a$ and $q >= n$ where $q$ is a power of 2.
It follows that $1 / q < b - a$ or $1 + a q < b q$.
Choose $p in ZZ$ such that $a q < p <= a q + 1$.
Then, $a q < p < b q$ or $a < p / q < b$.
Thus, the set is dense in $RR$.

(c)
When $a = 0 "and" b = 0.1$, $0 < p / q < 0.1$, implying $0 < p "and" (10 p) / q < 1$.
This is impossible. Thus, the set is not dense in $RR$.

*Exercise 1.4.7*

There exists $n_0 in NN$ such that $(alpha^2 - 2) / (2 alpha) > 1 / n_0$, $alpha^2 - 2 > (2 alpha) / n_0$ or $alpha^2 - (2 alpha) / n_0 > 2$.

$2 < alpha^2 - (2 alpha) / n_0 < alpha^2 - (2 alpha) / n_0 + 1 / n_0^2 = (alpha - 1 / n_0)^2$.
Thus, $alpha - 1 / n$ is an upper bound of $T$, which leads to contradiction.

*Exercise 1.4.8*

(a)
$A = [0, 1) inter II "and" B = [0, 1) inter QQ$.
$sup A = sup B = 1$.

(b)
Choose $J_i = (-1/n, 1/n)$. Then $inter.big_(n=1)^infinity J_n = {0}$.

(c)
$L_i = [i, infinity)$.
Assume $a in inter.big_(n=1)^infinity$.
There exists $n in NN$ satisfying $n > a$ and $a in L_n$, leading to contradiction.
Thus, $inter.big_(n=1)^infinity L_n = emptyset$.

(d)
Define $J_i = inter.big_(n=1)^i I_n$.
Then, $J_i != emptyset$.
Since $J_(i+1) = J_i inter I_(n+1)$, $J_(i+1) subset.eq J_i$ and $J_i$ is closed interval.
By *Theorem 1.4.1*, $inter.big_(n=1)^infinity J_n != emptyset$.
Let's consider its element $j$.
For all $n in NN$, $j in J_n = inter.big_(i=1)^n I_i$, implying $j in I_n$.
Since $j in inter.big_(n=1)^infinity I_n$, the request is impossible.
