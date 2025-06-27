
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
