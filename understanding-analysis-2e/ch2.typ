*Exercise 2.2.1*

Choose $epsilon = 2$ and $(x_n) = (1, -1, 1, -1, ...)$.
$(x_n)$ is verconges to 0 and 1/2.
This describes a sequence, where every element falls in $V_epsilon (x)$.

*Exercise 2.2.2*

(a)
$|(2 n + 1) / (5 n + 4) - 2 / 5| < epsilon <=> 3/(25 epsilon) - 4/5 < n$.
Let $epsilon > 0$ be arbitrary.
Choose $N in NN$ with $N > 3/(25 epsilon) - 4/5$.
$n >= N$ satisfies $|(2 n + 1) / (5 n + 4) - 2 / 5| < epsilon$ as desired.

(b)
$(2 n^2) / (n^3 + 3) < epsilon <=> 1/epsilon < n/2 + 3/(2 n^2)$.
Let $epsilon > 0$ be arbitrary.
Choose $N in NN$ such that $N > 2/epsilon$.
For $n >= N$, $n > 2/epsilon "or" n /2 > 1/epsilon$, which implies $n/2 + 3/(2 n^2) > 1/epsilon <=> (2 n^2)/(n^3 + 3) < epsilon$.

(c)
Let $epsilon > 0$ be arbitrary.
Choose $N in NN$ such that $N > 1/(epsilon^3)$.
For $n >= N$, $n > 1/(epsilon^3) >= (|sin^3(n^2)|)/(epsilon^3)$, implying $epsilon > |sin(n^2)/root(3, n)|$.

*Exercise 2.2.3*

(a)
Existence of a college where there is no student who is at least seven feet tall.

(b)
Existence of a college where there is no professor who gives every student a grade of either A or B.

(c)
For all colleges in the United States, there exists a student who is less than six feet tall.

*Exercise 2.2.4*

(a)
(1, -1, 1, -1, ...) contains an infinite number of ones but doesn't converge.

(b)
Assume that we have such sequence $(a_n)$ and the limit $a != 1$.
For any $epsilon > 0$, there exists $N in NN$ such that $|a_n - a| < e$ for every $n >= N$.
Let $epsilon = |a - 1| > 0$.
Since we have an infinite number of ones, there exists $n_0 >= N$ such that $a_n_0 = 1$.
$|a_n_0 - a| = |a - 1| < epsilon = |a - 1|$, which leads to contradiction.
The request is impossible.

(c)
(1, -1, 1, 1, -1, 1, 1, 1, -1, ...) contains $n$ consecutive ones.

*Exercise 2.2.5*

(a)
$a_n = [[5/n]] = 0$ for every $n >= 6$.
Let $epsilon > 0$ be arbitrary.
Choose $N = 6$, then $|a_n - 0| = 0 < epsilon$ for $n >= N$.
Thus, $lim a_n = 0$.

(b)
$1 < (12 + 4 n) / (3 n) = 4/3 + 4/n < 2$ for $n > 6$ or $n >= 7$.
$a_n = [[(12 + 4n)/(3n)]] = 1$ for $n >= 7$.
Let $epsilon > 0$ be arbitrary.
Choose $N = 7$, then $|a_n - 1| = 0 < epsilon$ for $n >= N$.
Thus, $lim a_n = 1$.

For some sequences, $N$ doesn't need to get larger for the smaller $epsilon$.

*Exercise 2.2.6*

Assume that $(a_n)$ has two different limits, $a$ and $a'$.
Note that $a != b$.
Let $epsilon = (|a - b|) / 2 > 0$.
There exists $N_1$ such that $|a_n - a| < epsilon$ for $n >= N_1$.
There exists $N_2$ such that $|a_n - b| < epsilon$ for $n >= N_2$.
For $n >= max(N_1, N_2)$, $|a_n - a| + |a_n - b| < 2 epsilon = |a - b|$, which leads to contradiction.

*Exercise 2.2.7*

(a)
$(-1)^n$ is frequently but not eventually.

(b)
_eventually_ is stronger than _frequently_ since the former implies the latter.

(c)
A sequence $(a_n)$ converges to $a$ if, given any $epsilon$-neighborhood $V_epsilon (a)$ of $a$, $(a_n)$ is eventually in a $V_epsilon (a)$.

(d)
$(x_n)$ is frequently in the interval $(1.9, 2.1)$.
$(2, 3, 2, 3, ...)$ is not eventually in $(1.9, 2.1)$.

*Exercise 2.2.8*

(a)
It is zero-heavy. Choose $M = 1$.

(b)
Assume that there is a finite number of zeros and $x_n$ is the last zero.
Then, we can choose $N = n+1$ and there exist $n < N <= m <= N + M$ such that $x_m = 0$, leading to contradiction.
Thus, the sequence contain an infinite number of zeros.

(c)
Consider $(x_n) = {1, 0, 1, 1, 0, 1, 1, 1, 0, ...}$.
$(x_n)$ has infinite zeros.
Assume that the sequence is zero-heavy.
Then, we can find $M$, where there is at least one zero among $M+1$ consecutive terms.
However, $(x_n)$ contains $M+1$ consecutive terms all equal to 1, leading to contradiction.
Thus, the sequence can be not zero-heavy.

(d)
A sequence is not zero-heavy if for every $M in NN$, there exists $N in NN$ such that $x_n != 0$ for all $n$ satisfying $N <= n <= N + M$.

*Exercise 2.3.1*

(a)
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that for every $n >= N$, $|x_n - 0| < epsilon^2$ or $|sqrt(x_n) - 0| < epsilon$ as needed.

(b)
By *Theorem 2.3.4*, $x >= 0$.
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that $|x_n - x| < epsilon^2$ for every $n >= N$.
$epsilon^2 > |sqrt(x_n) - sqrt(x)| (sqrt(x_n) + sqrt(x)) >= (sqrt(x_n) - sqrt(x))^2$ or $epsilon > |sqrt(x_n) - sqrt(x)|$ as needed.


*Exercise 2.3.2*

(a)
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that $|x_n - 2| < 3/2 epsilon$ for every $n >= N$.
$|(2 x_n - 4) / 3| < epsilon$ or $|(2 x_n - 1) / 3 - 1| < epsilon$ as desired.

(b)
Let $epsilon > 0$ be arbitrary.
There exists $N_1 in NN$ such that $|x_n - 2| < 3/2$ for every $n >= N_1$.
There exists $N_2 in NN$ such that $|x_n - 2| < epsilon$ for every $n >= N_2$.
Since $|x_n - 2| < 3/2$, $|x_n| > 1/2$.
For every $n >= max(N_1, N_2)$, $|1/x_n - 1/2| = (|x_n - 2|)/(2 |x_n|) < epsilon/(2 * 1/2) = epsilon$ as desired.

*Exercise 2.3.3*

Let $epsilon > 0$ be arbitrary.
There exists $N_1 in NN$ such that $|x_n - l| < epsilon$ for $n >= N_1$.
There exists $N_2 in NN$ such that $|z_n - l| < epsilon$ for $n >= N_2$.
For every $n >= max(N_1, N_2)$, $l - epsilon < x_n <= y_n <= z_n < l + epsilon$ or $|y_n - l| < epsilon$ as desired.

*Exercise 2.3.4*

(a)
$lim (1 + a_n) = 1 "and" lim (1 + 3 a_n - 4 a_n^2) = 1$.
Thus, $lim ((1 + 2 a_n)/(1 + 3 a_n - 4 a_n^2)) = 1 / 1 = 1$.

(b)
$lim (((a_n + 2)^2 - 4)/a_n) = lim ((a_n (a_n + 4)) / a_n) = lim (a_n + 4) = 4$.

(c)
$lim ((2/a_n + 3)/(1/a_n+5)) = lim ((2 + 3 a_n)/(1 + 5 a_n)) = 2$.

*Exercise 2.3.5*

Assume that $lim x_n = lim y_n = l$.
There exists $N_1 in NN$ such that $|x_n - l| < epsilon$ for $n >= N_1$.
Also, there exists $N_2 in NN$ such that $|y_n - l| < epsilon$ for $n >= N_2$.
If we choose $N >= max(2 N_1 - 1, 2 N_2)$, $|z_n - l| < epsilon$ for $n >= N$ as desired.

Now, assume that $(x_1, y_1, x_2, y_2, ..., x_n, y_n, ...)$ and $lim z_n = l$.
Let $epsilon > 0$ be arbirary.
There exists $N in NN$ such that $|z_n - l| < epsilon$ for every $n >= N$.
We can assume that ${z_N, x_(N+1)} = {x_N_1, y_N_2}$.
For every $n >= N_1$, $|x_n - l| < epsilon$.
For every $n >= N_2$, $|y_n - l| < epsilon$.
Thus, $lim x_n = lim y_n = l$.

*Exercise 2.3.6*

$x_n = 1 + 2/n$. Since $x_n >= 0 "and" (x_n) -> 1$, $sqrt(x_n) -> 1$.
$b_n = n - sqrt(n^2 + 2 n) = (n^2 - n^2 - 2 n) / (n + sqrt(n^2 + 2 n)) = (-2n)/(n+sqrt(n^2 + 2 n)) = (-2)/(1 + sqrt(1 + 2/n)) = (-2) / 2 = -1$.

*Exercise 2.3.7*

(a)
$(x_n) = {1, -1, 1, -1, ...}$ and $(y_n) = {-1, 1, -1, 1, ...}$.

(b)
Assume that $lim x_n = x "and" lim (x_n + y_n) = z$.
By *Theorem 2.3.3*, $lim (-x_n) = -x$ and $lim (x_n + y_n + (-x_n)) = lim (x_n + y_n) + lim (-x_n) = z - x$.
Thus, the request is impossible.

(c)
Consider $b_n = 1/n$.

(d)
Assume that the both $(b_n) "and" (a_n - b_n)$ are bounded.
Then, there exist $M_1, M_2 in NN$ such that $|b_n| <= M_1 "and" |a_n - b_n| <= M_2$.
Since $M_1 + M_2 >= |a_n - b_n| + |b_n| >= |a_n|$, $(a_n)$ is bounded, leading to contradiction.
Thus, the request is impossible.

(e)
Consider $a_n = 1/n "and" b_n = n$.

*Exercise 2.3.8*

(a)
By *Theorem 2.3.3*,
$lim (x_n^k) = lim (x_n^(k-1)) lim (x_n) = ... = (lim (x_n))^k = x^k$.
Also, $lim (p_k x_n^k) = p_k lim (x_n^k) = p_k x^k$.
Thus, $lim (p(x_n)) = lim(p_k x_n^k) + lim(p_(k-1) x_n^(k-1)) + ... + lim(p_1 x_n) + p_0$ = $p_k x^k + p_(k-1) x^(k-1) + ... + p_1 x + p_0 = p(x)$.

(b)
$x_n = 1/n "and" f(x) = cases(
  1 "if" x != 0,
  0 "else"
)$. For every $n in N$, $|f(x_n) - 1| = |f(1/n) - 1| = 0$.
Thus, $f(x_n)$ converges to 1. However, $f(0) = 0 != 1 = lim f(x_n)$.

*Exercise 2.3.9*

(a)
Since we don't know if $lim a_n$ exists, we are not allowed to use the Algebraic Limit Theorem.
Let $epsilon > 0$ be arbitrary.
There exists $M > 0$ such that $|a_n| <= M$.
There exists $N in NN$ such that $|b_n| < epsilon / M$ for every $n >= N_1$.
There exists $|a_n b_n| = |a_n||b_n| < M epsilon / M = epsilon$ as desired.
Thus, $lim (a_n b_n) = 0$.

(b)
$(a_n b_n)$ can be divergent.
Consider $a_n = (-1)^n a$ and $b_n = b$.

(c)
Since $lim a_n = 0 "and" b_n$ is bounded, $lim (a_n b_n) = 0$ by (a).

*Exercise 2.3.10*

(a)
False. Consider $a_n = n "and" b_n = -n$.

(b)
True.
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that
$||b_n| - |b|| <= |b_n - b| < epsilon$ for $n >= N$ as desired.

(c)
False when $a != 0$.
By *Theorem 2.3.3*, $lim (b_n) = lim (b_n - a_n) + lim (a_n) = 0 + 0 = 0$.

(d)
True.
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that
$epsilon > |a_n - 0| = |a_n| >= |b_n - b|$ as desired.

*Exercise 2.3.11*

(a)
Since $(x_n)$ is convergent, it is bounded.
Let $lim x_n = x$.
There exists $M in NN$ such that $|x_n - x| <= M$.
Let $epsilon > 0$ be arbitrary.
Choose any $epsilon_0 < min(epsilon, M)$.
There exists $N in NN$ such that $|x_n - x| < epsilon_0$.
$|y_n - x| = |(x_1 + x_2 + ... + x_n)/n - x | <= (|x_1 - x| + ... + |x_n - x|)/n < ((N - 1)M + (n - N + 1)epsilon_0)/n = ((N-1)(M-epsilon_0))/n + epsilon_0$, which is less than $epsilon$ for $n >= ((N - 1)(M - epsilon_0))/(epsilon - epsilon_0)$.

(b)
Consider $x_n = (-1)^n$.

*Exercise 2.3.12*

(a)
True. Since $sup B <= a_i$, $sup B <= a$ by *Theorem 2.3.4*.
Thus, $a$ is an upper bound.

(b)
False. Consider $a_n = -1/n$.

(c)
False. $a_1 = 1$ and $a_(n+1) = a_n + 1/k$ where $k$ is the smallest possible natural number such that $a_(n+1) < sqrt(2)$.
$a = sqrt(2)$, which is not rational.

*Exercise 2.3.13*

(a)

$lim_(n->infinity) (lim_(m->infinity) a_(m n))
= lim_(n->infinity) (lim_(m->infinity) m/(m+n))
= lim_(n->infinity) (lim_(m->infinity) 1/(1+n/m)) = 1$.

$lim_(m->infinity) (lim_(n->infinity) a_(m n))
= lim_(m->infinity) (lim_(n->infinity) m/(m+n))
= lim_(m->infinity) (lim_(n->infinity) (m/n)/(m/n+1)) = 0$.

(b)
Let $epsilon > 0$ be arbitrary.
Choose $N in NN$ such that $N > 1 / (2 epsilon)$.
For every $m,n >= N$,
$|a_(m n) - 0| = |1 / (m+n)| <= |1 / (2 N)| < epsilon$.
Thus, $lim_(m,n -> infinity) a_(m n) = 0$.

In the case of $a_(m n) = (m n)/(m^2 + n^2)$,
first two limits are 0 and 0
since $(m n)/(m^2 + n^2) = (n/m) / (1 + n^2/m^2)$.

When $m = n$, $a_(m n) = 1/2$.
When $m = 2 n$, $a_(m n) = 2/5$.
Thus, $lim_(m,n -> infinity) a_(m n)$ doesn't exist.

(c)
$a_(m n) = (-1)^n/m + (-1)^m/n$.

(d)
Let $epsilon > 0$ be arbitrary.
There exists $N_1 in NN$ such that $|a_(m n) - a| < epsilon/2$ for every $m, n >= N_1$.
There exists $N_2 in NN$ such that $|a_(m n) - b_m| < epsilon/2$ for every $n >= N_2$.
For every $m, n >= max(N_1, N_2)$,
$|b_m - a| <= |a_(m n) - a| + |b_m - a_(m n)| < epsilon$.
Thus, $lim_(m->infinity) b_m = a$.

(e)
Let $lim_(m,n -> infinity) a_(m n) = a, b_m = lim_(n->infinity) a_(m n), "and" c_n = lim_(n->infinity) a_(m n)$.
Using (d), $lim_(m->infinity) b_m = a$ and $lim_(n->infinity) c_n = a$ as desired.

*Exercise 2.4.1*

(a)
By *Theorem 2.4.2*, it is enough to prove that the sequence is decreasing and positive.
$x_2 = 1 <= x_1$ and $x_1, x_2 > 0$.
If $x_n, x_(n+1) > 0$ and $x_(n+1) <= x_n$, $x_(n+2) = 1 / (4-x_(n+1)) <= 1 / (4-x_n) = x_(n+1)$
(note that $x_n <= x_1 <= 3$). Since $x_(n+1) <= 3$, $x_(n+2) > 0$.
Thus, the sequence is decreasing and bounded ($>0$).

(b)
Since $x_(n+1)$ is also decreasing and bounded, $lim x_(n+1)$ must also exist.

(c)
$l = lim x_n$ = $lim x_(n+1)$ = $1 / (4 - l)$. $l = 2 - sqrt(3)$ since $2 + sqrt(3) > 3$.

*Exercise 2.4.2*

(a)
Assuming that $lim y_n$ exists before proving that $(y_n)$ converges is wrong.

(b)
To show the convergence, it is enough to show that $y_(n+1) >= y_n$ and $y_n < 3$.
$y_(n+2) = 3 - 1/y_(n+1) >= 3 - 1/y_n = y_(n+1)$. Since $y_n >= y_1 = 1$, $y_(n+1) = 3 - 1/y_n < 3$, $y_n < 3$.
Thus, we can use the strategy.

*Exercise 2.4.3*

(a)
The sequence is defined by $a_1 = sqrt(2) "and" a_(n+1) = sqrt(2 + a_n)$.
To show the convergence, it is enough to show that $a_n <= 2$ and $a_n <= a_(n+1)$.
By the induction, $a_(n+1) = sqrt(2 + a_n) <= sqrt(2 + 2) = 2$.
Also, $a_(n+1) = sqrt(2 + a_n) <= sqrt(2 + a_(n+1)) = a_(n+2)$.
Thus, the sequence converges.
Since $a_n + 2 >= 0$, $lim sqrt(a_n + 2) = sqrt(lim a_n + 2) = lim a_n$.
Let $a = lim a_n$.
Then, $a^2 = a + 2$.
Thus, $a = -1 "or" a = 2$.
Since $a_n >= 0$, $lim a_n = 2$.

(b)
The sequence is defined by $a_1 = sqrt(2) "and" a_(n+1) = sqrt(2 a_n)$.
If $a_n <= 2$, $a_(n+1) = sqrt(2 a_n) <= 2$. Thus, $a_n <= 2$.
If $a_n <= a_(n+1)$, $a_(n+1) = sqrt(2 a_n) <= sqrt(2 a_(n+1)) = a_(n+2)$.
Thus, $(a_n)$ converges.
Let $a = lim a_n$.
Since $2 a_n >= 0$, $lim sqrt(2 a_n) =sqrt(2 lim a_n) = sqrt(2 a) = a$.
Thus, $a = lim a_n = 2$.

*Exercise 2.4.4*

(a)
Let $a_n = r / n$.
$lim a_n = r lim 1 / n = 0$.
Let $epsilon > 0$ be arbitrary.
There exists $N in NN$ such that $|r/n| < epsilon$ for every $n >= N$.
$(|r|) / epsilon < n$, where we can choose $epsilon = 1$.
Thus, there exists $n in NN$ such that $r <= |r| < n$.

(b)
Since $a_n, b_n$ are bounded and monotone sequences, both $lim a_n "and" lim b_n$ exist.
Since $a_n <= b_n$, $lim a_n <= lim b_n$.
Thus, any number in $[lim a_n, lim b_n]$ exists in intersection.

*Exercise 2.4.5*

(a)
If $x_n^2 >= 2$, $x_(n+1)^2 = 1/4 (x_n^2 + 4 + 4/x_n^2) = 1/4 ((x_n - 2/x_n)^2 + 8) >= 2$.
$x_(n+1)^2 + 6 <= 4 x_(n+1)^2 = x_n^2 + 4 + 4 / x_n^2 <= x_n^2 + 6$.
Thus, $x_(n+1)^2 <= x_n^2$ and since $x_n > 0$, $x_(n+1) <= x_n$.
Thus, the sequence converges and let $x = lim x_n$.
We obtain $x = plus.minus sqrt(2)$ by solving $x = 1/2 (x + 2 / x)$.
Since $x_n >= 0$, $x = sqrt(2)$.

(b)
$x_(n+1) = 1/2(x_n + c / x_n)$ and let $x_1 > sqrt(c)$ be arbitrary.
Follow the same steps as (a).

*Exercise 2.4.6*

(a)
$sqrt(x y) <= (x + y)/ 2 <=> 0 <= (sqrt(x) - sqrt(y))^2/2$.

(b)
By (a), $0 <= x_n <= y_n$.
$y_(n+1) = (x_n + y_n)/2 <= y_n$ and $0 <= y_(n+1)$.
$x_(n+1) = sqrt(x_n y_n) >= x_n$ and $x_(n+1) <= y_(n+1) <= y_1$.
Thus, both $x_n "and" y_n$ converge. Let $x = lim x_n "and" y = lim y_n$.
$y = (x + y) / 2 <=> x = y$.

*Exercise 2.4.7*

(a)
Since $y_n >= a_k$ for every $k >= n$, $y_n >= sup{a_k : k >= n} = y_(n+1)$.
There exists $M in NN$ such that $a_n <= M$ for every $n in NN$.
Thus, $y_n <= M$ for every $n in NN$.
Since $y_n$ is decreasing and bounded, it converges.

(b)
$z_n = inf{a_k : k >= n}$ and we can show that $z_n <= z_(n+1)$.
Thus, $z_n$ converges.

(c)
Since $z_n <= y_n$, $lim z_n <= lim y_n$ by *Theorem 2.3.4*.
Consider $a_n = (-1)^n$, where $y_n = 1 "and" z_n = -1$.

(d)
Since $z_n <= a_n <= y_n$, if $lim z_n = lim y_n$, then $lim a_n = lim z_n = lim y_n$.
Assume that $lim a_n$ exists. Since $a_n <= y_n$, $lim a_n = a <= y = lim y_n$.
Assume that $a < y$.
There exists $N_1 in NN$ such that $|a_n_1 - a| < (y - a)/3 => a_n_1 < a + (y-a)/3$ for every $n_1 >= N_1$.
There exists $N_2 in NN$ such that $|y_n_2 - y| < (y - a)/3 => y_n_2 > y - (y-a)/3$ for every $n_2 >= N_2$.
$a_n_1 < a + (y-a)/3 = y - 2*(y-a)/3 < y_n_2 - (y-a)/3$ for $n_1 >= N_1 "and" n_2 >= N_2$.
If $N = max(N_1, N_2)$, $a_n < y_N - (y-a)/3$ for $n >= N$, which contradicts the definition of $y_N$.
Thus, $lim a_n = lim y_n$ and $lim a_n = lim z_n$ can be proven in similar manner.

*Exercise 2.4.8*

(a)
$s_n = 1/2 + ... 1/2^n = 1 - 1/2^n$. $lim s_n = 1 - 0 = 1$.

(b)
$s_n = 1/(1 * 2) + 1/(2 * 3) + ... + 1/(n * (n+1)) = 1 - 1/2 + 1/2 - 1/3 + ... + 1/n - 1/(n+1) = 1 - 1/(n+1)$.
$lim s_n = 1 - 0 = 1$.

(c)
$s_n = log(2/1) + log(3/2) + ... + log((n+1)/n) = log(2) - log(1) + log(3) - log(2) + ... + log(n+1) - log(n) = log(n+1)$.
The series doesn't converge.

*Exercise 2.4.9*

$t_k = b_1 + 2 b_2 + 4 b_4 + 8 b_8 + ... + 2^k b_(2^k)
<= b_1 + 2 b_2 + (2 b_3 + 2 b_4) + (2 b_5 + 2 b_6 + 2 b_7 + 2 b_8) + ... + (2 b_(2^(k-1) + 1) + 2 b_(2^(k-1)+2) + ... + 2 b_(2^k))
= 2 s_(2^k) - b_1$.
Since we assumed $t_k$ is divergent, for any $M in NN$, there exists $t_k > M$.
Thus, $s_n$ is not bounded. In other words, $s_n$ is divergent.

*Exercise 2.4.10*

(a)
$p_m = (2 / 1)(3 / 2) ... ((n+1)/n) = n+1$. Thus, the sequence is divergent.

(b)
$s_n = a_1 + a_2 + ... + a_n < p_n = (1 + a_1)(1 + a_2) ... (1 + a_n) <= 3^(s_n) = 3^(a_1 + a_2 + ... + a_n)$.
If $s_n$ converges, there exists $M in NN$ such that $s_n <= M$.
Then, $p_n <= 3^s_n = 3^M$ as desired.
If $p_n$ converges, there exists $M in NN$ such that $p_n <= M$.
Then, $s_n < p_n = M$ as desired.
