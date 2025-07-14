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
