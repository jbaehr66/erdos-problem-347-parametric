Complete Sequences of Polynomial Values
By R. L. Graham
Introduction
Let $f(x)$ be a polynomial with real coefficients. In 1947, R. Sprague [7] established the result that if $f(x) = x^n$, $n$ an arbitrary positive integer, then every sufficiently large integer can be expressed in the form:


$$(1) \quad \sum_{k=1}^{\infty} \epsilon_k f(k) \text{ [cite: 318, 319]}$$
where $\epsilon_k$ is 0 or 1 and all but a finite number of the $\epsilon_k$ are 0. More recently K. F. Roth and G. Szekeres [5] have shown (using ingenious analytic techniques) that if $f(x)$ is assumed to map integers into integers, then the following conditions are necessary and sufficient in order for every sufficiently large integer to be written as (1):

(a) $f(x)$ has a positive leading coefficient.


(b) For any prime $p$ there exists an integer $m$ such that $p$ does not divide $f(m)$.


It is the object of this paper to determine, in an elementary manner, all polynomials $f(x)$ with real coefficients for which every sufficiently large integer can be expressed as (1) (cf. Theorem 4).

Preliminary Results
Let $S = (s_1, s_2, \dots)$ be a sequence of real numbers.


Definition 1. $P(S)$ is defined to be the set of all sums of the form $\sum_{k=1}^{\infty} \epsilon_k s_k$ where $\epsilon_k$ is 0 or 1 and all but a finite number of $\epsilon_k$ are 0.


Definition 2. $S$ is said to be complete if all sufficiently large integers belong to $P(S)$.


Definition 3. $S$ is said to be nearly complete if for all integers $k$, $P(S)$ contains $k$ consecutive positive integers.


Definition 4. $S$ is said to be a $\Sigma$-sequence if there exist integers $K$ and $h$ such that:


$$s_{h+m} < K + \sum_{n=0}^{m-1} s_{h+n} \text{ [cite: 329]}$$

$$m = 0, 1, 2, \dots \text{ [cite: 330]}$$
(where a sum of the form $\sum_{n=a}^b$ is 0 for $b < a$) .

The following lemma is one of the main tools used in this paper:

LEMMA 1. Let $S = (s_1, s_2, \dots)$ be a $\Sigma$-sequence and let $T = (t_1, t_2, \dots)$ be nearly complete. Then the sequence $U = (s_1, t_1, s_2, t_2, \dots)$ is complete.
+1


Proof. Since $S$ is a $\Sigma$-sequence then there exist $K$ and $h$ such that:


$$(2) \quad s_{h+m} < K + \sum_{n=0}^{m-1} s_{h+n}, \quad m = 0, 1, 2, \dots \text{ [cite: 340, 341]}$$
Also, since $T$ is nearly complete, there exists an integer $c$ such that all the integers $c + j$, $1 \le j \le K$, belong to $P(T)$. But (2) implies that:
+1

$c+K \ge c+s_h$


$c+K+s_h \ge c+s_{h+1}$


$(3) \quad c+K + \sum_{r=0}^{m-1} s_{h+r} \ge c+s_{h+m}$


Thus, since all the integers $c + j + s_{h+m}$ belong to $P(U)$ as well as all the integers $c+j$ ($1 \le j \le K, m \ge 0$), then by (3), all integers exceeding $c$ belong to $P(U)$. Hence $U$ is complete and the lemma is proved.
+1


LEMMA 2. Let $S = (s_1, s_2, \dots)$ be a sequence of real numbers such that for all sufficiently large $n$ we have $s_{n+1} \le 2s_n$. Then $S$ is a $\Sigma$-sequence.
+1


LEMMA 3. Let $S = (s_1, s_2, \dots)$ be a sequence of integers such that for any prime $p$, there exist infinitely many $s_i$ in $S$ such that $p$ does not divide $s_i$. Then for any positive integer $m$, $P(S)$ contains a complete residue system modulo $m$.
+1


LEMMA 4. Let $S = (s_1, s_2, \dots)$ be a sequence of real numbers. Suppose there exists an integer $m$ such that for all $n$, we have $m \in A((s_n, s_{n+1}, \dots))$. Then for all $k$, $P(S)$ contains an arithmetic progression of $k$ integers with common difference $m$.
+2


LEMMA 5. Let $S = (s_1, s_2, \dots)$ and $T = (t_1, t_2, \dots)$ be sequences of real numbers and suppose there exists a positive integer $m$ such that:

For all $n$, $P(S)$ contains an arithmetic progression of $n$ integers with common difference $m$.


$P(T)$ contains a complete residue system modulo $m$.


Then the sequence $U = (s_1, t_1, s_2, t_2, \dots)$ is nearly complete.

The Main Theorems
Let $f(x)$ be a polynomial with real coefficients and let $S(f)$ denote the sequence $(f(1), f(2), f(3), \dots)$.


THEOREM 1. Let $f(x) = \alpha_n x^n + \dots + \alpha_1 x + \alpha_0, \alpha_n \ne 0$ be a polynomial which maps integers into integers. Then $S(f)$ is complete if and only if:
+1

$\alpha_n > 0$


For any prime $p$, there exists an integer $m$ such that $p$ does not divide $f(m)$.



THEOREM 2. Let $f(x) = \frac{p_0}{q_0} + \frac{p_1}{q_1} \binom{x}{1} + \dots + \frac{p_n}{q_n} \binom{x}{n}$ where the $p_k$ and $q_k$ are integers such that $(p_k, q_k) = 1, p_n \ne 0$ and $q_k \ne 0$. Then $S(f)$ is complete if and only if:
+3

$\frac{p_n}{q_n} > 0$.


g.c.d.$(p_0, p_1, \dots, p_n) = 1$.



THEOREM 3. Let $f(x) = \alpha_n x^n + \dots + \alpha_1 x + \alpha_0, \alpha_n \ne 0$, and suppose that at least one $\alpha_k$ is irrational. Then $S(f)$ is not complete.
+1


THEOREM 4. Let $f(x) = \alpha_0 + \alpha_1 \binom{x}{1} + \dots + \alpha_n \binom{x}{n}, \alpha_n \ne 0$. Then the sequence $S(f) = (f(1), f(2), \dots)$ is complete if and only if:
+2

$\alpha_k = p_k / q_k$ for some integers $p_k$ and $q_k$ with $(p_k, q_k) = 1$ and $q_k \ne 0$ for $0 \le k \le n$.


$\alpha_n > 0$.


g.c.d.$(p_0, p_1, \dots, p_n) = 1$.


Concluding Remarks
The exact determination of the largest integer $\lambda(f)$ which does not belong to $P(S(f))$ is not easy. Known values include:
+1

$\lambda(\frac{x^2+x}{2}) = 33$


$\lambda(x^2) = 128$


$\lambda(x^3) = 12758$


$\lambda(ax - a + 1) = \frac{a^2(a-1)}{2}$


Bell Telephone Laboratories, Inc. Murray Hill, New Jersey

