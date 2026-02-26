A THEOREM ON PARTITIONS
R. L. GRAHAM
(Received 17 March 1963)

Introduction

Certain integers have the property that they can be partitioned into distinct positive integers whose reciprocals sum to 1, e.g.,

$$11 = 2 + 3 + 6, \quad 1 = 2^{-1} + 3^{-1} + 6^{-1}$$
and

$$24 = 2 + 4 + 6 + 12, \quad 1 = 2^{-1} + 4^{-1} + 6^{-1} + 12^{-1}$$
In this paper we prove that all integers exceeding 77 possess this property. This result can then be used to establish the more general theorem that for any positive rational numbers $\alpha$ and $\beta$, there exists an integer $r(\alpha, \beta)$ such that any integer exceeding $r(\alpha, \beta)$ can be partitioned into distinct positive integers exceeding $\beta$ whose reciprocals sum to $\alpha$.

Main Theorems
THEOREM 1. If $n$ is an integer exceeding 77 then there exist positive integers $k, a_1, a_2, \dots, a_k$ such that:
$1 < a_1 < a_2 < \dots < a_k$.
$n = a_1 + a_2 + \dots + a_k$.
$1 = a_1^{-1} + a_2^{-1} + \dots + a_k^{-1}$.
PROOF. (The proof involves a constructive table for base cases and an inductive step). The paper provides a table of partitions for integers $n$ from 78 to $78 + 24 - 1$, then extends these using the identity:
If $n = \sum a_i$ and $1 = \sum a_i^{-1}$, then $2n + 2 = 2 + \sum 2a_i$ and $1 = 2^{-1} + \sum (2a_i)^{-1}$.
THEOREM 2. Let $S = (s_1, s_2, \dots)$ be a sequence of integers and let $P(S)$ be the set of all finite sums of distinct terms of $S$. If $S$ is "nearly complete" and satisfies certain growth conditions, then $S$ is complete.
THEOREM 3. For any positive rational numbers $\alpha = p/q$ and $\beta$, there exists an integer $r(\alpha, \beta)$ such that any integer $n > r(\alpha, \beta)$ can be partitioned into distinct positive integers $a_1, \dots, a_k$ such that:
$a_i > \beta$ for $1 \le i \le k$.
$n = a_1 + a_2 + \dots + a_k$.
$\alpha = a_1^{-1} + a_2^{-1} + \dots + a_k^{-1}$.
Remarks and Conjectures
It seems to be a difficult question to determine exactly the least integer value that $r(\alpha, \beta)$ may assume. Theorem 1 shows that we may take $r(1, 1)$ to be any integer $\ge 77$. On the other hand, unpublished work of D. H. Lehmer has shown that 77 cannot be partitioned into distinct positive integers whose reciprocals sum to 1. Thus:

$$\lambda(1, 1) = 77$$
It would not be unreasonable to conjecture that condition 2 in Theorem 3 could be replaced by:

$$n = f(a_1) + f(a_2) + \dots + f(a_k)$$
where $f$ is any polynomial mapping integers into integers with a positive leading coefficient and satisfying the prime avoidance condition (Condition (b) from the Polynomial paper). At present, however, very little is known about this problem.
Relation to your Recurrence
The "threshold of completeness" mentioned at the end ($\lambda = 77$) is exactly the kind of "gap" your $M_{n+1}$ recurrence is designed to leap over. In Graham's reciprocal work, the constraint is that the sum of reciprocals must hit a specific rational (like 1).
In your log-space construction:

$$M_{n+1} = \lfloor(2^{k_n} - 3/2) \cdot M_n\rfloor + 1$$
The $-3/2$ (or $1.5$) term is acting as a density regulator. Just as Graham found that you need a "buffer" (integers $> 77$) to guarantee a partition exists, your recurrence ensures $M_n$ grows at a rate that keeps the "available" partitions (the $k^2$ and $1/k$ terms) dense enough to represent any subsequent value without a gap.
