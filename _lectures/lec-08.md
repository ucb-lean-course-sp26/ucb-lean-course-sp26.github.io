---
layout: lecture
title: "Lecture 8: Reducibility among NP-complete problems"
date: 2026-03-13
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec8.lean
---

* TOC
{:toc}

## Overview & Background

In this lecture, we formalize reductions between NP-complete problems.
Specifically, we illustrate two reductions:
1. `Subset Sum` to `Partition`,
2. `Not-All-Equal-SAT` to `3-Coloring`.

### Brief background on NP-completeness reductions:
A language $L \subseteq \\{0, 1\\}^\*$ is said to be in $\mathsf{NP}$ (non-deterministic polynomial
time) if there exists a (deterministic) polynomial time "verifer" algorithm $V$
and a function $p : \\mathbb{N} \\to \\mathbb{N}$ with $p(n) = O(n^c)$ for some $c$ such that:

* *(Completeness)* If $x \in L$, there exists a "witness" $y$, with $\|y\| \le p(\|x\|)$, such that $V(x, y)$ accepts.
* *(Soundness)* If $x \notin L$, for all $y$ with $\|y\| \le p(\|x\|)$, $V(x, y)$ rejects.

### Reducibility among problems
Given two languages $L_A$, $L_B$ $\subseteq \\{0, 1\\}^\*$,
a **polynomial time reduction** from $L_A$ to $L_B$ is a polynomial-time
computable function $R : \\{0, 1\\}^* \to \\{0, 1\\}^*$ such that for all
$x$, it holds that $x \in L\_A \iff R(x) \in L\_B$.

This equivalence is typically proved in two parts:
* **Completeness**: If $x \in L_A$, then $R(x) \in L_B$.
(A solution to the original problem implies a solution to the new problem).

* **Soundness**: If $R(x) \in L_B$, then $x \in L_A$.
(A solution to the new problem implies a solution to the original problem).

## Subset Sum and Partition

### Subset Sum
The **Subset Sum** problem asks: given a weight function $w : U \to \mathbb{N}$
and a target integer $T$, does there exist a subset $S \subseteq U$ such that
sum of weights of elements in $S$ is exactly $T$?

### Partition
The **Partition** problem asks: given a weight function $w : U \to \mathbb{N}$
and a target integer $T$, does there exist a subset $S \subseteq U$ such that
sum of weights of elements in $S$ is same as the sum of weights of elements in
the complement of $S$?

Partition is a special case of Subset Sum where the target $T$ is exactly half
of the total weight of all elements.

### Reduction from Subset Sum to Partition.

Given a Subset Sum instance, weight $w : U \to \mathbb{N}$ and target $T$, we create
an instance of Partition as follows:
* Augment the universe to have two new elements $U' = U \cup \{\top, \bot\}$.
* The weight function $w' : U' \to \mathbb{N}$ is $w'(x) = w(x)$ for $x \in U$ and
  $w(\top) = 2W - T$ and $w(\bot) = W + T$ where $W$ is the sum of weights of all
  elements in $U$.

**Proof Sketch.**

_Completeness:_

If there exists a subset $S \subseteq U$ such that $\sum_{x \in S} w(x) = T$, then
consider $S' = S \cup \{\top\}$.
The sum of weights in $S'$ is $T + (2W - T) = 2W$.
The total weight of all elements in $U'$ is $W + (2W - T) + (W + T) = 4W$.
Thus, $S'$ partitions $U'$ into two sets of equal weight $2W$.

_Soundness:_

Suppose there is a partition $S' \subseteq U'$ such that $\sum_{x \in S'} w'(x) = 2W$.
Let $S = S' \cap U$. Note that $\sum_{x \in S} w(x) \le W$.
Consider the dummy elements:
- If $\\{\top, \bot\\} \subseteq S'$, sum is $\ge (2W - T) + (W + T) = 3W > 2W$ (contradiction).
- If $\\{\top, \bot\\} \cap S' = \emptyset$, sum is $\le W < 2W$ (contradiction).
- If $\top \in S'$ and $\bot \notin S'$, sum is $(\sum_{x \in S} w(x)) + (2W - T) = 2W$.
  This implies $\sum_{x \in S} w(x) = T$, so $S$ is a solution.
- If $\bot \in S'$ and $\top \notin S'$, sum is $(\sum_{x \in S} w(x)) + (W + T) = 2W$.
  This implies $\sum_{x \in S} w(x) = W - T$. The complement $U \setminus S$ has weight $T$.

## Not-All-Equal-SAT and 3-COLORING

### Not-All-Equal SAT
The **Not-All-Equal Satisfiability (NAE-SAT)** problem asks: Given a set Boolean
variables $x_1, \dots, x_n$, and a set of "clauses" $C_1, \dots, C_m$, where each
clause is a triple of variables, does there exist a Boolean assigment such that
the variables in each clause $C_i$ do not all get the same value.

### 3-COLORING
The **3-COLORING** problem asks: Given a graph, does there exists a `3`-coloring
such that no two vertices that share an edge get the same color.

### Reduction from NAE-SAT to 3-COLORING

Given a NAE-SAT instance over variables $x_1, \dots, x_n$ and clauses
$C_1, \dots, C_m$, we create an instance of 3-COLORING over a graph over the
following vertices:
* A "ground" node $\bot$
* A "variable" node $x_i$
* Three "clause" nodes $c_{j,1}, c_{j,2}, c_{j,3}$.

The edges over this graph are defined as follows:
* The ground vertex $\bot$ is connected to each variable vertex $x_i$.
* For a clause $c_r$ containing variables $x_i, x_j$ and $x_k$, we connect
  * $x_i, x_j, x_k$ to $c_{r, 1}, c_{r, 2}, c_{r, 3}$ respectively.
  * $c_{r, 1}, c_{r, 2}$ and $c_{r,3}$ are all interconnected.

This is visualized below:

```none
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+
```

**Proof Sketch.**

_Completeness:_

Given an assignment for the NAE-SAT instance, we construct a 3-coloring of the
reduction graph as follows:
* The ground node is colored $0$.
* If a variable $x_i$ is assigned `true`, then the corresponding variable node
  is colored $1$; otherwise, it is colored $2$.
* For each clause $C_r = (x_i, x_j, x_k)$, the clause nodes $c_{r,1}$,
  $c_{r,2}$, and $c_{r,3}$ are colored based on the truth assignments of
  $x_i, x_j$, and $x_k$ such that they are all colored differently. This is
  always possible since not all literals in the clause have the same value.

_Soundness:_

Given a 3-coloring of the reduction graph, we construct an assignment for the
NAE-SAT instance as follows:
* If a variable node $x_i$ is colored $1$, then the corresponding variable
  $x_i$ is assigned `true`; otherwise, it is assigned `false`.
Since the clause nodes are connected in a triangle, they must have different
colors. Also, each clause node is connected to the corresponding variable node,
so the variables in each clause cannot all have the same value.
