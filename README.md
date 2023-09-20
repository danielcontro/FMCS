# FMCS
Repository for the project of the Formal Methods for Cyber-physical Systems's course of the MSc in Computer Science @ Unipd A.Y. 2022/2023

## Project specification

The project requires to implement a symbolic algorithm for the verification of
the *General Reactivity of rank 1* (**GR(1)**) class of LTL formulas using BDDs
as data structure to represent and manipulate regions.

**GR(1)** formulas are of the form
```math
(\bigwedge_{i \in 1..n} \Box\Diamond f_i\,) \to (\bigwedge_{j \in 1..m} \Box\Diamond g_j\,)
```
where each $f_i$ and $g_j$ is a boolean combination of base formulas with no
temporal operators.
