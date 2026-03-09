# Informal Proof of Demand 0CFA Soundness in Lean 4

This document provides an informal walkthrough of the formal proof implemented in `DemandCfa.lean`. The proof establishes the bidirectional equivalence between the dynamic evaluation of a program and the static demand analysis.

## 1. The Core Definitions

### Language and Context
The language is a standard Lambda Calculus (Variables, Abstractions, Applications). The **Context** is represented as a "zipper," allowing us to focus on any sub-expression (the **Cursor**) and know exactly where it sits in the larger program (e.g., inside an argument, inside a function, or inside a lambda body).

### The Four Relations
1.  **Eval ($e \Downarrow v$)**: The standard big-step semantics.
2.  **Trace ($v \Rightarrow e$)**: The analysis relation. It draws a "wire" from a value (lambda) to a call site where that value is used as the function.
3.  **PathRel**: A unified structural relation that connects a variable reference to its binder (and vice versa) by traversing the lexical scope.

---

## 2. The Soundness Theorem

The goal is to prove:
**A call site $(e_0 e_1)$ evaluates to a lambda $(\lambda x.e)$ if and only if there is a demand trace from that lambda back to the call site.**

$$ \text{Eval}(E[(e_0 e_1)], \text{result}) \iff \text{Trace}(\text{result}, E[(e_0 e_1)]) $$

---

## 3. Forward Soundness: Evaluation Preserves Demand
**Theorem: `eval_to_trace`**

> *If $e_1 \Downarrow e_2$, then any demand on $e_1$ is also a demand on $e_2$.*

### Intuition
Think of a "demand" as a request for a value at a call site. If the program evaluates an expression $A$ into a value $B$, then $B$ is the thing that actually arrives at the call site. Therefore, the analysis must show that $B$ flows to that call site.

### Proof Sketch (By Induction on Eval)
1.  **Lambda**: A lambda is already a value ($e \Downarrow e$). The property holds trivially.
2.  **Application**: To evaluate $(e_0 e_1)$, we evaluate $e_0$ to a lambda, then evaluate its body. We show that the demand flows into the function, then through the body, and finally to the result.
3.  **Reference**: A variable $x$ evaluates to the result of an argument passed at some call site. We use the `PathRel` to jump from the variable to the call site and use the inductive hypothesis to show the demand follows.

---

## 4. Backward Soundness: Traces Invert Evaluation
**Theorem: `trace_to_eval_gen`**

> *If there is a trace from a lambda to a call site, then the function at that call site must evaluate to that lambda.*

### The Need for Generalization
We cannot simply prove that the call site evaluates to the *original* lambda. In a real program, a lambda might be passed through three different variables before being called. The "generalized" version proves that for *any* value $v$, if the starting point of the trace evaluates to $v$, then the destination call site's function must also evaluate to $v$.

### Proof Sketch (By Induction on Trace)
1.  **Base Case (`trace_fun`)**: The trace goes directly from a function $e_0$ to its own call site $(e_0 e_1)$.
    *   *Logic*: If $e_0 \Downarrow v$, then the function at the call site is $e_0$, so it obviously evaluates to $v$.
2.  **Inductive Step (`trace_arg`)**: The trace goes through a variable.
    *   *Logic*: The variable $x$ gets its value from an argument at a different call site. By the inductive hypothesis, we "hop" back to that argument. We repeat this until we hit the original lambda.
3.  **Inductive Step (`trace_bod`)**: The trace goes through a function body.
    *   *Logic*: If a value flows out of a function body, it must have been triggered by a call. We use a helper lemma (`trace_target_is_app`) to prove that any intermediate point in a trace through a body must eventually be an application, allowing us to recurse.

---

## 5. Conclusion

The proof is successful because `PathRel` allows us to move seamlessly between definitions and usages, while the mutual induction between `Eval` and `Trace` ensures that the static analysis (Trace) is a perfectly "faithful" map of the dynamic execution (Eval). 

**If the analysis says a lambda can reach a call site, there exists a real execution path that takes it there. If an execution path takes a lambda to a call site, the analysis is guaranteed to find it.**
