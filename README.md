# mu-recursive

An Isabelle/HOL project aiming to formalize µ-recursive functions, 
provide a compiler to a simple stack machine, and formally verify
the correctness of the compiler.

The project is inspired by Section 3.3 of *Isabelle/HOL - A Proof Assistant for
Higher-Order Logic* by T. Nipkow, M. Wenzel, and L. C. Paulson.

# Current state

This project is a work in progress.

I have defined a datatype `'a expr` modeling a language of primitive recursive
functions, with variables ranging over an arbitrary type `'a`, together with an
evaluation function `value`.

Most of the current development is devoted to proving termination of `value`.
The proof uses two measures on `'a expr`, called `weight` and `phase`.
`weight` measures the structural size of an expression while assigning
additional weight to constants according to their values. `phase` measures the
recursion depth of an expression.

# AI disclosure

The project originated from a conversation with ChatGPT (OpenAI), with the goal
of gaining experience in applying formal verification to software engineering.
ChatGPT suggested the idea of compiling a simple expression language to a stack
machine, following the general approach of Section 3.3 of *Isabelle/HOL - A
Proof Assistant for Higher-Order Logic* by T. Nipkow, M. Wenzel, and
L. C. Paulson.

I have also used ChatGPT for explanations of Isabelle/HOL and its tools,
debugging assistance, feedback on Isabelle code, and help expressing proof
ideas in Isar syntax. The design and implementation of the language and
evaluation function, as well as the formal proofs, are my own, and I take
responsibility for their correctness.
