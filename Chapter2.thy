theory Chapter2
imports Main
begin

text{*
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
*}

 "1 + (2::nat)"
 "1 + (2::int)"
 "1 - (2::nat)"
 "1 - (2::int)"
 "[a,b] @ [c,d]"

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

text{*
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
*}

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text{*
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
*}

lemma add_assoc: "add (add m n) p = add m (add n p)"
  apply(induction m)
  apply(auto)
  done

lemma add_0 [simp]: "add y 0 = y"
  apply(induction y)
  apply(auto)
  done

lemma succ_add [simp]: "Suc (add x y) = add x (Suc y)"
  apply(induction x)
  apply(auto)
  done

lemma add_comm: "add m n = add n m"
  apply(induction m)
  apply(auto)
  done

text{* Define a recursive function *}

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc x) = Suc(Suc(double x))"

text{* and prove that *}

lemma double_add: "double m = add m m"
  apply(induction m)
  apply(auto)
  done

text{*
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
*}

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] x = 0" |
"count (y # ys) x  = (if y=x then (add 1 (count ys x)) else (count ys x))"

value "count ([1, 4, 4, 5, 4]::nat list) 4"


text {*
Test your definition of @{term count} on some examples.
Prove the following inequality:
*}

theorem "count xs x \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

text{*
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] e = [e]" |
"snoc (x # xs) e = x # (snoc xs e)"

value "snoc ([1, 2, 3]::nat list) 4"
value "snoc ([]::nat list) 0"

text {*
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
*}

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse ([1,2,3]::nat list)"

text {*
Prove the following theorem. You will need an additional lemma.
*}
lemma reverse_snoc [simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

theorem "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

text{*
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
*}

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc m) = (Suc m) + (sum_upto m)"

value "sum_upto 3"

text {*
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
*}

lemma "sum_upto n = n * (n+1) div 2"
  apply(induction n)
  apply(auto)

text{*
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
*}
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) =(a # (contents l)) @ (contents r)"

value "contents ((Node (Node (Node Tip 1 Tip) 2 Tip) 5 (Node Tip 8 Tip)):: nat tree)"

text{*
Then define a function that sums up all values in a tree of natural numbers
*}

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

value "sum_tree ((Node (Node (Node Tip 1 Tip) 2 Tip) 5 (Node Tip 8 Tip)):: nat tree)"

text{* and prove *}

lemma "sum_tree t = sum_list(contents t)"
  apply(induction t)
  apply(auto)
  done

text{*
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions *}

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)" 

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) =  [a] @ (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

value "pre_order (mirror ((Node (Node (Node Tip 1 Tip) 2 Tip) 5 (Node Tip 8 Tip)):: nat tree))"
value "post_order ((Node (Node (Node Tip 1 Tip) 2 Tip) 5 (Node Tip 8 Tip)):: nat tree)"

text{*
that traverse a tree and collect all stored values in the respective order in
a list. Prove *}

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

text{*
\endexercise

\exercise
Define a recursive function
*}

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse y [] = []" |
"intersperse y [x] = [x]" |
"intersperse y (x # xs) = x # (y # (intersperse y xs))"

value "intersperse 8 [1,2,3,4]:: nat list"

text{*
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
*}

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule:intersperse.induct)
  apply(auto)
  done

text{*
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
*}

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 4 3"

text{*
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
*}

lemma "itadd m n = add m n"
 apply(induction m arbitrary:n)
 apply(auto)
 done

text{*
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
*}

datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"


text {*
Consider the following recursive function:
*}

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

value "nodes (explode 3 (Node Leaf Leaf))"

text {*
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
*}

lemma expl_tree: "nodes(explode n t) = (2^n)*(nodes t + 1) - 1"
  apply(induct n arbitrary:t)
  apply(auto simp:algebra_simps)
  done

text{*

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
*}

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text{*
Define a function @{text eval} that evaluates an expression at some value:
*}

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var v = v" |
"eval (Const e) v = e" |
"eval (Add e f) v = (eval e v) + (eval f v)" |
"eval (Mult e f) v = (eval e v) * (eval f v)"

value "eval (Mult (Const 5) (Add Var (Const 1))) 4"

text{*
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
*}

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] v = 0" |
"evalp (x # xs) v = x + v * (evalp xs v)" 

value "evalp [2,1,3] 2"
value "evalp [0,1] (-1)"

text{*
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
*}

fun add_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeff [] [] = []" |
"add_coeff [] ys = ys" |
"add_coeff xs [] = xs" |
"add_coeff (x # xs) (y # ys) = (x + y) # (add_coeff xs ys)" 

lemma evalp_add[simp]: "evalp (add_coeff xs ys) x = (evalp xs x) + (evalp ys x)"
  apply(induction xs rule:add_coeff.induct)
  apply(auto simp:algebra_simps)
  done

fun mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"mult n [] = []" |
"mult n (x # xs) = (n * x) # (mult n xs)"

lemma evalp_mul[simp]: "evalp (mult n xs) v = n * (evalp xs v)"
  apply(induction xs)
  apply(auto simp:algebra_simps)
  done

fun mult_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeff [] ys = []" |
"mult_coeff (x # xs) ys = add_coeff (mult x ys) (0 # (mult_coeff xs ys))"

lemma evalp_mult[simp]: "evalp (mult_coeff xs ys) x = (evalp xs x) * (evalp ys x)"
  apply(induction xs)
  apply(auto simp:algebra_simps)
  done

fun coeff :: "exp \<Rightarrow> int list" where
"coeff Var = [0,1]" |
"coeff (Const i) = [i]" |
"coeff (Add e f) = add_coeff (coeff e) (coeff f)" |
"coeff (Mult e f) = mult_coeff (coeff e) (coeff f)"


text{*
Prove that @{text coeffs} preserves the value of the expression:
*}

theorem evalp_coeffs: "evalp (coeff e) x = eval e x"
  apply(induction e arbitrary:x)
  apply(auto)
  done

text{*
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
*}

end