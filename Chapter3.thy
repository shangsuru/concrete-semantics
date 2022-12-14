theory Chapter3
imports "HOL-IMP.BExp"
        "HOL-IMP.ASM"
begin

text{*
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
*}

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (Plus (N i) (N j)) = False" |
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus a1 a2) = conj (optimal a1) (optimal a2)"


text{*
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
*}

lemma "optimal (asimp_const a)"
  apply(induction a)
  apply(auto split:aexp.split)
  done

text{*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
*}

fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N n) = n" |
"sumN (V x) = 0" |
"sumN (Plus a b) = sumN a + sumN b"

fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N n) = N 0" |
"zeroN (V x) = V x" |
"zeroN (Plus a b) = Plus (zeroN a) (zeroN b)"

text {*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*}

definition sepN :: "aexp \<Rightarrow> aexp" where
"sepN a = Plus (N (sumN a)) (zeroN a)"

(*
lemma aux_1: "aval t s = sumN t + aval (zeroN t) s"   
  apply(induction t arbitrary: s)
  apply(auto)
  done  
    
lemma aux_2: "aval (sepN t) s = sumN t + aval (zeroN t) s"
  apply(induction t arbitrary:s)
  apply(auto simp add:sepN_def)
  done  
*)

lemma aval_sepN: "aval (sepN t) s = aval t s"
  apply(induction t)
  apply(auto simp add:sepN_def)
  done

text {*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*}

definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (sepN a)"

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
  apply(induction t arbitrary:s)
  apply(auto simp add:full_asimp_def sepN_def simp:algebra_simps)
  done

text{*
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*}

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst var a (N n) = N n" |
"subst var a (V x) = (if var=x then a else (V x))" |
"subst var a (Plus b c) = Plus (subst var a b) (subst var a c)" 

text{*
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*}

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
  apply(auto)
  done

text {*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*}
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
  apply(auto)
  done

text{*
\endexercise

\exercise
Take a copy of theory @{short_theory "AExp"} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}



text{*
\endexercise

\exercise
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*}

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Times2 aexp2 aexp2 | Inc vname | Div aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
"aval2 (N2 n) s = (n, s)" |
"aval2 (V2 x) s = (s x, s)" |
"aval2 (Plus2 a b) s = (fst (aval2 a s) + fst (aval2 b s), (\<lambda> x. (snd (aval2 a s) x) + (snd (aval2 b s) x) - (s x)))" |
"aval2 (Times2 a b) s = (fst (aval2 a s) * fst (aval2 b s), (\<lambda> x. (snd (aval2 a s) x) + (snd (aval2 b s) x) - (s x)))" |
"aval2 (Inc x) s = (s x, s(x:= 1 + s x))" |
"aval2 (Div a b) s = (fst (aval2 a s) div fst (aval2 b s), (\<lambda> x. (snd (aval2 a s) x) + (snd (aval2 b s) x) - (s x)))"


text{*
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise*}


fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl a) s = a" |
"lval (Vl x) s = s x" |
"lval (Plusl a b) s = lval a s + lval b s" |
"lval (LET v a b) s = lval b (s(v:= lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl a) = N a" |
"inline (Vl x) = V x" |
"inline (Plusl a b) = Plus (inline a) (inline b)" |
"inline (LET v a b) = subst v (inline a) (inline b)"

lemma "aval (inline e) s = lval e s"
  apply (induction e arbitrary: s rule: inline.induct)
  apply (auto simp: subst_lemma)
  done

text{*
\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*}

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (Less b a)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not (Less a b)) (Not (Less b a)) "

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(auto simp add: Le_def)
  done

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(auto simp add: Eq_def)
  done

text{*
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional: *}

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b" |
"ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
"ifval (Less2 a b) s = (aval a s < aval b s)"

text{* Then define two translation functions *}

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b " |
"b2ifexp (Not a) = If (b2ifexp a) (Bc2 False) (Bc2 True)" |
"b2ifexp (And a b) = If (b2ifexp a) (b2ifexp b) (Bc2 False)" |
"b2ifexp (Less a b) = Less2 a b"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b" |
"if2bexp (If a b c) = (And (Not (And (if2bexp a) (Not (if2bexp b)))) 
                           (Not (And (Not (if2bexp a)) (Not (if2bexp c)))))" |
"if2bexp (Less2 a b) = Less a b"

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
  apply(induction exp)
  apply(auto)
  done

lemma "ifval (b2ifexp exp) s = bval exp s"
  apply(induction exp)
  apply(auto)
  done

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

text {* Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT p) = False" |
"is_nnf (AND p1 p2) = (is_nnf p1 \<and> is_nnf p2)" |
"is_nnf (OR p1 p2) = (is_nnf p1 \<and> is_nnf p2)"

text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x" |
"nnf (AND p1 p2) = AND (nnf p1) (nnf p2)" | 
"nnf (OR p1 p2) = OR (nnf p1) (nnf p2)" |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (NOT (NOT x)) = nnf x" |
"nnf (NOT (AND p1 p2)) = OR (nnf (NOT p1)) (nnf (NOT p2))" |
"nnf (NOT (OR p1 p2)) = AND (nnf (NOT p1)) (nnf (NOT p2))" 

value "nnf (NOT (OR (NOT (AND (VAR ''x'') (VAR ''y''))) (VAR ''z'')))"

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma neg_aux [simp]: "pbval (nnf (NOT b)) s = (\<not> (pbval (nnf b) s))"
  apply(induction b)
  apply(auto)
  done

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
  apply(induction b)
  apply(auto)
  done

lemma is_nnf_nnf: "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
  apply(auto)
  done

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun no_ors :: "pbexp \<Rightarrow> bool" where
"no_ors (OR e1 e2) = False" |
"no_ors (AND e1 e2) = (no_ors e1 \<and> no_ors e2)" |
"no_ors e = True"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR _) = True" |
"is_dnf (NOT b) = is_nnf (NOT b)" |
"is_dnf (AND b1 b2) =  (no_ors b1 \<and> no_ors b2 \<and> is_dnf b1 \<and> is_dnf b2)" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"

value "is_dnf (OR (AND (NOT (VAR ''x'')) (VAR ''y'')) (VAR ''z''))"
value "is_dnf (AND (OR (NOT (VAR ''x'')) (VAR ''y'')) (VAR ''z''))"

text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dist_AND (OR a b) c = OR (dist_AND a c) (dist_AND b c)" |
"dist_AND a (OR b c) = OR (dist_AND a b) (dist_AND a c)" |
"dist_AND a b = AND a b" 

text {* and prove that it behaves as follows: *}

lemma pbval_dist [simp]: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply(auto)
  done

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply(auto)
  done

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT a) = NOT a" |
"dnf_of_nnf (AND a b) = dist_AND (dnf_of_nnf a) (dnf_of_nnf b)" |
"dnf_of_nnf (OR a b) = OR (dnf_of_nnf a) (dnf_of_nnf b)" 

value "dnf_of_nnf (AND 
                       (AND 
                          (VAR ''b'') 
                          (OR 
                            (NOT (VAR ''c'')) 
                            (VAR ''d'')
                          ) 
                       ) 
                       (NOT (VAR ''a'')) 
                  )"

text {* Prove the correctness of your function: *}

lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply(induction b)
  apply(auto)
  done

lemma [simp]: "is_dnf a \<Longrightarrow> is_dnf b \<Longrightarrow> is_dnf (dist_AND a b)"
  apply(induction a b rule: dist_AND.induct)
  apply(auto)
  done

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply(induction b )
  apply(auto)
  done

text{*
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than 2. In our semantics
a term @{term "exec1 ADD s stk"} where @{prop "length stk < 2"}
is simply some unspecified value, not an error or exception --- HOL does not have those concepts.
Modify theory @{short_theory "ASM"}
such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
*}

text{*
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
*}
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text {*
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state: *}

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec1 (LDI i r) s rs = rs(r:= i)" |
"exec1 (LD x r) s rs = rs(r:= s(x))" |
"exec1 (ADD r1 r2) s rs = rs(r1:= (rs r1) + (rs r2))"

text{*
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
*}

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec [] _ rs = rs" |
"exec (i # is) s rs = exec is s (exec1 i s rs)"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r =  [LDI n r]" |
"comp (V x) r = [LD x r]" |
"comp (Plus a1 a2) r = (comp a1 r) @ (comp a2 (r+1)) @ [ADD r (r+1)]"

lemma [simp]: "exec (xs @ ys) s rs = exec ys s (exec xs s rs)"
  apply(induction xs arbitrary: rs)
  apply(auto)
  done

lemma [simp]: "r < q \<Longrightarrow> exec (comp a q) s rs r = rs r"
  apply(induction a arbitrary: rs r q)
  apply(auto)
  done


theorem "exec (comp a r) s rs r = aval a s"
  apply(induction a arbitrary: rs r)
  apply(auto)
  done

text{*
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
*}

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text{*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*}

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec01 (LDI0 x) s rs = rs(0:= x)" |
"exec01 (LD0 v) s rs = rs(0:= (s v))" |
"exec01 (MV0 r) s rs = rs(r:= (rs 0))" |
"exec01 (ADD0 r) s rs = rs(0:=(rs 0) + (rs r))" 

text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec0 [] _ rs = rs" |
"exec0 (x # xs) s rs = exec0 xs s (exec01 x s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) r = [LDI0 n]" |
"comp0 (V x) r = [LD0 x]" |
"comp0 (Plus a b) r = (comp0 a (r+1)) @ [MV0 (r+1)] @ (comp0 b (r+2)) @ [ADD0 (r+1)]"

lemma [simp]: "exec0 (xs @ ys) s rs = exec0 ys s (exec0 xs s rs)"
  apply(induction xs arbitrary: rs)
  apply(auto)
  done

lemma [simp]: "(0 < r) \<and> (r \<le> q) \<Longrightarrow> exec0 (comp0 a q) s rs r = rs r"
  apply(induction a arbitrary: r q rs)
  apply(auto)
  done

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r rs)
  apply(auto)
  done

text{*
\endexercise
*}

end

