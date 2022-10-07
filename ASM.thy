theory ASM
  imports "HOL-IMP.AExp"
begin

type_synonym val = int
type_synonym vname = string
datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"
type_synonym state = "vname \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some(n # stk)" |
"exec1 (LOAD x) s stk = Some(s(x) # stk)" |
"exec1 ADD _ (j # i # stk) = Some((i + j) # stk)" |
"exec1 ADD _ [v] = None" |
"exec1 ADD _ [] = None" 

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = 
  (case (exec1 i s stk) of
    Some res \<Rightarrow> exec is s res |
    None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]" 

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

lemma exec_append: "exec is1 s stk = Some new_stk \<Longrightarrow> exec (is1 @ is2) s stk = exec is2 s new_stk"
  apply(induction is1 arbitrary: stk)
  apply(auto split: option.split)
  done

lemma "exec (comp a) s stk = Some ((aval a s) # stk)"
  apply(induction a arbitrary: stk)
  apply(auto simp add: exec_append)
  done

end