theory AExp
  imports Main
begin

(* syntax  *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

(* semantics  *)
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s" |
"aval (Times a1 a2) s = (aval a1 s) * (aval a2 s)"

(* local optimizations *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N(i1 + i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus[simp]: "aval (plus a1 a2) s  = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
  apply(auto)
  done

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N i1) (N i2) = N(i1 * i2)" |
"times (N i) a = (if i=0 then (N 0) else (if i=1 then a else Times (N i) a))" |
"times a (N i) = (if i=0 then (N 0) else (if i=1 then a else Times a (N i)))" |
"times a1 a2 = Times a1 a2"

lemma aval_times[simp]: "aval (times a1 a2) s = aval a1 s * aval a2 s"
  apply(induction a1 a2 rule: times.induct)
  apply(auto)
  done

(* term traversing *)
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)" |
"asimp (Times a1 a2) = times (asimp a1) (asimp a2)"

lemma asimp_correctness[simp]: "aval (asimp a) s = aval a s"
  apply(induction a)
  apply(auto)
  done

end

