theory muRecursive
  imports Main
begin

(*
The goal of this theory is to define a language expr for primitive recursive functions
and a function value that evaluates any term in expr. We will add support for µ-recursion later.
The next step will be to define a compiler from expr to a stack machine with suitable control flow and show the 
correctness of the compiler
*)


(*We start with a fragment of expr that models variables.*)

(* Variables are either free variables or bound variables used during primitive recursion. *)
datatype ('a) variable = FreeVar "'a" | RecVar "nat"

(*This realizes substitution of variables for recursion.*)
fun "sub":: "nat \<Rightarrow> nat \<Rightarrow> (('a)variable \<Rightarrow> nat) \<Rightarrow> (('a)variable \<Rightarrow> nat)" where
  "(sub i j env)(FreeVar y) = (env (FreeVar y))"|
  "(sub i j env)(RecVar  y) = (if y=i then j else (env (RecVar y)))"


(*A language that models primitive recursive functions.*)
datatype ('a) expr = 
    Const "nat"                                           (*Constants*)
  | Var "('a)variable"                                    (*Variables*)
  | Succ "('a)expr"                                       (*Successor function*)
  | Proj "nat"  "('a)expr list"                           (*Projection to a component*)
  | PrimRec "nat" "nat" "('a)expr" "('a)expr"  "('a)expr" (*Primitive recursion; the nats are the variables for recursion*)

(*Not all expr terms are well-formed e.g. (Proj i []).
One is also not allowed to bind the same variable 
multiple times e.g. (PrimRec i j f g h) with i=j.*)



(*A good size function on expr that we will need to show 
termination of the evaluation of an expression.
Constants are weighted by their value so that replacing
Const (Suc r) by Const r during primitive recursion decreases
 the termination measure.*)
fun weight :: "('a)expr \<Rightarrow> nat" where
    "weight (Const v) = (Suc v)"
  | "weight (Var v) = 1"
  | "weight (Succ v) = 1 + (weight v)"
  | "weight (Proj i []) = 1"
  | "weight (Proj i (v#vs)) =  (weight v) + (weight (Proj i vs))"
  | "weight (PrimRec i j rec f g) = 3 + weight(rec) + weight(f) + weight(g)"


(* We wish to show that weight decreases on recursive evaluation of a term.
For Const, Var, and Succ this is immediate. For Proj i vs we use a
diagonal induction. The base case follows from
     weight (Proj 0 (v # vs)) > weight v,
while the induction step uses
     weight (Proj (Suc i) (v # vs)) > weight (Proj i vs).*)

(*the general strategy of diagonal induction*)
lemma diag_induct:
  assumes base: " P ws 0"
    and step: "\<And>v vs i. P (vs@ws) i \<Longrightarrow> P ((v#vs)@ws) (Suc i)"
  shows "P (vs@ws) (length vs)"
  using assms
proof (induction vs)
  case Nil
  then show ?case
    by auto
next
  case (Cons v vs)
  have "P (vs@ws) (length vs)"
    using Cons.IH base step by simp
  then have "P ((v # vs)@ws) (Suc (length vs))"
    by (rule step)
  then show ?case
    by simp
qed


(*This is needed for the base case,*)
lemma weight_positive_proj: "weight(Proj i v) > 0" 
  apply(induction v) 
  by auto

(*The base case follows from the previous lemma.*)
lemma weight_positive: "(weight v) > 0" 
  apply(induction v) 
  using weight_positive_proj by auto

(*This is the induction step.*)
lemma i_indep_var:"weight(Proj (Suc i) (v#vs)) > weight(Proj i vs)" 
  apply(induction vs) 
  using weight_positive by auto

(*Now we can assemble the induction.*)
lemma Proj_size1:
  shows "weight((vs@(w#ws)) ! (length vs)) < weight(Proj (length vs) (vs@(w#ws)))" 
proof (rule diag_induct)
  show "weight((w#ws) ! 0) < weight(Proj 0 (w#ws))" 
    using weight_positive by auto
  show "\<And>v vs i.(weight((vs@(w#ws)) ! i) < weight(Proj i (vs@(w#ws)))) \<Longrightarrow> (weight(((v#vs)@(w#ws)) ! (Suc i)) < weight(Proj (Suc i) ((v#vs)@(w#ws))))"
    using i_indep_var order_less_trans by fastforce
qed

(*The following easy splitting fact is proven by sledgehammer.*)
(*It might be nicer to find a more explicit proof*)
(*The left hand side of the implication ensures that xs has positive length and any non-emptyl list has a splitting as described on the right*)
(*We need this to translate the awkward statement of Proj_size1 into something better.*)
lemma length_splitting: 
  shows "(i < length xs) \<Longrightarrow> (\<exists> w ws vs. (xs=(vs@(w#ws)) \<and> i=(length vs)))" 
  apply (induction i) 
  apply (metis list.size(3) list.exhaust not_gr_zero self_append_conv2)
  by (metis Suc_lessD append_eq_conv_conj id_take_nth_drop length_append_singleton take_hd_drop) 
 
lemma Proj_size2:
  shows "(i < length vs) \<Longrightarrow> weight(vs ! i) < weight(Proj i vs)" using Proj_size1 length_splitting by blast

(*Before we define our value function, we need a second measure, that captures the recursion depth of a term*)
(*This is important for terms of the form (PrimRec i j rec f g).*)
function phase :: "('a)expr \<Rightarrow> nat" where
    "phase (Const v) = 0"
  | "phase (Var v) = 1"
  | "phase (Succ v) = 1 + (phase v)"
  | "phase (Proj i vs) = Suc(if (i < length vs) then (phase (vs ! i)) else 0)"
  | "phase (PrimRec i j rec f g) = 1 + (phase rec) + (phase f) + (phase g)"
  by pat_completeness auto
termination  apply (relation "measures [(\<lambda> (x). weight x)]") 
  using Proj_size2 by auto


lemma phase_zero: "(phase x) = 0 \<Longrightarrow> \<exists>y:: nat . x=Const(y)" 
  by (metis One_nat_def add_Suc expr.exhaust nat.distinct(1) phase.simps(2,3,4,5)) 


(*Mathematically evaluating a primitive recursive function*)
function "value" :: "('a)expr \<Rightarrow> (('a)variable  \<Rightarrow> nat) \<Rightarrow> nat option" where
    "value (Const v) env = Some v"              
  | "value (Var v) env  =  Some (env v)"      
  | "value (Succ v) env = (case (value v env) of 
       None \<Rightarrow> None
     | Some n \<Rightarrow> Some (n + 1))"
  | "value (Proj i vs) env  = (if (i < length vs)  then (value (vs ! i) env) else None)"
  (*We assume (PrimRec i j rec f g) to be well formed, in particular \<not>(i=j).*)
  | "value (PrimRec i j rec f g) env = (case (value rec env) of
        None \<Rightarrow> None
     | Some 0 \<Rightarrow> (value f env)
     | Some (Suc r) \<Rightarrow> (case (value (PrimRec i j (Const r) f g) env) of
          None \<Rightarrow> None 
        | Some x \<Rightarrow> value g (sub i r (sub j x env))))"
  by pat_completeness auto
(*The weight measure always decreases except for terms (PrimRec i j rec f g) where
rec might have smaller weight than (Const (case (value rec env)), think of variables (Var v).
In this case, phase captures the depth of recursion.*)
termination apply (relation "measures [(\<lambda> (x, env). phase x),(\<lambda> (x, env). weight x)]") 
  apply auto
  using not_less_eq phase_zero value.psimps(1) by fastforce
end

