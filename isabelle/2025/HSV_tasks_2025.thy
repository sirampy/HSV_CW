theory HSV_tasks_2025 imports Main begin

section \<open> Task 1: Assessing the efficiency of a logic synthesiser. \<close>

text \<open> A datatype representing simple circuits. \<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> An optimisation that removes two successive NOT gates. \<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open> A function that counts the number of gates in a circuit. \<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

text \<open> A function that estimates the computational "cost" of the opt_NOT function. \<close>

fun cost_opt_NOT :: "circuit \<Rightarrow> nat" where
  "cost_opt_NOT (NOT (NOT c)) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (NOT c) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (AND c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT (OR c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT TRUE = 1"
| "cost_opt_NOT FALSE = 1"
| "cost_opt_NOT (INPUT _) = 1"

text \<open> opt_NOT has complexity O(n) where n is the input circuit's area. \<close>

theorem opt_NOT_linear: 
  "\<exists> a b ::nat. cost_opt_NOT c \<le> a * area c + b"
proof (induct c)
  case TRUE
  then show ?case by auto
next
  case FALSE
  then show ?case by auto
next
  case (INPUT _)
  then show ?case by auto
next
  case (NOT c)
  then show ?case using le_add2 by blast
next
  case (AND c c)
  then show ?case using le_add2 by blast
next
  case (OR c c)
  then show ?case using le_add2 by blast
qed

text \<open> Another optimisation, introduced in the 2021 coursework. This
  optimisation exploits identities like `(a | b) & (a | c) = a | (b & c)` 
  in order to remove some gates. \<close>

fun factorise :: "circuit \<Rightarrow> circuit" where
  "factorise (NOT c) = NOT (factorise c)"
| "factorise (AND (OR c1 c2) (OR c3 c4)) = (
    let c1' = factorise c1; c2' = factorise c2; c3' = factorise c3; c4' = factorise c4 in
    if c1' = c3' then OR c1' (AND c2' c4') 
    else if c1' = c4' then OR c1' (AND c2' c3') 
    else if c2' = c3' then OR c2' (AND c1' c4') 
    else if c2' = c4' then OR c2' (AND c1' c3') 
    else AND (OR c1' c2') (OR c3' c4'))"
| "factorise (AND c1 c2) = AND (factorise c1) (factorise c2)"
| "factorise (OR c1 c2) = OR (factorise c1) (factorise c2)"
| "factorise TRUE = TRUE"
| "factorise FALSE = FALSE"
| "factorise (INPUT i) = INPUT i"

text \<open> A function that estimates the computational "cost" of the factorise function. \<close>

fun cost_factorise :: "circuit \<Rightarrow> nat" where
  "cost_factorise (NOT c) = 1 + cost_factorise c"
| "cost_factorise (AND (OR c1 c2) (OR c3 c4)) = 
   4 + cost_factorise c1 + cost_factorise c2 + cost_factorise c3 + cost_factorise c4"
| "cost_factorise (AND c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise (OR c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise TRUE = 1"
| "cost_factorise FALSE = 1"
| "cost_factorise (INPUT i) = 1"

text \<open> factorise has complexity O(n) where n is the input circuit's area. \<close>

theorem factorise_linear: "\<exists> a b ::nat. cost_factorise c \<le> a * area c + b"
proof (induct c) 
  case TRUE
  then show ?case by auto
next
  case FALSE
  then show ?case by auto
next
  case (INPUT _)
  then show ?case by auto
next
  case (NOT c)
  then show ?case using le_add2 by blast
next
  case (AND c c)
  then show ?case using le_add2 by blast
next
  case (OR c c)
  then show ?case using le_add2 by blast
qed

section \<open> Task 2: Palindromic numbers. \<close>

fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [4,2,3]"

text \<open> Rephrasing the definition of sum10 so that elements 
  are peeled off the _end_ of the list, not the start. \<close>

lemma sum10_snoc:
  "sum10 (ds @ [d]) = sum10 ds + 10 ^ (length ds) * d "
proof (induct ds)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

text \<open> If ds is a palindrome of even length, then the number it represents is divisible by 11. \<close>

fun pallindrome :: "nat list \<Rightarrow> nat list" 
  where
"pallindrome ds = ds @ rev ds"

fun sum10_pall :: "nat list \<Rightarrow> nat"
  where
   "sum10_pall [] = 0"
 | "sum10_pall (d # ds) = 10 * sum10_pall ds + d + d * (10 ^ (2 * length (d # ds) - 1))"

value "sum10_pall [1,2]"

lemma sum10_pall_equiv:
  "sum10_pall ds = sum10 (pallindrome ds)" 
proof (induct ds)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  (*split both palindrome terms*)
  have "pallindrome (x # xs) = x # pallindrome xs  @ [x]" by simp
  then have "sum10 (x # (pallindrome xs)) = 10 * sum10(pallindrome xs) + x" by simp
  then have "sum10 (xs @ [x]) = sum10 xs + x  * (10 ^ (length (xs))::nat)"
    by (simp add: sum10_snoc)  
  then have non_pall_case : "sum10 (x # xs @ [x]) = 10 * sum10 xs + x  + x  * (10 ^ (length (x # xs))::nat)"
    by simp
  then have "length (pallindrome xs) = 2 * length xs" 
    by simp
  then have "length (d # pallindrome xs) = 2 * length xs + 1" 
    by simp
  then have non_pall_case : "sum10 (x # (pallindrome xs) @ [x]) = 
    10 * sum10 (pallindrome xs) + x  + x  * (10 ^ (length (x # pallindrome xs))::nat)"
    by (metis Cons_eq_appendI add.commute mult.commute sum10.simps(2) sum10_snoc)
  then have "sum10 (x # (pallindrome xs) @ [x]) = 10 * sum10 (pallindrome xs) 
    + x  + x  * (10 ^ (2 * length (x # xs) - 1)::nat)"
    by simp
  then have "sum10 (x # (pallindrome xs) @ [x]) = 10 * sum10 (pallindrome xs) 
    + x  + x  * (10 ^ (2 * length (x # xs) - 1)::nat)"
    by simp
  then have "sum10 (x # (pallindrome xs) @ [x]) = 
    10 * sum10 (pallindrome xs) + x + x * (10 ^ (2 * length (x # xs) - 1)::nat)"
    by simp
  then have "sum10 (pallindrome (x # xs)) = sum10 (x # pallindrome xs @ [x])" by simp
  then have "sum10 (pallindrome (x # xs)) = 10 * sum10 (pallindrome xs) + x + x * (10 ^ (2 * length (x # xs) - 1)::nat)"
    using \<open>sum10 (x # pallindrome xs @ [x]) = 10 * sum10 (pallindrome xs) + x + x * 10 ^ (2 * length (x # xs) - 1)\<close> by argo
    
  thus ?case
    using local.Cons sum10_pall.simps(2) by presburger 
qed

lemma dvd11_prim:
  "\<forall>n::nat. 11 dvd (x + x * (10 ^ (2 * n + 1)::nat))"
proof
  fix n :: nat
  have "x + x * (10 ^ (2 * n + 1)::nat) = x * (1 + 10 ^ (2 * n + 1)::nat)"
    by simp
  then have base: "11 dvd (1 + 10 ^ (2 * n + 1) ::nat)"
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc prev)
      let ?A = "10 ^ (2 * prev + 1)::nat"
      have old_case: "11 dvd (1 + ?A)" using local.Suc by simp
      moreover have "1 + 10 ^ (2 * Suc prev + 1) 
                   = 1 + 100 * ?A" 
        by (simp add: power_add)
      hence "1 + 100 * ?A = (1 + ?A) + 99 * ?A" by simp
      hence "11 dvd 99 * ?A" by simp  
      hence "11 dvd (1 + ?A) + 99 * ?A" using old_case by fastforce 
      hence "11 dvd (1 + 100 * ?A)" by simp
      thus ?case by simp
  qed
  then have "11 dvd (x * (1 + 10 ^ (2 * n + 1)::nat))" by fastforce
  then show "11 dvd (x + x * (10 ^ (2 * n + 1)::nat))" by simp
qed

lemma sum10_pall_div11:
  "11 dvd sum10_pall ds"
proof (induct ds)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "sum10_pall (x # xs) = 10 * sum10_pall xs + x + x * (10 ^ (2 * length (x # xs) - 1))" 
    by simp
  also have "... = 10 * sum10_pall xs + (x + x * (10 ^ (2 * length xs + 1)))"
    by simp
  finally have expand: "sum10_pall (x # xs) = 10 * sum10_pall xs + (x + x * (10 ^ (2 * length xs + 1)))" .
  
  have "11 dvd (10 * sum10_pall xs)" 
    using Cons.hyps by simp
  moreover have "11 dvd (x + x * (10 ^ (2 * length xs + 1)))"
    using dvd11_prim by simp
  ultimately have "11 dvd (10 * sum10_pall xs + (x + x * (10 ^ (2 * length xs + 1))))"
    by simp
  thus ?case using expand by metis
qed

value "Suc 0"

theorem dvd11:
  assumes "even (length ds)"
  assumes "ds = rev ds"
  shows "11 dvd (sum10 ds)"
proof - 
  let ?half_len = "length ds div 2"
  let ?half_ds = "take ?half_len ds"
  have "pallindrome ?half_ds = ds"
    by (metis Suc_1 add_diff_cancel_left' append_take_drop_id assms(1,2) dvdE mult_1 mult_Suc
        nonzero_mult_div_cancel_left pallindrome.elims rev_take zero_neq_numeral)
  then have "sum10 (pallindrome ?half_ds) = sum10 ds" by simp
  then have "sum10 (pallindrome ?half_ds) = sum10_pall ?half_ds" using sum10_pall_equiv by simp
  then show ?thesis
    by (metis \<open>pallindrome (take (length ds div 2) ds) = ds\<close> sum10_pall_div11)
qed

section \<open> Task 3: 3SAT reduction. \<close>

text \<open> We shall use integers to represent smbols. \<close>
type_synonym symbol = "nat"

text \<open> A literal is either a symbol or a negated symbol. \<close>
type_synonym literal = "symbol * bool"

text \<open> A clause is a disjunction of literals. \<close>
type_synonym clause = "literal list"

text \<open> A SAT query is a conjunction of clauses. \<close>
type_synonym query = "clause list"

text \<open> A valuation is a function from symbols to truth values. \<close>
type_synonym valuation = "symbol \<Rightarrow> bool"

text \<open> Given a valuation, evaluate a literal to its truth value. \<close>
fun evaluate_literal :: "valuation \<Rightarrow> literal \<Rightarrow> bool"
where 
  "evaluate_literal \<rho> (x,b) = (\<rho> x = b)"

text \<open> Given a valuation, evaluate a clause to its truth value. \<close>
definition evaluate_clause :: "valuation \<Rightarrow> clause \<Rightarrow> bool"
where 
  "evaluate_clause \<rho> c \<equiv> \<exists>l \<in> set c. evaluate_literal \<rho> l"

text \<open> Given a valuation, evaluate a query to its truth value. \<close>
definition evaluate :: "query \<Rightarrow> valuation \<Rightarrow> bool"
where 
  "evaluate q \<rho> \<equiv> \<forall>c \<in> set q. evaluate_clause \<rho> c"

text \<open> Checks whether a query is in 3SAT form; i.e. no clause has more than 3 literals. \<close>
definition is_3SAT :: "query \<Rightarrow> bool"
where[simp]:
  "is_3SAT q \<equiv> \<forall>c \<in> set q. length c \<le> 3"

text \<open> Converts a clause into an equivalent sequence of 3SAT clauses. The 
       parameter x is the next symbol number to use whenever a fresh symbol 
       is required. It should be greater than every symbol that appears in c.
       When the function returns, it returns a new value for this parameter
       that may have been increased as a result of adding new symbols; the 
       function guarantees that the new value is still greater than every
       symbol that appears in sequence of reduced clauses. \<close>

fun reduce_clause :: "symbol \<Rightarrow> clause \<Rightarrow> (symbol * query)"
where
  "reduce_clause x (l1 # l2 # l3 # l4 # c) = 
  (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
  (x', [[(x, True), l1, l2]] @ cs))"
| "reduce_clause x c = (x, [c])"

value "reduce_clause 3 [(0, True), (1, False), (2, True)]"
value "reduce_clause 4 [(0, True), (1, False), (2, True), (3, False)]"
value "reduce_clause 5 [(0, True), (1, False), (2, True), (3, False), (4, True)]"

text \<open> Converts a SAT query into a 3SAT query. The parameter x is the next
       symbol number to use whenever a fresh symbol is required. It should
       be greater than every symbol that appears in q. We shall sometimes
       write "reduction of q at x". \<close>
fun reduce :: "symbol \<Rightarrow> query \<Rightarrow> query"
where
  "reduce _ [] = []"
| "reduce x (c # q) = (let (x',cs) = reduce_clause x c in cs @ reduce x' q)"

text \<open> "x \<triangleright> q" holds if all the symbols in q are below x.  \<close>
definition all_below :: "nat \<Rightarrow> query \<Rightarrow> bool" (infix "\<triangleright>" 50)
where [simp]:
  "x \<triangleright> q \<equiv> \<forall>c \<in> set q. \<forall>(y,_) \<in> set c. y<x"

definition "q_example \<equiv> [[(0,True), (1,True), (2,True), (3,False)], [(1,False), (2,True)]]"

value "3 \<triangleright> q_example"
value "4 \<triangleright> q_example"

value "reduce 4 q_example"

text \<open> The constant-False valuation satisfies q_example... \<close>
value "evaluate q_example (\<lambda>_. False)"

text \<open> ...but it doesn't satisfy the reduced version of q_example. \<close>
value "evaluate (reduce 4 q_example) (\<lambda>_. False)"

text \<open> Extract the symbol from a given literal. \<close>
fun symbol_of_literal :: "literal \<Rightarrow> symbol"
where
  "symbol_of_literal (x, _) = x"

text \<open> Extract the set of symbols that appear in a given clause. \<close>
definition symbols_clause :: "clause \<Rightarrow> symbol set"
where 
  "symbols_clause c \<equiv> set (map symbol_of_literal c)"

text \<open> Extract the set of symbols that appear in a given query. \<close>
definition symbols :: "query \<Rightarrow> symbol set"
where
  "symbols q \<equiv> \<Union> (set (map symbols_clause q))"



thm reduce_clause.induct

lemma is_3SAT_reduce_clause:
  "\<forall>c \<in> set (snd (reduce_clause x clause)). length c \<le> 3"
proof (induct x clause rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  value "?case"
  then have "reduce_clause x (l1 # l2 # l3 # l4 # c) = 
  (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
  (x', [[(x, True), l1, l2]] @ cs))" by simp
  then have "length [(x, True), l1, l2] \<le> 3" by simp
  then have "let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
    \<forall>cl \<in> set ([[(x, True), l1, l2]] @ cs) .
    length cl \<le> 3" by (simp add: "1" case_prodI2)
  then show ?case 
    by auto
next
  case ("2_1" x)
  then show ?case by simp
next
  case ("2_2" x v)
  then show ?case by simp
next
  case ("2_3" x v vb)
  then show ?case by simp
next
  case ("2_4" x v vb vd)
  then show ?case by simp
qed

text \<open> The reduce function really does return queries in 3SAT form. \<close>
theorem is_3SAT_reduce:
  "is_3SAT (reduce x q)" 
proof (induct x q rule: reduce.induct)
  case (1 uu)
  then show ?case
    by simp
next
  case (2 x c q)
  value "?case"
  then have "reduce x (c # q) = (let (x',cs) = reduce_clause x c in cs @ reduce x' q)" by simp
  then have "let cs = snd (reduce_clause x c) in 
    (\<forall> clause \<in> set cs.
    length clause \<le> 3) " 
    using is_3SAT_reduce_clause by presburger
  then have term1:"let (x', cs) =  reduce_clause x c in 
    (\<forall> clause \<in> set cs.
    length clause \<le> 3) " 
    by auto
  then have term2: "let (x', cs) =  reduce_clause x c in ( 
    let tail = reduce x' q in (
      \<forall> clause \<in> set tail.
      length clause \<le> 3
     )
  )" using "2" by fastforce 
  then have "let (x', cs) =  reduce_clause x c in ( 
    let tail = reduce x' q in (
      (\<forall> clause \<in> set tail.
      length clause \<le> 3)
      \<and>
      (\<forall> clause \<in> set cs.
      length clause \<le> 3)
     )
  )" using term1 term2 by auto 
  then have term2: "let (x', cs) =  reduce_clause x c in ( 
    let tail = reduce x' q in (
      \<forall> clause \<in> set (cs @ tail).
      length clause \<le> 3
     )
  )" by auto 
  then show ?case by auto 
qed

text \<open> Task 3 Part 2 / 4 \<close>
lemma reduce_clause_length_nondecreasing:
  "length (snd (reduce_clause x clause)) \<ge> 1"
proof (induct x clause rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  value "?case"
  then have literal_form: "
    (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
    reduce_clause x (l1 # l2 # l3 # l4 # c) = 
    (x', [[(x, True), l1, l2]] @ cs))" by auto
  then have literal_equivalence: "length (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) = 
    length (snd (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
    (x', [[(x, True), l1, l2]] @ cs)))" by simp
  then have literal_proof:
    "let (x', cs) = reduce_clause (x + 1) ((x, False) # l3 # l4 # c)
     in length (snd (x', [[(x, True), l1, l2]] @ cs)) \<ge> 1"
    by simp
  then have "length (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) \<ge> 1" 
    using literal_form literal_proof by auto 
  then show ?case by simp 
next
  case ("2_1" x)
  then show ?case by simp
next
  case ("2_2" x v)
  then show ?case by simp
next
  case ("2_3" x v vb)
  then show ?case by simp
next
  case ("2_4" x v vb vd)
  then show ?case by simp
qed

text \<open> The reduce function never decreases the number of clauses in a query. \<close>
lemma reduce_min_extension:
  "\<exists>x'::nat. length (reduce x (q # qs)) \<ge> 1 + length (reduce x' qs)"
proof -
  let ?x' = "fst (reduce_clause x q)"
  have "length (reduce x (q # qs)) =
          length (snd (reduce_clause x q)) + length (reduce ?x' qs)"
    by (simp add: Let_def split_def)
  also have "... \<ge> 1 + length (reduce ?x' qs)"
    using reduce_clause_length_nondecreasing by auto
  finally have "length (reduce x (q # qs)) \<ge> 1 + length (reduce ?x' qs)" .
  thus ?thesis
    by (rule exI[of _ ?x'])
qed

theorem "length q \<le> length (reduce x q)"
proof (induct x q rule: reduce.induct)
  case (1 uu)
  value "?case"
  then show ?case by simp
next
  case (2 x d ds)
  value "?case"
  then have "reduce x (d # ds) = 
    (let (x', cs) = reduce_clause x d in cs @ reduce x' ds)"
    by simp
  then have "reduce x (d # ds) = 
    (snd (reduce_clause x d)) @ reduce (fst (reduce_clause x d)) ds"
    by (simp add: Let_def split_def)
  then have literal_equivalence: "length (reduce x (d # ds)) = 
    length ((snd (reduce_clause x d)) @ reduce (fst (reduce_clause x d)) ds)"
    by simp
  then have length_concat_rule: "\<forall> aa ab ::'a list. length (aa @ ab) = length aa + length ab"
    by simp
  then have "length (reduce x (d # ds)) =
    length (snd (reduce_clause x d)) + 
    length (reduce (fst (reduce_clause x d)) ds)"
    using literal_equivalence length_concat_rule by simp
  then have min_length_rule: "length (reduce x (d # ds)) \<ge>
    1 + 
    length (reduce (fst (reduce_clause x d)) ds)"
    using reduce_clause_length_nondecreasing by auto
  then have "length (reduce (fst (reduce_clause x d)) ds)
    \<ge> length ds"
    by (metis "2" surjective_pairing)
  then have min_length_rule: "length (d # ds) \<le>
    1 + 
    length (reduce (fst (reduce_clause x d)) ds)"
    by simp
  then have min_length_rule: "length (d # ds) \<le>
    length (reduce x (d # ds))"
    using
      \<open>length (reduce x (d # ds)) = length (snd (reduce_clause x d)) + length (reduce (fst (reduce_clause x d)) ds)\<close>
      add_le_mono1 le_trans reduce_clause_length_nondecreasing
    by presburger
  then show ?case by simp   
qed

definition "satisfiable q \<equiv> \<exists>\<rho>. evaluate q \<rho>"

text \<open> Task 3 Part 3 / 4 \<close>

lemma evluate_reduce_clause_implies_evaluate:
  "evaluate (snd (reduce_clause x c)) valuation \<Longrightarrow> evaluate [c] valuation"
proof (induct x c rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  obtain x' cs where red_eq: "(x', cs) = reduce_clause (x+1) ((x,False) # l3 # l4 # c)" 
    using prod.collapse by blast

  have reduce_eq: "reduce_clause x (l1 # l2 # l3 # l4 # c) = (x', [[(x, True), l1, l2]] @ cs)" 
      by (metis case_prod_conv red_eq reduce_clause.simps(1))
  then have "evaluate ([[(x, True), l1, l2]] @ cs) valuation"
    using \<open>evaluate (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) valuation\<close> by auto

  (* Handle first half *)
  then have first_half_evaluation: "evaluate_clause valuation [(x, True), l1, l2]"
    using \<open>evaluate (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) valuation\<close> evaluate_def by auto
  then have "\<exists>l \<in> set[(x, True), l1, l2]. evaluate_literal valuation l "
    using evaluate_clause_def by blast
  then have "evaluate_literal valuation (x, True) \<or> evaluate_literal valuation l1 \<or> evaluate_literal valuation l2"
    by simp
  then have "evaluate [l1 # l2 # []] valuation \<or> evaluate_literal valuation (x, True)"
    using evaluate_clause_def evaluate_def by auto

  thm "1"

  (* Handle second half *)
  then have "cs = snd (reduce_clause (x+1) ((x, False) # l3 # l4 # c))"
    by (metis red_eq snd_eqD)
  then have second_half_satisfies: "evaluate [(x, False) # l3 # l4 # c] valuation"
    using "1.hyps" \<open>evaluate ([[(x, True), l1, l2]] @ cs) valuation\<close> evaluate_def satisfiable_def by auto  
  then have "evaluate_literal valuation (x, False)
    \<or> evaluate_literal valuation l3 \<or> evaluate_literal valuation l4
    \<or> evaluate_clause valuation c"
    by (simp add: evaluate_clause_def evaluate_def)
  then have "evaluate [l3 # l4 # c] valuation \<or> evaluate_literal valuation (x, False)"
    using evaluate_clause_def evaluate_def by auto

  (* Combine halves *)
  then have "(evaluate [l3 # l4 # c] valuation \<or> evaluate_literal valuation (x, False))
    \<and> (evaluate [l1 # l2 # []] valuation \<or> evaluate_literal valuation (x, True))"
    using \<open>evaluate [[l1, l2]] valuation \<or> evaluate_literal valuation (x, True)\<close> by force
  then have "(evaluate [l3 # l4 # c] valuation)
    \<or> (evaluate [l1 # l2 # []] valuation)"
    by auto
  then have one_component_must_satisfy:
    "evaluate_literal valuation l1 \<or> evaluate_literal valuation l2
    \<or> evaluate_literal valuation l3 \<or> evaluate_literal valuation l4
    \<or> evaluate_clause valuation c"
    using
      \<open>evaluate_literal valuation (x, False) \<or> evaluate_literal valuation l3 \<or> evaluate_literal valuation l4 \<or> evaluate_clause valuation c\<close>
      \<open>evaluate_literal valuation (x, True) \<or> evaluate_literal valuation l1 \<or> evaluate_literal valuation l2\<close> by auto
  then have clause_satisfies: "evaluate_clause valuation (l1 # l2 # l3 # l4 # c)"
    using one_component_must_satisfy by (simp add: evaluate_clause_def)
  then have "evaluate [l1 # l2 # l3 # l4 # c] valuation" 
    using clause_satisfies
    by (simp add: evaluate_def)

  then show ?case by simp
next
  case ("2_1" x)
  then show ?case by simp
next
  case ("2_2" x v)
  then show ?case by simp
next
  case ("2_3" x v vb)
  then show ?case by simp
next
    case ("2_4" x v vb vd)
    then show ?case by simp
qed

lemma reduce_preserves_clauses:
  "clause \<in> set q \<Longrightarrow> \<exists>x'. set (snd (reduce_clause x' clause)) \<subseteq> set (reduce x q)"
proof (induct q arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons c q')
  then show ?case
  proof (cases "clause = c")
    case True
    then have "reduce x (c # q') = (let (x', cs) = reduce_clause x c in cs @ reduce x' q')"
      by simp
    then have "set (snd (reduce_clause x c)) \<subseteq> set (reduce x (c # q'))"
      by (auto simp: Let_def split_def)
    then show ?thesis using True by blast
  next
    case False
    then have "clause \<in> set q'" using Cons.prems by simp
    then obtain x'' where "set (snd (reduce_clause x'' clause)) \<subseteq> set (reduce (fst (reduce_clause x c)) q')"
      using Cons.hyps by blast
    moreover have "set (reduce (fst (reduce_clause x c)) q') \<subseteq> set (reduce x (c # q'))"
      by (auto simp: Let_def split_def)
    ultimately show ?thesis by blast
  qed
qed

text \<open> If reduce x q is satisfiable, then so is q. \<close>

theorem sat_reduce1:
  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
proof -
  from assms obtain valuation where eval_reduce: "evaluate (reduce x q) valuation"
    unfolding satisfiable_def by auto

  (* Prove each reduced elem of q evaluates *)
  have "\<forall> clause \<in> set (reduce x q). evaluate [clause] valuation"
    using eval_reduce evaluate_def by auto
  then have "\<forall>clause \<in> (set q). \<exists> x'. set (reduce x' [clause]) \<subseteq> set (reduce x q)"
    by (simp add: case_prod_unfold reduce_preserves_clauses)
    
  then have "\<forall>clause \<in> (set q). \<exists> x'. \<forall> reduced_clause \<in> set (reduce x' [clause]). evaluate [reduced_clause] valuation"
    by (meson \<open>\<forall>clause\<in>set (reduce x q). evaluate [clause] valuation\<close> in_mono)
  then have "\<forall>clause \<in> (set q). \<exists> x'. \<forall> reduced_clause \<in> set (snd (reduce_clause x' clause)). evaluate [reduced_clause] valuation"
    by (simp add: case_prod_unfold)

  (* use lemma to show each elem of q evauates *)
  then have "\<forall>clause \<in> (set q). evaluate [clause] valuation"
    by (meson evaluate_def evluate_reduce_clause_implies_evaluate list.set_intros(1))

  thus ?thesis
    using evaluate_def satisfiable_def by auto
qed

(*
theorem sat_reduce1:
  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
proof -
  from assms obtain valuation where eval_reduce: "evaluate (reduce x q) valuation"
    unfolding satisfiable_def by auto
  have "reduce some_x (d # ds) = (let (x',cs) = reduce_clause some_x d in cs @ reduce x' ds)"
    by simp

  hence ?thesis proof (induct q)
    case Nil
    then have "evaluate [] \<rho>" unfolding evaluate_def by simp
    then show ?case unfolding satisfiable_def by auto
  next
    case (Cons c cs)
    have "reduce x (c # cs) = 
      (let (x', cs') = reduce_clause x c in cs' @ reduce x' cs)"
      by simp
    value "q" 
    then have "satisfiable (reduce x' [c])" 
    then have "evaluate (reduce (c # cs) valuation)" try 
    thus ?case sorry
  qed
qed

  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
proof (induct x q rule: reduce.induct)
  case (1 uu)
  then show ?case 
    by (simp add: evaluate_def satisfiable_def)
next
  case (2 x c q)
  value "?case"
  then have "satisfiable (reduce x (c # q))" try
  then have "reduce x' (d # ds) = 
    (snd (reduce_clause x' d)) @ reduce (fst (reduce_clause x' d)) ds"
    by (simp add: Let_def split_def)
  then have "satisfiable (reduce x' (d # ds)) = 
    satisfiable ((snd (reduce_clause x' d)) @ reduce (fst (reduce_clause x' d)) ds)"
    by simp
  then have "satisfiable (reduce x (c # q)) = 
    satisfiable ((snd (reduce_clause x c)) @ reduce (fst (reduce_clause x c)) q)"
  by (simp add: Let_def split_def)lemma satisfiable_reduce_clause_implies_satisfiable:
  "satisfiable (snd (reduce_clause x c)) \<Longrightarrow> satisfiable [c]"
proof (induct x c rule: reduce_clause.induct)
case (1 x l1 l2 l3 l4 c)
  
  obtain x' cs where red_eq: "(x', cs) = reduce_clause (x+1) ((x,False) # l3 # l4 # c)" 
    using prod.collapse by blast
  obtain valuation where "evaluate (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) valuation "
    using "1.prems" satisfiable_def by blast

  have reduce_eq: "reduce_clause x (l1 # l2 # l3 # l4 # c) = (x', [[(x, True), l1, l2]] @ cs)" 
      by (metis case_prod_conv red_eq reduce_clause.simps(1))
  then have "evaluate ([[(x, True), l1, l2]] @ cs) valuation"
    using \<open>evaluate (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) valuation\<close> by auto


  (* Handle first half *)
  then have first_half_evaluation: "evaluate_clause valuation [(x, True), l1, l2]"
    using \<open>evaluate (snd (reduce_clause x (l1 # l2 # l3 # l4 # c))) valuation\<close> evaluate_def by auto
  then have "\<exists>l \<in> set[(x, True), l1, l2]. evaluate_literal valuation l "
    using evaluate_clause_def by blast
  then have "evaluate_literal valuation (x, True) \<or> evaluate_literal valuation l1 \<or> evaluate_literal valuation l2"
    by simp
  then have "\<exists> valuation2. evaluate_literal valuation2 (x, True) \<or> evaluate_literal valuation2 l1 \<or> evaluate_literal valuation2 l2"
    by blast

  (* Infer first half from second *)
  then have "cs = snd (reduce_clause (x+1) ((x, False) # l3 # l4 # c))"
    by (metis red_eq snd_eqD)
  then have second_half_satisfies: "satisfiable [(x, False) # l3 # l4 # c]"
    using "1.hyps" \<open>evaluate ([[(x, True), l1, l2]] @ cs) valuation\<close> evaluate_def satisfiable_def by auto
  then have second_half_satisfies: "satisfiable [((x, False) # l3 # l4 # c) # [(x, True), l1, l2]]"
    using "1.hyps" \<open>evaluate ([[(x, True), l1, l2]] @ cs) valuation\<close> evaluate_def satisfiable_def by auto

  (* Handle second half *)
  thm "1"

  then have "\<exists> valuation2. evaluate [(x, False) # l3 # l4 # c] valuation2"
    using satisfiable_def by blast
  then have "\<exists> valuation2. evaluate_clause valuation2 ((x, False) # l3 # l4 # c)"
    by (simp add: evaluate_def)
  then have "\<exists> valuation2. evaluate_literal valuation2 (x, False)
    \<or> evaluate_literal valuation2 l3 \<or> evaluate_literal valuation2 l4
    \<or> evaluate_clause valuation2 c"
    by auto

  (* Combine halves *)  
  then have "\<exists> valuation2. 
    evaluate_literal valuation2 (x, True) \<or> evaluate_literal valuation2 l1 \<or> evaluate_literal valuation2 l2
    \<or> evaluate_literal valuation2 (x, False) \<or> evaluate_literal valuation2 l3 \<or> evaluate_literal valuation2 l4
    \<or> evaluate_clause valuation2 c"
    by auto
  then have "\<exists> valuation2. evaluate_literal valuation2 (x, False)
    \<or> evaluate_literal valuation2 l3 \<or> evaluate_literal valuation2 l4
    \<or> evaluate_clause valuation2 c"
    by auto


  then have "\<exists>l \<in> set[(x, False) # l3 # l4 # c]. evaluate_literal valuation l "
    try
  

  (* Get satisifability of both relevant queries*)
  then have "evaluate_literal evaluation (x,True) \<or> evaluate_literal evaluation l1 \<or> evaluate_literal evaluation l2" 
    try
  
  (* Now show original clause is satisfiable *)
  then show ?case
    sorry (* Need to show: satisfiable [[(x, False), l3, l4] @ c] \<Longrightarrow> satisfiable [[l1, l2, l3, l4] @ c] *)
  then show ?case 
next
  case ("2_1" x)
  then show ?case by (simp add: satisfiable_def evaluate_def)
next
  case ("2_2" x v)
  then show ?case by (simp add: satisfiable_def evaluate_def)
next
  case ("2_3" x v vb)
  then show ?case by (simp add: satisfiable_def evaluate_def)
next
  case ("2_4" x v vb vd)
  then show ?case by (simp add: satisfiable_def evaluate_def)
qed

  then have 
    
  then show ?case 
qed
*)

text \<open> If q is satisfiable, and all the symbols in q are below x, 
  then reduce x q is also satisfiable. \<close>
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
  sorry

text \<open> If all symbols in q are below x, then q and its reduction at x are equisatisfiable. \<close>
corollary sat_reduce:
  assumes "x \<triangleright> q"
  shows "satisfiable q = satisfiable (reduce x q)"
  using assms sat_reduce1 sat_reduce2 by blast

end