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

value "symbols_clause []"
value "symbols [[]]"

lemma symbols_empty_empty:
  "symbols [[]] = {}" 
  unfolding symbols_def symbols_clause_def
  by simp

lemma symbols_from_symbols_clause:
  "\<forall> symbol \<in> symbols [c]. symbol \<in> symbols_clause c" 
  unfolding symbols_def by simp

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

text \<open> Task 3 Part 4 / 4 \<close>

lemma all_below_single_clause:
  assumes "x \<triangleright> q" and "clause \<in> set q"
  shows "x \<triangleright> [clause]"
  using assms by auto

lemma reduce_clause_fst_ge:
  "fst (reduce_clause x clause) \<ge> x"
proof (induct x clause rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  thm 1
  value ?case
  have "reduce_clause x (l1 # l2 # l3 # l4 # c) = 
    (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
    (x', [[(x, True), l1, l2]] @ cs))"
    by simp
  have "x \<le> fst (reduce_clause x (l1 # l2 # l3 # l4 # c))"
    by (metis (no_types, lifting) "1"
        \<open>reduce_clause x (l1 # l2 # l3 # l4 # c) = (let (x', cs) = reduce_clause (x + 1) ((x, False) # l3 # l4 # c) in (x', [[(x, True), l1, l2]] @ cs))\<close>
        add_leD1 case_prod_unfold split_pairs)
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

lemma all_below_monotone:
  assumes "y \<ge> x" and "x \<triangleright> q"
  shows "y \<triangleright> q"
proof -
  value ?thesis
  have "\<forall> clause \<in> set q. \<forall> (y,_) \<in> set clause.  y < x" 
    using all_below_def assms(2) by presburger
  then have "\<forall> clause \<in> set q. \<forall> (term,_) \<in> set clause.  term < y" 
    using assms(1) by fastforce
  thus ?thesis 
    by simp
qed

lemma reduce_clause_subset:
  assumes "x \<triangleright> q"
  shows "\<forall>clause \<in> set q. \<exists>x'. x \<le> x' \<and> x' \<triangleright> [clause] \<and> 
         set (snd (reduce_clause x' clause)) \<subseteq> set (reduce x q)"
  using assms
proof (induction q arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons c q)
  (* From x \<triangleright> (c # q), we know x \<triangleright> [c] and x \<triangleright> q *)
  have x_above_c: "x \<triangleright> [c]" using Cons.prems by simp
  have x_above_q: "\<forall>clause \<in> set q. \<forall>(y,_) \<in> set clause. y < x" 
    using Cons.prems by simp
  
  (* Unfold reduce_clause *)
  obtain x' cs where reduce_c: "reduce_clause x c = (x', cs)"
    by (metis surj_pair)
  
  (* reduce x (c # q) = cs @ reduce x' q *)
  have reduce_unfold: "reduce x (c # q) = cs @ reduce x' q"
    using reduce_c by (simp add: Let_def)
  
  (* Need to show: for every clause in (c # q), the property holds *)
  show ?case
  proof (intro ballI)
    fix clause
    assume "clause \<in> set (c # q)"
    
    then consider (head) "clause = c" | (tail) "clause \<in> set q" 
      by auto
    
    then show "\<exists>x''. x \<le> x'' \<and> x'' \<triangleright> [clause] \<and> 
               set (snd (reduce_clause x'' clause)) \<subseteq> set (reduce x (c # q))"
    proof cases
      case head
      (* When clause = c, use x' = x *)
      have "set cs \<subseteq> set (reduce x (c # q))"
        using reduce_unfold by auto
      moreover have "snd (reduce_clause x c) = cs"
        using reduce_c by simp
      ultimately show ?thesis
        using head x_above_c by (metis order_refl)
    next
      case tail
      (* When clause \<in> q, we need x' \<triangleright> q to apply IH *)
      (* First, need a lemma that reduce_clause increases x *)
      have "x \<le> x'" 
        by (metis fst_conv reduce_c reduce_clause_fst_ge)
      
      hence "x' \<triangleright> q"
        using x_above_q by fastforce
      
      (* Apply induction hypothesis *)
      then obtain x'' where IH: "x' \<le> x'' \<and> x'' \<triangleright> [clause] \<and> 
                                 set (snd (reduce_clause x'' clause)) \<subseteq> set (reduce x' q)"
        using Cons.IH tail by blast
      
      (* Combine results *)
      have "set (reduce x' q) \<subseteq> set (reduce x (c # q))"
        using reduce_unfold by auto
      
      with IH have "set (snd (reduce_clause x'' clause)) \<subseteq> set (reduce x (c # q))"
        by blast
      
      moreover have "x \<le> x''" using `x \<le> x'` IH by simp
      
      ultimately show ?thesis using IH by blast
    qed
  qed
qed

lemma reduce_clause_symbols_bounded:
  assumes "x \<triangleright> [c]"
  shows "\<forall>clause \<in> set (snd (reduce_clause x c)). \<forall>(s,b) \<in> set clause. s < fst (reduce_clause x c)"
  using assms
proof (induct x c rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  obtain x' cs where rec: "reduce_clause (x+1) ((x, False) # l3 # l4 # c) = (x', cs)"
    by (metis surj_pair)
  have reduce_eq: "reduce_clause x (l1 # l2 # l3 # l4 # c) = (x', [[(x, True), l1, l2]] @ cs)"
    using rec by simp
  
  have bound_rec: "x+1 \<triangleright> [((x, False) # l3 # l4 # c)]"
    using "1.prems" by auto
  
  have IH: "\<forall>clause \<in> set cs. \<forall>(s,b) \<in> set clause. s < x'"
    using "1.hyps"[OF bound_rec] rec by auto
  
  have first_clause: "\<forall>(s,b) \<in> set [(x, True), l1, l2]. s < x'"
  proof -
    have "\<forall>(s,b) \<in> set [(x, True), l1, l2]. s \<le> x"
      using "1.prems" by auto
    moreover have "x < x'"
      using rec reduce_clause_fst_ge by (metis fst_conv less_iff_succ_less_eq)
    ultimately show ?thesis by auto
  qed
  
  show ?case using reduce_eq first_clause IH by auto
next
  case ("2_1" x) then show ?case by simp
next
  case ("2_2" x v) then show ?case by simp  
next
  case ("2_3" x v va) then show ?case by simp
next
  case ("2_4" x v va vb) then show ?case by simp
qed

lemma reduced_clause_symbols_bounded:
  shows "\<forall> symbol \<in> symbols (snd (reduce_clause x clause)).
         symbol \<in> symbols_clause clause \<or> (symbol \<ge> x \<and> symbol < fst (reduce_clause x clause))"
proof -
  show ?thesis
  proof (induct x clause rule: reduce_clause.induct)
    case (1 x l1 l2 l3 l4 c)
    (* unfold the definition of the recursive branch and name the result *)
    obtain x' cs where RC_def:
      "reduce_clause x (l1 # l2 # l3 # l4 # c) = (x', [[(x, True), l1, l2]] @ cs)"
      and REC:
      "reduce_clause (x + 1) ((x, False) # l3 # l4 # c) = (x', cs)"
      by force 

    have cs_eq: "cs = snd (reduce_clause (x + 1) ((x, False) # l3 # l4 # c))"
      using REC by simp

    (* instantiate the IH on the recursive call *)
    have IH_cs:
      "\<forall>s \<in> symbols cs. s \<in> symbols_clause ((x, False) # l3 # l4 # c) \<or> (s \<ge> x + 1 \<and> s < x')"
      using REC cs_eq by (metis "1" fst_conv)

    (* show that every symbol in the front singleton either is x or comes from the big clause *)
    have front_prop:
      "\<forall>s \<in> symbols [[(x, True), l1, l2]]. s \<in> symbols_clause (l1 # l2 # l3 # l4 # c) \<or> s = x"
    proof
      fix s
      assume "s \<in> symbols [[(x, True), l1, l2]]"
      then have "s \<in> symbols_clause [(x, True), l1, l2]"
        using symbols_from_symbols_clause by blast
      (* symbols_clause [(x,True),l1,l2] = {symbol_of_literal (x,True)} \<union> {symbol_of_literal l1, symbol_of_literal l2} *)
      hence "s = x \<or> s \<in> {symbol_of_literal l1, symbol_of_literal l2}"
        by (simp add: symbols_clause_def)
      thus "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c) \<or> s = x"
        using symbols_clause_def by auto
    qed

    (* union/concatenation fact for symbols *)
    have union_eq: "symbols ([[ (x, True), l1, l2 ]] @ cs) = symbols [[(x, True), l1, l2]] \<union> symbols cs"
      by (simp add: symbols_def)

    (* complete the case by splitting on where the symbol comes from *)
    show ?case
    proof
      fix s
      assume "s \<in> symbols (snd (reduce_clause x (l1 # l2 # l3 # l4 # c)))"
      with RC_def have "s \<in> symbols ([[ (x, True), l1, l2 ]] @ cs)"
        by simp
      with union_eq have "s \<in> symbols [[(x, True), l1, l2]] \<or> s \<in> symbols cs"
        by auto
      then show "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c) \<or> (s \<ge> x \<and> s < fst (reduce_clause x (l1 # l2 # l3 # l4 # c)))"
      proof
        assume "s \<in> symbols [[(x, True), l1, l2]]"
        then have "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c) \<or> s = x"
          using front_prop by simp
        thus ?thesis
        proof
          assume "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c)"
          then show ?thesis by simp
        next
          assume "s = x"
          (* in this branch we want to show s \<ge> x \<and> s < x' (where x' = fst (reduce_clause x ...)) *)
          moreover from RC_def have "fst (reduce_clause x (l1 # l2 # l3 # l4 # c)) = x'"
            by simp
          moreover have "x' \<ge> x + 1"
            using REC reduce_clause_fst_ge[of "x + 1" "((x, False) # l3 # l4 # c)"] by simp
          ultimately show ?thesis by (simp add: \<open>s = x\<close>)
        qed
      next
        assume "s \<in> symbols cs"
        then have "s \<in> symbols_clause ((x, False) # l3 # l4 # c) \<or> (s \<ge> x + 1 \<and> s < x')"
          using IH_cs by blast
        thus ?thesis
        proof
          assume "s \<in> symbols_clause ((x, False) # l3 # l4 # c)"
          then have "s = x \<or> s \<in> symbols_clause (l3 # l4 # c)"
            by (simp add: symbols_clause_def)
          hence "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c) \<or> s = x"
            using symbols_clause_def by auto
          thus ?thesis
          proof
            assume "s \<in> symbols_clause (l1 # l2 # l3 # l4 # c)"
            then show ?thesis by simp
          next
            assume "s = x"
            (* use monotonicity again: x' \<ge> x+1 so x < x' *)
            from RC_def have "fst (reduce_clause x (l1 # l2 # l3 # l4 # c)) = x'" by simp
            moreover have "x' \<ge> x + 1"
              using REC reduce_clause_fst_ge[of "x + 1" "((x, False) # l3 # l4 # c)"] by simp
            ultimately show ?thesis using \<open>s = x\<close> by simp
          qed
        next
          (* second disjunct of IH_cs *)
          assume "(s \<ge> x + 1 \<and> s < x')"
          from RC_def have "fst (reduce_clause x (l1 # l2 # l3 # l4 # c)) = x'" by simp
          hence "s \<ge> x \<and> s < fst (reduce_clause x (l1 # l2 # l3 # l4 # c))"
            using \<open>s \<ge> x + 1 \<and> s < x'\<close> by auto
          thus ?thesis by simp
        qed
      qed
    qed
  next
    case ("2_1" x)
    then show ?case by (simp add: symbols_empty_empty)
  next
    case ("2_2" x v)
    then show ?case by (simp add: symbols_from_symbols_clause)
  next
    case ("2_3" x v vb)
    then show ?case by (simp add: symbols_from_symbols_clause)
  next
    case ("2_4" x v vb vd)
    then show ?case by (simp add: symbols_from_symbols_clause)
  qed
qed

lemma all_below_imp_symbols_lt:
  assumes "x \<triangleright> q"
  shows "\<forall> s \<in> symbols q. s < x"
proof
  fix s assume "s \<in> symbols q"
  then obtain c where "c \<in> set q" and "s \<in> symbols_clause c"
    by (auto simp: symbols_def)
  then have "\<forall> s \<in> symbols_clause c. s < x"
  proof (intro ballI)
    fix s' assume "s' \<in> symbols_clause c"
    then obtain y b where "(y,b) \<in> set c" and "s' = y"
      by (auto simp: symbols_clause_def split: prod.splits)
    from assms \<open>c \<in> set q\<close> \<open>(y,b) \<in> set c\<close>
    have "y < x" by auto
    with \<open>s' = y\<close> show "s' < x" by simp
  qed
  with \<open>s \<in> symbols_clause c\<close> show "s < x" by auto
qed

lemma evaluate_clause_cong_on_symbols:
  assumes "\<forall>x \<in> symbols_clause c. \<rho> x = \<rho>' x"
  shows   "evaluate_clause \<rho> c = evaluate_clause \<rho>' c"
proof -
  have "\<forall>l \<in> set c. evaluate_literal \<rho> l = evaluate_literal \<rho>' l"
  proof
    fix l
    assume "l \<in> set c"
    obtain sym pol where l_def: "l = (sym, pol)" by (cases l) auto
    then have "sym \<in> symbols_clause c"
      using \<open>l \<in> set c\<close> 
      unfolding symbols_clause_def symbol_of_literal.simps
      by force
    then have "\<rho> sym = \<rho>' sym"
      using assms by auto
    then show "evaluate_literal \<rho> l = evaluate_literal \<rho>' l"
      using l_def by simp
  qed
  then show ?thesis
    by (auto simp: evaluate_clause_def)
qed

lemma evaluate_cong_on_query_symbols:
  assumes "\<forall>x \<in> symbols q. \<rho> x = \<rho>' x"
  shows   "evaluate q \<rho> = evaluate q \<rho>'"
proof -
  have H: "\<forall>c \<in> set q. evaluate_clause \<rho> c = evaluate_clause \<rho>' c"
  proof
    fix c assume "c \<in> set q"
    have "\<forall>x \<in> symbols_clause c. \<rho> x = \<rho>' x"
      using assms \<open>c \<in> set q\<close> by (auto simp: symbols_def)
    thus "evaluate_clause \<rho> c = evaluate_clause \<rho>' c"
      using evaluate_clause_cong_on_symbols by blast
  qed
  show ?thesis
    unfolding evaluate_def using H by auto
qed

lemma reduced_symbols_subset_clause_or_fresh:
  assumes "x \<triangleright> [c]"
  shows "symbols (snd (reduce_clause x c))
         \<subseteq> symbols_clause c \<union> {s. x \<le> s \<and> s < fst (reduce_clause x c)}"
  using assms
  by (simp add: reduced_clause_symbols_bounded subsetI)

lemma patch_outside_relevant_keeps_eval:
  assumes "x \<triangleright> [c]"
  assumes Eval_v: "evaluate (snd (reduce_clause x c)) v"
  shows "\<forall> other_valuation.
           evaluate (snd (reduce_clause x c))
                    (\<lambda>s. if s \<in> symbols_clause c \<union> {t. x \<le> t \<and> t < fst (reduce_clause x c)}
                         then v s else other_valuation s)"
proof (intro allI)
  fix other_valuation
  let ?Relevant = "symbols_clause c \<union> {t. x \<le> t \<and> t < fst (reduce_clause x c)}"
  let ?patched = "\<lambda>s. if s \<in> ?Relevant then v s else other_valuation s"
  have AgreeOnReduced:
    "\<forall> s \<in> symbols (snd (reduce_clause x c)). ?patched s = v s"
    using reduced_symbols_subset_clause_or_fresh[OF assms(1)] by auto
  have "evaluate (snd (reduce_clause x c)) ?patched
        = evaluate (snd (reduce_clause x c)) v"
    by (rule evaluate_cong_on_query_symbols, use AgreeOnReduced in auto)
  thus "evaluate (snd (reduce_clause x c)) ?patched"
    using Eval_v by simp
qed

lemma sat_clause_implies_reduced_sat:
  assumes "evaluate_clause clause_valuation c" 
  and "x \<triangleright> [c]"
  shows "\<exists> valuation.   
    (\<forall>symbol. (symbol < x \<or> symbol \<ge> fst (reduce_clause x c)) \<longrightarrow> clause_valuation symbol = valuation symbol)
    \<and> evaluate (snd (reduce_clause x c)) valuation"
  sorry

text \<open> If q is satisfiable, and all the symbols in q are below x, 
  then reduce x q is also satisfiable. \<close>

theorem sat_reduce2:
  assumes "satisfiable thm_q" and "thm_x \<triangleright> thm_q"
  shows "satisfiable (reduce thm_x thm_q)"
proof -

  have "\<exists>valuation. evaluate thm_q valuation \<Longrightarrow> thm_x \<triangleright> thm_q \<Longrightarrow>
    \<forall> q_valuation.  evaluate thm_q  q_valuation \<longrightarrow> 
      (\<exists> valuation. evaluate (reduce thm_x thm_q) valuation 
      \<and> (\<forall>symbol. (symbol < thm_x ) \<longrightarrow> q_valuation symbol = valuation symbol))"
  proof (induct thm_q arbitrary: thm_x)
    case Nil
    then show ?case by auto
  next
    case (Cons q qs)
    thm Cons
    term ?case

    (* Expand Cons thm *)
    have "\<exists>a. evaluate (q # qs) a \<and> evaluate qs a" 
      using Cons.prems(1) evaluate_def by auto

    obtain base_valuation where "evaluate (q # qs) base_valuation" 
      using \<open>\<exists>a. evaluate (q # qs) a \<and> evaluate qs a\<close> by blast

    then have "evaluate (q # qs) base_valuation" by simp

    then have "evaluate qs base_valuation" 
      by (simp add: evaluate_def)

    (* Unwrap reduce definition *)
    obtain next_x q_reduced where "(next_x, q_reduced) = reduce_clause thm_x q"
      using prod.collapse by blast

    then have "next_x \<ge> thm_x" 
      by (metis fst_conv reduce_clause_fst_ge)
    then have "next_x  \<triangleright> qs"
      using Cons.prems(2) by fastforce

    then have "reduce thm_x (q # qs) = (let (x',cs) = reduce_clause thm_x q in cs @ reduce x' qs)" by simp
  
    then have "reduce thm_x (q # qs) = (q_reduced @ reduce next_x qs)" 
      by (metis \<open>(next_x, q_reduced) = reduce_clause thm_x q\<close> case_prod_conv)


    (* obtain qs_valuation satisfying q # qs *)
    then have "\<exists>a. evaluate (q # qs) a \<and> evaluate qs a \<and> thm_x \<triangleright> qs" 
      using Cons.prems(2) \<open>\<exists>a. evaluate (q # qs) a \<and> evaluate qs a\<close> by auto

    then have "\<exists>a. evaluate (q # qs) a  \<and> next_x \<triangleright> qs"
      using \<open>next_x \<triangleright> qs\<close> by blast

    then have "\<forall>q_valuation. evaluate qs q_valuation \<longrightarrow> 
      (\<exists>valuation. evaluate (reduce next_x qs) valuation \<and> (\<forall>symbol<next_x. q_valuation symbol = valuation symbol))"
      using Cons.hyps \<open>\<exists>a. evaluate (q # qs) a \<and> next_x \<triangleright> qs\<close> by blast

    then obtain qs_valuation where "evaluate (reduce next_x qs) qs_valuation \<and> (\<forall>symbol<next_x. base_valuation symbol = qs_valuation symbol)"
      using \<open>evaluate qs base_valuation\<close> by blast

    then have "evaluate (q # qs) qs_valuation" 
      by (metis Cons.prems(2) \<open>evaluate (q # qs) base_valuation\<close> \<open>thm_x \<le> next_x\<close> all_below_imp_symbols_lt evaluate_cong_on_query_symbols order.strict_trans2)

    (* obtain q_valuation satisfying q # qs *)
    then have "evaluate_clause base_valuation q" 
      using \<open>evaluate (q # qs) base_valuation\<close> evaluate_def by force
    then have "thm_x  \<triangleright> [q]" 
      using Cons.prems(2) by auto

    then obtain q_valuation where "evaluate q_reduced q_valuation \<and> (\<forall>symbol< thm_x. q_valuation symbol = base_valuation symbol)"
      by (metis \<open>(next_x, q_reduced) = reduce_clause thm_x q\<close> \<open>evaluate_clause base_valuation q\<close> sat_clause_implies_reduced_sat split_pairs)

    then have "\<forall> symbol< thm_x. q_valuation symbol = base_valuation symbol"
      by simp

    then have "\<forall> symbol \<in> symbols (q # qs). symbol < thm_x"
      using Cons.prems(2) all_below_imp_symbols_lt by presburger

    then have "\<forall> symbol \<in> symbols (q # qs). q_valuation symbol = base_valuation symbol" 
      using \<open>\<forall>symbol<thm_x. q_valuation symbol = base_valuation symbol\<close> by blast

    then have "evaluate (q # qs) q_valuation" using evaluate_cong_on_query_symbols 
      using \<open>evaluate (q # qs) base_valuation\<close> by presburger

    (* obtain mixed_valuation satisfying q_valuation and qs_valuation criteria *)
    then have "\<forall>q_valuation. evaluate qs q_valuation \<longrightarrow> 
      (\<exists>valuation. evaluate (reduce next_x qs) valuation \<and> (\<forall>symbol<next_x. q_valuation symbol = valuation symbol))"
      using Cons.hyps \<open>\<exists>a. evaluate (q # qs) a \<and> next_x \<triangleright> qs\<close> by blast

    then obtain mixed_valuation where "evaluate (reduce next_x qs) mixed_valuation \<and> (\<forall>symbol<next_x. q_valuation symbol = mixed_valuation symbol)" 
      using \<open>evaluate (q # qs) q_valuation\<close> evaluate_def by fastforce

    (* Show mixed_evaluation solved thesis *)

    then have "evaluate (q # qs) mixed_valuation" 
      by (metis Cons.prems(2) \<open>evaluate (q # qs) q_valuation\<close> \<open>thm_x \<le> next_x\<close> all_below_imp_symbols_lt evaluate_cong_on_query_symbols order.strict_trans2)

    then have "evaluate (reduce next_x qs) mixed_valuation"
      using \<open>evaluate (reduce next_x qs) mixed_valuation \<and> (\<forall>symbol<next_x. q_valuation symbol = mixed_valuation symbol)\<close> by blast 

    then have "\<forall> symbol< next_x. q_valuation symbol = mixed_valuation symbol"
      using \<open>evaluate (reduce next_x qs) mixed_valuation \<and> (\<forall>symbol<next_x. q_valuation symbol = mixed_valuation symbol)\<close> by blast

     have XBelow_q: "thm_x \<triangleright> [q]"
      using Cons.prems(2) by simp

    have Symbols_head_or_fresh:
      "\<forall> s \<in> symbols q_reduced. s \<in> symbols_clause q \<or> (thm_x \<le> s \<and> s < next_x)"
      using XBelow_q \<open>(next_x, q_reduced) = reduce_clause thm_x q\<close> by (metis fst_eqD reduced_clause_symbols_bounded snd_conv)

    (* Symbols of q are < thm_x, hence also < next_x since next_x \<ge> thm_x *)
    have Symbols_q_lt_x: "\<forall> s \<in> symbols_clause q. s < thm_x"
      using XBelow_q by (metis (no_types, opaque_lifting) Sup_empty Sup_insert all_below_imp_symbols_lt list.map(1,2) list.set(1,2) sup_bot.right_neutral
          symbols_def)

    have "\<forall> symbol \<in> symbols q_reduced. symbol < next_x"
    proof
      fix s assume Hs: "s \<in> symbols q_reduced"
      from Symbols_head_or_fresh[rule_format, OF Hs]
      show "s < next_x"
      proof
        assume "s \<in> symbols_clause q"
        then have "s < thm_x" using Symbols_q_lt_x by auto
        moreover have "thm_x \<le> next_x" using \<open>next_x \<ge> thm_x\<close> by simp
        ultimately show "s < next_x" by (meson less_le_trans)
      next
        assume "thm_x \<le> s \<and> s < next_x"
        then show "s < next_x" by simp
      qed
    qed

    then have "\<forall> symbol \<in> symbols q_reduced. q_valuation symbol = mixed_valuation symbol" 
      using \<open>\<forall>symbol<next_x. q_valuation symbol = mixed_valuation symbol\<close> by blast

    then have "evaluate q_reduced  mixed_valuation" using evaluate_cong_on_query_symbols 
      using \<open>evaluate q_reduced q_valuation \<and> (\<forall>symbol<thm_x. q_valuation symbol = base_valuation symbol)\<close> by presburger

    then have "evaluate q_reduced mixed_valuation" by simp

    then have "evaluate (q_reduced @ reduce next_x qs) mixed_valuation" 
      using \<open>evaluate (reduce next_x qs) mixed_valuation\<close> evaluate_def by auto


    have Agree_lt_x':
      "\<forall>symbol<thm_x. q_valuation symbol = mixed_valuation symbol"
      using \<open>\<forall> symbol< next_x. q_valuation symbol = mixed_valuation symbol\<close> \<open>thm_x \<le> next_x\<close> by auto

    (* Conclude the desired implication for this specific q_valuation *)
    have
      "evaluate (q # qs) q_valuation \<longrightarrow>
         (\<exists> valuation.
             evaluate (reduce thm_x (q # qs)) valuation \<and>
             (\<forall>symbol<thm_x. q_valuation symbol = valuation symbol))"
    proof
      assume Ev_q_qs: "evaluate (q # qs) q_valuation"
      (* We already have evaluate (reduce thm_x (q # qs)) mixed_valuation from earlier *)
      have Ev_reduced_mixed:
        "evaluate (reduce thm_x (q # qs)) mixed_valuation"
        using \<open>reduce thm_x (q # qs) = q_reduced @ reduce next_x qs\<close>
              \<open>evaluate q_reduced mixed_valuation\<close>
              \<open>evaluate (reduce next_x qs) mixed_valuation\<close>
        using \<open>evaluate (q_reduced @ reduce next_x qs) mixed_valuation\<close> by argo
      show "\<exists> valuation.
               evaluate (reduce thm_x (q # qs)) valuation \<and>
               (\<forall>symbol<thm_x. q_valuation symbol = valuation symbol)"
        by (intro exI[of _ mixed_valuation] conjI)
           (use Ev_reduced_mixed Agree_lt_x' in auto)
    qed

    then have " \<forall>q_valuation.
       evaluate (q # qs) q_valuation \<longrightarrow>
           evaluate
            (reduce thm_x (q # qs))
            mixed_valuation \<and>
           (\<forall>symbol<thm_x.
               q_valuation symbol =
               mixed_valuation symbol)" sorry


    then show ?case by auto
  qed
  

  then show ?thesis
    using assms(1,2) satisfiable_def by blast
qed

(*then have "\<exists>valuation. evaluate thm_q valuation \<Longrightarrow> thm_x \<triangleright> thm_q \<Longrightarrow> evaluate (reduce thm_x thm_q) valuation" 
  proof (induct thm_q arbitrary: thm_x valuation)
    case Nil
    then show ?case
      by (simp add: evaluate_def)
  next
    case (Cons q qs)
    thm Cons
    term ?case

    (* Expand Cons thm *)
    have "\<exists>a. evaluate (q # qs) a \<and> evaluate qs a" 
      using Cons.prems(1) evaluate_def by auto

    (* Unwrap reduce definition *)
    obtain next_x q_reduced where "(next_x, q_reduced) = reduce_clause thm_x q"
      using prod.collapse by blast

    (* obtain qs_valuation satisfying q # qs *)
    then have "next_x \<ge> thm_x" 
      by (metis fst_conv reduce_clause_fst_ge)
    then have "next_x  \<triangleright> qs"
      using Cons.prems(2) by fastforce

    then have "\<exists>a. evaluate (q # qs) a \<and> evaluate qs a \<and> thm_x \<triangleright> qs" 
      using Cons.prems(2) \<open>\<exists>a. evaluate (q # qs) a \<and> evaluate qs a\<close> by auto

    then have "\<exists>a. evaluate (q # qs) a  \<and> next_x \<triangleright> qs"
      using \<open>next_x \<triangleright> qs\<close> by blast

    then have "\<exists>a. evaluate (q # qs) a \<and> evaluate (reduce next_x qs) a"
      by (metis Cons.hyps Cons.prems(3) evaluate_def list.set_intros(2))

    then have "reduce thm_x (q # qs) = (let (x',cs) = reduce_clause thm_x q in cs @ reduce x' qs)" by simp

    obtain qs_valuation where "evaluate (q # qs) qs_valuation \<and> evaluate (reduce next_x qs) qs_valuation "
      using \<open>\<exists>a. evaluate (q # qs) a \<and> evaluate (reduce next_x qs) a\<close> by blast

    (* obtain q_valuation satisfying q # qs *)

    obtain q_valuation where "evaluate (q # qs) q_valuation \<and> evaluate q_reduced q_valuation " sorry

    (* obtain valuation satisfying q_valuation and qs_valuation criteria *)

    have "evaluate (q # qs) valuation \<and> evaluate q_reduced valuation \<and> evaluate (reduce next_x qs) x" sorry

    then have "evaluate (reduce thm_x (q # qs)) valuation" sorry

    then show ?case sorry
  qed
*)

theorem sat_reduce2:
  assumes "satisfiable thm_q" and "thm_x \<triangleright> thm_q"
  shows "satisfiable (reduce thm_x thm_q)"
  proof -
    have "\<forall> c \<in> set thm_q. satisfiable [c]" 
      using assms(1) evaluate_def satisfiable_def by auto
  
    then have rewritten_theorem: "\<exists> valuation. thm_x \<triangleright> thm_q \<longrightarrow> evaluate thm_q valuation \<longrightarrow> evaluate (reduce thm_x thm_q) valuation " 
    proof (induction thm_x thm_q rule: reduce.induct)
      case (1 uu)
      thm 1
      then show ?case 
        by (simp add: evaluate_def)
    next
      case (2 x c q)
  
      thm 2
      term ?case
  
      have "satisfiable [c]" 
        by (simp add: "2.prems") 
  
      obtain next_x c_reduced where "(next_x, c_reduced) = reduce_clause x c"
        using prod.collapse by blast
  
      then have "reduce x (c # q) = (let (x',cs) = reduce_clause x c in cs @ reduce x' q)" by simp
      then have "reduce x (c # q) = c_reduced @ reduce next_x q" 
        by (metis \<open>(next_x, c_reduced) = reduce_clause x c\<close> case_prod_conv)
  
      
      then have "x \<triangleright> (c # q)" sorry
  
      (* show that next_x \<ge> x *)
  
      (* Obtain valuation for reduced q that evaluates (c#q) *)
  
      (* Obtain valuation for c that is equal to reduced_q valuation outside of *)
  
      (* Show this evaluates reduce x (c # q) *)
  
      thus ?case sorry
    qed

    then show ?thesis try by (rule HSV_tasks_2025.sat_reduce2)
qed

(*
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
proof -
  obtain q_valuation where "evaluate q q_valuation"
    using assms(1) satisfiable_def by blast

  have "\<forall> c \<in> set q. satisfiable [c]" 
    using \<open>evaluate q q_valuation\<close> evaluate_def satisfiable_def by auto

  have "\<forall> c \<in> set q. evaluate_clause q_valuation c" 
    using \<open>evaluate q q_valuation\<close> evaluate_def by blast

  then have "\<forall> c \<in> set q. \<exists> x'. set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)" 
    using reduce_preserves_clauses by blast

  then have valuation_in_final_reduce_exists_for_each_reduced_clause:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation"
    using \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_clause_subset sat_clause_implies_reduced_sat by blast

  then have valuation_equivalence_below_x':
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> (\<forall> symbol < x'. valuation symbol = q_valuation symbol)" 
    by (metis \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_clause_subset sat_clause_implies_reduced_sat)

  then have reduced_query_x'_ge_x:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x" 
    by (meson \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_clause_subset sat_clause_implies_reduced_sat)

  then have reduced_query_x'_ge_x_with_x'_valuation_equivalence:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x
    \<and> (\<forall> symbol < x'. valuation symbol = q_valuation symbol)" 
    by (metis \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_clause_subset sat_clause_implies_reduced_sat)

  then have valuation_matches_original_for_original_symbols:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x
    \<and> (\<forall> symbol < x. valuation symbol = q_valuation symbol)" 
    by force

  then have valuation_matches_original_for_original_symbols:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x
    \<and> (\<forall> symbol \<in> symbols q. valuation symbol = q_valuation symbol)"
    by (metis all_below_imp_symbols_lt assms(2))

  then have reduced_clause_symbols_from_clause_and_x_range:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> (\<forall> symbol \<in> symbols (snd (reduce_clause x' c)). symbol \<in> symbols_clause c \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c)))" 
    using reduced_clause_symbols_bounded valuation_in_final_reduce_exists_for_each_reduced_clause by presburger

  then have valuation_symbol_ranges:
    "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x
    \<and> (\<forall> symbol \<in> symbols q. valuation symbol = q_valuation symbol)
    \<and> (\<forall> symbol \<in> symbols (snd (reduce_clause x' c)). symbol \<in> symbols_clause c \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c)))" 
    using reduced_clause_symbols_bounded valuation_matches_original_for_original_symbols by presburger

  (* Now we need to show that the valuation doesn't depend on symbols outside symbols q *)
  then have valuation_symbol_outside_range_dosnt_matter:
    "\<forall> c \<in> set q. \<forall> other_valuation. \<exists> x' valuation. 
      set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> x' \<ge> x
    \<and> (\<forall> symbol \<in> symbols (snd (reduce_clause x' c)).
          symbol \<in> symbols_clause c \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c)))
    \<and> (\<forall> symbol. (\<not> (symbol \<in> symbols_clause c
                      \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c)))
               \<longrightarrow> valuation symbol = other_valuation symbol))"
  proof (intro ballI allI)
    fix c assume C: "c \<in> set q"
    from valuation_symbol_ranges C obtain x' v where Props:
      "set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)"
      "evaluate (snd (reduce_clause x' c)) v"
      "x' \<ge> x"
      "\<forall> s \<in> symbols (snd (reduce_clause x' c)).
           s \<in> symbols_clause c \<or> (s \<ge> x' \<and> s < fst (reduce_clause x' c))"
      by blast
    fix other_valuation
    let ?Relevant = "symbols_clause c \<union> {s. s \<ge> x' \<and> s < fst (reduce_clause x' c)}"
    let ?valuation = "\<lambda>s. if s \<in> ?Relevant then v s else other_valuation s"
    have AgreeOnReduced:
      "\<forall> s \<in> symbols (snd (reduce_clause x' c)). ?valuation s = v s"
      using Props(4) by auto
    have EvalEq:
      "evaluate (snd (reduce_clause x' c)) ?valuation
       = evaluate (snd (reduce_clause x' c)) v"
      by (rule evaluate_cong_on_query_symbols, use AgreeOnReduced in auto)
    have EvalPatched: "evaluate (snd (reduce_clause x' c)) ?valuation"
      using Props(2) EvalEq by simp
    show "\<exists> x'' valuation.
            set (snd (reduce_clause x'' c)) \<subseteq> set (reduce x q)
          \<and> evaluate (snd (reduce_clause x'' c)) valuation
          \<and> x'' \<ge> x
          \<and> (\<forall> symbol \<in> symbols (snd (reduce_clause x'' c)).
                symbol \<in> symbols_clause c \<or> (symbol \<ge> x'' \<and> symbol < fst (reduce_clause x'' c)))
          \<and> (\<forall> symbol. \<not> (symbol \<in> symbols_clause c
                           \<or> (symbol \<ge> x'' \<and> symbol < fst (reduce_clause x'' c)))
                 \<longrightarrow> valuation symbol = other_valuation symbol)"
    proof (intro exI[of _ x'] exI[of _ ?valuation] conjI)
      show "set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)" using Props(1).
      show "evaluate (snd (reduce_clause x' c)) ?valuation" using EvalPatched.
      show "x' \<ge> x" using Props(3).
      show "\<forall> symbol \<in> symbols (snd (reduce_clause x' c)).
              symbol \<in> symbols_clause c \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c))"
        using Props(4).
      show "\<forall> symbol. \<not> (symbol \<in> symbols_clause c
                         \<or> (symbol \<ge> x' \<and> symbol < fst (reduce_clause x' c)))
               \<longrightarrow> ?valuation symbol = other_valuation symbol"
        by auto
    qed
  qed  

  (* Now we need to show that the x' ranges are orthogonal *)

  (* Now we need to construct a valuation that is the union of the other valuations *)

  then have "\<exists> valuation. evaluate (reduce x q) valuation" 
  proof (induction x q rule: reduce.induct)
    case (1 uu)
    thm 1
    then show ?case 
      by (simp add: evaluate_def)
  next
    case (2 x c q)
    (* Decompose the head reduction *)
    obtain x' cs where RC: "reduce_clause x c = (x', cs)"
      by (cases "reduce_clause x c") auto


  (* Finally tie it back to the ?thesis *)
  thus ?thesis 
    by (simp add: satisfiable_def)

qed
*)

(*
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
  using assms
proof (induct q arbitrary: x)
  case Nil
  then show ?case by (simp add: satisfiable_def evaluate_def)
next
  case (Cons c q')

  thm Cons
  
  obtain q_valuation where q_sat: "evaluate (c # q') q_valuation"
    using Cons.prems(1) satisfiable_def by blast
  
  have c_sat: "evaluate_clause q_valuation c"
    using q_sat by (simp add: evaluate_def)
  
  have q'_sat: "evaluate q' q_valuation"
    using q_sat by (simp add: evaluate_def)
  
  have x_above_c: "x \<triangleright> [c]"
    using Cons.prems(2) by simp
  
  have x_above_q': "x \<triangleright> q'"
    using Cons.prems(2) by simp
  
  obtain x' cs where reduce_c: "reduce_clause x c = (x', cs)"
    by (metis surj_pair)
  
  obtain c_valuation where c_val_props:
    "(\<forall>symbol. (symbol < x \<or> symbol \<ge> x') \<longrightarrow> q_valuation symbol = c_valuation symbol) \<and>
     evaluate cs c_valuation"
    using sat_clause_implies_reduced_sat[OF c_sat x_above_c] reduce_c
    by (metis fst_conv snd_conv)
  
  have x'_ge_x: "x' \<ge> x"
    using reduce_c reduce_clause_preserves_bound 
    by (metis fst_conv reduce_c reduce_clause_fst_ge)
  
  have x'_above_q': "x' \<triangleright> q'"
    using x'_ge_x x_above_q' all_below_monotone by blast
  
  have "satisfiable q'"
    using q'_sat satisfiable_def by blast

  then obtain q'_valuation where q'_red_sat: "evaluate (reduce x' q') q'_valuation 
    \<and> (\<forall>symbol < x'. q'_valuation symbol = q_valuation symbol)" sorry

  
  define merged where "merged = (\<lambda>s. if s < x then q_valuation s 
                                     else if s < x' then c_valuation s 
                                     else q'_valuation s)"
  
  have cs_symbols_bounded: "\<forall>clause \<in> set cs. \<forall>(s,b) \<in> set clause. s < x'"
    using reduce_clause_symbols_bounded[OF x_above_c] reduce_c by auto
  
  have "evaluate cs merged"
  proof -
    have "\<forall>clause \<in> set cs. evaluate_clause merged clause"
    proof
      fix clause assume "clause \<in> set cs"
      then have "evaluate_clause c_valuation clause"
        using c_val_props by (simp add: evaluate_def)
      then have "\<forall>(s,b) \<in> set clause. merged s = c_valuation s"
        using cs_symbols_bounded \<open>clause \<in> set cs\<close> merged_def c_val_props by force
      then show "evaluate_clause merged clause"
        using \<open>evaluate_clause c_valuation clause\<close> evaluate_clause_def by fastforce
    qed
    thus ?thesis by (simp add: evaluate_def)
  qed
  
  moreover have "evaluate (reduce x' q') merged"
  proof -
    have "\<forall>clause \<in> set (reduce x' q'). evaluate_clause merged clause"
    proof
      fix clause assume clause_in: "clause \<in> set (reduce x' q')"
      hence "evaluate_clause q'_valuation clause"
        using q'_red_sat by (simp add: evaluate_def)
      moreover have "\<forall>(s,b) \<in> set clause. merged s = q'_valuation s"
      proof clarify
        fix sym pol 
        assume sb_in: "(sym, pol) \<in> set clause"

        have "\<forall> c \<in> set q'. \<forall>(symbol, _) \<in> set c. symbol < x" using x_above_q' by simp
        then have "sym \<in> symbols q \<or> sym > x'" sorry

        then have "sym < x \<or> sym \<ge> x'"
          sorry
        
        then show "merged sym = q'_valuation sym"
        proof (cases "sym < x'")
          case True
          term ?thesis
          then have "sym < x"
            using \<open>sym < x \<or> x' \<le> sym\<close> linorder_not_le by blast
          then have "merged sym = q_valuation sym" 
            using merged_def by presburger
          thus ?thesis
            using True q'_red_sat by presburger
        next
          case False
          thus ?thesis
            using merged_def x'_ge_x by force
        qed
      qed
      ultimately show "evaluate_clause merged clause"
        using evaluate_clause_def by fastforce
    qed
    thus ?thesis by (simp add: evaluate_def)
  qed
  
  ultimately have "evaluate (cs @ reduce x' q') merged"
    using evaluate_def by auto
  
  moreover have "reduce x (c # q') = cs @ reduce x' q'"
    using reduce_c by (simp add: Let_def)
  
  ultimately show ?case
    using satisfiable_def by auto
qed
*)
(*

theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
proof -
  obtain q_valuation where "evaluate q q_valuation"
    using assms(1) satisfiable_def by blast

  have "\<forall> c \<in> set q. satisfiable [c]" 
    using \<open>evaluate q q_valuation\<close> evaluate_def satisfiable_def by auto

  have "\<forall> c \<in> set q. evaluate_clause q_valuation c" 
    using \<open>evaluate q q_valuation\<close> evaluate_def by blast

  then have "\<forall> c \<in> set q. \<exists> x'. set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)" 
    using reduce_preserves_clauses by blast

  then have "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation"
    by (meson \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_maintains_bounds sat_clause_implies_reduced_sat)

  then have "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> (\<forall> symbol < x'. valuation symbol = q_valuation symbol)"
    by (metis \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_maintains_bounds sat_clause_implies_reduced_sat)

  then have "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> (\<forall> symbol < x'. valuation symbol = q_valuation symbol)
    \<and> (\<forall> symbol \<ge> fst (reduce_clause x' c) . valuation symbol = q_valuation symbol)" using sat_clause_implies_reduced_sat
    by (metis \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> assms(2) reduce_maintains_bounds)
*)
(*

  then have "\<forall> cb \<in> set q. \<forall>ca \<in> set q. \<exists> xa xb. 
    set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<ge> x
    \<and> set (snd (reduce_clause xb cb)) \<subseteq> set (reduce x q)
    \<and> xb \<ge> x" 
    by (simp add: \<open>\<forall>c\<in>set q. \<exists>x'. set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q) \<and> x \<le> x'\<close>)

  then have "\<forall> cb \<in> set q. \<forall>ca \<in> set q. \<exists> xa xb. 
    set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<ge> x
    \<and> set (snd (reduce_clause xb cb)) \<subseteq> set (reduce x q)
    \<and> xb \<ge> x
    \<and> set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)"
    by blast

  then have "\<forall> cb \<in> set q. \<forall>ca \<in> set q. \<exists> xa xb. 
    set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<ge> x
    \<and> set (snd (reduce_clause xb cb)) \<subseteq> set (reduce x q)
    \<and> xb \<ge> x
    \<and> set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<triangleright> [ca]
    \<and> xb \<triangleright> [cb]"
    by (meson assms(2) reduce_maintains_bounds)

  then have "\<forall> cb \<in> set q. \<forall>ca \<in> set q. \<exists> xa xb valuation_a valuation_b. 
    set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<ge> x
    \<and> set (snd (reduce_clause xb cb)) \<subseteq> set (reduce x q)
    \<and> xb \<ge> x
    \<and> set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<triangleright> [ca]
    \<and> xb \<triangleright> [cb]
    \<and> evaluate (snd (reduce_clause xa ca)) valuation_a
    \<and> evaluate (snd (reduce_clause xb cb)) valuation_b"
    by (meson \<open>\<forall>c\<in>set q. evaluate_clause q_valuation c\<close> sat_clause_implies_reduced_sat)

  then have "\<forall> cb \<in> set q. \<forall>ca \<in> set q. \<exists> xa xb valuation_a valuation_b. 
    set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<ge> x
    \<and> set (snd (reduce_clause xb cb)) \<subseteq> set (reduce x q)
    \<and> xb \<ge> x
    \<and> set (snd (reduce_clause xa ca)) \<subseteq> set (reduce x q)
    \<and> xa \<triangleright> [ca]
    \<and> xb \<triangleright> [cb]
    \<and> evaluate (snd (reduce_clause xa ca)) valuation_a
    \<and> evaluate (snd (reduce_clause xb cb)) valuation_b
    \<and> (\<forall> symbol < xa. valuation_a symbol = q_valuation symbol)" 


  then have "\<forall> c \<in> set q. \<exists> x' valuation. 
    set (snd (reduce_clause x' c)) \<subseteq> set (reduce x q)
    \<and> x \<triangleright> [c]
    \<and> evaluate (snd (reduce_clause x' c)) valuation
    \<and> (\<forall> symbol < x'. valuation symbol = q_valuation symbol)
    \<and> (\<forall> symbol \<ge> fst (reduce_clause x' c) . valuation symbol = q_valuation symbol)"
*)
(*
  then show ?thesis
  proof (induct x q rule: reduce.induct)
    case (1 uu)
    term ?case
    then show ?case by (simp add: evaluate_def satisfiable_def)
  next
    case (2 x' c q)
    thm 2
    term ?case

    have "satisfiable [c]" 
    then have "x' \<ge> x" try 
    then have  "x' \<triangleright> [c]" 

    obtain next_x c_reduced where "(next_x, c_reduced) = reduce_clause x' c"
      using prod.collapse by blast
    obtain q_reduced where "q_reduced = reduce next_x q"
      by simp
    obtain q_eval where "evaluate q_reduced q_eval" 
      using "2" \<open>(next_x, c_reduced) = reduce_clause x' c\<close> \<open>q_reduced = reduce next_x q\<close> satisfiable_def try
    
    

    obtain c_eval_plain where "evaluate c_reduced c_eval_plain" 
    obtain c_eval where "evaluate c_reduced c_eval 
      \<and> (\<forall> symbol \<ge> next_x. c_eval symbol = q_eval symbol) 
      \<and> (\<forall> symbol < x. c_eval symbol = q_eval symbol )"
      

    then show ?case sorry
  qed *)
qed

text \<open> If all symbols in q are below x, then q and its reduction at x are equisatisfiable. \<close>
corollary sat_reduce:
  assumes "x \<triangleright> q"
  shows "satisfiable q = satisfiable (reduce x q)"
  sorry
  using assms sat_reduce1 sat_reduce2 by blast


end