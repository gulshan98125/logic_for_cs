datatype term = C of string (* constant symbols *)
			  | V of string (* variable symbols *)
			  | F of string * (term list);
datatype form = PRED of string * (term list) 
			  | NOT of form 
			  | AND of form * form 
			  | OR of form * form 
			  | FORALL of term * form (* term can only be a variable *)
			  | EXISTS of term * form (* term can only be a variable *);

exception Not_wff of (term list * form list);

exception Not_closed of term list;
exception DPLL_unsat of int;

Control.Print.stringDepth := 200;
Control.Print.printDepth  := 100;
Control.Print.printLength := 100;

(* gets length of list *)
fun len(L) = case L of []=> 0| x::xs => 1+len(xs);
fun list_contains(L,element) = case L of
								[] => false
							|   x::xs => if(x=element) then true else list_contains(xs,element);

exception empty;
fun get(L,x) = case L of [] => raise empty| q::qs => if(x=0) then q else get(qs,x-1);
(* fun numberofAppearance(L, element, result) = case L of [] => result
													|  x::xs => if(x=element) then numberofAppearance(xs, element, result+1)
																else numberofAppearance(xs, element ,result); *)


(*WFF CODE STARTS*)

fun get_term_tracker( (term_tracker, pred_tracker) ) = term_tracker;
fun get_pred_tracker( (term_tracker, pred_tracker) )= pred_tracker;

(* given term list as an input, it gets arities of functions in that term list and returns term*arity list *)
fun get_term_arities_from_termlist(t_list,output) = 
		case t_list of [] => output
		| x::xs => 
				  case x of 
				  C(a) => get_term_arities_from_termlist(xs,output)
				| V(a) => get_term_arities_from_termlist(xs,output)
				| F(s, l) => get_term_arities_from_termlist(xs, output@[(F(s, l), len(l))]);

(* term tracker stores term_string*arity value for all the encountered terms *)
(* pred tracker stores pred_string*arity value for all the encountered predicates *)
(* get_arity_lists returns (term_string*arity_list, pred_string*arity_list) *)
fun get_arity_lists(formula, term_tracker, pred_tracker) = 
			case formula of 
		   NOT(x) => get_arity_lists(x, term_tracker, pred_tracker)
		|  AND(x1,x2) => get_arity_lists(x2, get_term_tracker(get_arity_lists(x1, term_tracker, pred_tracker)), get_pred_tracker(get_arity_lists(x1, term_tracker, pred_tracker)))
		|  OR(x1,x2) =>  get_arity_lists(x2, get_term_tracker(get_arity_lists(x1, term_tracker, pred_tracker)), get_pred_tracker(get_arity_lists(x1, term_tracker, pred_tracker)))
		|  FORALL(C(x),form) => raise Not_wff([],[])
		|  EXISTS(C(x),form) => raise Not_wff([],[])
		|  FORALL(F(x,y),form) => raise Not_wff([],[])
		|  EXISTS(F(x,y),form) => raise Not_wff([],[])
		|  FORALL(x,form) => get_arity_lists(form, term_tracker, pred_tracker)
		|  EXISTS(x,form) => get_arity_lists(form, term_tracker, pred_tracker)
		|  PRED(str, t_list) => ( get_term_arities_from_termlist(t_list,[]), pred_tracker@[(PRED(str, t_list), len(t_list))] );


fun contains_different_pred((PRED(str, t_list), value), pred_val_list) = 
		case pred_val_list of [] => false
		| 	 x::xs => case x of (PRED(str2, t_list2), value2) => if(str2=str) 
												  then 
												  	  if(value=value2) then contains_different_pred((PRED(str, t_list), value), xs) else true
												  else
													  contains_different_pred((PRED(str, t_list), value), xs);

fun contains_different_term((F(str, t_list), value), term_val_list) = 
		case term_val_list of [] => false
		| 	 x::xs => case x of (F(str2, t_list2), value2) => if(str2=str) 
												  then 
												  	  if(value=value2) then contains_different_term((F(str, t_list), value), xs) else true
												  else
													  contains_different_term((F(str, t_list), value), xs);
fun pred_list_consistent_temp(pred_list, pred_list_copy) = 
		case pred_list of [] => true
		| x::xs => if (contains_different_pred(x, pred_list_copy)=false) then pred_list_consistent_temp(xs,pred_list_copy) 
					else false;

fun term_list_consistent_temp(term_list, term_list_copy) = 
		case term_list of [] => true
		| x::xs => if (contains_different_term(x, term_list_copy)=false) then term_list_consistent_temp(xs,term_list_copy) 
					else false;



fun pred_list_consistent(predList) = pred_list_consistent_temp(predList, predList);
fun term_list_consistent(termList) = term_list_consistent_temp(termList, termList);

fun get_different_preds(pred_list, pred_list_copy, result) = 
		case pred_list of [] => result
		| x::xs => 	case x of (p,value) =>
					if (contains_different_pred(x, pred_list_copy)=false) then get_different_preds(xs,pred_list_copy, result) 
					else get_different_preds(xs,pred_list_copy, result@[p]);

fun get_different_terms(term_list, term_list_copy, result) = 
		case term_list of [] => result
		| x::xs => case x of (t,value) =>
					if (contains_different_term(x, term_list_copy)=false) then get_different_terms(xs,term_list_copy, result) 
					else get_different_terms(xs,term_list_copy, result@[t]);


fun term_list_to_string(l) = 
			 case l of
			 [] => ""
		|    F(a,b)::[] => "F('" ^ a ^ "," ^ term_list_to_string(b) ^ ")"
		|    C(a)::[] => "C '" ^ a ^ "'"
		|    V(a)::[] => "V '" ^ a ^ "'"
		|    F(a,b)::xs => "F('" ^ a ^ "'," ^ term_list_to_string(b) ^ ")," ^ term_list_to_string(xs)
		|    C(a)::xs => "C '" ^ a ^ "'," ^ term_list_to_string(xs)
		|    V(a)::xs => "V '" ^ a ^ "'," ^ term_list_to_string(xs);
								

fun pred_list_to_string(l) = case l of [] => ""
								|  	 PRED(a,b)::[] => "PRED('" ^ a ^ "',[" ^ term_list_to_string(b) ^ "])"
								|  	 PRED(a,b)::xs => "PRED('" ^ a ^ "',[" ^ term_list_to_string(b) ^ "]), " ^ pred_list_to_string(xs);
								


fun wff(formula) =  let
						val termlist = get_term_tracker(get_arity_lists(formula, [], []));
						val predlist = get_pred_tracker(get_arity_lists(formula, [], []));
					in
						if(term_list_consistent(termlist) andalso pred_list_consistent(predlist)) 
						then 
							true
						else
							let
								val a = get_different_terms(termlist, termlist,[]);
								val b = get_different_preds(predlist, predlist, []);
								val temp= print("terms list = [" ^ term_list_to_string(a) ^ "]\n");
								val temp = print("predicates list = [" ^ pred_list_to_string(b) ^ "]\n");
							in
								raise (Not_wff(a,b))
							end
					end;

(*WFF CODE ENDS*)

fun getFV_from_termlist(t_list, closed_tracker, result) = 
			case t_list of
			[] => result
		|	C(s)::xs => getFV_from_termlist(xs, closed_tracker, result)
		| 	V(s)::xs => if(list_contains(closed_tracker, V(s))) 
						then getFV_from_termlist(xs, closed_tracker, result)
						else if(list_contains(closed_tracker, V(s))=false andalso (list_contains(result, V(s)))=false)
						then getFV_from_termlist(xs, closed_tracker, result@[V(s)])
					    else getFV_from_termlist(xs, closed_tracker, result)
		|   F(s,t)::xs => getFV_from_termlist(xs, closed_tracker, getFV_from_termlist(t, closed_tracker, result));

fun fv_temp(formula, closed_tracker) = 
			case formula of 
			NOT(x) => fv_temp(x, closed_tracker)
		|   FORALL(x,form) => fv_temp(form, closed_tracker@[x])
		| 	EXISTS(x,form) => fv_temp(form, closed_tracker@[x]) 
		|   AND(x1,x2) => fv_temp(x1, closed_tracker) @ fv_temp(x2, closed_tracker)
		|   OR(x1,x2) => fv_temp(x1, closed_tracker) @ fv_temp(x2, closed_tracker)
		|   PRED(str, t_list) => getFV_from_termlist(t_list, closed_tracker, []);

fun filter_fv_temp(l, l_copy, result) = case l of [] => result
										| x::xs => if(list_contains(result,x)=true) then  filter_fv_temp(xs, l_copy, result)
													else filter_fv_temp(xs, l_copy, result@[x]);

fun fv(formula) =  let
					  val a  = fv_temp(formula, []);
					in
					  filter_fv_temp(a,a,[])
					end;

fun closed(formula) = if(fv(formula)=[]) then true 
						else 
							let
								val out = fv(formula);
								val v = print("unclosed variable list = [" ^ term_list_to_string(out) ^"]\n");
							in
								raise Not_closed(out)
							end;

(* --------------------------------------------------------------------------------------------------------------------------------------- *)
(* skolemization starts *)

(*this function replaces a given old variable to a given new variable in the termlist, oldvar and newvar are strings*)
fun replace_var_from_termlist(termlist, old_var, new_var) = 
		  case termlist of 
		  [] => []
		| C(A)::xs => if(A=old_var) then C(new_var)::(replace_var_from_termlist(xs, old_var, new_var)) 
						else C(A)::(replace_var_from_termlist(xs, old_var, new_var))
		| V(A)::xs => if(A=old_var) then V(new_var)::(replace_var_from_termlist(xs, old_var, new_var)) 
						else V(A)::(replace_var_from_termlist(xs, old_var, new_var))
		| F(A, B)::xs => if(A=old_var) then F(new_var, replace_var_from_termlist(B, old_var, new_var))::(replace_var_from_termlist(xs, old_var, new_var)) 
						 else F(A, replace_var_from_termlist(B, old_var, new_var))::(replace_var_from_termlist(xs, old_var, new_var));


fun generate_random_var_a(x) = x^"a";
fun generate_random_var_b(x) = x^"b";

(*this function replaces a given old variable to a given new variable in the formula, oldvar and newvar are strings*)
fun replace_var_from_formula(formula,old_var, new_var)   = 
		  case formula of 
		  PRED(A,T) => if(old_var=A) then PRED(new_var, replace_var_from_termlist(T,A,new_var)) 
						else PRED(A, replace_var_from_termlist(T,old_var,new_var))
		| NOT(A) => NOT(replace_var_from_formula(A,old_var,new_var))
		| AND(A, B) => AND(replace_var_from_formula(A,old_var,new_var), replace_var_from_formula(B,old_var,new_var))
		| OR(A, B) => OR(replace_var_from_formula(A,old_var,new_var), replace_var_from_formula(B,old_var,new_var))
		| FORALL(V(S),form) => if(old_var=S) then replace_var_from_formula(FORALL(V(generate_random_var_a(new_var)), replace_var_from_formula(form,old_var,generate_random_var_a(new_var))), old_var, new_var) 
								else FORALL(V(S), replace_var_from_formula(form,old_var,new_var))
		| EXISTS(V(S),form) => if(old_var=S) then replace_var_from_formula(EXISTS(V(generate_random_var_b(new_var)), replace_var_from_formula(form,old_var,generate_random_var_b(new_var))), old_var, new_var) 
								else EXISTS(V(S), replace_var_from_formula(form,old_var,new_var));

val alphabets = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"];
val globalVar = ref 0;
fun generate_rand_var(global_variable, alphabets_list) = let
															val first_letter_index = (!global_variable) div 676;
															val second_letter_index = ((!global_variable) mod 676) div 26;
															val third_letter_index = (!global_variable) mod 26;
															val increase = global_variable := !global_variable+1;
														in
															get(alphabets_list,first_letter_index) ^ get(alphabets_list,second_letter_index) ^ get(alphabets_list,third_letter_index)

														end;
fun enumerate(x) = if(x=0) then "done" else let
											  val temp = generate_rand_var(globalVar,alphabets);
											in
											  enumerate(x-1)
											end;

fun generate_random_var2(x) = x^"2";
fun generate_random_var3(x) = x^"3";
fun generate_random_var4(x) = x^"4";
fun generate_random_var5(x) = x^"5";


fun rename_bound_var(formula, X) =
			case formula of
		    PRED(S,T) => PRED(S,T)
		|	FORALL(V(S),form) =>  FORALL(V(X),rename_bound_var(replace_var_from_formula(form,S,X), generate_random_var2(X)))
		| 	EXISTS(V(S),form) =>  EXISTS(V(X),rename_bound_var(replace_var_from_formula(form,S,X), generate_random_var3(X)))
		|   NOT(form) => NOT(rename_bound_var(form, X))
		|   AND(form1,form2) => AND(rename_bound_var(form1, X), rename_bound_var(form2, generate_random_var4(X)))
		|   OR(form1, form2) => OR(rename_bound_var(form1, X), rename_bound_var(form2, generate_random_var5(X)));

(* fun rename_bound_var(formula, X) =
			case formula of
		    PRED(S,T) => PRED(S,T)
		|	FORALL(V(S),form) =>  FORALL(V(X),rename_bound_var(replace_var_from_formula(form,S,X), generate_rand_var(globalVar,alphabets)))
		| 	EXISTS(V(S),form) =>  EXISTS(V(X),rename_bound_var(replace_var_from_formula(form,S,X), generate_rand_var(globalVar,alphabets)))
		|   NOT(form) => NOT(rename_bound_var(form, X))
		|   AND(form1,form2) => AND(rename_bound_var(form1, X), rename_bound_var(form2, generate_rand_var(globalVar,alphabets)))
		|   OR(form1, form2) => OR(rename_bound_var(form1, X), rename_bound_var(form2, generate_rand_var(globalVar,alphabets))); *)

fun take_out_quantifiers(formula) = 
			case formula of 
			PRED(S,T) => PRED(S,T)								
		|   FORALL(S,form) => FORALL(S,take_out_quantifiers(form))
		|   EXISTS(S,form) => EXISTS(S, take_out_quantifiers(form))
		|	NOT(FORALL(S,form)) => EXISTS(S,NOT(take_out_quantifiers(form)))
		|   NOT(EXISTS(S,form)) => FORALL(S,NOT(take_out_quantifiers(form)))
		|   OR(EXISTS(S,form1), form2) => EXISTS(S, OR(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   OR(FORALL(S,form1), form2) => FORALL(S, OR(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   OR(form1, EXISTS(S,form2)) => EXISTS(S, OR(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   OR(form1, FORALL(S,form2)) => FORALL(S, OR(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   AND(EXISTS(S,form1), form2) => EXISTS(S, AND(take_out_quantifiers(form1),take_out_quantifiers(form2)))								
		|   AND(FORALL(S,form1), form2) => FORALL(S, AND(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   AND(form1, FORALL(S,form2)) => FORALL(S, AND(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   AND(form1, EXISTS(S,form2)) => EXISTS(S, AND(take_out_quantifiers(form1),take_out_quantifiers(form2)))
		|   NOT(form) => NOT(take_out_quantifiers(form))
		|   OR(form1,form2) => OR(take_out_quantifiers(form1), take_out_quantifiers(form2))
		|   AND(form1,form2) => AND(take_out_quantifiers(form1), take_out_quantifiers(form2));

fun loop(a, integer) = if(integer=0) then a else loop(take_out_quantifiers(a), integer-1);
fun makePrenex(formula) = loop(rename_bound_var(formula,"s"), 1000);

fun nnf (PRED(S,T)) = PRED(S,T)
| nnf (NOT (PRED(S,T))) = NOT (PRED(S,T))
| nnf (NOT (NOT (O))) = nnf (O)
| nnf (AND (O ,Q)) = AND (nnf (O) , nnf (Q))
| nnf (NOT (AND (O, Q))) = nnf (OR (NOT (O), NOT (Q)))
| nnf (OR (O, Q)) = OR (nnf (O) , nnf (Q))
| nnf (NOT (OR (O, Q))) = nnf (AND (NOT (O), NOT (Q)))
| nnf (FORALL(S,form)) = FORALL(S,nnf(form))
| nnf (EXISTS(S,form)) = EXISTS(S,nnf(form))
;

fun distOR (O, AND (Q, R)) = AND (distOR (O, Q), distOR (O ,R))
| distOR (AND (Q, R) , O) = AND (distOR (Q, O), distOR (R, O))
| distOR (O, Q) = OR (O, Q)
;

fun conj_of_disj (AND (O, Q)) = AND (conj_of_disj (O), conj_of_disj (Q))
| conj_of_disj (OR (O, Q)) = distOR (conj_of_disj (O), conj_of_disj (Q))
| conj_of_disj (O) = O
;
fun cnf (O) = conj_of_disj (nnf(O));

fun pre_make_pcnf(formula) = case formula of
						FORALL(S,form) => FORALL(S, cnf(form))
					|   EXISTS(S,form) => EXISTS(S, cnf(form))
					| 	form => cnf(form);
fun make_pcnf(form) = pre_make_pcnf(makePrenex(form));

fun replace_term_from_termlist(termlist, new_term, str) = 
		case termlist of 
		[] => []
		| C(A)::xs => C(A)::(replace_term_from_termlist(xs, new_term, str))
		| V(A)::xs => if(A=str) then new_term::(replace_term_from_termlist(xs, new_term, str)) 
					  else V(A)::(replace_term_from_termlist(xs, new_term, str))
		| F(A, B)::xs => F(A, replace_term_from_termlist(B, new_term, str))::(replace_term_from_termlist(xs, new_term, str));

fun replaceTerm(formula,new_term,str) = 
			case formula of
			PRED(S,T) => PRED(S, replace_term_from_termlist(T,new_term,str))
		|	FORALL(S,form) => FORALL(S,replaceTerm(form,new_term,str))
		|	EXISTS(S,form) => EXISTS(S,replaceTerm(form,new_term,str))
		|	NOT(form) => NOT(replaceTerm(form,new_term,str))
		|	OR(form1,form2) => OR(replaceTerm(form1,new_term,str), replaceTerm(form2,new_term,str))
		|	AND(form1,form2) => AND(replaceTerm(form1,new_term,str), replaceTerm(form2,new_term,str));

fun to_scnf(formula,term_list, String) = 
			case (formula,String) of
		  (EXISTS(V(S),form),str1) => if (term_list=[]) then to_scnf(replaceTerm(form,C(S^"*"), S),term_list, str1)
		  							  else  to_scnf(replaceTerm(form,F(S^"*", term_list), S),term_list, str1)
		| (FORALL(V(S),form),str1) => FORALL(V(S),to_scnf(form,term_list@[V(S)],str1))
		| (PRED(S,T),str1) => PRED(S,replace_term_from_termlist(T,F(S,term_list),str1))
		| (NOT(form),str1) => to_scnf(form,term_list,str1)
		| (OR(form1,form2),str1) => OR(to_scnf(form1,term_list,str1), to_scnf(form2,term_list,str1))
		| (AND(form1,form2),str1) => AND(to_scnf(form1,term_list,str1), to_scnf(form2,term_list,str1));

fun scnf(formula) = to_scnf(make_pcnf(formula),[],"");

(* skolemization ends *)
(* --------------------------------------------------------------------------------------------------------------------------------------- *)