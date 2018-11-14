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

(* gets length of list *)
fun len(L) = case L of []=> 0| x::xs => 1+len(xs);


(*WFF CODE STARTS*)

fun get_term_tracker( (term_tracker, pred_tracker) ) = term_tracker;
fun get_pred_tracker( (term_tracker, pred_tracker) )= pred_tracker;

(* given term list as an input, it gets arities of functions in that term list and returns term*arity list *)
fun get_term_arities_from_termlist(t_list,output) = case t_list of [] => output
											| x::xs => case x of C(a) => get_term_arities_from_termlist(xs,output)
																| V(a) => get_term_arities_from_termlist(xs,output)
																| F(s, l) => get_term_arities_from_termlist(xs, output@[(F(s, l), len(l))]);

(* term tracker stores term_string*arity value for all the encountered terms *)
(* pred tracker stores pred_string*arity value for all the encountered predicates *)
(* get_arity_lists returns (term_string*arity_list, pred_string*arity_list) *)
fun get_arity_lists(formula, term_tracker, pred_tracker) = case formula of 
								   NOT(x) => get_arity_lists(x, term_tracker, pred_tracker)
								|  AND(x1,x2) => get_arity_lists(x2, get_term_tracker(get_arity_lists(x1, term_tracker, pred_tracker)), get_pred_tracker(get_arity_lists(x1, term_tracker, pred_tracker)))
								|  OR(x1,x2) =>  get_arity_lists(x2, get_term_tracker(get_arity_lists(x1, term_tracker, pred_tracker)), get_pred_tracker(get_arity_lists(x1, term_tracker, pred_tracker)))
								|  FORALL(x,form) => get_arity_lists(form, term_tracker, pred_tracker)
								|  EXISTS(x,form) => get_arity_lists(form, term_tracker, pred_tracker)
								|  PRED(str, t_list) => ( get_term_arities_from_termlist(t_list,[]), pred_tracker@[(PRED(str, t_list), len(t_list))] );


fun contains_different_pred((PRED(str, t_list), value), pred_val_list) = case pred_val_list of [] => false
																		| 	 x::xs => case x of (PRED(str2, t_list2), value2) => if(str2=str) 
																												  then 
																												  	  if(value=value2) then contains_different_pred((PRED(str, t_list), value), xs) else true
																												  else
																													  contains_different_pred((PRED(str, t_list), value), xs);

fun contains_different_term((F(str, t_list), value), term_val_list) = case term_val_list of [] => false
																		| 	 x::xs => case x of (F(str2, t_list2), value2) => if(str2=str) 
																												  then 
																												  	  if(value=value2) then contains_different_term((F(str, t_list), value), xs) else true
																												  else
																													  contains_different_term((F(str, t_list), value), xs);
fun pred_list_consistent_temp(pred_list, pred_list_copy) = case pred_list of [] => true
														| x::xs => if (contains_different_pred(x, pred_list_copy)=false) then pred_list_consistent_temp(xs,pred_list_copy) else false;

fun term_list_consistent_temp(term_list, term_list_copy) = case term_list of [] => true
														| x::xs => if (contains_different_term(x, term_list_copy)=false) then term_list_consistent_temp(xs,term_list_copy) else false;



(* fun string_list_consistent_temp(string_list, string_list_copy) = case string_list of [] => true
														| x::xs => if (contains_different(x, string_list_copy)=false) then string_list_consistent_temp(xs,string_list_copy) else false;
 *)

fun pred_list_consistent(predList) = pred_list_consistent_temp(predList, predList);
fun term_list_consistent(termList) = term_list_consistent_temp(termList, termList);

(* fun string_list_consistent(stringList) = string_list_consistent_temp(stringList, stringList); *)
fun get_different_preds(pred_list, pred_list_copy, result) = case pred_list of [] => result
														| x::xs => 	case x of (p,value) =>
																	if (contains_different_pred(x, pred_list_copy)=false) then get_different_preds(xs,pred_list_copy, result) else get_different_preds(xs,pred_list_copy, result@[p]);

fun get_different_terms(term_list, term_list_copy, result) = case term_list of [] => result
														| x::xs => case x of (t,value) =>
																	if (contains_different_term(x, term_list_copy)=false) then get_different_terms(xs,term_list_copy, result) else get_different_terms(xs,term_list_copy, result@[t]);

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
							in
								raise (Not_wff(a,b))
							end
					end;

fun wff_error(formula) = let
							val termlist = get_term_tracker(get_arity_lists(formula, [], []));
							val predlist = get_pred_tracker(get_arity_lists(formula, [], []));
						in
							if(term_list_consistent(termlist) andalso pred_list_consistent(predlist)) 
							then 
								([],[])
							else
								let
									val a = get_different_terms(termlist, termlist,[]);
									val b = get_different_preds(predlist, predlist, []);
								in
									(b,a)
								end
						end;

(*WFF CODE ENDS*)