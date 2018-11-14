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

(* gets length of list *)
fun len(L) = case L of []=> 0| x::xs => 1+len(xs);
fun list_contains(L,element) = case L of
								[] => false
							|   x::xs => if(x=element) then true else list_contains(xs,element);
(* fun numberofAppearance(L, element, result) = case L of [] => result
													|  x::xs => if(x=element) then numberofAppearance(xs, element, result+1)
																else numberofAppearance(xs, element ,result); *)


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



fun pred_list_consistent(predList) = pred_list_consistent_temp(predList, predList);
fun term_list_consistent(termList) = term_list_consistent_temp(termList, termList);

fun get_different_preds(pred_list, pred_list_copy, result) = case pred_list of [] => result
														| x::xs => 	case x of (p,value) =>
																	if (contains_different_pred(x, pred_list_copy)=false) then get_different_preds(xs,pred_list_copy, result) else get_different_preds(xs,pred_list_copy, result@[p]);

fun get_different_terms(term_list, term_list_copy, result) = case term_list of [] => result
														| x::xs => case x of (t,value) =>
																	if (contains_different_term(x, term_list_copy)=false) then get_different_terms(xs,term_list_copy, result) else get_different_terms(xs,term_list_copy, result@[t]);


fun term_list_to_string(l) = case l of
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

fun getFV_from_termlist(t_list, closed_tracker, result) = case t_list of
													[] => result
												|	C(s)::xs => getFV_from_termlist(xs, closed_tracker, result)
												| 	V(s)::xs => if(list_contains(closed_tracker, V(s))) 
																then getFV_from_termlist(xs, closed_tracker, result)
																else if(list_contains(closed_tracker, V(s))=false andalso (list_contains(result, V(s)))=false)
																then getFV_from_termlist(xs, closed_tracker, result@[V(s)])
															    else getFV_from_termlist(xs, closed_tracker, result)
												|   F(s,t)::xs => getFV_from_termlist(xs, closed_tracker, getFV_from_termlist(t, closed_tracker, result));

fun fv_temp(formula, closed_tracker) = case formula of 
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

					