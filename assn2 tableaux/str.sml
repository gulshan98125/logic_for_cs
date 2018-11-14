structure PropLogicTableau : PropLogicTableau = struct

exception Atom_exception
datatype Prop =
		ATOM of string |
		NOT of Prop |
		AND of Prop * Prop |
		OR of Prop * Prop |
		COND of Prop * Prop |
		BIC of Prop * Prop
type Argument = Prop list * Prop;

fun rewrite (ATOM a) = ATOM a
| rewrite (NOT (O)) = NOT (rewrite (O))
| rewrite (AND (O, Q)) = AND (rewrite (O) , rewrite (Q))
| rewrite (OR (O, Q)) = OR (rewrite (O) , rewrite (Q) )
| rewrite (COND (O, Q)) = OR (NOT (rewrite (O)) , rewrite (Q))
| rewrite (BIC (O, Q)) = AND (rewrite (COND (O, Q)), rewrite (COND (Q, O)))
;

fun nnf (ATOM a) = ATOM a
| nnf (NOT (ATOM a)) = NOT (ATOM a)
| nnf (NOT (NOT (O))) = nnf (O)
| nnf (AND (O ,Q)) = AND (nnf (O) , nnf (Q))
| nnf (NOT (AND (O, Q))) = nnf (OR (NOT (O), NOT (Q)))
| nnf (OR (O, Q)) = OR (nnf (O) , nnf (Q))
| nnf (NOT (OR (O, Q))) = nnf (AND (NOT (O), NOT (Q)))
;

datatype Node = NODE of Prop;
datatype Nodemap = NODEMAP of Node*int;
datatype Ancestor = ANCESTOR of int * int; (* here 1st int is ancestor of 2nd *)
datatype Tree = TREE of int*int;
datatype Closed = CLOSED of int*int;


exception empty;
fun get(L,x) = case L of [] => raise empty| q::qs => if(x=0) then q else get(qs,x-1);
fun len(L) = case L of []=> 0| x::xs => 1+len(xs);
fun getIndex(L,element,startIndex) = case L of [] => ~1
								| x::xs => if(x=element) then startIndex else getIndex(xs,element,startIndex+1);

(****************************************helper functions start**********************************************)
(* fun nodelist_contains_complement_and_index(L,node) = case (L,node) of 
																([],node) => (false,~1)
															|	(L,NODE(ATOM(A))) => 	   let 
																					val index = getIndex(L,NODE(NOT(ATOM(A))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|  	(L,NODE(NOT(ATOM(B)))) => let
																						val index = getIndex(L,NODE(ATOM(B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|  	(L,_) => (false,~1);  *)

fun nodelist_contains_complement_and_index(L,node) = case (L,node) of 
																([],node) => (false,~1)
															|	(L,NODE(NOT(NOT(P)))) => let 
																					val index = getIndex(L,NODE(NOT(P)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|	(L,NODE(ATOM(A))) => let 
																					val index = getIndex(L,NODE(NOT(ATOM(A))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|  	(L,NODE(NOT(ATOM(B)))) => let
																						val index = getIndex(L,NODE(ATOM(B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|   (L, NODE(AND(A,B))) => let
																						val index = getIndex(L,NODE(NOT(AND(A,B))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|   (L, NODE(NOT(AND(A,B)))) => let 
																					val index = getIndex(L,NODE(AND(A,B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															
															| 	(L, NODE(OR(A,B))) 	=> let
																						val index = getIndex(L,NODE(NOT(OR(A,B))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|   (L, NODE(NOT(OR(A,B)))) => let 
																					val index = getIndex(L,NODE(OR(A,B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															| 	(L, NODE(COND(A,B))) 	=> let
																						val index = getIndex(L,NODE(NOT(COND(A,B))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|   (L, NODE(NOT(COND(A,B)))) => let 
																					val index = getIndex(L,NODE(COND(A,B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															| 	(L, NODE(BIC(A,B))) 	=> let
																						val index = getIndex(L,NODE(NOT(BIC(A,B))),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end
															|   (L, NODE(NOT(BIC(A,B)))) => let 
																					val index = getIndex(L,NODE(BIC(A,B)),0);
																					in
																						if(index <> ~1) then (true,index) else (false,~1)
																					end;


fun list_contains(L,element) = case L of
								[] => false
							|   x::xs => if(x=element) then true else list_contains(xs,element);

fun remove_from_list(L,element,res) = case L of
								  		[] => res
								  	|   x::xs => if(x=element) then res@xs else remove_from_list(xs, element,res@[x]);

fun replace_with_lists(list_of_list,index,L1,L2) = case (index,list_of_list) of 
													(0,x::xs) => L1::L2::xs
												|   (index,x::xs) => x::replace_with_lists(xs,index-1,L1,L2); 

fun replace_with_a_list(list_of_list,index,L) = case (index,list_of_list) of 
													(0,x::xs) => L::xs
												|   (index,x::xs) => x::replace_with_a_list(xs,index-1,L);

(*replaces an oldList with newList in the list_of_list*)
fun replace_with_a_list2(list_of_list,oldList,newList) = case list_of_list of
														x::xs => if(x=oldList) 
																then newList::xs
																else x::(replace_with_a_list2(xs,oldList,newList));

fun replace_with_lists2(list_of_list,oldList,newList1,newList2) = case list_of_list of 
																 x::xs => if(x=oldList)
																 		then newList1::newList2::xs
																 		else x::replace_with_lists2(xs,oldList,newList1,newList2);


fun contains_complementary(L,element) = case L of
										[] => false
									| x::xs => if(x=NOT(element)) then true else contains_complementary(xs,element);

fun list_satisfiable2(L1,L2) = case (L1,L2) of
							(L1,[]) => true
						| (L1,x::xs) => if(contains_complementary(L1,x)) then false else list_satisfiable2(L1,xs);

(*checks if prop list contains a complement, if it does then return false else true*)
fun list_satisfiable(L) = list_satisfiable2(L,L);

fun isAnAtom(p) = case p of
						ATOM(c) => true
					|   NOT(ATOM(Q)) => true
					|   NOT(NOT(ATOM(D))) => true
					|   _ => false;
fun list_contains_prop(L) = case L of 
									[] => false
								| x::xs => if(isAnAtom(x)) then list_contains_prop(xs) else true;

(*if list contains the element then returns (list,true) else appends element to the list and returns the (updated_list,false)*)
fun does_it_contain_else_add(L,element) = if (list_contains(L,element)=true) then (L,true) else (L@[element],false);

fun unsat2(list_of_list,length) = case (list_of_list, length) of 
													([],0) => true
												|   (x::xs,length) => if(list_satisfiable(x)=false) then unsat2(xs,length-1) else false; 

fun can_be_branced(propList) = case propList of [] => false
													| 	OR(A,B)::xs => true
													| 	NOT(AND(A,B))::xs => true
													|   COND(A,B)::xs  => true
													| 	BIC(A,B)::xs => true
													| 	NOT(BIC(A,B))::xs => true
													|   _::xs => can_be_branced(xs);

fun can_be_elongated(propList) = case propList of [] => false
													| 	AND(A,B)::xs => true
													|   NOT(OR(A,B))::xs => true
													| 	NOT(COND(A,B))::xs => true
													|   NOT(NOT(P))::xs => true
													|   _::xs => can_be_elongated(xs);

(****************************************helper functions end**********************************************)


(*
propArr = list of list of propostions, a list of prop corresponds to a branch
nodeArr = list of list of nodes, it stores the nodes of all branches in the list, NODE(prop)
globalVar = this is used to label nodes according to integers
ancestorMapArr = this is a list which stores ANCESTOR(x,y) which means x is ancestor of y
closedArr = this stores CLOSED(x,y) which means x and y are complement of each other and closes that branch path
nodeMapArr = this stores the nodes which are connected in the graph
nodeIntArr = is similar to nodeArr but instead of NODE it contains numbers that is mapped to that node
list_index = this is index of the prop list on which work is performed on that time

*)

(*this function takes a proposition list as input and
works for a the first proposition it encounter on that list, just 1 proposition, and updates arrays accordingly*)
(*If OR(a,b) is encountered then the list is replicated and a is added to 1st list and b is added to 2nd list*)
(*If AND(a,b) is encountered then a and b are added on the same list*)

(*BELOW IS THE IMPLEMENTATION OF TABLEAU RULES*)

(*THIS WORKS ON CASES WHICH ARE SIMILAR TO AND, elongation ones*)
fun propListWorker_AND(propList,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index) =
		case propList of [] => true
					|  NOT(NOT(P))::xs => 
									let
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updated_propList = [P]@remove_from_list(propListCopy,NOT(NOT(P)),[]);
										val updated_propArrList2 = replace_with_a_list(propArrList2,list_index,updated_propList);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement1,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(NOT(NOT(P))));
										val replacement2 = replacement1@[NODE(P)];
										val updated_nodeArrList2 = replace_with_a_list(nodeArrList2,list_index,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2 = if(truthVaue=false) 
																	then 
																		nodeIntList2@[!globalVar]@[!globalVar+1]
																	else 
																		nodeIntList2@[!globalVar+1]
										val updated_nodeIntArrList2 = replace_with_a_list(nodeIntArrList2,list_index,updated_nodeIntList2);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(NOT(NOT(P))),!globalVar)]@[NODEMAP(NODE(P),!globalVar+1)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);

										(*ancestor work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(NOT(NOT(P))),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(P));
										val updated_closedArrList2 = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2);


										val temp = globalVar := !globalVar + 2;

									in
										true
									end

					| 	AND(A,B)::xs => (*now work on it and update the arrays*)
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updated_propList = [A,B]@remove_from_list(propListCopy,AND(A,B),[]);
										val updated_propArrList2 = replace_with_a_list(propArrList2,list_index,updated_propList);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement1,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(AND(A,B)));
										val replacement2 = replacement1@[NODE(A),NODE(B)];
										val updated_nodeArrList2 = replace_with_a_list(nodeArrList2,list_index,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2 = if(truthVaue=false) 
																	then 
																		nodeIntList2@[!globalVar]@[!globalVar+1]@[!globalVar+2]
																	else 
																		nodeIntList2@[!globalVar+1]@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_a_list(nodeIntArrList2,list_index,updated_nodeIntList2);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(AND(A,B)),!globalVar)]@[NODEMAP(NODE(A),!globalVar+1)]@[NODEMAP(NODE(B),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);

										(*ancestor work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(AND(A,B)),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(A));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(B));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);


										val temp = globalVar := !globalVar + 3;

									in
										true
									end
					| 	NOT(OR(A,B))::xs => (*now work on it and update the arrays*)
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updated_propList = [NOT(A),NOT(B)]@remove_from_list(propListCopy,NOT(OR(A,B)),[]);
										val updated_propArrList2 = replace_with_a_list(propArrList2,list_index,updated_propList);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement1,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(NOT(OR(A,B))));
										val replacement2 = replacement1@[NODE(NOT(A)),NODE(NOT(B))];
										val updated_nodeArrList2 = replace_with_a_list(nodeArrList2,list_index,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2 = if(truthVaue=false) 
																	then 
																		nodeIntList2@[!globalVar]@[!globalVar+1]@[!globalVar+2]
																	else 
																		nodeIntList2@[!globalVar+1]@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_a_list(nodeIntArrList2,list_index,updated_nodeIntList2);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(NOT(OR(A,B))),!globalVar)]@[NODEMAP(NODE(NOT(A)),!globalVar+1)]@[NODEMAP(NODE(NOT(B)),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);

										(*ancestor work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(NOT(OR(A,B))),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(A)));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(B)));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);


										val temp = globalVar := !globalVar + 3;

									in
										true
									end
					| 	NOT(COND(A,B))::xs => (*now work on it and update the arrays*)
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updated_propList = [A,NOT(B)]@remove_from_list(propListCopy,NOT(COND(A,B)),[]);
										val updated_propArrList2 = replace_with_a_list(propArrList2,list_index,updated_propList);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement1,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(NOT(COND(A,B))));
										val replacement2 = replacement1@[NODE(A),NODE(NOT(B))];
										val updated_nodeArrList2 = replace_with_a_list(nodeArrList2,list_index,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2 = if(truthVaue=false) 
																	then 
																		nodeIntList2@[!globalVar]@[!globalVar+1]@[!globalVar+2]
																	else 
																		nodeIntList2@[!globalVar+1]@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_a_list(nodeIntArrList2,list_index,updated_nodeIntList2);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(NOT(COND(A,B))),!globalVar)]@[NODEMAP(NODE(A),!globalVar+1)]@[NODEMAP(NODE(NOT(B)),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);

										(*ancestor work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(NOT(COND(A,B))),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(A));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(B)));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);


										val temp = globalVar := !globalVar + 3;

									in
										true
									end
					|   _::xs =>  propListWorker_AND(xs,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index);



(*THIS WORKS ON CASES WHICH ARE SIMILAR TO OR, Branching ones*)
fun propListWorker_OR(propList,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index) = 
		case propList of [] => true 
					|   NOT(AND(A,B))::xs  =>
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updatedList1 = [NOT(A)]@remove_from_list(propListCopy,NOT(AND(A,B)),[]);
										val updatedList2 = [NOT(B)]@remove_from_list(propListCopy,NOT(AND(A,B)),[]);
										val updated_propArrList2 = replace_with_lists(propArrList2,list_index,updatedList1,updatedList2);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(NOT(AND(A,B))));
										val replacement1 = replacement@[NODE(NOT(A))];
										val replacement2 = replacement@[NODE(NOT(B))];
										val updated_nodeArrList2 = replace_with_lists(nodeArrList2,list_index,replacement1,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2_one = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+1]
																		else 
																			nodeIntList2@[!globalVar+1];
										val updated_nodeIntList2_two = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+2]
																		else 
																			nodeIntList2@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_lists(nodeIntArrList2,list_index,updated_nodeIntList2_one,updated_nodeIntList2_two);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(NOT(AND(A,B))),!globalVar)]@[NODEMAP(NODE(NOT(A)),!globalVar+1)]@[NODEMAP(NODE(NOT(B)),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);



										(*ancestorMapArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeArrList2 = Array.sub(nodeArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(NOT(AND(A,B))),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(A)));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(B)));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);

										val temp = globalVar := !globalVar + 3;

									in
										true
									end

					|   OR(A,B)::xs  =>
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updatedList1 = [A]@remove_from_list(propListCopy,OR(A,B),[]);
										val updatedList2 = [B]@remove_from_list(propListCopy,OR(A,B),[]);
										val updated_propArrList2 = replace_with_lists(propArrList2,list_index,updatedList1,updatedList2);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(OR(A,B)));
										val replacement1 = replacement@[NODE(A)];
										val replacement2 = replacement@[NODE(B)];
										val updated_nodeArrList2 = replace_with_lists(nodeArrList2,list_index,replacement1,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2_one = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+1]
																		else 
																			nodeIntList2@[!globalVar+1];
										val updated_nodeIntList2_two = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+2]
																		else 
																			nodeIntList2@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_lists(nodeIntArrList2,list_index,updated_nodeIntList2_one,updated_nodeIntList2_two);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(OR(A,B)),!globalVar)]@[NODEMAP(NODE(A),!globalVar+1)]@[NODEMAP(NODE(B),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);



										(*ancestorMapArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeArrList2 = Array.sub(nodeArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(OR(A,B)),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(A));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(B));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);

										val temp = globalVar := !globalVar + 3;

									in
										true
									end

					

					|   COND(A,B)::xs  =>
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updatedList1 = [NOT(A)]@remove_from_list(propListCopy,COND(A,B),[]);
										val updatedList2 = [B]@remove_from_list(propListCopy,COND(A,B),[]);
										val updated_propArrList2 = replace_with_lists(propArrList2,list_index,updatedList1,updatedList2);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(COND(A,B)));
										val replacement1 = replacement@[NODE(NOT(A))];
										val replacement2 = replacement@[NODE(B)];
										val updated_nodeArrList2 = replace_with_lists(nodeArrList2,list_index,replacement1,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2_one = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+1]
																		else 
																			nodeIntList2@[!globalVar+1];
										val updated_nodeIntList2_two = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+2]
																		else 
																			nodeIntList2@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_lists(nodeIntArrList2,list_index,updated_nodeIntList2_one,updated_nodeIntList2_two);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(COND(A,B)),!globalVar)]@[NODEMAP(NODE(NOT(A)),!globalVar+1)]@[NODEMAP(NODE(B),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);



										(*ancestorMapArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeArrList2 = Array.sub(nodeArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(COND(A,B)),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(NOT(A)));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(B));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);

										val temp = globalVar := !globalVar + 3;

									in
										true
									end

					|   BIC(A,B)::xs  =>
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updatedList1 = [AND(A,B)]@remove_from_list(propListCopy,BIC(A,B),[]);
										val updatedList2 = [AND(NOT(A),NOT(B))]@remove_from_list(propListCopy,BIC(A,B),[]);
										val updated_propArrList2 = replace_with_lists(propArrList2,list_index,updatedList1,updatedList2);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(BIC(A,B)));
										val replacement1 = replacement@[NODE(AND(A,B))];
										val replacement2 = replacement@[NODE(AND(NOT(A),NOT(B)))];
										val updated_nodeArrList2 = replace_with_lists(nodeArrList2,list_index,replacement1,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2_one = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+1]
																		else 
																			nodeIntList2@[!globalVar+1];
										val updated_nodeIntList2_two = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+2]
																		else 
																			nodeIntList2@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_lists(nodeIntArrList2,list_index,updated_nodeIntList2_one,updated_nodeIntList2_two);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(BIC(A,B)),!globalVar)]@[NODEMAP(NODE(AND(A,B)),!globalVar+1)]@[NODEMAP(NODE(AND(NOT(A),NOT(B))),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);



										(*ancestorMapArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeArrList2 = Array.sub(nodeArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(BIC(A,B)),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(AND(A,B)));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(AND(NOT(A),NOT(B))));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);

										val temp = globalVar := !globalVar + 3;

									in
										true
									end

					|   NOT(BIC(A,B))::xs  =>
									let
										(* val propArrList2 = Array.sub(propArr,0); *)
										(* val nodeArrList2 = Array.sub(nodeArr,0); *)
										(* val nodeIntArrList2 = Array.sub(nodeIntArr,0); *)
										(* val nodeMapArrList2 = Array.sub(nodeMapArr,0); *)
										(* val ancestorMapArrList2 = Array.sub(ancestorMapArr,0); *)
										val closedArrList2 = Array.sub(closedArr,0); 
										
										(*propArr update work below*)
										val propArrList2 = Array.sub(propArr,0);
										val updatedList1 = [AND(A,NOT(B))]@remove_from_list(propListCopy,NOT(BIC(A,B)),[]);
										val updatedList2 = [AND(NOT(A),B)]@remove_from_list(propListCopy,NOT(BIC(A,B)),[]);
										val updated_propArrList2 = replace_with_lists(propArrList2,list_index,updatedList1,updatedList2);
										val updating_propArr = Array.update(propArr,0,updated_propArrList2);

										(*nodeArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val (replacement,truthVaue) = does_it_contain_else_add(get(nodeArrList2,list_index),NODE(NOT(BIC(A,B))));
										val replacement1 = replacement@[NODE(AND(A,NOT(B)))];
										val replacement2 = replacement@[NODE(AND(NOT(A),B))];
										val updated_nodeArrList2 = replace_with_lists(nodeArrList2,list_index,replacement1,replacement2);
										val updating_nodeArr = Array.update(nodeArr,0,updated_nodeArrList2);

										(*nodeIntArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val updated_nodeIntList2_one = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+1]
																		else 
																			nodeIntList2@[!globalVar+1];
										val updated_nodeIntList2_two = if (truthVaue = false) 
																		then 
																			nodeIntList2@[!globalVar]@[!globalVar+2]
																		else 
																			nodeIntList2@[!globalVar+2];
										val updated_nodeIntArrList2 = replace_with_lists(nodeIntArrList2,list_index,updated_nodeIntList2_one,updated_nodeIntList2_two);
										val updating_nodeIntArr = Array.update(nodeIntArr,0,updated_nodeIntArrList2);

										(*nodeMapArr work below*)
										val nodeMapArrList2 = Array.sub(nodeMapArr,0);
										val updated_nodeMapArrList2 = nodeMapArrList2@[NODEMAP(NODE(NOT(BIC(A,B))),!globalVar)]@[NODEMAP(NODE(AND(A,NOT(B))),!globalVar+1)]@[NODEMAP(NODE(AND(NOT(A),B)),!globalVar+2)];
										val updating_nodeMapArr = Array.update(nodeMapArr,0,updated_nodeMapArrList2);



										(*ancestorMapArr work below*)
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val nodeArrList2 = Array.sub(nodeArr,0);
										val ancestorMapArrList2 = Array.sub(ancestorMapArr,0);
										val location = if(truthVaue = true) then getIndex(get(nodeArrList2,list_index),NODE(NOT(BIC(A,B))),0) else ~1;
										val nodeIntList2 = get(nodeIntArrList2,list_index);
										val parentValue = if (location <> ~1) then get(nodeIntList2,location) else ~1;
										val updated_ancestormapArrList2 = if(location <> ~1) then 
																								ancestorMapArrList2@[ANCESTOR(parentValue,!globalVar+1)]@[ANCESTOR(parentValue,!globalVar+2)] 
																							else 
																								ancestorMapArrList2;
										val updating_ancestorMapArr = Array.update(ancestorMapArr,0,updated_ancestormapArrList2);

										(*closedArr work below*)
										val nodeArrList2 = Array.sub(nodeArr,0);
										val closedArrList2 = Array.sub(closedArr,0);
										val nodeIntArrList2 = Array.sub(nodeIntArr,0);
										val (value,loc) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(AND(A,NOT(B))));
										val (value1,loc1) = nodelist_contains_complement_and_index(get(nodeArrList2,list_index),NODE(AND(NOT(A),B)));
										val updated_closedArrList2_one = if(loc <> ~1) then closedArrList2@[CLOSED(get(nodeIntList2,loc),!globalVar+1)] else closedArrList2;
										val updated_closedArrList2_two = if(loc1 <> ~1) then updated_closedArrList2_one@[CLOSED(get(nodeIntList2,loc1),!globalVar+2)] else updated_closedArrList2_one;
										val updating_closedArr = Array.update(closedArr,0,updated_closedArrList2_two);

										val temp = globalVar := !globalVar + 3;

									in
										true
									end
					|   _::xs =>  propListWorker_OR(xs,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index);

(* fun propListWorker_OTHER(propList,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index) = 
				case propList of [] => true
					
					|   _::xs =>  propListWorker_AND(xs,propListCopy,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index); *)

(*this function goes thorugh the propArr and updates it if required*)
fun propWorker(propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index) =
				let
					val propArrList = Array.sub(propArr,0);
					val nodeArrList = Array.sub(nodeArr,0);
					val nodeIntArrList = Array.sub(nodeIntArr,0);
					val nodeMapArrList = Array.sub(nodeMapArr,0);
					val ancestorMapArrList = Array.sub(ancestorMapArr,0);
					val closedArrList = Array.sub(closedArr,0);

					val index_max_value = len(propArrList);
					val propList = if(list_index = index_max_value) then [] else get(propArrList,list_index);

				in
					if(list_index = index_max_value)
					then
						(propArrList,nodeArrList,nodeIntArrList,nodeMapArrList,ancestorMapArrList,closedArrList)
					else
						
						(*if the working list doesn't contain complements and it still contains proposition then work on it*)
						if(list_satisfiable(propList) = true andalso list_contains_prop(propList)=true)
						then (*work on that list using propListWorker and call propWorker again from the start*)
							
							if(can_be_elongated(propList)) then
									let
										val work_done = propListWorker_AND(propList,propList,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index);
									in
										propWorker(propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,0)
									end
							else
									let
										val work_done = propListWorker_OR(propList,propList,propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index);
									in
										propWorker(propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,0)
									end
							
							
						else
							(* call list worker with list index of list+1 *)
							propWorker(propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,list_index+1)
				end;

(*--------------------------------------MAIN FUNCTION---------------------------------*)
fun main(prop) = let
					val propArr = Array.array(1,[[prop]]);
					val nodeArr = Array.array(1,[[]]);
					val globalVar = ref 0;
					val nodeIntArr = Array.array(1,[[]]);
					val nodeMapArr = Array.array(1,[]);
					val ancestorMapArr = Array.array(1,[]);
					val closedArr = Array.array(1,[]);
				in
					propWorker(propArr,nodeArr,nodeIntArr,globalVar,nodeMapArr,ancestorMapArr,closedArr,0)
				end;
(*--------------------------------------MAIN FUNCTION---------------------------------*)


fun closed(prop) = let
						val (propArrList,nodeArrList,nodeIntArrList,nodeMapArrList,ancestorMapArrList,closedArrList) = main(prop);
					in
						unsat2(propArrList,len(propArrList))
					end;



(*file printing related code from below onwards*)

(*for a given number gives the Node that is mapped to it*)
fun getNodeMap(number,nodemapList) = case nodemapList of [] => raise empty 
														|	x::xs => case x of 
																			NODEMAP(A,B) => if (B=number) then NODEMAP(A,B) else getNodeMap(number,xs);

fun treeupdate1(nodeIntList,treeArr,travelledArr,startIndex,nodeIntList2) = let
																	val treeList = Array.sub(treeArr,0);
																	val travelledList = Array.sub(travelledArr,0);
																in
																	case nodeIntList of [] => true
																			|  x::xs => if(list_contains(travelledList,x) = false) then
																																let 
																																	val temp = Array.update(travelledArr,0,travelledList@[x]);
																																	val temp2 = Array.update(treeArr,0,treeList@[TREE(get(nodeIntList2,startIndex-1),x)]);
																																in
																																	treeupdate1(xs,treeArr,travelledArr,startIndex+1,nodeIntList2)
																																end
																						else 
																							treeupdate1(xs,treeArr,travelledArr,startIndex+1,nodeIntList2)
																end;

fun tree_temp(nodeIntListList,treeArr,travelledArr) = case nodeIntListList of
																[] => (Array.sub(treeArr,0),Array.sub(travelledArr,0))
															|   x::xs => let
																			val temp = treeupdate1(x,treeArr,travelledArr,0,x);
																		 in
																		 	tree_temp(xs,treeArr,travelledArr)
																		 end;
fun final_treeList(nodeIntListList) = let
										 val treeArr = Array.array(1,[]);
										 val travelledArr = Array.array(1,[0]);
										in
											tree_temp(nodeIntListList,treeArr,travelledArr)
										end;

(*returns TREE nodes and the travelled nodes indexes useful in graph file writing*)
fun treeList_and_travelled(prop) = let
						val (propArrList,nodeArrList,nodeIntArrList,nodeMapArrList,ancestorMapArrList,closedArrList) = main(prop);
					 in
					 	final_treeList(nodeIntArrList)
					 end;

fun updatedAncesorList(ancestorList,treeList,result) = case (ancestorList,result) of 
																	([],result) => result
																| 	((ANCESTOR(x,y))::xs,result) => if(list_contains(treeList,TREE(x,y))=false) then updatedAncesorList(xs,treeList,result@[ANCESTOR(x,y)]) else updatedAncesorList(xs,treeList,result);

fun updatedNodemapList(nodemapList,travelledList,result) = case (nodemapList,result) of
																([],result) => result
															|  	((NODEMAP(A,integer))::xs,result) => if(list_contains(travelledList,integer)=true) then updatedNodemapList(xs,travelledList,result@[NODEMAP(A,integer)]) else updatedNodemapList(xs,travelledList,result);

(*returns TREE nodes, ANCESTOR nodes, CLOSED and NODEMAP nodes which contains information about the nodes of the graph*)
fun tree_ancestor_closed_nodemap(prop) = let
									val (propArrList,nodeArrList,nodeIntArrList,nodeMapArrList,ancestorMapArrList,closedArrList) = main(prop);
									val (treeList,travelledList) = final_treeList(nodeIntArrList);
									val ancestorList = updatedAncesorList(ancestorMapArrList,treeList,[]);
									val nodemapList = updatedNodemapList(nodeMapArrList,travelledList,[]);
								 in
								 	(treeList,ancestorList,closedArrList,nodemapList)
								 end;

(*val (T,A,C,N) = tree_ancestor_closed_nodemap(prop); *)

fun tree_toString(treenode) = case treenode of TREE(x,y) => Int.toString(x)^" -> "^Int.toString(y)^";";

fun ancestor_toString(ancestornode) = case ancestornode of ANCESTOR(x,y) => Int.toString(x)^" -> "^Int.toString(y)^";";

fun closed_toString(closednode) = case closednode of CLOSED(x,y) => Int.toString(x)^" -> "^Int.toString(y)^";";

fun prop_toString(prop) = case prop of ATOM(x) => x
									|  NOT(P)  => "\\neg " ^ prop_toString(P)
									|  COND(A,B) => "(" ^prop_toString(A) ^ " \\rightarrow " ^ prop_toString(B) ^")"
									|  BIC(A,B) => "(" ^prop_toString(A) ^ " \\leftrightarrow " ^ prop_toString(B) ^")"
									|  AND(A,B) =>  "(" ^prop_toString(A) ^ " \\wedge " ^ prop_toString(B) ^")"
									|  OR(A,B)  =>  "(" ^prop_toString(A) ^ " \\vee " ^ prop_toString(B) ^")";

(* fun prop_toString(prop) = case prop of ATOM(x) => x
									|  NOT(P)  => "~" ^ prop_toString(P)
									|  COND(A,B) => "(" ^prop_toString(A) ^ " COND " ^ prop_toString(B) ^")"
									|  BIC(A,B) => "(" ^prop_toString(A) ^ " BIC " ^ prop_toString(B) ^")"
									|  AND(A,B) =>  "(" ^prop_toString(A) ^ " ^ " ^ prop_toString(B) ^")"
									|  OR(A,B)  =>  "(" ^prop_toString(A) ^ " v " ^ prop_toString(B) ^")"; *)

fun nodemap_toString(nodemap) = case nodemap of NODEMAP(NODE(prop),x) => Int.toString(x)^" "^"[texlbl=\"\\underline{"^Int.toString(x)^". {\\LARGE \\color{green} $" ^ prop_toString(prop) ^"$}}\"];";
(* fun nodemap_toString(nodemap) = case nodemap of NODEMAP(NODE(prop),x) => Int.toString(x)^" [label=\"" ^ prop_toString(prop) ^"\"];"; *)

val stringList1 = ["digraph{","ranksep = 0.35;","node [shape=plaintext];"];
val stringList2 = ["subgraph dir","{"];
val stringList3 = ["}","subgraph ancestor","{","edge [dir=back, color=blue, style=dashed]"];
val stringList4 = ["}","subgraph undir","{","edge [dir=none, color=red]"];
val stringList5 = ["}","}"];

fun nodemapList_toStringList(nodemapList,res) = case (nodemapList,res) of ([],res) => res
												|  	 (x::xs,res) =>  nodemapList_toStringList(xs,res@[nodemap_toString(x)]);

fun treeList_toStringList(treeList,res) = case (treeList,res) of ([],res) => res
												|  	 (x::xs,res) =>  treeList_toStringList(xs,res@[tree_toString(x)]);

fun ancestorList_toStringList(ancestorList,res) = case (ancestorList,res) of ([],res) => res
												|  	 (x::xs,res) =>  ancestorList_toStringList(xs,res@[ancestor_toString(x)]);

fun closedList_toStringList(closedList,res) = case (closedList,res) of ([],res) => res
												|  	 (x::xs,res) =>  closedList_toStringList(xs,res@[closed_toString(x)]);



fun final_string_list(prop) = let
								val (propArrList,nodeArrList,nodeIntArrList,nodeMapArrList,ancestorMapArrList,closedArrList) = main(prop);
								(* val (list_of_list,nodeIntListList,nodemapList,ancestorList,closedList) = tableau2(prop); *)
								val (treeList,travelledList) = final_treeList(nodeIntArrList);
								val ancestorList = updatedAncesorList(ancestorMapArrList,treeList,[]);
								val nodemapList = updatedNodemapList(nodeMapArrList,travelledList,[]);
								
								val nodemapStringList = nodemapList_toStringList(nodemapList,[]);
								val treeStringList = treeList_toStringList(treeList,[]);
								val ancestorStringList = ancestorList_toStringList(ancestorList,[]);
								val closedStringList = closedList_toStringList(closedArrList,[]);
							  in
							  	(* stringList1@nodemapStringList@stringList2@treeStringList@stringList3@ancestorStringList@stringList4@closedStringList@stringList5 *)
							  	stringList1@nodemapStringList@stringList2@treeStringList@stringList3@stringList4@closedStringList@stringList5
							  end;

fun write(outFile: string, list: string list) =
  let
    val outStream = TextIO.openOut outFile
    fun out(xs : string list) =  
          case xs of
              [] => (TextIO.closeOut outStream)
            | x::xs' => (TextIO.output(outStream, x ^ "\r\n"); out(xs'))
  in
    out(list)
  end;

fun list_to_prop(L) = case L of x::[] => x
							|  x::xs => AND(list_to_prop(xs),x); 

fun isClosed(propList) = closed(list_to_prop(propList));

fun tableau(propList) = write("arg.dot",final_string_list(list_to_prop(propList)));

fun read file =
let val inStream = TextIO.openIn file

in
        TextIO.input1 inStream
end;


end;
