val perceive = ATOM "a";
val delusive = ATOM "b";
val veridical = ATOM "c";
val something = ATOM "d";
val material = ATOM "e";
val sensation = ATOM "f";
val differ = ATOM "g";

val h1 = COND (perceive, NOT (BIC (delusive, veridical)));
val h2 = COND (delusive, AND (perceive, NOT (material)));
val h3 = COND (AND (perceive, NOT (material)), sensation);
val h4 = COND (veridical, perceive);
val h5 = COND (AND (veridical, material), differ);
val h6 = NOT (differ);
val c = COND (perceive, AND (sensation, NOT (material)));
val arg = ([h1,h2,h3,h4,h5,h6],c);